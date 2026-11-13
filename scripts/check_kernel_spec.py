#!/usr/bin/env python3
"""Coverage gate for the compiled kernel.

For every `@[export llb_*]` function of BitcoinLedger/FreestandingKernels.lean this
checks, and fails otherwise, that:

1. it is named in a statement of Spec.lean, or is listed in PENDING below with the
   reason it has no statement yet;
2. every statement of Spec.lean has a theorem of that type in Proofs/KernelSpec.lean
   and is part of `Spec.KernelSpec`;
3. the set of exports that neither app calls is exactly NOT_CALLED below, so a new
   dead export, or a newly used one, has to be acknowledged here.

Run from the repository root: `python3 scripts/check_kernel_spec.py`.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KERNEL = ROOT / "BitcoinLedger" / "FreestandingKernels.lean"
SPEC = ROOT / "Spec.lean"
PROOFS = ROOT / "Proofs" / "KernelSpec.lean"
BOLOS_PATCH = ROOT / "ffi" / "bolos" / "patches" / "app-bitcoin-lean-opt.patch"
VND_PATCH = ROOT / "ffi" / "vanadium" / "patches" / "vanadium-bitcoin-lean-opt.patch"
VND_LIB = ROOT / "ffi" / "vanadium" / "src" / "lib.rs"

# Exports without a statement in Spec.lean yet, and why.
MODEL = "proved equal to a definition of the app model (Proofs/FreestandingKernels.lean), not yet restated in Spec.lean"
BUFFER = "reads or writes a buffer; the kernel has no memory model yet, so no statement about it can be written"
PENDING = {
    "llb_version_packed": "constant",
    "llb_bip32_standard_purpose_ok": MODEL,
    "llb_bip32_pubkey_export_prefix_ok": MODEL,
    "llb_bech32_polymod_step": MODEL,
    "llb_bech32_final_constant": "constant table",
    "llb_minimal_push_opcode_ok": "only soundness is proved (Proofs/FreestandingKernels.lean)",
    "llb_merkle_depth_index_ok": MODEL,
    "llb_merkle_advance_state": MODEL,
    "llb_merkle_state_dir": MODEL,
    "llb_bolos_sw_for_error": MODEL,
    "llb_wallet_name_char_ok": "restates its implementation; needs an independent statement",
    "llb_miniscript_older_ok": MODEL,
    "llb_miniscript_after_ok": MODEL,
    "llb_miniscript_andor_branches_valid": "restates its implementation; needs an independent statement",
    "llb_psbt_locktime_init": MODEL,
    "llb_psbt_locktime_step": MODEL,
    "llb_psbt_locktime_finalize": MODEL,
    "llb_bip32_harden": "not called by either app",
    "llb_miniscript_check_postfix": BUFFER + "; only its combinators are proved",
    "llb_psbt_determine_locktime": BUFFER,
    "llb_bytes_eq": BUFFER,
    "llb_check_dual_utxo": BUFFER,
    "llb_sum_amounts_le64": BUFFER,
    "llb_bip32_check_export_path": BUFFER,
    "llb_read_compact_size_checked": BUFFER,
    "llb_sort_fixed_bytes": BUFFER + "; no theorem at all",
    "llb_sort_u16": BUFFER + "; no theorem at all",
    "llb_format_sats_ascii": BUFFER + "; no theorem at all",
}

# Exports that neither app calls in a release build. They should be removed from the
# export list the next time the generated IR and the patches are regenerated.
NOT_CALLED = {
    "llb_varint_encoded_len",
    "llb_bip32_harden",
    "llb_bip32_standard_purpose_ok",
    "llb_bech32_polymod_step",
    "llb_minimal_push_opcode_ok",
    "llb_merkle_depth_index_ok",
    "llb_bolos_sw_for_error",
    "llb_sats_div_1e8",
    "llb_sats_mod_1e8",
    "llb_merkle_state_dir",
    "llb_psbt_determine_locktime",
    "llb_bytes_eq",
    "llb_sum_amounts_le64",
    "llb_miniscript_andor_branches_valid",
}


def exports():
    text = KERNEL.read_text()
    pairs = re.findall(r"@\[export (llb_\w+)\]\s*\n(?:@\[[^\]]*\]\s*\n)*\s*def (\w+)", text)
    return dict(pairs)


def called_from_bolos():
    used, current = set(), ""
    for line in BOLOS_PATCH.read_text(errors="replace").splitlines():
        if line.startswith("+++ "):
            current = line[4:].strip()
            continue
        if not line.startswith("+") or line.startswith("+++"):
            continue
        if "lean_kernels/" in current or "unit-tests/" in current:
            continue
        code = line[1:].split("//")[0]
        if code.lstrip().startswith(("*", "/*")):
            continue
        used.update(re.findall(r"\b(llb_\w+)\s*\(", code))
    return used


def called_from_vanadium():
    lib = VND_LIB.read_text()
    wrappers = {}
    for m in re.finditer(r"pub fn (\w+)\b(.*?)(?=\n\s*(?:///|#\[|pub fn |\}\s*\n\s*#\[cfg\(test\)\])|\Z)", lib, re.S):
        if m.group(1).startswith("llb_"):
            continue
        wrappers[m.group(1)] = set(re.findall(r"\b(llb_\w+)\s*\(", m.group(2)))
    used = set()
    for line in VND_PATCH.read_text(errors="replace").splitlines():
        if not line.startswith("+") or line.startswith("+++"):
            continue
        code = line[1:].split("//")[0]
        if "debug_assert" in code:
            continue
        for name in re.findall(r"llb_vanadium_ffi::(\w+)", code):
            used.update(wrappers.get(name, set()))
            if "llb_" + name in wrappers.get(name, set()) or not wrappers.get(name):
                used.add("llb_" + name)
    return used


def main():
    errors = []
    exp = exports()
    spec = SPEC.read_text()
    proofs = PROOFS.read_text()

    specified = {sym for sym, lean in exp.items() if re.search(r"\b%s\b" % lean, spec)}
    for sym in sorted(exp):
        if sym in specified and sym in PENDING:
            errors.append(f"{sym}: has a statement in Spec.lean, remove it from PENDING")
        if sym not in specified and sym not in PENDING:
            errors.append(f"{sym}: no statement in Spec.lean and not listed in PENDING")
    for sym in sorted(set(PENDING) - set(exp)):
        errors.append(f"{sym}: listed in PENDING but not exported")

    statements = re.findall(r"^def (\w+) : Prop :=", spec, re.M)
    bundle = spec[spec.index("def KernelSpec : Prop") :] if "def KernelSpec : Prop" in spec else ""
    for name in statements:
        if name == "KernelSpec":
            continue
        if not re.search(r"^theorem \w+ : Spec\.%s\b" % name, proofs, re.M):
            errors.append(f"Spec.{name}: no theorem of this type in Proofs/KernelSpec.lean")
        if not re.search(r"\b%s\b" % name, bundle):
            errors.append(f"Spec.{name}: not part of Spec.KernelSpec")
    if not re.search(r"^theorem kernel_meets_spec : Spec\.KernelSpec\b", proofs, re.M):
        errors.append("Proofs/KernelSpec.lean: kernel_meets_spec is missing")

    called = called_from_bolos() | called_from_vanadium()
    not_called = set(exp) - called
    for sym in sorted(not_called - NOT_CALLED):
        errors.append(f"{sym}: exported but called by neither app, and not listed in NOT_CALLED")
    for sym in sorted(NOT_CALLED - not_called):
        errors.append(f"{sym}: listed in NOT_CALLED but an app calls it (or it is no longer exported)")

    print(f"exports: {len(exp)}")
    print(f"  with a statement in Spec.lean: {len(specified)}")
    print(f"  pending: {len(set(exp) - specified)}")
    print(f"  called by an app: {len(set(exp) & called)}; by neither: {len(not_called)}")
    print(f"statements in Spec.lean: {len([s for s in statements if s != 'KernelSpec'])}")
    if errors:
        print("\nFAIL")
        for e in errors:
            print("  " + e)
        return 1
    print("\nPASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
