#!/usr/bin/env python3
"""Assemble benchmarks/vanadium_trace.json from the raw runs of the harness trace mode.

Input: the TRACE_OUT_DIR written by `TRACE_OUT_DIR=... bash benchmarks/vanadium_benchmark.sh`
(run-NN-<variant>.json, elfs/SHA256SUMS) and a provenance JSON describing the measurement host.

The script copies the measured samples verbatim: it does not smooth, resample or interpolate.
It refuses to write the output (exit code 2) when the final cumulative instruction count of any
run differs by more than the tolerance from the committed benchmarks/vanadium_results.json.
"""

import argparse
import glob
import json
import os
import sys

VARIANTS = ("reference", "lean_optimized", "same_profile_lean")
COUNTERS = ("rv32_instructions", "vm_page_loads", "vm_page_commits")
SAMPLE_KEYS = ("t_ms", "phase", "apdu_index") + COUNTERS


def read_sha256sums(path):
    sums = {}
    with open(path) as f:
        for line in f:
            digest, name = line.split()
            sums[name.lstrip("*")] = digest
    return sums


def phase_ranges(samples):
    ranges = []
    for s in samples:
        if ranges and ranges[-1]["phase"] == s["phase"]:
            ranges[-1]["last_apdu_index"] = s["apdu_index"]
            ranges[-1]["end"] = s
        else:
            ranges.append({"phase": s["phase"], "first_apdu_index": s["apdu_index"],
                           "last_apdu_index": s["apdu_index"], "end": s})
    out = []
    previous = {c: 0 for c in COUNTERS}
    for r in ranges:
        entry = {k: r[k] for k in ("phase", "first_apdu_index", "last_apdu_index")}
        for c in COUNTERS:
            entry[c] = r["end"][c] - previous[c]
            previous[c] = r["end"][c]
        out.append(entry)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("trace_dir")
    ap.add_argument("--provenance", required=True)
    ap.add_argument("--results", required=True, help="committed vanadium_results.json")
    ap.add_argument("--out", required=True)
    ap.add_argument("--tolerance-pct", type=float, default=1.0)
    args = ap.parse_args()

    sums = read_sha256sums(os.path.join(args.trace_dir, "elfs", "SHA256SUMS"))
    with open(args.results) as f:
        committed = json.load(f)["speculos_flex_e2e"]
    with open(args.provenance) as f:
        provenance = json.load(f)

    runs = []
    guard = []
    for path in sorted(glob.glob(os.path.join(args.trace_dir, "run-*.json"))):
        with open(path) as f:
            raw = json.load(f)
        variant = raw["variant"]
        assert variant in VARIANTS, variant
        samples = raw["samples"]
        assert [s["apdu_index"] for s in samples] == list(range(len(samples)))
        for a, b in zip(samples, samples[1:]):
            assert b["t_ms"] >= a["t_ms"], (path, b["apdu_index"])
            for c in COUNTERS:
                assert b[c] >= a[c], (path, c, b["apdu_index"])
        assert samples[-1]["vm_state"] == "vapp_exited", path

        final = {c: samples[-1][c] for c in COUNTERS}
        expected = committed[variant]["sign_transaction"]
        delta_pct = 100.0 * (final["rv32_instructions"] - expected["rv32_instructions"]) / expected["rv32_instructions"]
        guard.append({
            "seq": raw["seq"],
            "variant": variant,
            "traced_rv32_instructions": final["rv32_instructions"],
            "committed_rv32_instructions": expected["rv32_instructions"],
            "delta_pct": round(delta_pct, 4),
            "within_tolerance": abs(delta_pct) <= args.tolerance_pct,
        })
        runs.append({
            "seq": raw["seq"],
            "variant": variant,
            "elf_sha256": sums[variant + ".elf"],
            "wall_ms": raw["wall_ms"],
            "apdu_exchanges": len(samples),
            "apdu_exchanges_before_vapp_start": sum(1 for s in samples if s["vm_state"] == "no_vapp"),
            "final": final,
            "phases": phase_ranges(samples),
            "samples": [{k: s[k] for k in SAMPLE_KEYS} for s in samples],
        })

    assert runs, "no run-*.json in " + args.trace_dir
    for row in guard:
        print("guard seq {seq:02d} {variant:<18} traced {traced_rv32_instructions} vs committed "
              "{committed_rv32_instructions} ({delta_pct:+.4f}%) ok={within_tolerance}".format(**row))
    if not all(row["within_tolerance"] for row in guard):
        print("GUARD FAILED: final instruction totals are not within "
              f"{args.tolerance_pct}% of {args.results}; not writing {args.out}", file=sys.stderr)
        return 2

    doc = {
        "trace_suite": "vanadium-bitcoin-vapp-apdu-trace",
        "workload": "sign_transaction (Taproot tr(@0/**), Speculos --model flex, autoapprove V-App builds)",
        "sampling": (
            "One GetMetrics (E0 F0 00 00) exchange after every APDU exchange of the flow; the probe "
            "exchanges are not counted in apdu_index. t_ms is the host monotonic time, since Speculos "
            "accepted the APDU connection, at which the sampled exchange returned. Counters are "
            "cumulative for the V-App execution and are 0 for the exchanges that precede StartVApp."
        ),
        "phases": ["app_start", "account_registration", "sign_transaction", "exit"],
        "vm_metrics_binary_sha256": sums["app-vanadium-live-metrics"],
        "guard": {
            "reference_file": "benchmarks/vanadium_results.json",
            "tolerance_pct": args.tolerance_pct,
            "runs": guard,
        },
        "provenance": provenance,
        "runs": runs,
    }
    with open(args.out, "w") as f:
        f.write("{\n")
        head = {k: v for k, v in doc.items() if k != "runs"}
        body = json.dumps(head, indent=1)[2:-2]
        f.write(" " + body.lstrip() + ",\n \"runs\": [\n")
        for i, run in enumerate(runs):
            meta = {k: v for k, v in run.items() if k != "samples"}
            f.write("  " + json.dumps(meta)[:-1] + ", \"samples\": [\n")
            f.write(",\n".join("   " + json.dumps(s, separators=(",", ":")) for s in run["samples"]))
            f.write("\n  ]}" + ("," if i + 1 < len(runs) else "") + "\n")
        f.write(" ]\n}\n")
    with open(args.out) as f:
        json.load(f)
    print(f"Wrote {args.out} ({os.path.getsize(args.out)} bytes, {len(runs)} runs)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
