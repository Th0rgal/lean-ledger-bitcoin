#!/usr/bin/env bash
# b1_build.sh: builds the frozen paired BOLOS ELFs for item B on the Boat VM.
#   A = unmodified LedgerHQ/app-bitcoin @ APP_REF
#   B = the same commit + ffi/bolos/patches/app-bitcoin-lean-opt.patch as committed at LLB_REF
# Both trees are built at the same absolute path (slot/app-bitcoin), every variant twice.
set -uo pipefail
source /var/lib/orb-node/work/trace/vmenv.sh
export LEAN_NATIVE=/var/lib/orb-node/work/trace/turbo-lean-8c3503fa/lean/.lake/build/bin/lean-native
export LEDGER_HUB=$H
B=/var/lib/orb-node/work/b1
LLB_REF=e3e815562d68a04c5d7ab56b06e408a8fd361e38
APP_REF=f010982d3050e02813cd7129bebd68cf2d1f2099
S=$B/build_summary.txt
rm -rf "$B/src" "$B/slot" "$B/art" "$B/logs" "$B/build_evidence.json"; mkdir -p "$B/src" "$B/slot" "$B/art" "$B/logs"
cd "$B"; : > "$S"
say() { echo "$*" >> "$S"; }
die() { say "FATAL $*"; exit 1; }
say "start=$(date -u +%FT%TZ) LLB_REF=$LLB_REF APP_REF=$APP_REF"
git clone -q https://github.com/Th0rgal/lean-ledger-bitcoin.git src/lean-ledger-bitcoin || die clone_llb
git -C src/lean-ledger-bitcoin checkout -q $LLB_REF || die checkout_llb
ln -s /var/lib/orb-node/work/trace/turbo-lean-8c3503fa src/turbo-lean
ln -s "$H/vanadium" src/vanadium
LLB=$B/src/lean-ledger-bitcoin
( cd "$LLB" && bash scripts/build-freestanding.sh ) > logs/build_freestanding.log 2>&1 || die build_freestanding
grep -E 'symbols ok|stack budget ok' logs/build_freestanding.log >> "$S"
say "llb_status_after_build=[$(git -C "$LLB" status --porcelain | tr '\n' ';')]"

VARIANTS="nanosp-mainnet:nanosplus:bitcoin: nanox-mainnet:nanox:bitcoin: nanosp-testnet:nanosplus:bitcoin_testnet: nanox-testnet:nanox:bitcoin_testnet: nanosp-testnet-perf:nanosplus:bitcoin_testnet:AUTOAPPROVE_FOR_PERF_TESTS=1 nanox-testnet-perf:nanox:bitcoin_testnet:AUTOAPPROVE_FOR_PERF_TESTS=1"
SAMEFLAGS="nanosp-mainnet-sameflags:nanosplus:bitcoin:LLB_KEEP_UPSTREAM_DEFINES=1 nanox-mainnet-sameflags:nanox:bitcoin:LLB_KEEP_UPSTREAM_DEFINES=1"

build_arm() { # arm, variant list
  local arm="$1" list="$2" pass v name sdk coin extra out rc
  for pass in 1 2; do
    for v in $list; do
      IFS=: read -r name sdk coin extra <<< "$v"
      out="$B/art/$arm/$name"; [ "$pass" = 2 ] && out="$B/art/$arm-rebuild/$name"
      mkdir -p "$out"
      ( cd "$B/slot/app-bitcoin" && rm -rf build bin debug && BOLOS_SDK="$H/dev-tools-rootfs/opt/$sdk-secure-sdk" make -j8 COIN="$coin" DEBUG=0 $extra ) > "$B/logs/$arm-$name-$pass.log" 2>&1
      rc=$?
      [ $rc = 0 ] || die "build $arm $name pass=$pass rc=$rc"
      cp slot/app-bitcoin/bin/app.elf slot/app-bitcoin/bin/app.apdu slot/app-bitcoin/debug/app.map slot/app-bitcoin/debug/app.asm "$out/" || die "copy $arm $name"
      say "BUILT $arm $name pass=$pass sha=$(sha256sum "$out/app.elf" | cut -c1-64)"
    done
  done
}

git clone -q --shared "$H/app-bitcoin" slot/app-bitcoin && git -C slot/app-bitcoin checkout -q $APP_REF || die clone_ref
say "ref_head=$(git -C slot/app-bitcoin rev-parse HEAD) ref_tree=$(git -C slot/app-bitcoin rev-parse 'HEAD^{tree}') ref_status=[$(git -C slot/app-bitcoin status --porcelain | tr '\n' ';')]"
build_arm ref "$VARIANTS"
say "ref_status_after_build=[$(git -C slot/app-bitcoin status --porcelain | tr '\n' ';')]"
mv slot/app-bitcoin src/app-bitcoin

git clone -q --shared "$H/app-bitcoin" slot/app-bitcoin && git -C slot/app-bitcoin checkout -q $APP_REF || die clone_lean
git -C slot/app-bitcoin apply "$LLB/ffi/bolos/patches/app-bitcoin-lean-opt.patch" || die apply_patch
say "lean_head=$(git -C slot/app-bitcoin rev-parse HEAD) lean_changed_files=$(git -C slot/app-bitcoin status --porcelain | wc -l)"
build_arm lean "$VARIANTS $SAMEFLAGS"
mv slot/app-bitcoin src/app-bitcoin-lean

python3 - "$B" "$LLB_REF" "$APP_REF" <<'PY'
import hashlib, json, subprocess, sys
from pathlib import Path
B, llb_ref, app_ref = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
git = lambda d, *a: subprocess.check_output(['git', '-C', str(d), *a], text=True).strip()
llb = B / 'src/lean-ledger-bitcoin'
arts = {}
for arm in ('ref', 'lean'):
    arts[arm] = {}
    for d in sorted((B / 'art' / arm).iterdir()):
        r = B / 'art' / f'{arm}-rebuild' / d.name
        arts[arm][d.name] = {f: sha(d / f) for f in ('app.elf', 'app.apdu', 'app.map', 'app.asm')}
        arts[arm][d.name]['rebuild_app_elf_sha256'] = sha(r / 'app.elf')
        arts[arm][d.name]['rebuild_identical'] = sha(r / 'app.elf') == sha(d / 'app.elf') and sha(r / 'app.apdu') == sha(d / 'app.apdu')
ir = {}
for t in ('thumbv6m', 'thumbv8m.main'):
    name = f'liblean_ledger_bitcoin_{t}.ll'
    fresh = (llb / 'ffi/bolos/build/lto' / name).read_text().splitlines()
    shipped = (B / 'src/app-bitcoin-lean/src/lean_kernels' / name).read_text().splitlines()
    diff = [i for i, (a, b) in enumerate(zip(fresh, shipped)) if a != b]
    ir[t] = {'fresh_sha256': sha(llb / 'ffi/bolos/build/lto' / name),
             'shipped_in_patch_sha256': sha(B / 'src/app-bitcoin-lean/src/lean_kernels' / name),
             'line_count_equal': len(fresh) == len(shipped), 'differing_line_indexes': diff,
             'only_module_id_line_differs': len(fresh) == len(shipped) and diff == [0] and fresh[0].startswith('; ModuleID')}
ev = {
    'vm_work_dir': str(B),
    'lean_ledger_bitcoin': {'head': git(llb, 'rev-parse', 'HEAD'), 'expected': llb_ref,
                            'status_after_kernel_build': git(llb, 'status', '--porcelain'),
                            'kernel_source_sha256': sha(llb / 'BitcoinLedger/FreestandingKernels.lean'),
                            'bolos_patch_sha256': sha(llb / 'ffi/bolos/patches/app-bitcoin-lean-opt.patch')},
    'turbo_lean': {'head': git(B / 'src/turbo-lean', 'rev-parse', 'HEAD'),
                   'status': git(B / 'src/turbo-lean', 'status', '--porcelain'),
                   'lean_native_sha256': sha(B / 'src/turbo-lean/lean/.lake/build/bin/lean-native')},
    'reference_tree': {'path': str(B / 'src/app-bitcoin'), 'head': git(B / 'src/app-bitcoin', 'rev-parse', 'HEAD'),
                       'expected': app_ref, 'tree': git(B / 'src/app-bitcoin', 'rev-parse', 'HEAD^{tree}'),
                       'status': git(B / 'src/app-bitcoin', 'status', '--porcelain')},
    'lean_tree': {'path': str(B / 'src/app-bitcoin-lean'), 'head': git(B / 'src/app-bitcoin-lean', 'rev-parse', 'HEAD'),
                  'status': git(B / 'src/app-bitcoin-lean', 'status', '--porcelain').splitlines(),
                  'kernel_bundle_sha256': {p.name: sha(p) for p in sorted((B / 'src/app-bitcoin-lean/src/lean_kernels').iterdir())}},
    'build_path_shared_by_both_trees': str(B / 'slot/app-bitcoin'),
    'make': 'BOLOS_SDK=<hub>/dev-tools-rootfs/opt/<sdk>-secure-sdk make -j8 COIN=<coin> DEBUG=0 [AUTOAPPROVE_FOR_PERF_TESTS=1 | LLB_KEEP_UPSTREAM_DEFINES=1]',
    'compiler': subprocess.check_output(['clang', '--version'], text=True).splitlines()[0],
    'linker': subprocess.check_output(['ld.lld', '--version'], text=True).splitlines()[0],
    'kernel_ir_fresh_vs_shipped': ir,
    'artifacts': arts,
}
(B / 'build_evidence.json').write_text(json.dumps(ev, indent=2) + '\n')
bad = [f'{a}/{v}' for a in arts for v in arts[a] if not arts[a][v]['rebuild_identical']]
print('EVIDENCE ok; non-reproducible:', bad, '; ir module-id-only:', {t: ir[t]['only_module_id_line_differs'] for t in ir})
PY
say "evidence_rc=$? end=$(date -u +%FT%TZ)"
say DONE
