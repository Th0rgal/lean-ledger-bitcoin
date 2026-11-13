#!/usr/bin/env bash
# b1_run.sh: freezes the built ELFs, measures them, then runs the paired Speculos benchmark on them.
set -uo pipefail
source /var/lib/orb-node/work/trace/vmenv.sh
B=/var/lib/orb-node/work/b1
export PYTHONPATH=$B/py-extra
CYCLES=12
cd "$B"; rm -rf run1 run1.tgz
T=$B/src/lean-ledger-bitcoin/benchmarks/t7_abba.py
echo "report_script_sha256=$(sha256sum bolos_paired.py | cut -c1-64) recorded=$(date -u +%FT%TZ)" > run1_pre.txt
echo "harness_sha256=$(sha256sum "$T" | cut -c1-64)" >> run1_pre.txt
python3 "$T" prepare --baseline art/ref --candidate art/lean --client-root src/app-bitcoin --profile testnet-perf --output "$B/run1" --build-evidence build_evidence.json > run1_prepare.log 2>&1 || { echo PREPARE_FAILED; tail -n 5 run1_prepare.log; exit 1; }
python3 bolos_paired.py metrics --art art --benchmark-script src/lean-ledger-bitcoin/benchmarks/bolos_benchmark.sh --out "$B/elf_metrics.json" > run1_metrics.log 2>&1 || { echo METRICS_FAILED; tail -n 5 run1_metrics.log; exit 1; }
echo "run_start=$(date -u +%FT%TZ) cycles=$CYCLES" >> run1_pre.txt
python3 "$T" run --output "$B/run1" --cycles $CYCLES --cores 2,3 --wait-timeout 600 --max-load 2.0 > run1_run.log 2>&1
echo "run_rc=$? run_end=$(date -u +%FT%TZ)" >> run1_pre.txt
cp build_evidence.json elf_metrics.json run1_pre.txt run1/
tar czf run1.tgz run1 build_summary.txt run1_prepare.log run1_metrics.log run1_run.log b1_build.sh b1_run.sh b1_pilot.sh bolos_paired.py logs/build_freestanding.log
cat run1_pre.txt; tail -n 3 run1_run.log | cut -c1-200; wc -l run1/samples.jsonl; ls -la run1.tgz
