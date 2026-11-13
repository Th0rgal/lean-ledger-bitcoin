#!/usr/bin/env bash
# Pilot: checks that the harness starts on this VM and measures seconds per launch.
# Its samples are discarded and never compared between arms.
set -uo pipefail
source /var/lib/orb-node/work/trace/vmenv.sh
B=/var/lib/orb-node/work/b1
export PYTHONPATH=$B/py-extra
cd "$B"; rm -rf pilot
T=$B/src/lean-ledger-bitcoin/benchmarks/t7_abba.py
python3 "$T" prepare --baseline art/ref --candidate art/lean --client-root src/app-bitcoin --profile testnet-perf --output "$B/pilot" --build-evidence build_evidence.json > pilot_prepare.log 2>&1; echo "prepare rc=$?"
timeout -s INT 170 python3 "$T" run --output "$B/pilot" --cycles 6 --cores 2,3 --wait-timeout 600 --max-load 2.0 > pilot_run.log 2>&1; echo "run rc=$?"
sleep 3
tail -n 4 pilot_prepare.log | cut -c1-300; tail -n 6 pilot_run.log | cut -c1-300
python3 - <<'PY'
import json
rt=[json.loads(l) for l in open('/var/lib/orb-node/work/b1/pilot/runtime.jsonl')]
print('launches', len(rt), [(r['phase'], r['model'], r['api']) for r in rt])
s=[json.loads(l) for l in open('/var/lib/orb-node/work/b1/pilot/samples.jsonl')]
t=sorted(r['time_ns'] for r in s)
print('samples', len(s), 'span_s', round((t[-1]-t[0])/1e9,1), 'artifacts', sorted({r['artifact'] for r in s}))
PY
echo "leftover: $(pgrep -fc 'qemu-arm-static|speculos')"; uptime
