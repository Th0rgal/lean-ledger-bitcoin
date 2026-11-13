#!/usr/bin/env python3
"""Paired BOLOS report: sizes and Speculos latencies taken from the same frozen ELFs.

  metrics  runs next to the built ELFs and measures each one with the analyzer
           embedded in bolos_benchmark.sh.
  report   is a pure function of an evidence directory (t7_abba.py outputs,
           build_evidence.json, elf_metrics.json, provenance.json) and writes
           benchmarks/bolos_results.json. It fails if any consistency check fails.
"""
import argparse
import ast
import hashlib
import itertools
import json
import math
import os
import re
import statistics
import subprocess
import sys
from pathlib import Path

PRIMARY = ('SIGN_PSBT_TR_3IN', 'SIGN_PSBT_WSH3OF5_3IN', 'REGISTER_WALLET')
SECONDARY = ('GET_VERSION', 'GET_MASTER_FINGERPRINT', 'GET_EXTENDED_PUBKEY', 'GET_WALLET_ADDRESS')
MODELS = ('nanosp', 'nanox')
ARMS = {'A': 'ref', 'B': 'lean'}
ALPHA = 0.05
DECISION_RULE = (
    'Unit = one block (cycle, device, phase) of four Speculos launches, two per label, ordered ABBA or BAAB. '
    'Block statistic = (mean of the two B launches - mean of the two A launches) / mean of the two A launches. '
    'In the AB phase A is the reference ELF and B the Lean ELF; in the AA phase both labels run the reference ELF '
    '(placebo). A block is dropped when the harness marked any of its launches contaminated. '
    'A cell (device, scenario) is called faster or slower only if all three hold on the AB phase: '
    'Holm-adjusted two-sided paired-t p < 0.05 within its family (primary: SIGN_PSBT_TR_3IN, SIGN_PSBT_WSH3OF5_3IN, '
    'REGISTER_WALLET on both devices; secondary: the four other scenarios on both devices), exact sign-flip '
    'p < 0.05, and |mean block statistic| greater than the |placebo mean| of the same cell. '
    'Otherwise the cell is not distinguishable from noise. Sizes are exact integers read from the ELFs.')
SIZE_METRICS = ('load_flash_bytes', 'text_code_bytes', 'rodata_bytes', 'data_bytes', 'bss_ram_bytes',
                'total_static_ram_bytes', 'elf_stripped_bytes', 'apdu_bytes')
STACK_METRICS = ('worst_case_stack_bytes', 'total_arm_thumb_insns')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def analyzer(script):
    body = script.read_text().split("python3 - << 'PY'\n", 1)[1].rsplit('\nPY', 1)[0]
    wanted = ('analyze_asm', 'parse_map_input_sections', 'collect_elf_metrics')
    nodes = [n for n in ast.parse(body).body if isinstance(n, ast.FunctionDef) and n.name in wanted]
    if sorted(n.name for n in nodes) != sorted(wanted):
        raise RuntimeError('Analyzer functions not found in bolos_benchmark.sh')
    namespace = {'os': os, 're': re, 'subprocess': subprocess}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(script), 'exec'), namespace)
    return namespace['collect_elf_metrics']


def metrics(args):
    collect = analyzer(args.benchmark_script)
    result = {'analyzer': {'path': str(args.benchmark_script.resolve()), 'sha256': digest(args.benchmark_script)},
              'artifacts': {}}
    for arm in sorted(ARMS.values()):
        result['artifacts'][arm] = {}
        for folder in sorted((args.art / arm).iterdir()):
            result['artifacts'][arm][folder.name] = {
                'elf_sha256': digest(folder / 'app.elf'), 'apdu_sha256': digest(folder / 'app.apdu'),
                'map_sha256': digest(folder / 'app.map'), 'asm_sha256': digest(folder / 'app.asm'),
                'metrics': collect(str(folder))}
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(args.out)


def betacf(a, b, x):
    tiny = 1e-300
    c, d = 1.0, 1.0 - (a + b) * x / (a + 1.0)
    d = 1.0 / (d if abs(d) > tiny else tiny)
    h = d
    for m in range(1, 500):
        for num in (m * (b - m) * x / ((a - 1.0 + 2 * m) * (a + 2 * m)),
                    -(a + m) * (a + b + m) * x / ((a + 2 * m) * (a + 1.0 + 2 * m))):
            d = 1.0 + num * d
            d = 1.0 / (d if abs(d) > tiny else tiny)
            c = 1.0 + num / c
            c = c if abs(c) > tiny else tiny
            h *= d * c
        if abs(d * c - 1.0) < 1e-15:
            break
    return h


def betai(a, b, x):
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    front = math.exp(math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) + a * math.log(x) + b * math.log(1.0 - x))
    if x < (a + 1.0) / (a + b + 2.0):
        return front * betacf(a, b, x) / a
    return 1.0 - front * betacf(b, a, 1.0 - x) / b


def t_p(t, df):
    return betai(df / 2.0, 0.5, df / (df + t * t))


def t_crit(df, alpha=ALPHA):
    lo, hi = 0.0, 1000.0
    for _ in range(200):
        mid = (lo + hi) / 2.0
        lo, hi = (mid, hi) if t_p(mid, df) > alpha else (lo, mid)
    return hi


def sign_flip_p(values):
    observed = abs(sum(values))
    hits = sum(abs(sum(s * v for s, v in zip(signs, values))) >= observed - 1e-15
               for signs in itertools.product((1, -1), repeat=len(values)))
    return hits / 2 ** len(values)


def paired(values):
    n = len(values)
    mean = statistics.fmean(values)
    sd = statistics.stdev(values)
    se = sd / math.sqrt(n)
    half = t_crit(n - 1) * se
    p = (1.0 if mean == 0 else 0.0) if se == 0 else t_p(mean / se, n - 1)
    return {'n_blocks': n, 'mean_pct': round(100 * mean, 3), 'sd_pct': round(100 * sd, 3),
            'ci95_pct': [round(100 * (mean - half), 3), round(100 * (mean + half), 3)],
            'p_paired_t': p, 'p_sign_flip': sign_flip_p(values)}


def holm(pvalues):
    order = sorted(pvalues, key=pvalues.get)
    adjusted, running = {}, 0.0
    for rank, key in enumerate(order):
        running = max(running, min(1.0, (len(order) - rank) * pvalues[key]))
        adjusted[key] = running
    return adjusted


def jsonl(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def report(args):
    ev = args.evidence
    manifest = json.loads((ev / 'manifest.json').read_text())
    build = json.loads((ev / 'build_evidence.json').read_text())
    sizes = json.loads((ev / 'elf_metrics.json').read_text())
    provenance = json.loads((ev / 'provenance.json').read_text())
    run_log, samples = jsonl(ev / 'run.jsonl'), jsonl(ev / 'samples.jsonl')
    runtime = jsonl(ev / 'runtime.jsonl')
    cycles = run_log[0]['cycles']
    scenarios = PRIMARY + SECONDARY
    launches = {}
    for row in samples:
        launches.setdefault((row['phase'], row['model'], row['cycle'], row['position']), []).append(row)

    def frozen(label, model):
        return manifest['artifacts'][label][model]

    def variant(label, model):
        return sizes['artifacts'][ARMS[label]][f'{model}-testnet-perf']

    checks = {
        'run_completed': run_log[-1].get('execution') == 'completed',
        'at_least_six_cycles': cycles >= 6,
        'run_used_this_manifest': run_log[0]['manifest_sha256'] == digest(ev / 'manifest.json'),
        'manifest_embeds_this_build_evidence': manifest['build_evidence'] == build,
        'all_launches_present': len(launches) == cycles * 16 and len(samples) == cycles * 16 * len(scenarios)
        and all(sorted(r['scenario'] for r in rows) == sorted(scenarios) for rows in launches.values()),
        'schedule_is_counterbalanced': all(
            ''.join(launches[(phase, model, cycle, pos)][0]['label'] for pos in range(4))
            == ('ABBA' if cycle % 2 == 0 else 'BAAB')
            for phase in ('AA', 'AB') for model in MODELS for cycle in range(cycles)
            if all((phase, model, cycle, pos) in launches for pos in range(4))),
        'artifact_matches_phase_and_label': all(
            r['artifact'] == ('A' if r['phase'] == 'AA' else r['label']) for r in samples),
        'every_sample_ran_a_frozen_elf': all(
            r['sha256'] == frozen(r['artifact'], r['model'])['sha256'] for r in samples),
        'frozen_elfs_are_the_built_elfs': all(
            frozen(label, model)['sha256'] == build['artifacts'][ARMS[label]][f'{model}-testnet-perf']['app.elf']
            for label in ARMS for model in MODELS),
        'sizes_measured_on_the_frozen_elfs': all(
            frozen(label, model)['sha256'] == variant(label, model)['elf_sha256']
            for label in ARMS for model in MODELS),
        'every_build_reproduced_bit_for_bit': all(
            item['rebuild_identical'] for arm in build['artifacts'].values() for item in arm.values()),
        'size_inputs_are_the_built_files': all(
            sizes['artifacts'][arm][name][f'{kind}_sha256'] == item[f'app.{kind}']
            for arm, group in build['artifacts'].items() for name, item in group.items()
            for kind in ('elf', 'apdu', 'map', 'asm')),
        'reference_is_unmodified_upstream': build['reference_tree']['head'] == build['reference_tree']['expected']
        and build['reference_tree']['status'] == '',
        'lean_tree_is_the_committed_patch': build['lean_ledger_bitcoin']['head'] == build['lean_ledger_bitcoin']['expected']
        and build['lean_tree']['head'] == build['reference_tree']['expected'],
        'shipped_kernel_ir_matches_fresh_emission': all(
            item['only_module_id_line_differs'] for item in build['kernel_ir_fresh_vs_shipped'].values()),
        'qemu_runtime_verified_for_every_launch': len(runtime) == cycles * 16 and all(
            r['library_sha256'] == frozen('A', r['model'])['library']['sha256']
            and r['api'] == frozen('A', r['model'])['api'] for r in runtime),
        'same_api_level_both_arms': all(frozen('A', m)['api'] == frozen('B', m)['api'] for m in MODELS),
        'analyzer_is_the_frozen_benchmark_script': sizes['analyzer']['sha256'] == manifest['workloads']['sha256'],
    }

    def block_values(phase, model, scenario, clean_only):
        values, used = [], 0
        for cycle in range(cycles):
            rows = [r for pos in range(4) for r in launches.get((phase, model, cycle, pos), [])]
            if clean_only and any(r['contaminated'] for r in rows):
                continue
            a = [r['elapsed_ns'] for r in rows if r['scenario'] == scenario and r['label'] == 'A']
            b = [r['elapsed_ns'] for r in rows if r['scenario'] == scenario and r['label'] == 'B']
            if len(a) == 2 and len(b) == 2:
                values.append((statistics.fmean(b) - statistics.fmean(a)) / statistics.fmean(a))
                used += 1
        return values

    def ms(model, scenario, artifact, phase='AB'):
        return [r['elapsed_ns'] / 1e6 for r in samples if r['phase'] == phase and r['model'] == model
                and r['scenario'] == scenario and r['artifact'] == artifact and not r['contaminated']]

    latency = {model: {} for model in MODELS}
    for model in MODELS:
        for scenario in scenarios:
            ref, lean = ms(model, scenario, 'A'), ms(model, scenario, 'B')
            latency[model][scenario] = {
                'family': 'primary' if scenario in PRIMARY else 'secondary',
                'launches_per_arm': len(ref),
                'ref_median_ms': round(statistics.median(ref), 3), 'lean_median_ms': round(statistics.median(lean), 3),
                'delta_median_ms': round(statistics.median(lean) - statistics.median(ref), 3),
                'ref_min_ms': round(min(ref), 3), 'lean_min_ms': round(min(lean), 3),
                'ref_mean_ms': round(statistics.fmean(ref), 3), 'lean_mean_ms': round(statistics.fmean(lean), 3),
                'lean_vs_ref': paired(block_values('AB', model, scenario, True)),
                'placebo_ref_vs_ref': paired(block_values('AA', model, scenario, True)),
                'all_blocks_including_contaminated': paired(block_values('AB', model, scenario, False)),
            }
    for family in (PRIMARY, SECONDARY):
        adjusted = holm({(m, s): latency[m][s]['lean_vs_ref']['p_paired_t'] for m in MODELS for s in family})
        for (model, scenario), value in adjusted.items():
            cell = latency[model][scenario]
            effect, placebo = cell['lean_vs_ref'], cell['placebo_ref_vs_ref']
            cell['lean_vs_ref']['p_holm'] = value
            distinct = (value < ALPHA and effect['p_sign_flip'] < ALPHA
                        and abs(effect['mean_pct']) > abs(placebo['mean_pct']))
            cell['verdict'] = ('lean_slower' if effect['mean_pct'] > 0 else 'lean_faster') if distinct \
                else 'not_distinguishable_from_noise'
    for model in MODELS:
        for cell in latency[model].values():
            for key in ('lean_vs_ref', 'placebo_ref_vs_ref', 'all_blocks_including_contaminated'):
                for name in ('p_paired_t', 'p_sign_flip', 'p_holm'):
                    if name in cell[key]:
                        cell[key][name] = round(cell[key][name], 5)

    def flat(entry):
        return {'elf_sha256': entry['elf_sha256'], **entry['metrics']}

    storage, size_verdicts = {}, {}
    for name in sorted(sizes['artifacts']['ref']):
        key = name.replace('-', '_')
        storage[key] = {'same_elfs_as_latency': name.endswith('-testnet-perf'),
                        'reference': flat(sizes['artifacts']['ref'][name]),
                        'lean_opt': flat(sizes['artifacts']['lean'][name])}
        same = sizes['artifacts']['lean'].get(name + '-sameflags')
        if same:
            storage[key]['lean_sameflags'] = flat(same)
        ref, lean = sizes['artifacts']['ref'][name]['metrics'], sizes['artifacts']['lean'][name]['metrics']
        pairs = [(m, ref[m], lean[m]) for m in SIZE_METRICS]
        pairs += [(m, ref['stack_and_insns'][m], lean['stack_and_insns'][m]) for m in STACK_METRICS]
        size_verdicts[key] = {m: {'reference': r, 'lean': l, 'delta': l - r,
                                  'verdict': 'lean_smaller' if l < r else 'lean_larger' if l > r else 'equal'}
                              for m, r, l in pairs}

    contaminated = sum(1 for rows in launches.values() if rows[0]['contaminated'])
    loads = [x for entry in jsonl(ev / 'load.jsonl') for x in
             ([entry['loadavg'][0]] if 'loadavg' in entry else [entry['before']['loadavg'][0], entry['after']['loadavg'][0]])]
    snapshots = manifest['source_snapshots_not_build_attestations']
    files = sorted(p.name for p in ev.iterdir() if p.is_file())
    result = {
        'status': 'validated' if all(checks.values()) else 'invalid',
        'status_meaning': 'validated = every entry of validation.checks is true; it is not an on-device measurement.',
        'supersedes': 'T6 static-fleet results and the T7 cycle files as the reference BOLOS numbers.',
        'metadata': {
            'upstream_repo': 'LedgerHQ/app-bitcoin',
            'upstream_commit': build['reference_tree']['head'],
            'lean_ledger_bitcoin_commit': build['lean_ledger_bitcoin']['head'],
            'bolos_patch_sha256': build['lean_ledger_bitcoin']['bolos_patch_sha256'],
            'kernel_source_sha256': build['lean_ledger_bitcoin']['kernel_source_sha256'],
            'turbo_lean_commit': build['turbo_lean']['head'],
            'lean_native_sha256': build['turbo_lean']['lean_native_sha256'],
            'source_snapshots_at_freeze': {k: v['head'] for k, v in snapshots.items()},
            'measurement_host': {**provenance['host'], 'same_host_reference_and_lean': True,
                                 'harness_host': manifest['host'], 'cpu_model': manifest['cpu_model'][0],
                                 'pinned_cores': run_log[1]['affinity'], 'exclusive_reservation': False,
                                 'load1_min': round(min(loads), 3), 'load1_max': round(max(loads), 3)},
            'targets': {m: f"{provenance['targets'][m]}, ELF ledger.api_level {frozen('A', m)['api']}, "
                           f"QEMU runtime API verified for every launch" for m in MODELS},
            'compiler': build['compiler'], 'linker': build['linker'],
            'tools': manifest['tools'], 'speculos_version': manifest['speculos_version'],
            'harness': manifest['harness'], 'harness_command': provenance['commands'],
            'build_flags': {'latency_and_primary_sizes': 'COIN=bitcoin_testnet DEBUG=0 AUTOAPPROVE_FOR_PERF_TESTS=1',
                            'make': build['make'], 'build_path_shared_by_both_trees': build['build_path_shared_by_both_trees']},
        },
        'validation': {
            'checks': checks, 'decision_rule': DECISION_RULE,
            'decision_rule_fixed_before_run': provenance['report_script_before_run'],
            'cycles': cycles, 'launches': len(launches), 'samples': len(samples),
            'contaminated_launches': contaminated,
            'evidence_files_sha256': {name: digest(ev / name) for name in files},
            'limitations': [
                'Latency is host wall-clock time of APDU exchanges against Speculos (QEMU user-mode emulation); '
                'it ranks the two ELFs on this host and is not a time on a physical device.',
                'The latency ELFs are testnet builds with AUTOAPPROVE_FOR_PERF_TESTS=1. Mainnet production ELFs are '
                'listed for size only and were not timed.',
                'worst_case_stack_bytes is a static estimate from the disassembly call graph (direct calls only, '
                'recursion cut); total_arm_thumb_insns is a static count of emitted instructions, not executed ones.',
                'The VM is a guest on a shared hypervisor: two cores are pinned, not reserved.',
            ] + provenance.get('limitations', []),
        },
        'frozen_elfs': {arm: {m: {'variant': f'{m}-testnet-perf', 'sha256': frozen(label, m)['sha256'],
                                  'elf_file_bytes': frozen(label, m)['elf_file_bytes'], 'api_level': frozen(label, m)['api'],
                                  'speculos_library_sha256': frozen(label, m)['library']['sha256']}
                              for m in MODELS} for label, arm in (('A', 'reference'), ('B', 'lean'))},
        'size_verdicts': size_verdicts,
        'latency_verdicts': {m: {s: {'verdict': c['verdict'], 'lean_vs_ref_mean_pct': c['lean_vs_ref']['mean_pct'],
                                     'ci95_pct': c['lean_vs_ref']['ci95_pct'],
                                     'placebo_mean_pct': c['placebo_ref_vs_ref']['mean_pct']}
                                 for s, c in latency[m].items()} for m in MODELS},
        'storage_ram_stack': storage,
        'speculos_apdu_latency_ms': latency,
    }
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    for name, ok in checks.items():
        print(('ok   ' if ok else 'FAIL ') + name)
    print(result['status'], args.out)
    if result['status'] != 'validated':
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest='command', required=True)
    measure = commands.add_parser('metrics')
    measure.add_argument('--art', type=Path, required=True)
    measure.add_argument('--benchmark-script', type=Path, default=Path(__file__).with_name('bolos_benchmark.sh'))
    measure.add_argument('--out', type=Path, required=True)
    summarize = commands.add_parser('report')
    summarize.add_argument('--evidence', type=Path, required=True)
    summarize.add_argument('--out', type=Path, default=Path(__file__).with_name('bolos_results.json'))
    args = parser.parse_args()
    (metrics if args.command == 'metrics' else report)(args)


if __name__ == '__main__':
    main()
