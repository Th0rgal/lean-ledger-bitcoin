import argparse
import ast
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import shutil
import socket
import subprocess
import sys
import time


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def emit(path, value):
    with path.open('a') as stream:
        stream.write(json.dumps(value, sort_keys=True) + '\n')
        stream.flush()
        os.fsync(stream.fileno())


def processes():
    rows = []
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():
            continue
        try:
            name = (entry / 'comm').read_text().strip()
            if name.startswith(('lake', 'lean', 'clang', 'ld.lld', 'lld', 'cargo',
                                'rustc', 'opt', 'make', 'cc1', 'speculos', 'qemu')) or (
                    name.startswith('python') and b'speculos' in (entry / 'cmdline').read_bytes()):
                rows.append({'pid': int(entry.name), 'comm': name})
        except (OSError, ProcessLookupError):
            pass
    return rows


def tree_hashes(root):
    return {str(path.resolve()): digest(path) for path in sorted(root.rglob('*.py'))}


def host():
    return {'hostname': platform.node(), 'kernel': platform.release(),
            'machine': platform.machine(), 'boot_id': Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
            'affinity': sorted(os.sched_getaffinity(0))}


def guard(output, timeout=300, max_load=2.0):
    deadline = time.monotonic() + timeout
    while True:
        state = {'time_ns': time.time_ns(), 'loadavg': os.getloadavg(), 'builds': processes()}
        emit(output / 'load.jsonl', state)
        if not state['builds'] and state['loadavg'][0] < max_load:
            return
        if time.monotonic() >= deadline:
            raise RuntimeError('Quiet-window timeout; see load.jsonl. No external process stopped.')
        time.sleep(min(10, max(0, deadline - time.monotonic())))


def free_port():
    with socket.socket() as probe:
        probe.bind(('127.0.0.1', 0))
        return probe.getsockname()[1]


def schedule(cycles):
    for cycle in range(cycles):
        for phase in (('AA', 'AB') if cycle % 2 == 0 else ('AB', 'AA')):
            for model in ('nanosp', 'nanox'):
                for position, label in enumerate('ABBA' if cycle % 2 == 0 else 'BAAB'):
                    yield cycle, phase, model, position, label


def workload_namespace(source):
    text = source.read_text()
    shell_python = text.split("python3 - << 'PY'\n", 1)[1].rsplit('\nPY', 1)[0]
    tree = ast.parse(shell_python)
    functions = [node for node in tree.body if isinstance(node, ast.FunctionDef)
                 and node.name == 'make_perf_workloads']
    if len(functions) != 1:
        raise RuntimeError('Expected exactly one workload definition')
    from ledger_bitcoin import WalletPolicy
    from test_utils import txmaker
    namespace = {'WalletPolicy': WalletPolicy, 'txmaker': txmaker}
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(source), 'exec'), namespace)
    return namespace['make_perf_workloads'](), txmaker.SPECULOS_SEED


def runtime_api(parent, model, expected_api, library):
    pending = [parent]
    for _ in range(6):
        next_level = []
        for pid in pending:
            try:
                args = Path(f'/proc/{pid}/cmdline').read_bytes().decode().split('\0')
                if '-m' in args and '-a' in args and '-c' in args:
                    device = args[args.index('-m') + 1]
                    api = args[args.index('-a') + 1]
                    loaded = Path(args[args.index('-c') + 1].split(':', 1)[0]).resolve()
                    if (device != model or api != expected_api or
                            loaded != Path(library['path']).resolve() or digest(loaded) != library['sha256']):
                        raise RuntimeError('Runtime model/API/library mismatch')
                    return {'model': device, 'api': api, 'library_sha256': digest(loaded), 'pid': pid}
                children = Path(f'/proc/{pid}/task/{pid}/children').read_text().split()
                next_level.extend(map(int, children))
            except (OSError, ProcessLookupError):
                pass
        pending = next_level
    raise RuntimeError('Unable to verify the actual QEMU model, API and shared library')


def prepare(args):
    from ledgered.binary import LedgerBinaryApp
    import speculos
    output = args.output.resolve()
    output.mkdir(parents=False, exist_ok=False)
    speculos_root = Path(speculos.__file__).resolve().parent
    artifacts = {}
    for label, root in [('A', args.baseline), ('B', args.candidate)]:
        artifacts[label] = {}
        for model in ('nanosp', 'nanox'):
            source = root / f'{model}-testnet-perf/app.elf'
            target = output / f'{label}-{model}.elf'
            shutil.copyfile(source, target)
            target.chmod(0o444)
            api = str(LedgerBinaryApp(str(target)).sections.api_level)
            if api in ('None', '0'):
                raise RuntimeError('Missing concrete firmware API')
            folder = 'cxlib' if int(api) < 23 else 'sharedlib'
            suffix = 'cx' if int(api) < 23 else 'shared'
            library = speculos_root / folder / f'{model}-api-level-{suffix}-{api}.elf'
            from elftools.elf.elffile import ELFFile
            with target.open('rb') as stream:
                elf = ELFFile(stream)
                sections = {section.name: {'bytes': section['sh_size'], 'flags': section['sh_flags'],
                                           'type': section['sh_type']} for section in elf.iter_sections()}
            artifacts[label][model] = {'path': str(target), 'sha256': digest(target), 'api': api,
                                       'elf_file_bytes': target.stat().st_size, 'sections': sections,
                                       'library': {'path': str(library), 'sha256': digest(library)}}
    for model in ('nanosp', 'nanox'):
        if artifacts['A'][model]['api'] != artifacts['B'][model]['api']:
            raise RuntimeError('A/B APIs differ')
    tools = {}
    for name in ('clang-21', 'ld.lld', 'qemu-arm-static'):
        path = shutil.which(name)
        if not path:
            raise RuntimeError(f'Missing tool: {name}')
        tools[name] = {'path': path, 'sha256': digest(path),
                       'version': subprocess.check_output([path, '--version'], text=True).splitlines()[0]}
    source = Path(__file__).with_name('bolos_benchmark.sh').resolve()
    repo = source.parent.parent
    sources = {}
    kernels = {}
    for name in ('lean-ledger-bitcoin', 'turbo-lean', 'app-bitcoin', 'vanadium'):
        root = repo.parent / name
        sources[name] = {'head': subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip(),
                         'status': subprocess.check_output(['git', '-C', str(root), 'status', '--porcelain'], text=True)}
    for path in sorted((repo / 'ffi/bolos/build').rglob('*.ll')):
        kernels[str(path)] = digest(path)
    evidence = json.loads(args.build_evidence.read_text()) if args.build_evidence else None
    cpu = [line for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')]
    governors = {str(path): path.read_text().strip() for path in Path('/sys/devices/system/cpu').glob('cpu*/cpufreq/scaling_governor')}
    manifest = {'status': 'experimental_nonvalidated', 'created_ns': time.time_ns(),
                'host': host(), 'profile': args.profile, 'artifacts': artifacts, 'tools': tools,
                'source_snapshots_not_build_attestations': sources,
                'kernel_ir_snapshots_not_build_attestations': kernels,
                'build_evidence': evidence,
                'defines': ['AUTOAPPROVE_FOR_PERF_TESTS=1'],
                'cpu_model': cpu, 'governors': governors,
                'pip_freeze': subprocess.check_output([sys.executable, '-m', 'pip', 'freeze'], text=True).splitlines(),
                'sampling_unit': 'launch',
                'stack_bytes': None,
                'stack_limitation': 'No stack attribution without ELF-hash-linked build evidence.',
                'harness': {'path': str(Path(__file__).resolve()), 'sha256': digest(__file__)},
                'workloads': {'path': str(source), 'sha256': digest(source)},
                'client_root': str(args.client_root.resolve()),
                'client_python': tree_hashes(args.client_root.resolve() / 'bitcoin_client'),
                'test_utils': {'path': str((args.client_root.resolve() / 'test_utils/__init__.py')),
                               'sha256': digest(args.client_root.resolve() / 'test_utils/__init__.py')},
                'txmaker': {'path': str((args.client_root.resolve() / 'test_utils/txmaker.py')),
                            'sha256': digest(args.client_root.resolve() / 'test_utils/txmaker.py')},
                'speculos_version': importlib.metadata.version('speculos'),
                'python': {'path': sys.executable, 'sha256': digest(sys.executable)},
                'limitations': ['Build profile is operator-declared, not independently reconstructed.',
                               'Shared-host timing is experimental; no zero-regression claim.',
                               'Wall time only; no executed-instruction, heap or stack inference.']}
    path = output / 'manifest.json'
    path.write_text(json.dumps(manifest, indent=2) + '\n')
    path.chmod(0o444)
    print(path)


def run(args):
    output = args.output.resolve()
    manifest_path = output / 'manifest.json'
    m = json.loads(manifest_path.read_text())
    if args.cycles < 6:
        raise RuntimeError('At least six counterbalanced blocks required')
    if (output / 'run.jsonl').exists():
        raise RuntimeError('Run already started; prepare a new output directory')
    emit(output / 'run.jsonl', {'status': 'experimental_nonvalidated', 'manifest_sha256': digest(manifest_path), 'cycles': args.cycles})
    try:
        if host() != m['host']:
            raise RuntimeError('Host/boot/affinity differs from frozen manifest')
        pinned = [m['harness'], m['workloads'], m['python'], m['test_utils'], m['txmaker'], *m['tools'].values()]
        for group in m['artifacts'].values():
            for artifact in group.values():
                pinned.extend([artifact, artifact['library']])
        for item in pinned:
            if digest(item['path']) != item['sha256']:
                raise RuntimeError(f"Frozen input changed: {item['path']}")
        if tree_hashes(Path(m['client_root']) / 'bitcoin_client') != m['client_python']:
            raise RuntimeError('Frozen client python tree changed')
        cores = list(map(int, args.cores.split(',')))
        if len(set(cores)) != 2 or 0 in cores or not set(cores) <= set(os.sched_getaffinity(0)):
            raise RuntimeError('Select two distinct available nonzero CPUs')
        os.sched_setaffinity(0, cores)
        emit(output / 'run.jsonl', {'affinity': cores, 'exclusive_reservation': False,
                                  'limitation': 'Affinity pins execution but does not reserve cores against external tasks.'})
        guard(output, args.wait_timeout, args.max_load)
        sys.path.insert(0, m['client_root'])
        sys.path.insert(0, str(Path(m['client_root']) / 'bitcoin_client'))
        from speculos.client import SpeculosClient
        from ledger_bitcoin import createClient, Chain
        workloads, seed = workload_namespace(Path(m['workloads']['path']))
        os.environ['SPECULOS_APPNAME'] = 'Bitcoin Test:2.5.1'
        for cycle, phase, model, position, label in schedule(args.cycles):
            guard(output, args.wait_timeout, args.max_load)
            actual = 'A' if phase == 'AA' else label
            artifact = m['artifacts'][actual][model]
            port = free_port()
            rows = []
            comm = SpeculosClient(artifact['path'], ['--model', model, '--apiLevel', artifact['api'],
                '--seed', seed, '--display', 'headless', '--api-port', str(port), '--apdu-port', '0'],
                api_url=f'http://127.0.0.1:{port}')
            before = {'time_ns': time.time_ns(), 'loadavg': os.getloadavg(), 'builds': processes()}
            try:
                comm.start()
                runtime = runtime_api(comm.process.pid, model, artifact['api'], artifact['library'])
                client = createClient(comm, chain=Chain.TEST, debug=False)
                _, hmac_value = client.register_wallet(workloads['wp_wsh_3of5'])
                calls = {
                    'GET_VERSION': lambda: comm.apdu_exchange(0xB0, 0x01, b'', p1=0, p2=0),
                    'GET_MASTER_FINGERPRINT': client.get_master_fingerprint,
                    'GET_EXTENDED_PUBKEY': lambda: client.get_extended_pubkey("m/48'/1'/0'/2'", False),
                    'GET_WALLET_ADDRESS': lambda: client.get_wallet_address(workloads['wp_tr'], None, 0, 7, False),
                    'REGISTER_WALLET': lambda: client.register_wallet(workloads['wp_wsh_3of5']),
                    'SIGN_PSBT_TR_3IN': lambda: client.sign_psbt(workloads['psbt_tr_3in'], workloads['wp_tr'], None),
                    'SIGN_PSBT_WSH3OF5_3IN': lambda: client.sign_psbt(workloads['psbt_wsh_3in'], workloads['wp_wsh_3of5'], hmac_value),
                }
                for scenario, call in calls.items():
                    call()
                    start = time.perf_counter_ns()
                    call()
                    elapsed = time.perf_counter_ns() - start
                    rows.append({'phase': phase, 'model': model, 'cycle': cycle,
                         'position': position, 'label': label, 'artifact': actual,
                         'sha256': artifact['sha256'], 'api': runtime['api'], 'scenario': scenario,
                         'unit': 'launch', 'elapsed_ns': elapsed, 'time_ns': time.time_ns()})
            finally:
                comm.stop()
            after = {'time_ns': time.time_ns(), 'loadavg': os.getloadavg(), 'builds': processes()}
            contaminated = bool(before['builds'] or after['builds'] or after['loadavg'][0] >= args.max_load)
            for row in rows:
                row['contaminated'] = contaminated
            with (output / 'samples.jsonl').open('a') as stream:
                stream.writelines(json.dumps(row, sort_keys=True) + '\n' for row in rows)
                stream.flush()
                os.fsync(stream.fileno())
            emit(output / 'runtime.jsonl', {'phase': phase, 'model': model, 'cycle': cycle,
                                          'position': position, 'port': port, **runtime})
            emit(output / 'load.jsonl', {'before': before, 'after': after, 'contaminated': contaminated})
        for item in pinned:
            if digest(item['path']) != item['sha256']:
                raise RuntimeError('Frozen input changed during run')
        if tree_hashes(Path(m['client_root']) / 'bitcoin_client') != m['client_python']:
            raise RuntimeError('Frozen client python tree changed during run')
        emit(output / 'run.jsonl', {'status': 'experimental_nonvalidated', 'execution': 'completed', 'time_ns': time.time_ns()})
    except Exception as error:
        emit(output / 'run.jsonl', {'status': 'experimental_nonvalidated', 'execution': 'blocked_or_failed',
                                  'error': str(error), 'time_ns': time.time_ns()})
        raise


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest='command', required=True)
    prep = commands.add_parser('prepare')
    prep.add_argument('--baseline', type=Path, required=True)
    prep.add_argument('--candidate', type=Path, required=True)
    prep.add_argument('--client-root', type=Path, required=True)
    prep.add_argument('--profile', required=True)
    prep.add_argument('--output', type=Path, required=True)
    prep.add_argument('--build-evidence', type=Path)
    execute = commands.add_parser('run')
    execute.add_argument('--output', type=Path, required=True)
    execute.add_argument('--cycles', type=int, default=8)
    execute.add_argument('--cores', default='2,3')
    execute.add_argument('--wait-timeout', type=int, default=300)
    execute.add_argument('--max-load', type=float, default=2.0)
    args = parser.parse_args()
    if args.command == 'prepare':
        prepare(args)
    else:
        if args.wait_timeout < 0 or args.max_load <= 0:
            parser.error('Invalid wait timeout or load threshold')
        run(args)


if __name__ == '__main__':
    main()
