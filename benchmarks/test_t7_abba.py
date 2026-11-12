import argparse
import importlib.util
import json
from pathlib import Path
import socket
import sys
import tempfile
import types
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location('t7_abba', Path(__file__).with_name('t7_abba.py'))
h = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(h)


class HarnessTests(unittest.TestCase):
    def test_schedule_balance_and_parity(self):
        rows = list(h.schedule(8))
        self.assertEqual(len(rows), 128)
        for cycle in range(8):
            selected = [r for r in rows if r[0] == cycle]
            self.assertEqual(selected[0][1], 'AA' if cycle % 2 == 0 else 'AB')
            for phase in ('AA', 'AB'):
                for model in ('nanosp', 'nanox'):
                    labels = ''.join(r[4] for r in selected if r[1:3] == (phase, model))
                    self.assertEqual(labels, 'ABBA' if cycle % 2 == 0 else 'BAAB')

    def test_own_descendants_excluded_external_builds_retained(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for pid, name, children, cmd in (
                (100, 'python3', '101', b'python\0harness'),
                (101, 'python3', '102', b'python\0-m\0speculos'),
                (102, 'qemu-arm-static', '', b'qemu'),
                (200, 'python3', '', b'python\0-m\0speculos'),
                (201, 'cargo', '', b'cargo'),
                (202, 'qemu-arm-static', '', b'qemu'),
                (203, 'rustc', '', b'rustc'),
                (204, 'opt', '', b'opt'),
                (205, 'make', '', b'make'),
                (206, 'cc1', '', b'cc1'),
                (207, 'ld.lld', '', b'ld.lld'),
                (208, 'lake', '', b'lake'),
                (209, 'lean', '', b'lean'),
                (210, 'clang', '', b'clang'),
            ):
                entry = root / str(pid)
                (entry / 'task' / str(pid)).mkdir(parents=True)
                (entry / 'task' / str(pid) / 'children').write_text(children)
                (entry / 'comm').write_text(name)
                (entry / 'cmdline').write_bytes(cmd)
            with patch.object(h.os, 'getpid', return_value=100):
                result = h.processes(root)
            self.assertEqual({r['pid'] for r in result}, set(range(200, 211)))

    def test_guard_waits_and_returns_without_real_sleep(self):
        with patch.object(h, 'processes', side_effect=[[{'pid': 1}], []]), \
                patch.object(h.os, 'getloadavg', return_value=(1, 1, 1)), \
                patch.object(h.time, 'monotonic', side_effect=[0, 0, 0]), \
                patch.object(h.time, 'sleep') as sleep, patch.object(h, 'emit') as emit:
            h.guard(Path('/unused'), timeout=10)
            sleep.assert_called_once_with(10)
            self.assertEqual(emit.call_count, 2)

    def test_guard_timeout_uses_monotonic(self):
        with patch.object(h, 'processes', return_value=[]), \
                patch.object(h.os, 'getloadavg', return_value=(3, 1, 1)), \
                patch.object(h.time, 'monotonic', side_effect=[10, 11]), \
                patch.object(h.time, 'sleep') as sleep, patch.object(h, 'emit'):
            with self.assertRaisesRegex(RuntimeError, 'timeout'):
                h.guard(Path('/unused'), timeout=1)
            sleep.assert_not_called()

    def test_free_port_probe_releases_socket(self):
        port = h.free_port()
        with socket.socket() as probe:
            probe.bind(('127.0.0.1', port))

    def test_runtime_verification_accepts_match_rejects_mismatch(self):
        library = {'path': '/tmp/mock-library.elf', 'sha256': 'abc'}
        with patch.object(h.Path, 'read_bytes', return_value=b'qemu\0-m\0nanox\0-a\027\0-c\0/tmp/mock-library.elf:0x0\0'), \
                patch.object(h, 'digest', return_value='abc'):
            with self.assertRaisesRegex(RuntimeError, 'Unable|mismatch'):
                h.runtime_api(123, 'nanox', '27', library)
        command = b'qemu\0-m\0nanox\0-a\0' + b'27\0-c\0/tmp/mock-library.elf:0x0\0'
        with patch.object(h.Path, 'read_bytes', return_value=command), patch.object(h, 'digest', return_value='abc'):
            self.assertEqual(h.runtime_api(123, 'nanox', '27', library)['api'], '27')
            with self.assertRaisesRegex(RuntimeError, 'mismatch'):
                h.runtime_api(123, 'nanox', '22', library)

    def test_mock_run_warmup_launch_unit_and_start_before_api(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = {'host': {}, 'harness': {'path': 'mock', 'sha256': 'hash'},
                        'workloads': {'path': 'mock', 'sha256': 'hash'},
                        'python': {'path': 'mock', 'sha256': 'hash'},
                        'test_utils': {'path': 'mock', 'sha256': 'hash'},
                        'txmaker': {'path': 'mock', 'sha256': 'hash'}, 'tools': {},
                        'client_root': '/mock', 'client_python': {},
                        'artifacts': {'A': {'nanox': {'path': 'mock', 'sha256': 'hash',
                                                     'api': '27', 'library': {'path': 'mock', 'sha256': 'hash'}}}}}
            (root / 'manifest.json').write_text(json.dumps(manifest))
            events = []
            calls = []

            class Comm:
                process = types.SimpleNamespace(pid=123)

                def __init__(self, *args, **kwargs):
                    pass

                def start(self):
                    events.append('start')

                def stop(self):
                    events.append('stop')

                def apdu_exchange(self, *args, **kwargs):
                    calls.append('GET_VERSION')

            class Client:
                def register_wallet(self, *args):
                    calls.append('REGISTER_WALLET')
                    return None, 'mock-hmac'

                def __getattr__(self, name):
                    return lambda *args: calls.append(name)

            def runtime(*args):
                self.assertEqual(events, ['start'])
                return {'api': '27', 'model': 'nanox', 'pid': 123}

            modules = {'speculos': types.ModuleType('speculos'),
                       'speculos.client': types.SimpleNamespace(SpeculosClient=Comm),
                       'ledger_bitcoin': types.SimpleNamespace(createClient=lambda *a, **k: Client(),
                                                              Chain=types.SimpleNamespace(TEST='test'))}
            args = argparse.Namespace(output=root, cycles=8, cores='2,3', wait_timeout=0, max_load=2)
            with patch.dict(sys.modules, modules), patch.dict(h.os.environ), \
                    patch.object(h, 'host', return_value={}), patch.object(h, 'digest', return_value='hash'), \
                    patch.object(h, 'tree_hashes', return_value={}), \
                    patch.object(h.os, 'sched_getaffinity', return_value={2, 3}), \
                    patch.object(h.os, 'sched_setaffinity') as affinity, \
                    patch.object(h, 'guard'), patch.object(h, 'processes', return_value=[]), \
                    patch.object(h.os, 'getloadavg', return_value=(0, 0, 0)), \
                    patch.object(h, 'runtime_api', side_effect=runtime), \
                    patch.object(h, 'schedule', return_value=[(0, 'AA', 'nanox', 0, 'B')]), \
                    patch.object(h, 'workload_namespace', return_value=(dict.fromkeys(
                        ['wp_wsh_3of5', 'wp_tr', 'psbt_tr_3in', 'psbt_wsh_3in']), 'mock-seed')):
                h.run(args)
                affinity.assert_called_once_with(0, [2, 3])
            rows = [json.loads(line) for line in (root / 'samples.jsonl').read_text().splitlines()]
            self.assertEqual(len(rows), 7)
            self.assertTrue(all(r['unit'] == 'launch' and r['artifact'] == 'A' for r in rows))
            self.assertTrue(all(not r['contaminated'] for r in rows))
            self.assertEqual(len(calls), 15)
            self.assertEqual(events, ['start', 'stop'])


if __name__ == '__main__':
    unittest.main()
