import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'scripts' / 'evidence.py'
spec = importlib.util.spec_from_file_location('evidence', SCRIPT)
evidence = importlib.util.module_from_spec(spec)
spec.loader.exec_module(evidence)


class EvidenceTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / 'source.py'
        self.data = 'name = "意味"\r\nreturn name\n'.encode('utf-8')
        self.path.write_bytes(self.data)
        self.map = {
            'sources': [{'id': 'code', 'uri': 'https://example.org/source.py',
                         'revision': 'r1', 'digest': 'sha256:' + hashlib.sha256(self.data).hexdigest()}],
            'origins': [{'id': 'read', 'mode': 'observed', 'method': 'semantic reading',
                         'locations': [{'source': 'code', 'path': 'source.py', 'span': [0, len(self.data)]}]}],
            'snapshots': [{'id': 'v', 'atoms': [
                {'id': 'a', 'subject': 's', 'field': 'N.E.name', 'value': '意味', 'origin': 'read'},
                {'id': 'b', 'subject': 's', 'field': 'N.E.returnsName', 'value': True, 'origin': 'read'}]}],
        }

    def test_shared_origin_preserves_values_and_exact_bytes(self):
        result = evidence.expand(self.map, ['v/a', 'v/b'], {'code': self.path})
        self.assertEqual(len(result['origins']), 1)
        self.assertEqual(result['atoms'][0]['value'], '意味')
        self.assertEqual(result['origins'][0]['locations'][0]['excerpt'].encode(), self.data)
        self.assertIn('not verified', result['verification'])

    def test_missing_links_and_stale_source_fail(self):
        for selector, files in [('v/missing', {'code': self.path}), ('v/a', {})]:
            with self.assertRaises(KeyError):
                evidence.expand(self.map, [selector], files)
        for collection in ['sources', 'origins']:
            value = copy.deepcopy(self.map)
            value[collection] = []
            with self.assertRaises(KeyError):
                evidence.expand(value, ['v/a'], {'code': self.path})
        self.path.write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'digest mismatch'):
            evidence.expand(self.map, ['v/a'], {'code': self.path})

    def test_utf8_boundaries_and_bounds(self):
        for span in [[-1, 2], [0, len(self.data) + 1], [2, 1], [False, 1], [9, 10]]:
            value = copy.deepcopy(self.map)
            value['origins'][0]['locations'][0]['span'] = span
            with self.assertRaises(ValueError):
                evidence.expand(value, ['v/a'], {'code': self.path})

    def test_cli_duplicate_keys_and_selection(self):
        path = Path(self.temp.name) / 'map.json'
        path.write_text(json.dumps(self.map))
        command = [sys.executable, str(SCRIPT), str(path), '--atom', 'v/a', '--source', f'code={self.path}']
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['atoms'][0]['origin'], 'read')
        path.write_text('{"sources":[],"sources":[]}')
        result = subprocess.run(command, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, '')


if __name__ == '__main__':
    unittest.main()
