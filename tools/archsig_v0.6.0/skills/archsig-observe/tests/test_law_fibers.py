import importlib.util
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'scripts' / 'law_fibers.py'
spec = importlib.util.spec_from_file_location('law_fibers', SCRIPT)
fibers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fibers)


def table():
    return {'scope': 'Three candidate operation models, two selected Law values.',
            'sources': ['a', 'b', 'c'], 'laws': ['preserves', 'authorized'],
            'q': {'a': 'same', 'b': 'same', 'c': 'other'},
            'v': {'a': {'preserves': 'yes', 'authorized': 'yes'},
                  'b': {'preserves': 'yes', 'authorized': 'yes'},
                  'c': {'preserves': 'no', 'authorized': 'yes'}}}


class FibersTest(unittest.TestCase):
    def test_descent_and_coarsest_partition(self):
        result = fibers.check(table())
        self.assertTrue(result['adequate_on_table'])
        self.assertFalse(result['vacuous'])
        self.assertEqual(result['joint_law_partition'], [['a', 'b'], ['c']])
        for source, q in table()['q'].items():
            self.assertEqual(result['descent'][q], table()['v'][source])

    def test_added_law_breaks_previous_compression(self):
        value = table()
        value['laws'].append('new')
        for s in value['sources']:
            value['v'][s]['new'] = 'x' if s == 'a' else 'y'
        result = fibers.check(value)
        self.assertFalse(result['adequate_on_table'])
        self.assertEqual(result['counterexamples'], [{'left': 'a', 'right': 'b', 'laws': ['new']}])
        self.assertNotIn('descent', result)
        value['q']['b'] = 'refined'
        self.assertTrue(fibers.check(value)['adequate_on_table'])

    def test_all_binary_functions_on_three_sources(self):
        # Exhaust all q and two-Law functions; independently check every ordered pair.
        for bits in itertools.product(('0', '1'), repeat=9):
            value = table()
            for i, s in enumerate(value['sources']):
                value['q'][s] = bits[i]
                value['v'][s] = dict(zip(value['laws'], bits[3 + 2*i:5 + 2*i]))
            result = fibers.check(value)
            expected = all(value['q'][a] != value['q'][b] or value['v'][a] == value['v'][b]
                           for a in value['sources'] for b in value['sources'])
            self.assertEqual(result['adequate_on_table'], expected)
            classes = result['joint_law_partition']
            for a in value['sources']:
                for b in value['sources']:
                    self.assertEqual(any(a in c and b in c for c in classes), value['v'][a] == value['v'][b])

    def test_incomplete_or_ambiguous_tables(self):
        variants = []
        value = table(); del value['v']['a']['preserves']; variants.append(value)
        value = table(); del value['q']['a']; variants.append(value)
        value = table(); value['sources'].append('a'); variants.append(value)
        value = table(); value['laws'].append('preserves'); variants.append(value)
        value = table(); value['v']['a']['preserves'] = None; variants.append(value)
        value = table(); value['q']['a'] = True; variants.append(value)
        value = table(); value['v']['extra'] = {}; variants.append(value)
        value = table(); value['adequate'] = True; variants.append(value)
        for value in variants:
            with self.subTest(value=value), self.assertRaises(ValueError):
                fibers.check(value)

    def test_empty_family_is_explicit(self):
        value = table()
        value.update(sources=[], q={}, v={})
        result = fibers.check(value)
        self.assertTrue(result['adequate_on_table'])
        self.assertTrue(result['vacuous'])
        value = table()
        value.update(laws=[], v={s: {} for s in value['sources']})
        self.assertTrue(fibers.check(value)['vacuous'])
        self.assertEqual(fibers.check(value)['joint_law_partition'], [['a', 'b', 'c']])

    def test_cli_exit_codes_and_duplicate_json(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'table.json'
            value = table()
            for expected in (0, 1):
                if expected:
                    value['q']['c'] = 'same'
                path.write_text(json.dumps(value))
                run = subprocess.run([sys.executable, str(SCRIPT), str(path)], capture_output=True, text=True)
                self.assertEqual(run.returncode, expected)
                self.assertEqual(json.loads(run.stdout)['adequate_on_table'], expected == 0)
            path.write_text('{"scope":"first","scope":"second"}')
            run = subprocess.run([sys.executable, str(SCRIPT), str(path)], capture_output=True, text=True)
            self.assertEqual(run.returncode, 2)
            self.assertEqual(run.stdout, '')
            self.assertIn('duplicate key', run.stderr)


if __name__ == '__main__':
    unittest.main()
