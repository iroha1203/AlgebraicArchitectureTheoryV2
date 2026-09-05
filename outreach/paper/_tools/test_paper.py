"""出力汚染・検査の見逃し・古い文献記録に対する回帰検査。"""
import csv
import json
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path
import paper


class PaperTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.data = {'main.tex': b'\\documentclass{article}\n\\begin{document}\n\\label{ok}\\ref{ok}\\cite{real}\\bibliography{refs}\n\\end{document}',
                     'refs.bib': b'@article{real, title={Real paper}}'}
        self.cfg = {'schema': 'paper-project/v1', 'main': 'main.tex',
                    'environment': {'tectonic': 'Tectonic 0.16.9', 'texlive': '2025'},
                    'files': [{'source': k, 'target': k} for k in self.data]}
        for name, raw in self.data.items():
            (self.root / name).write_bytes(raw)
        self.config = self.root / 'paper.json'
        self.config.write_text(json.dumps(self.cfg))

    def test_missing_reference_citation_and_asset(self):
        self.data['main.tex'] += b'\\ref{missing}\\cite{fake}\\includegraphics{lost}'
        findings = paper.check(self.cfg, self.data)
        self.assertEqual(len(findings), 3)

    def test_comments_do_not_define_labels(self):
        self.data['main.tex'] += b'\n% \\label{fake}\n\\ref{fake}'
        self.assertEqual(len(paper.check(self.cfg, self.data)), 1)

    def test_marker_in_comment_is_included_in_submission_scan(self):
        self.data['main.tex'] += b'\n% TODO insert real results'
        self.assertTrue(paper.check(self.cfg, self.data))

    def test_path_escape_and_symlink(self):
        for value in ['../private.tex', '/private.tex', 'a/../../private.tex']:
            with self.assertRaises(ValueError):
                paper.relative(value)
        (self.root / 'refs.bib').unlink()
        (self.root / 'refs.bib').symlink_to(self.root / 'main.tex')
        with self.assertRaises(ValueError):
            paper.load(self.config)

    def test_output_preserved(self):
        out = self.root / 'out'
        out.mkdir()
        (out / 'precious').write_text('keep')
        with self.assertRaises(ValueError):
            paper.prepare(out, self.data)
        self.assertEqual((out / 'precious').read_text(), 'keep')

    def test_stale_reference_record(self):
        cfg, data, sha, _ = paper.load(self.config)
        csvpath = self.root / 'references.csv'
        row = {'key': 'real', 'status': 'verified', 'source_url': 'https://example.org/paper',
               'source_locator': 'p.1', 'cited_claim': 'claim', 'reviewer': 'reviewer',
               'checked_on': '2026-09-05', 'bib_sha256': paper.digest(paper.encoded({'refs.bib': paper.digest(data['refs.bib'])})),
               'manuscript_sha256': sha}
        with csvpath.open('w', newline='') as stream:
            writer = csv.DictWriter(stream, row.keys()); writer.writeheader(); writer.writerow(row)
        self.assertFalse(paper.check(cfg, data, csvpath, sha))
        (self.root / 'main.tex').write_bytes(data['main.tex'] + b' changed')
        cfg, data, sha, _ = paper.load(self.config)
        self.assertTrue(paper.check(cfg, data, csvpath, sha))

    def test_pdf_record_mismatch(self):
        pdf = self.root / 'main.pdf'
        pdf.write_bytes(b'PDF fixture')
        record = self.root / 'build.json'
        record.write_text(json.dumps({'pdf_sha256': paper.digest(pdf.read_bytes()),
                                      'source_sha256': 'stale'}))
        with patch.object(sys, 'argv', ['paper.py', 'check', str(self.config), '--pdf', str(pdf), '--build-record', str(record)]), patch.object(paper, 'run', return_value=(0, 'clean text')), patch('builtins.print'):
            self.assertEqual(paper.main(), 1)

    def test_duplicate_destination_rejected(self):
        self.cfg['files'][1]['target'] = 'main.tex'
        self.config.write_text(json.dumps(self.cfg))
        with self.assertRaises(ValueError):
            paper.load(self.config)

    def test_zip_reproducibility_and_allowlist(self):
        (self.root / 'private.txt').write_text('do not publish')
        for name in ['first', 'second']:
            run = subprocess.run([sys.executable, str(Path(paper.__file__)), 'package', str(self.config), '--out', str(self.root / name)], capture_output=True)
            self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual((self.root/'first/source.zip').read_bytes(), (self.root/'second/source.zip').read_bytes())
        with paper.zipfile.ZipFile(self.root/'first/source.zip') as z:
            self.assertEqual(set(z.namelist()), set(self.data))
        manifest = json.loads((self.root/'first/manifest.json').read_text())
        self.assertFalse(manifest['submission_ready'])


if __name__ == '__main__':
    unittest.main()
