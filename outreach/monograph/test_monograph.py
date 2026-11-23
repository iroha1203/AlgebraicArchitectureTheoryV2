"""AAT モノグラフ生成パイプラインの回帰テストおよび失敗ケース検査。"""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import monograph  # noqa: E402


def make_fixture(root: Path, files: dict[str, str], manifest_extra: dict | None = None) -> tuple[Path, Path, Path]:
    src = root / 'src'
    src.mkdir(parents=True, exist_ok=True)
    for rel, content in files.items():
        p = src / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding='utf-8')
    preamble = root / 'preamble.tex'
    preamble.write_text(
        '% test preamble\n\\newcommand{\\aattoc}{\\phantomsection\\label{doc:toc}}\n',
        encoding='utf-8',
    )
    structure = manifest_extra.get('structure') if manifest_extra else [
        {
            'kind': 'part',
            'id': 'part_1',
            'label': 'part:1',
            'part_num': '第I部',
            'title': '基礎',
            'subtitle': '第1章',
            'chapters': [{'id': 'chapter_01', 'source': 'ch1.md'}],
        }
    ]
    cfg = {
        'schema': 'aat-monograph-manifest/v1',
        'title': 'テストモノグラフ',
        'subtitle': 'Test',
        'main': 'aat_monograph.tex',
        'source_dir': 'src',
        'environment': {'tectonic': 'Tectonic 0.16.9', 'texlive': '2025'},
        'excluded_files': ['README.md'],
        'readme_anchor_map': {
            '': 'doc:toc',
            '第i部-基礎': 'part:1',
        },
        'structure': structure,
    }
    if manifest_extra:
        cfg.update(manifest_extra)
    manifest = root / 'manifest.json'
    manifest.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding='utf-8')
    return manifest, preamble, src


class MonographConversionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_declarations_branch_numbers_equations_proof_and_qed(self) -> None:
        md = (
            '# 第11章 修復\n\n'
            '## 11.1 基本定理\n\n'
            '**定理11.5a（枝番保持と数学記号 $`C_4\\to C_2`$）.** 任意の $`x\\in X`$ について成り立つ。\n\n'
            '**式(11.5a)**\n\n'
            '```math\n'
            'f(x) = \\sum_{i=1}^n a_i x^i\n'
            '```\n\n'
            '**証明.** 直接計算による。$`[\\theta](\\delta)`$ はリンクと誤認しない。 □\n\n'
            '[前章](ch1.md) · [全体の構成](README.md)\n'
        )
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': md, 'README.md': '# Top\n'})
        _, tex_files, _, _, findings, stats = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertEqual(findings, [])
        ch_tex = tex_files['chapters/chapter_01.tex'].decode('utf-8')
        self.assertIn(r'\aatdecl{decl:chapter_01:d001}{定理11.5a（枝番保持と数学記号 $C_4\to C_2$）.}', ch_tex)
        self.assertIn(r'\label{eq:11_5a}\tag{11.5a}', ch_tex)
        self.assertIn(r'\aatproof{証明.}', ch_tex)
        self.assertIn(r'$[\theta](\delta)$', ch_tex)
        self.assertIn(r'\aatqed', ch_tex)
        self.assertNotIn('全体の構成', ch_tex)
        self.assertEqual(stats.declarations, 1)
        self.assertEqual(stats.equations, 1)
        self.assertEqual(stats.proofs, 1)
        self.assertEqual(stats.qed_marks, 1)
        self.assertEqual(stats.stripped_nav_footers, 1)

    def test_prose_ending_with_link_is_not_stripped(self) -> None:
        md = (
            '# 第1章 テスト\n\n'
            '詳細は[第I部](README.md#第i部-基礎)を参照する。\n'
        )
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': md, 'README.md': '# Top\n'})
        _, tex_files, _, _, findings, stats = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertEqual(findings, [])
        ch_tex = tex_files['chapters/chapter_01.tex'].decode('utf-8')
        self.assertIn(r'\hyperref[part:1]{第I部}', ch_tex)
        self.assertEqual(stats.stripped_nav_footers, 0)

    def test_cross_file_links_and_anchors(self) -> None:
        ch1 = (
            '# 第1章 はじめに\n\n'
            '## 1.1 定義と記号\n\n'
            '次章の[2.1節](../part_2/ch2.md#21-結果)と[第I部](../README.md#第i部-基礎)を参照。\n'
        )
        ch2 = (
            '# 第2章 つづき\n\n'
            '## 2.1 結果\n\n'
            '[第1章](../part_1/ch1.md)および[1.1節](../part_1/ch1.md#11-定義と記号)を使う。\n'
        )
        structure = [
            {
                'kind': 'part',
                'id': 'part_1',
                'label': 'part:1',
                'part_num': '第I部',
                'title': '基礎',
                'subtitle': '第1–2章',
                'chapters': [
                    {'id': 'chapter_01', 'source': 'part_1/ch1.md'},
                    {'id': 'chapter_02', 'source': 'part_2/ch2.md'},
                ],
            }
        ]
        manifest, preamble, src = make_fixture(
            self.root,
            {'part_1/ch1.md': ch1, 'part_2/ch2.md': ch2, 'README.md': '# Top\n'},
            {'structure': structure},
        )
        _, tex_files, _, _, findings, stats = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertEqual(findings, [])
        ch1_tex = tex_files['chapters/chapter_01.tex'].decode('utf-8')
        ch2_tex = tex_files['chapters/chapter_02.tex'].decode('utf-8')
        self.assertIn(r'\hyperref[sec:chapter_02:h001]{2.1節}', ch1_tex)
        self.assertIn(r'\hyperref[part:1]{第I部}', ch1_tex)
        self.assertIn(r'\hyperref[doc:chapter_01]{第1章}', ch2_tex)
        self.assertIn(r'\hyperref[sec:chapter_01:h001]{1.1節}', ch2_tex)
        self.assertEqual(stats.internal_links, 4)

    def test_tables_nested_lists_and_indented_math(self) -> None:
        md = (
            '# 第1章 構造\n\n'
            '## 1.1 表と箇条書き\n\n'
            '| 記号 | 意味 | 参照 |\n'
            '| --- | --- | --- |\n'
            '| $`A\\vert_U`$ | 制限と `apply` の操作 | [1.1](#11-表と箇条書き) |\n\n'
            '1. 外側の項目\n'
            '   ```math\n'
            '   x + y = z\n'
            '   ```\n'
            '   継続の文。\n'
            '   - 内側の項目（100% & #1_a）\n'
        )
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': md, 'README.md': '# Top\n'})
        _, tex_files, _, _, findings, stats = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertEqual(findings, [])
        ch_tex = tex_files['chapters/chapter_01.tex'].decode('utf-8')
        self.assertIn(r'\begin{xltabular}{\linewidth}', ch_tex)
        self.assertIn(r'$A\vert_U$', ch_tex)
        self.assertIn(r'\texttt{apply}', ch_tex)
        self.assertIn(r'\begin{enumerate}', ch_tex)
        self.assertIn(r'\begin{itemize}', ch_tex)
        self.assertIn('x + y = z', ch_tex)
        self.assertIn(r'100\% \& \#1\_a', ch_tex)
        self.assertEqual(stats.tables, 1)
        self.assertEqual(stats.display_maths, 1)


class MonographFailureDetectionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_unclosed_inline_math_fails(self) -> None:
        md = '# 第1章 失敗\n\n未閉じの数式 $`x + y を含む。\n'
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': md, 'README.md': '# Top\n'})
        _, _, _, _, findings, _ = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertTrue(any('未閉じのインライン数式' in f['message'] for f in findings))

    def test_bare_dollar_fails(self) -> None:
        md = '# 第1章 失敗\n\n単独の $x$ 記法。\n'
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': md, 'README.md': '# Top\n'})
        _, _, _, _, findings, _ = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertTrue(any('非標準の $' in f['message'] for f in findings))

    def test_unclosed_math_fence_fails(self) -> None:
        md = '# 第1章 失敗\n\n```math\nx = 1\n'
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': md, 'README.md': '# Top\n'})
        _, _, _, _, findings, _ = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertTrue(any('未閉じのコード/数式ブロック' in f['message'] for f in findings))

    def test_missing_link_file_and_anchor_fail(self) -> None:
        md = (
            '# 第1章 失敗\n\n'
            '## 1.1 実在節\n\n'
            '[不在ファイル](missing.md) と [不在アンカー](ch1.md#存在しない節) と [脱出](../../outside.md)。\n'
        )
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': md, 'README.md': '# Top\n'})
        _, _, _, _, findings, _ = monograph.build_tex_bundle(manifest, preamble, str(src))
        link_errors = [f for f in findings if '存在しない相対リンクまたはアンカー' in f['message']]
        self.assertEqual(len(link_errors), 3)

    def test_unregistered_markdown_file_fails(self) -> None:
        manifest, preamble, src = make_fixture(
            self.root,
            {'ch1.md': '# 第1章 OK\n', 'extra_unregistered.md': '# 忘れられた付録\n', 'README.md': '# Top\n'},
        )
        _, _, _, _, findings, _ = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertTrue(any('マニフェスト未登録ファイル: extra_unregistered.md' in f['message'] for f in findings))

    def test_hidden_unicode_and_local_path_fail(self) -> None:
        sample_local = '/' + 'Users/alice/secret.tex'
        md = f'# 第1章 衛生\n\n隠し文字\u200b と {sample_local}。\n'
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': md, 'README.md': '# Top\n'})
        _, _, _, _, findings, _ = monograph.build_tex_bundle(manifest, preamble, str(src))
        self.assertTrue(any('hidden / bidirectional Unicode' in f['message'] for f in findings))
        self.assertTrue(any('ローカル絶対パス' in f['message'] for f in findings))

    def test_refuse_overwrite_existing_output(self) -> None:
        out = self.root / 'existing_out'
        out.mkdir()
        (out / 'keep.txt').write_text('precious', encoding='utf-8')
        with self.assertRaises(ValueError):
            monograph.prepare_output(out, {'main.tex': b'hello'})
        self.assertEqual((out / 'keep.txt').read_text(encoding='utf-8'), 'precious')

    def test_analyze_tex_log_detects_errors(self) -> None:
        bad_log = '\n'.join([
            '! [] \\OML/cmm/m/it/10 H[]\\OT1/cmr/m/n/10 (F)',
            '! Undefined control sequence.',
            'l.42 \\unknownmacro',
            "LaTeX Warning: Reference `sec:missing' on page 3 undefined on input line 10.",
            'LaTeX Warning: There were undefined references.',
            'Missing character: There is no 𠮷 (U+20BB7) in font HaranoAjiMincho!',
            'Overfull \\hbox (12.3pt too wide) in paragraph at lines 50--52',
        ])
        res = monograph.analyze_tex_log(bad_log)
        self.assertEqual(len(res['errors']), 4)
        self.assertFalse(any('\\OML/cmm' in e for e in res['errors']))
        self.assertEqual(len(res['overfull']), 1)

    def test_pdf_check_detects_hash_mismatch_and_unresolved_marks(self) -> None:
        manifest, preamble, src = make_fixture(self.root, {'ch1.md': '# 第1章 OK\n', 'README.md': '# Top\n'})
        pdf = self.root / 'aat_monograph.pdf'
        pdf.write_bytes(b'%PDF-1.5 fixture')
        rec = self.root / 'build.json'
        rec.write_text(
            json.dumps({'pdf_sha256': monograph.digest(pdf.read_bytes()), 'source_sha256': 'stale'}),
            encoding='utf-8',
        )
        with (
            patch.object(monograph.shutil, 'which', return_value='/usr/bin/pdftotext'),
            patch.object(monograph, 'run_cmd', return_value=(0, 'Section ?? text')),
            patch('builtins.print'),
        ):
            rc = monograph.main([
                'check',
                '--manifest', str(manifest),
                '--preamble', str(preamble),
                '--source', str(src),
                '--pdf', str(pdf),
                '--build-record', str(rec),
            ])
        self.assertEqual(rc, 1)


class RealCorpusIntegrationTests(unittest.TestCase):
    def test_real_aat_corpus_checks_cleanly(self) -> None:
        _, tex_files, originals, _, findings, stats = monograph.build_tex_bundle(
            monograph.DEFAULT_MANIFEST,
            monograph.DEFAULT_PREAMBLE,
        )
        self.assertEqual(findings, [], f'Unexpected findings: {findings[:5]}')
        self.assertEqual(len(originals), 27)
        self.assertEqual(stats.chapters, 27)
        self.assertEqual(stats.declarations, 378)
        self.assertEqual(stats.equations, 132)
        self.assertEqual(stats.tables, 18)
        self.assertIn('chapters/appendix_f.tex', tex_files)
        ch11 = tex_files['chapters/chapter_11.tex'].decode('utf-8')
        ch14 = tex_files['chapters/chapter_14.tex'].decode('utf-8')
        ch16 = tex_files['chapters/chapter_16.tex'].decode('utf-8')
        ch19 = tex_files['chapters/chapter_19.tex'].decode('utf-8')
        appf = tex_files['chapters/appendix_f.tex'].decode('utf-8')
        self.assertIn('命題11.5a', ch11)
        self.assertIn('構成14.6b', ch14)
        self.assertIn(r'\tag{16.22a}', ch16)
        self.assertIn('定理19.2a', ch19)
        self.assertIn('付録F', appf)


if __name__ == '__main__':
    unittest.main()
