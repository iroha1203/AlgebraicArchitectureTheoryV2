# SAGA paper — English LaTeX source

このディレクトリは Zenodo 投稿用 SAGA 論文の**英語正本**(LaTeX)である。
最終投稿言語は英語であり(2026-07-24 決定)、投稿成果物はここからコンパイルした PDF を一次、
tex / bib / 図ソース一式を添付として deposit する。

日本語正本は [`../zenodo_saga_draft.md`](../zenodo_saga_draft.md)。
本文内容の変更は両正本セットで行う。canonical 対応表(内部監査用)は
[`../zenodo_canonical_map.md`](../zenodo_canonical_map.md) が正本
(草稿管理付録は release 時に除去済み、2026-07-26)。

## 構成

| ファイル | 内容 |
| --- | --- |
| `main.tex` | preamble、タイトル、要旨、章の取り込み、謝辞、参考文献 |
| `sec01_intro.tex` 〜 `sec10_conclusion.tex` | 第1〜10章 |
| `appendix.tex` | Appendix A(仮定の帰属)、Appendix B(Lean source 対応)、Appendix C(測定契約と監査面) |

参考文献の正本は [`../zenodo_saga_references.bib`](../zenodo_saga_references.bib)、
図2点は `../zenodo_saga_figure1_comparison.png` / `../zenodo_saga_figure2_one_cent.png` を
相対参照する(重複コピーを置かない)。deposit bundle 作成時にこれらを同梱する。

## ビルド

```bash
cd outreach/paper/en && tectonic main.tex   # main.pdf を生成
```

tectonic は単体バイナリの TeX エンジン(`brew install tectonic`)。
生成物 `main.pdf` はコミットしない(`.gitignore` 済み)。

## 規約

- 定理番号は日本語原稿と同一(節内共有カウンタ。補題 5.2A は手動番号環境 `lemmafiveA`)。
- release identity は確定・印字済み(tag `saga-paper-v1.0.0`、version DOI
  `10.5281/zenodo.21603762`、CC BY 4.0。Draft note は除去済み、2026-07-26)。
- 本文にはリポジトリ内部参照(repo パス、canonical 番号、schema id)を書かない。
  例外は Appendix B の Lean source 構成と Appendix C の deposit / 再現面
  (いずれも status・再現の一次証拠)である。
