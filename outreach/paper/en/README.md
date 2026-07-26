# SAGA paper — English LaTeX source

このディレクトリは Zenodo 投稿用 SAGA 論文の**英語正本**(LaTeX)である。
最終投稿言語は英語であり(2026-07-24 決定)、投稿成果物はここからコンパイルした PDF を一次、
tex / bib / 図ソース一式を添付として deposit する。

日本語原稿 [`../zenodo_saga_draft.md`](../zenodo_saga_draft.md) は執筆原本であり、
草稿管理(執筆残作業チェックリスト、canonical 対応表=内部監査用付録)は日本語原稿側で管理を続ける。
本文内容の変更は英語正本とセットで行う。

## 構成

| ファイル | 内容 |
| --- | --- |
| `main.tex` | preamble、タイトル、要旨、章の取り込み、謝辞、参考文献 |
| `sec01_intro.tex` 〜 `sec10_conclusion.tex` | 第1〜10章 |
| `appendix.tex` | Appendix A(仮定の帰属)、Appendix B(Lean source 対応) |

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
- 本文中の `TODO:` は release identity(release tag、CI run、deposit path、metadata)確定時に
  固定する箇所を示す。冒頭の Draft note と `% REMOVE AT RELEASE` ブロックは release 時に除去する。
- 本文にはリポジトリ内部参照(repo パス、canonical 番号、schema id)を書かない。
  例外は Appendix B の Lean source 構成(status の一次証拠)である。
