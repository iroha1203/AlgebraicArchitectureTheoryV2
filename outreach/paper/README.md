# 否定形禁止

> 各文・各段落・各節は、対象の肯定的な定義、役割、価値、達成から始める。

# Paper Workspace

このディレクトリは、AAT / SFT / ArchSig の研究成果を査読論文へまとめるための作業面である。
論文原稿、投稿先別の図表、claim-to-evidence 対応表、再現 artifact の案内を置く。

数学本文、Lean 実装、tooling 仕様、研究の進行状態は、それぞれの canonical source で管理する。
このディレクトリに置く論文中の各 claim は、canonical source と固定された一次証拠へ対応させる。

## Zenodo SAGA paper

SAGA の数学、Lean 形式化、ArchSig による実コード診断を統合する長編論文の要件は
[zenodo_saga.md](zenodo_saga.md) で整理する。論文は、一つの SAGA 比較定理が数学的構成、
機械検証、有限 measurement を通って実在 software の一セントへ到達した研究成果として構成する。

Related Work の原典調査、必須文献、比較軸、本文候補は
[zenodo_saga_related_work.md](zenodo_saga_related_work.md) に整理する。

論文本文の初稿下書きは [zenodo_saga_draft.md](zenodo_saga_draft.md) に置く。
本文中の `TODO:` は release identity 確定時に固定する箇所を示す。

投稿言語は英語であり、英語正本(LaTeX)は [en/](en/) に置く。
日本語原稿は執筆原本・草稿管理面として維持し、本文内容の変更は英語正本とセットで行う。
ビルド手順と規約は [en/README.md](en/README.md) を正とする。
