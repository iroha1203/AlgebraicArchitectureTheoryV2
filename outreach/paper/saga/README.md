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
[zenodo_saga_related_work.md](../zenodo_saga_related_work.md) に整理する。

論文の日本語正本は [zenodo_saga_draft.md](zenodo_saga_draft.md) に置く。
release identity は確定済み: release tag `saga-paper-v1.0.0`、v1.0.0 deposit の version DOI
`10.5281/zenodo.21605207`(concept DOI `10.5281/zenodo.21603761`)、license CC BY 4.0。
本文は v1.0.1(2026-08-21、arXiv 投稿時の文言修正。release identity は不変)。

投稿言語は英語であり、英語正本(LaTeX)は [en/](en/) に置く。
本文内容の変更は両正本セットで行う。ビルド手順と規約は
[en/README.md](en/README.md) を正とする。

Release 監査面: claim-to-evidence 対応は
[zenodo_claim_evidence_matrix.md](zenodo_claim_evidence_matrix.md)、
canonical 対応表(内部監査用)は [zenodo_canonical_map.md](zenodo_canonical_map.md)、
deposit metadata は [zenodo_metadata.md](zenodo_metadata.md)、
deposit bundle の組成は [bundle/build_bundle.py](bundle/build_bundle.py) が固定する。

## 作業環境

共通の執筆・品質基準は [Paper guideline](../../../docs/paper/guideline.md)、
検査・投稿用 source の作成は [共通ツール](../_tools/README.md) を参照する。
`zenodo_saga.md` のチェック欄は初稿の計画であり、公開時の完了記録は
`zenodo_claim_evidence_matrix.md` の「P0-6 final review 記録」にある。
現在の再生成物の確認は、その都度の検査結果と投稿記録に残す。

証拠 bundle の再生成例:

```bash
python3 outreach/paper/saga/bundle/build_bundle.py --pdf .tmp/paper-saga-tectonic/build/main.pdf --out .tmp/saga-reconstruction
```

再生成 bundle は公開時の固定 commit から証拠と供給工程を取得し、現在の原稿と指定 PDF を
組み合わせる。`MANIFEST.json` は `local-reconstruction` と記録する。
指定 PDF と現在の原稿は共通ビルド記録の hash と照合する。公開済み deposit との
byte 一致と投稿可否は、その都度確認する。
