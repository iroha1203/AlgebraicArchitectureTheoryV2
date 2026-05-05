# docs 読み方

このディレクトリは、第一級設計書、全体方針、Lean 形式化、個別 design、
実証 protocol を分けて管理する。

## 初めて読む順序

初見では次の順に読む。

1. [研究の全体目標](research_goal.md)
2. [AAT v2 数学設計書](aat_v2_mathematical_design.md)
3. [AAT v2 ツール設計書](aat_v2_tooling_design.md)
4. [証明義務と実証仮説](proof_obligations.md)
5. [Lean 定義・定理索引](lean_theorem_index.md)
6. 必要に応じて [個別設計メモ](design/README.md), [PRD 一覧](prd/README.md), `docs/empirical/`

## 全体文書

- [研究の全体目標](research_goal.md): AAT v2 の全体目標と研究全体像を示す入口文書。
- [AAT v2 数学設計書](aat_v2_mathematical_design.md): AAT を機能追加による architecture extension theory として整理し、split extension、obstruction witness、Architecture Extension Formula、homotopy skeleton、解析的 representation の責務境界を定義する。
- [AAT v2 ツール設計書](aat_v2_tooling_design.md): Feature Extension Report、AIR、claim taxonomy、coverage metadata、AI session の厳格扱い、CI integration を定義する。
- [AAT v2 数学設計書の Design principle classification](aat_v2_mathematical_design.md#41-design-principle-classification): SOLID, Layered, Clean Architecture, Event Sourcing, Saga, CRUD などの役割分担。
- [証明義務と実証仮説](proof_obligations.md): 未解決の proof obligation と empirical hypothesis の台帳。

## 外部向けドラフト

- [Qiita 初回紹介記事ドラフト](outreach/qiita_intro_draft.md): アーキテクチャ零曲率定理、ArchitectureSignature、Lean proof と empirical hypothesis の分担を現場エンジニア向けに説明する記事案。

## Lean 形式化

- [Lean 定義・定理索引](lean_theorem_index.md): 現在 Lean に存在する主要な定義・定理の索引。
- [Lean module 階層整理方針](formal/lean_module_organization.md): `Formal/Arch` 以下の facade / import 方針、責務分類、段階移行ルール。
- [アーキテクチャ零曲率定理 Lean 化設計](formal/flatness_obstruction_lean_design.md): 数学草案を Lean の generic witness-count kernel / law diagram / finite zero-count bridge へ落とす設計。
- [runtimePropagation 設計](design/runtime_propagation_design.md): runtime metric を static structural core から分け、0/1 runtime graph 上の zero bridge は bounded Lean theorem package、policy-aware coverage、extractor completeness、incident 相関は実用・実証層として扱う設計。
- [B6 empirical hypothesis evaluation plan](design/b6_empirical_hypothesis_evaluation.md): Feature Extension Report / Architecture Signature / obstruction profile と outcome linkage を H1-H5 の evaluation query へ接続する Phase B6 の研究検証計画。
- [B9/B10 schema version catalog](design/schema_version_catalog.md): schema version、compatibility policy、B10 operational feedback artifact の catalog と non-conclusion boundary。
- [ArchSig tooling index](design/archsig_tooling_index.md): ArchSig tooling の schema、CLI、fixture、non-conclusion boundary の索引。

Lean で証明済みの構造的事実、定義のみの概念、将来の証明義務、実証仮説は混同しない。

## 個別 design / protocol

- [個別設計メモ](design/README.md)

`docs/design/` には、全体方針から切り出した個別 design、tooling protocol、empirical protocol を置く。

## PRD

- [PRD 一覧](prd/README.md)

`docs/prd/` には、実装前または検討中の product requirement document を置く。
PRD の内容は、そのまま証明済み主張とは扱わず、実装・設計メモ・proof obligation へ分解してから追跡する。

## Archive

- [AAT v2 research requirements revised split](archive/aat_v2_research_requirements_revised_split.md): 数学設計書とツール設計書へ分割する前の原本。
- [Flatness–Obstruction Conjecture](archive/Flatness–Obstruction%20Conjecture.md): AAT v2 数学設計書へ整理する前の数学草案。
- [AAT v2 研究概要](archive/aat_v2_overview.md): `research_goal.md` へ統合する前の研究概要。
- [Paper-ready research note outline](archive/research_note_outline.md): 第一級設計書へ整理する前の外部説明用 technical note / paper outline。
- [設計原則の分類](archive/design_principle_classification.md): 数学設計書へ統合する前の設計原則分類メモ。
- [証明義務と実証仮説 full ledger](archive/proof_obligations_full_ledger.md): `docs/proof_obligations.md` を索引化する前の詳細 ledger。
- [ArchitectureSignature v1 後半戦まとめ](archive/signature_v1_wrapup.md): Signature v1 の個別 Issue 完了条件を整理した履歴メモ。
- [HANDOFF](archive/HANDOFF.md): 開発キックオフ時の引き継ぎメモ。

## Empirical pilot

- [B6 case study paper skeleton](empirical/b6_case_study_paper_skeleton.md):
  Feature Extension Report と outcome linkage を使った Phase B6 case study / technical note の骨子。
- [lean4-samples empirical pilot](empirical/lean4_samples_pilot/README.md):
  外部小規模 Lean repository に `archsig` と empirical dataset v0 schema を適用した
  5 件の before / after signature record と、最小 policy を適用した測定済み 0 の
  pilot record。
