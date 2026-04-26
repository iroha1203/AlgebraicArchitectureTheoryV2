# docs 読み方

このディレクトリは、全体方針、Lean 形式化、個別 design、実証 protocol を分けて管理する。

## 初めて読む順序

初見では次の順に読む。

1. [研究の最終ゴール](research_goal.md)
2. [研究概要](aat_v2_overview.md)
3. [アーキテクチャ零曲率定理 Lean 化設計](formal/flatness_obstruction_lean_design.md)
4. [Paper-ready research note outline](research_note_outline.md)
5. [設計原則の分類](design_principle_classification.md)
6. [証明義務と実証仮説](proof_obligations.md)
7. [Lean 定義・定理索引](formal/lean_theorem_index.md)

## 全体文書

- [研究概要](aat_v2_overview.md): アーキテクチャ零曲率定理を中心に置いた現在の理論構成、Signature v0/v1 の位置づけ。
- [研究の最終ゴール](research_goal.md): アーキテクチャ零曲率定理を軸に、完成時に何を説明・測定できる状態を目指すか。
- [Paper-ready research note outline](research_note_outline.md): 外部説明用 technical note / paper outline として、Lean proof、executable metric、empirical hypothesis の責務境界を圧縮した文書。
- [設計原則の分類](design_principle_classification.md): SOLID, Layered, Clean Architecture, Event Sourcing, Saga, CRUD などの役割分担。
- [証明義務と実証仮説](proof_obligations.md): 未解決の proof obligation と empirical hypothesis の台帳。

## 外部向けドラフト

- [Qiita 初回紹介記事ドラフト](outreach/qiita_intro_draft.md): アーキテクチャ零曲率定理、ArchitectureSignature、Lean proof と empirical hypothesis の分担を現場エンジニア向けに説明する記事案。

## Lean 形式化

- [Lean 定義・定理索引](formal/lean_theorem_index.md): 現在 Lean に存在する主要な定義・定理の索引。
- [Lean module 階層整理方針](formal/lean_module_organization.md): `Formal/Arch` 以下の責務分類、移動判断基準、当面の配置ルール。
- [アーキテクチャ零曲率定理 Lean 化設計](formal/flatness_obstruction_lean_design.md): 数学草案を Lean の generic witness-count kernel / law diagram / finite zero-count bridge へ落とす設計。

Lean で証明済みの構造的事実、定義のみの概念、将来の証明義務、実証仮説は混同しない。

## 個別 design / protocol

- [個別設計メモ](design/README.md)

`docs/design/` には、全体方針から切り出した個別 design、tooling protocol、empirical protocol を置く。

## PRD

- [PRD 一覧](prd/README.md)

`docs/prd/` には、実装前または検討中の product requirement document を置く。
PRD の内容は、そのまま証明済み主張とは扱わず、実装・設計メモ・proof obligation へ分解してから追跡する。

## Empirical pilot

- [lean4-samples empirical pilot](empirical/lean4_samples_pilot/README.md):
  外部小規模 Lean repository に `archsig` と empirical dataset v0 schema を適用した
  5 件の before / after signature record と、最小 policy を適用した測定済み 0 の
  pilot record。
