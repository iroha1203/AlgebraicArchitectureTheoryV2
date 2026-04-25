# docs 読み方

このディレクトリは、全体方針、Lean 形式化、個別 design、実証 protocol を分けて管理する。

## 初めて読む順序

初見では次の順に読む。

1. [研究の最終ゴール](research_goal.md)
2. [研究概要](aat_v2_overview.md)
3. [設計原則の分類](design_principle_classification.md)
4. [証明義務と実証仮説](proof_obligations.md)
5. [Lean 定義・定理索引](formal/lean_theorem_index.md)

## 全体文書

- [研究概要](aat_v2_overview.md): 現在の理論構成、三層構造、Signature v0/v1 の位置づけ。
- [研究の最終ゴール](research_goal.md): 完成時に何を説明・測定できる状態を目指すか。
- [設計原則の分類](design_principle_classification.md): SOLID, Layered, Clean Architecture, Event Sourcing, Saga, CRUD などの役割分担。
- [証明義務と実証仮説](proof_obligations.md): 未解決の proof obligation と empirical hypothesis の台帳。

## Lean 形式化

- [Lean 定義・定理索引](formal/lean_theorem_index.md): 現在 Lean に存在する主要な定義・定理の索引。

Lean で証明済みの構造的事実、定義のみの概念、将来の証明義務、実証仮説は混同しない。

## 個別 design / protocol

- [個別設計メモ](design/README.md)

`docs/design/` には、全体方針から切り出した個別 design、tooling protocol、empirical protocol を置く。
