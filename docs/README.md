# docs 読み方

このディレクトリは、AAT の数学理論、AAT / SFT の境界、SFT の場の理論、
Lean 形式化 status、tooling / empirical protocol を分けて管理する。

第一級本文は次の 3 文書である。

1. [AAT 数学理論](aat/mathematical_theory.md)
2. [AAT / SFT Interface](sft/aat_interface.md)
3. [ソフトウェアの場の理論](sft/software_field_theory.md)

## 初めて読む順序

1. [研究の全体目標](research_goal.md)
2. [AAT 数学理論](aat/mathematical_theory.md)
3. [AAT / SFT Interface](sft/aat_interface.md)
4. [ソフトウェアの場の理論](sft/software_field_theory.md)
5. [証明義務と実証仮説](aat/proof_obligations.md)
6. [Lean 定義・定理索引](aat/lean_theorem_index.md)
7. [AAT Tooling Documentation](tooling/README.md)
8. 必要に応じて [AAT directory guide](aat/README.md), [SFT directory guide](sft/README.md), [個別設計メモ](design/README.md), `docs/empirical/`

## 全体文書

- [研究の全体目標](research_goal.md): AAT / SFT / ArchSig / AI-driven Development の全体像を示す入口文書。
- [AAT 数学理論](aat/mathematical_theory.md): `ArchitectureObject`, operation, invariant, obstruction witness, signature, theorem boundary, repair, path, diagram filling, analytic representation を整理する。
- [AAT / SFT Interface](sft/aat_interface.md): SFT が AAT から借りる概念と、片方向依存の境界を整理する。
- [ソフトウェアの場の理論](sft/software_field_theory.md): PRD / Spec / Issue / PR / Review / CI / organization / AI / lifecycle を force, field, trajectory, control として整理する。
- [証明義務と実証仮説](aat/proof_obligations.md): theorem boundary、未解決課題、empirical hypothesis の台帳。
- [Lean 定義・定理索引](aat/lean_theorem_index.md): 現在 Lean に存在する主要な定義・定理の索引。
- [AAT directory guide](aat/README.md): AAT 配下の補助文書の読み方。
- [SFT directory guide](sft/README.md): SFT 配下の補助文書の読み方。

## 層の分担

```text
AAT gives laws.
ArchSig measures state.
SFT predicts trajectories.
AI proposes operations.
Review / CI controls transitions.
```

| 層 | 役割 | 主な文書 |
| --- | --- | --- |
| AAT | 局所的・代数的・形式的・証明可能な核。 | `docs/aat/mathematical_theory.md` |
| AAT / SFT Interface | AAT から SFT への片方向依存と claim boundary。 | `docs/sft/aat_interface.md` |
| ArchSig | AAT 的観測量を抽出し、SFT 的予測・制御に渡す計測層。 | `docs/tooling/`, `docs/design/archsig_tooling_index.md` |
| SFT | 大域的・力学的・予測的・制御的な上位理論。 | `docs/sft/software_field_theory.md` |
| AI-driven Development | SFT の forecast と AAT の theorem boundary の中で operation を生成する制御対象。 | `docs/sft/software_field_theory.md`, tooling / AIR docs |

Lean で証明済みの構造的事実、定義のみの概念、将来の証明義務、実証仮説は混同しない。

## Lean 形式化

- [Lean 定義・定理索引](aat/lean_theorem_index.md): 実装済み Lean API の入口。
- [証明義務と実証仮説](aat/proof_obligations.md): theorem boundary、未解決課題、empirical hypothesis の台帳。

## Tooling / Empirical

- [AAT Tooling Documentation](tooling/README.md): AIR、claim boundary、signature artifact、report、extractor、workflow、schema compatibility の tool 側総合入口。
- [ArchSig tooling index](design/archsig_tooling_index.md): ArchSig tooling の schema、CLI、fixture、non-conclusion boundary の索引。
- [Architecture Dynamics tooling 設計](design/architecture_dynamics_tooling_design.md): SFT / Architecture Dynamics を PR force report、trajectory report、dynamics metrics report へ落とす設計。
- [B6 empirical hypothesis evaluation plan](design/b6_empirical_hypothesis_evaluation.md): Feature Extension Report / Architecture Signature / obstruction profile と outcome linkage を evaluation query へ接続する計画。

## Archive

- [2026-05-09 AAT/SFT reorg archive](archive/2026-05-09-aat-sft-reorg/): AAT/SFT 階層へ再編する前の旧 AAT Part 文書、旧数学設計書、旧 proof obligations、旧 theorem index、旧 Architecture Signature Dynamics 設計。
- [2026-05-09 first-class docs archive](archive/2026-05-09-first-class-docs/): 後方互換のためだけに残っていた facade 文書、薄い索引、旧 PRD の退避先。
- [AAT v2 research requirements revised split](archive/aat_v2_research_requirements_revised_split.md): 数学設計書とツール設計書へ分割する前の原本。
- [Flatness-Obstruction Conjecture](archive/Flatness%E2%80%93Obstruction%20Conjecture.md): AAT 数学理論へ整理する前の数学草案。
- [証明義務と実証仮説 full ledger](archive/proof_obligations_full_ledger.md): `docs/aat/proof_obligations.md` を索引化する前の詳細 ledger。

## Empirical pilot

- [B6 case study paper skeleton](empirical/b6_case_study_paper_skeleton.md)
- [lean4-samples empirical pilot](empirical/lean4_samples_pilot/README.md)
