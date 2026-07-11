---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: repair-potential / traceability / atom-supported-quality-geometry / invariance
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle31
tags: [quality-surface, repair, support, source-ref, frontier]
created: 2026-06-20
cycle: 31
lean: research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairFrontier.lean
---

# Support-local repair action frontier restriction theorem

## 主張

有限 `SourceRefPacket` と `SourceRefRepairAction` に対し、repair action が support-local、すなわち
declared `repairSupport` 上では support 内に新しい missing source-ref を作らず、support 外では
source-ref table を保存するなら、`repairPacket action packet` の post repair frontier は
pre-repair frontier から declared repair support を引いたものとして正確に計算できる。

形式的には、pre packet が `RepairFrontierExact` であり、action が

- supported atoms に token を供給する、
- support 外の source-ref table を保存する、

を満たすとき、任意の atom について

```text
(repairPacket action packet).repairFrontier atom
  ↔ packet.repairFrontier atom ∧ ¬ action.repairSupport atom
```

が成り立つ。

## 候補種別

`closure`

## 依拠

- Cycle 21: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceRepairTrajectory.lean`
- Cycle 25: `research/lean/ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean`
- Cycle 30: `research/lean/ResearchLean/AG/QualitySurface/LawfulRepairTransportCommutator.lean`

## 非自明性

Cycle 21 は特定の storage repair action が missing source-ref locus を collapse することを示した。
この候補は特定 action ではなく、support-local law から post-frontier formula を導く。
Cycle 30 の `RepairActionTransportNaturality.support_iff` は現行 proof では直接使われていなかったため、
support law を repair frontier calculus として実効化する。

## 数学的興味

repair action の作用域を、post-state repair frontier の set-theoretic restriction として読む。
これにより repair support は単なる metadata ではなく、source-ref frontier をどう削るかを決める
bounded semantics になる。

## GOAL への前進

support law が decorative な仮定ではなく、repair-potential と traceability の protected frontier を
計算する構造であることを固定する。

## SCORE 見込み

- `score_reason`: support-local repair theorem frontier を一般形に押し上げ、Cycle 30 の open question「support law が実際に効く semantics」を閉じる closure result として base 65。新しい反例や不変量ではないため、主張は closure / frontier calculus として評価する。
- `dullness_risk`: medium。特定 storage repair の再包装ではなく、support 外保存と supported fill law から frontier restriction formula を導く必要がある。
- `proof_or_evidence_plan`: `SupportLocalSourceRefRepair` を、結論を含まない table-level laws として定義する。具体的には `fillsSupportedAtoms` と `preservesOutsideSupport` を分離し、pre `RepairFrontierExact` から `supportLocalRepair_frontier_eq_preFrontier_diff_support`、outside-support preservation、supported-frontier clearing、storage repair action instance を Lean で証明する。

## CS / SWE への帰結

repair action が「どこを直す」と宣言するだけではなく、その support が post repair frontier をどう縮めるかを
式で検査できる。visible reading は変わらなくても、support-local source-ref semantics は修復済み frontier と
残 frontier を区別する。

## 証明・根拠の見込み

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairFrontier.lean`

Declarations:

- `SupportLocalSourceRefRepair`
- `SupportLocalSourceRefRepair.outside_preserves_missing_iff`
- `SupportLocalSourceRefRepair.supported_atoms_not_missing`
- `supportLocalRepair_frontier_eq_preFrontier_diff_support`
- `supportLocalRepair_preserves_outsideFrontier`
- `supportLocalRepair_clears_supportedFrontier`
- `storageRepairAction_supportLocal`
- `storageRepairAction_frontier_eq_preFrontier_diff_support`
- `supportLocalRepairFrontierRestriction_package`

Local G3 checks:

- `focused Lean check: ResearchLean/AG/QualitySurface/SupportLocalRepairFrontier.lean`: pass
- `Research package build`: pass
- `lake env lean .tmp/support_local_repair_frontier_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; `SupportLocalSourceRefRepair` is non-circular and proves the frontier restriction for arbitrary packet/action under table-level support laws and pre-frontier exactness

## 審判メモ

- 厳密性: initial `revise`。supported frontier atoms だけを埋める条件では、support 内だが pre-frontier でない atom に新しい missing source-ref を作れる。`fillsSupportedAtoms` を support 内 no-new-missing law として強め、base 55-65 に下げる必要あり。
- 研究価値: `accept`、base 70。repair support を decorative metadata から frontier calculus へ昇格させるが、新しい反例・不変量級ではない。
- repo 全体価値: `accept`、base 65。Cycle 30 の support-law frontier に自然に接続するが、storage 専用 theorem や `FillsExactlyMissingSourceRefs` の言い換えに縮まないことが条件。

## 関連

- `research/ideas/g-aat-quality-surface-01-lawful-repair-transport-commutator-criterion.md`
- `research/ideas/g-aat-quality-surface-01-visible-repair-transport-commutator-counterexample.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-table-law-sharp-obstruction.md`

## 進捗ログ

- 2026-06-20: Cycle 31 G1 で作成。
- 2026-06-20: G2 initial review。A は `revise`、B/C は `accept`。support 内 no-new-missing law を明示し、base 65 / final 130 へ下げた。
- 2026-06-20: G2-A recheck `accept`。base 65 / final 130 で picked。
- 2026-06-20: G3 Lean verification pass。対象 Lean、`ResearchLean`、axiom harness が pass。
- 2026-06-20: G3 independent axiom audit / formalization-quality audit pass。
