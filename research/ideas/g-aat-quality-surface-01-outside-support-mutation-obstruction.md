---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: obstruction / repair-potential / traceability / invariance
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle32
tags: [quality-surface, repair, support, source-ref, obstruction]
created: 2026-06-20
cycle: 32
lean: research/lean/ResearchLean/AG/QualitySurface/OutsideSupportMutationObstruction.lean
---

# Outside-support mutation obstruction for support-local frontier restriction

## 主張

Cycle 31 の `SupportLocalSourceRefRepair` から `preservesOutsideSupport` を落とすと、
declared support 上の token supply が成功しても frontier restriction は壊れる。

具体的には、`partialPacket` に対し declared repair support を storage に置き、storage には
`storageRef` を供給する一方、support 外の endpoint source-ref table を `none` に変える repair action を作る。
この action は declared support 上の fill law を満たすが support-local ではない。repair 後 packet では
endpoint が post frontier に新規発生し、

```text
post frontier = pre frontier ∧ ¬ repairSupport
```

が失敗する。さらに full packet との source-ref exact visualization と packet holonomy annihilation も失敗する。
この失敗は可視面の不一致ではなく、full packet と mutation repair packet が visible packet / tuple surface では
一致したまま、endpoint の repair-frontier / source-ref table defect によって source-ref exactness が破れる
lossy packet-to-tuple visualization として証明する。

## 候補種別

`orientation`

## 依拠

- Cycle 23: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceHolonomyPacket.lean`
- Cycle 24: `research/lean/ResearchLean/AG/QualitySurface/SourceRefExactVisualization.lean`
- Cycle 25: `research/lean/ResearchLean/AG/QualitySurface/SourceRefRepairHolonomy.lean`
- Cycle 31: `research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairFrontier.lean`

## 非自明性

Cycle 31 は support-local action の十分条件から post frontier formula を導いた。
この候補はその仮定のうち `preservesOutsideSupport` が removable ではないことを、declared support 上の fill は成功している有限 witness で示す。
単なる contrapositive ではなく、post frontier 新規発生、packet holonomy defect、source-ref exact visualization failure を同じ witness に束ねる。

## 数学的興味

support-locality は「support 内を直す」だけでは足りず、「外側を動かさない」ことを含む exactness 条件である。
この候補は repair support の境界を、support 補集合上の obstruction carrier として読む。

## GOAL への前進

outside-support mutation obstruction を finite witness として固定し、support-local repair calculus の sharpness と
repair-potential / traceability の protected boundary を進める。

## SCORE 見込み

- `score_reason`: Cycle 31 の positive theorem に対する sharp obstruction として base 60。frontier failure 自体は定義計算に近いため抑えめに評価し、declared support fill success、visible packet / tuple flatness、frontier / holonomy / exact visualization の三破綻を同一 witness に束ねることで dullness を避ける。
- `dullness_risk`: medium。単なる仮定除去の反例に落とさず、declared support fill success、post frontier creation、exactness obstruction、component localization を同時に証明する。
- `proof_or_evidence_plan`: weak support fill law、outside-support mutation action、post frontier creation、frontier formula failure、visible packet / tuple equivalence、component packet holonomy defect、lossy packet-to-tuple visualization、source-ref exact visualization failure、package theorem を Lean で証明する。

## CS / SWE への帰結

repair action が declared support 上では成功して見えても、support 外 source-ref table を壊すと、
残 frontier と exact visualization が破綻する。support-aware repair dashboard は outside-support preservation law を
見なければ false success を表示しうる。

## 証明・根拠の見込み

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/OutsideSupportMutationObstruction.lean`

Declarations:

- `WeakSupportFillSourceRefRepair`
- `outsideSupportMutationRepairAction`
- `outsideSupportMutationRepairPacket`
- `outsideSupportMutation_fillsDeclaredSupport`
- `outsideSupportMutation_not_supportLocal`
- `outsideSupportMutation_endpointFrontier`
- `outsideSupportMutation_breaks_frontierRestriction`
- `outsideSupportMutation_endpointRepairFrontierDefect`
- `outsideSupportMutation_endpointSourceRefTableDefect`
- `outsideSupportMutation_hasPacketHolonomyDefect`
- `outsideSupportMutation_visiblePacketSurface`
- `outsideSupportMutation_visibleTupleSurface`
- `outsideSupportMutation_lossyPacketToTupleVisualization`
- `outsideSupportMutation_not_sourceRefExactVisualization`
- `outsideSupportMutationObstruction_package`

Local G3 checks:

- `focused Lean check: ResearchLean/AG/QualitySurface/OutsideSupportMutationObstruction.lean`: pass
- `Research package build`: pass
- `lake env lean .tmp/outside_support_mutation_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; exactness failure is not weakened to visible mismatch because the same witness has visible packet / tuple equivalence and lossy visualization

## 審判メモ

- 厳密性: initial `revise`、recheck `accept`。`¬ SourceRefExactVisualization` だけでは可視面の不一致による失敗に弱まるため、visible packet / tuple equivalence と `LossyPacketToTupleVisualization` を同じ witness で証明すること。base は 60 に下げる。
- 研究価値: `accept`、base 75。declared support fill success と外側 mutation、frontier 新規発生、holonomy/exactness failure を同時に固定できれば、Cycle 31 の support-locality を鋭くする。
- repo 全体価値: `accept`、base 70。Tooling / paper では false repair success の境界として使えるが、単なる仮定除去反例に縮めないこと。

## G4 SCORE 監査

- `score_verdict`: `confirm`
- `base_score`: 60
- `evidence_multiplier`: 2.0
- `penalty`: 0
- `final_score`: 120
- `category`: obstruction / repair-potential / traceability / invariance
- `reason`: 同一 finite witness が weak fill success、outside-support mutation、frontier restriction failure、visible packet / tuple agreement、packet holonomy defect、lossy visualization、non-exactness を束ねており、Cycle 31 の `preservesOutsideSupport` の必要性を示す obstruction として base 60 が妥当。
- `checked`: Lean claim と card/report の claim boundary は一致。Cycle 31 の 3820 に +120 して 3940/5000、proved-in-research は 32。
- `unchecked`: なし。

## 関連

- `research/ideas/g-aat-quality-surface-01-support-local-repair-frontier-restriction.md`
- `research/ideas/g-aat-quality-surface-01-source-ref-table-law-sharp-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-visible-repair-transport-commutator-counterexample.md`

## 進捗ログ

- 2026-06-20: Cycle 32 G1 で作成。
- 2026-06-20: G2 initial review。A は `revise`、B/C は `accept`。visible packet / tuple flatness と lossy visualization を証明対象に追加し、base 60 / final 120 に下げた。
- 2026-06-20: G2-A recheck `accept`。base 60 / final 120 で picked。
- 2026-06-20: G3 Lean verification pass。対象 Lean、`ResearchLean`、axiom harness が pass。
- 2026-06-20: G3 independent axiom audit / formalization-quality audit pass。
- 2026-06-20: G4 SCORE audit `confirm`。base 60 / multiplier 2.0 / final 120、累積 3940/5000。
