---
status: picked
goal: G-aat-quality-surface-01
exploration_role: unifier / transport-criterion / genius-support
candidate_type: genius-support / transport-criterion / projection-nonfaithfulness
capability_category: semantic-obstruction / transport-naturality / repair-coherence / certificate-transport / quality-surface
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: Component-preserving transport and exact image support are not enough; semantic repair closure transports exactly through supported target residual lifts or a residual support transport.
origin: cycle-85
tags: [quality-surface, semantic-repair, residual-transport, transport-naturality, projection-nonfaithfulness, genius-support]
created: 2026-06-22
cycle: 85
lean: proved-in-research
---

# Semantic residual transport naturality

## 主張

semantic repair closure は、source support の image を target support として運ぶだけでは保存されない。
exact image support の下で target closure が成立するための必要十分条件は、target residual atom ごとに supported source lift が存在することである。
さらに、residual support transport は source / target の `SemanticRepairClosed` を同値に反映する。

selected witness では、protected component を保存する `obligationAliasTransport` が repair-frontier obligation residual を surface atom に潰す。
この transport は component-preserving で、complete support の exact image は surface support になるが、target obligation residual の supported lift を持たないため semantic repair closure を保存できない。

## 候補種別

`genius-support` / `transport-criterion` / `projection-nonfaithfulness`

## 依拠

- Cycle 78: refined semantic support projection kernel。
- Cycle 81: residual alias gap が closure nonfaithfulness を生む十分条件。
- Cycle 83: semantic repair closure の residual-component coverage / faithfulness 分解。
- Cycle 84: same component projection 下の missed residual / alias gap normal form。

## 非自明性

Cycle 83/84 は fixed projection / cover 上で actual residual atom identity の必要性を示した。
Cycle 85 はそれを profile / vocabulary transport の条件へ上げる。
component-preserving transport、component row equality、exact image support のいずれも、target residual atom そのものを lift しない限り closure preservation には足りない。

## 数学的興味

`ResidualSupportTransport` は、残差を残差へ写し、target residual を残差 source lift で覆い、support truth を residual atom 上で保存する。
この構造があると `SemanticRepairClosed source` と `SemanticRepairClosed target` は同値になる。
一方、exact transported support だけを仮定する場合、target closure は `TargetResidualSupportedBySource` と同値であり、missed target residual はその supported-lift criterion に対する明示的な obstruction witness になる。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` に対し、
finite atlas gluing theorem の transport 側 kernel を Lean-proved criterion として切り出した。
これは 1000 点 unlock ではなく、global repair-gluing obstruction theorem へ向かう transport-naturality support node である。

## ライバルに対する有効性

ADL、component dashboard、component-preserving migration、AI review summary は protected component の保存を主張できる。
しかし target residual atom の supported lift を証明しない限り、semantic repair closure は保存されない。
AAT は、component-preserving transport がどこで residual obstruction を落とすかを theorem package として示せる。

## SCORE 見込み

- `score_reason`: Cycle 83/84 の residual identity boundary を transport-natural criterion へ一般化し、positive iff と selected component-preserving failure witness を同梱する。
- `dullness_risk`: exact image support 側の closure iff は定義に近い。価値は `ResidualSupportTransport` iff と selected no-residual-transport witness を合わせた transport criterion にある。
- `proof_or_evidence_plan`: `SemanticResidualTransportNaturality.lean` で `ResidualSupportTransport`、closure iff、exact image support criterion、missed target residual obstruction、selected alias transport witness を証明する。

## CS / SWE への帰結

component-preserving refactor や migration でも、target residual obligation の supported lift を落とすと repair closure は壊れる。
quality surface は transport success を component equality ではなく residual lift / residual support transport として読む必要がある。

## 証明・根拠

Lean 証拠は `Formal/AG/Research/QualitySurface/SemanticResidualTransportNaturality.lean` に固定した。

- `TransportedSemanticSupportExact`
- `TargetResidualLiftedBySourceResidual`
- `TargetResidualSupportedBySource`
- `MissedTargetResidualTransport`
- `ComponentPreservingSemanticTransport`
- `ResidualSupportTransport`
- `residualSupportTransport_semanticRepairClosed_iff`
- `targetResidualLiftedBySourceResidual_of_residualSupportTransport`
- `semanticRepairClosed_iff_targetResidualSupportedTransport_of_exactSupport`
- `targetResidualSupported_of_residualLiftedTransport_of_sourceClosed`
- `semanticRepairClosed_of_residualLiftedTransport_of_exactSupport`
- `missedTargetResidualTransport_obstructs_semanticRepairClosed`
- `missedTargetResidualTransport_obstructs_supportedResidualTransport`
- `residualLiftedTransport_rules_out_missedTargetResidual`
- `missedTargetResidualTransport_obstructs_residualLiftedTransport_of_sourceClosed`
- `obligationAliasTransport`
- `obligationAliasTransport_componentPreserving`
- `surfaceRepairSupport_is_obligationAliasTransport_image`
- `selected_obligationAliasTransport_misses_obligationResidual`
- `selected_obligationAliasTransport_not_residualLifted`
- `selected_componentPreserving_transport_not_semanticRepairClosed`
- `selected_no_residualSupportTransport_for_obligationAlias`
- `semanticResidualTransportNaturality_package`

G3 実績:

- `lake env lean Formal/AG/Research/QualitySurface/SemanticResidualTransportNaturality.lean`: pass。
- `lake build Formal.AG.Research.QualitySurface.SemanticResidualTransportNaturality`: pass。
- `lake build FormalAGResearch`: pass。
- `lake build`: pass。既存の `Formal/Arch/Extension/FeatureExtensionExamples.lean` linter warning のみ。
- axiom probe: generic theorem 群は axiom-free。selected witness / package は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。
- `git diff --check`: pass。
- hidden / bidirectional Unicode scan: pass。
- local path scan: pass。

## 審判メモ

- G1 theorem-candidate review: `semantic residual transport naturality criterion` は +150 目標。positive theorem だけでなく component-natural transport failure witness を入れる必要あり。
- G1 boundary review: source closure と explicit residual lift / supported lift を仮定しない bare transport claim は過大。`repairFrontierOnlySupport` のように non-residual atom deletion では closure が壊れないため、residual atom に相対化する必要あり。
- G1 repo-fit review: residual alias 系に近いので、単なる transport 版では弱い。より大きな repair-gluing obstruction theorem の seed にするなら support-lift / cocycle exactness へ進めるべき。
- G1 genius-push review: `ResidualSupportTransport` closure iff と selected no-transport theorem は、finite semantic repair-gluing obstruction theorem への現実的 support node。1000 点 unlock ではなく、genius support として扱うのが妥当。
- G2 rigor: accept / base 80 / genius no。`missed target residual` は exact obstruction ではなく explicit obstruction witness として記述する境界修正後に accept。
- G2 research value: accept / base 80 / genius no。Cycle 83/84 を cross-vocabulary transport 条件へ上げるが、中心 iff は定義近傍なので base 80 上限。
- G2 repo integration: content / verification / leakage / protected boundary は問題なし。G4 確定後に report SCORE ledger へ反映すること。
- G2 rival comparison: accept / base 80 / genius no。component-preserving rival surface との差分は supported residual lift の有無。
- G4 SCORE 監査: confirm / base 80 / multiplier 2.0 / penalty 0 / final +160。total 11508 -> 11668。genius は support node であり unlock ではない。

## 追加 required fields

- `mathematical_interest`: semantic repair closure preservation を residual support transport / supported target residual lift として特徴づける。
- `goal_advancement`: global repair-gluing obstruction theorem の transport-naturality kernel を Lean-proved support node として固定する。
- `planned_theorem_names`: `residualSupportTransport_semanticRepairClosed_iff`, `semanticRepairClosed_iff_targetResidualSupportedTransport_of_exactSupport`, `selected_componentPreserving_transport_not_semanticRepairClosed`, `semanticResidualTransportNaturality_package`
- `visible_projection`: component-preserving semantic atom transport。
- `protected_structure`: target residual atom, supported source lift, residual support transport, semantic repair closure。
- `exactness_or_minimality_claim`: exact image support の下で target closure は supported target residual lift と同値。residual support transport があると source / target closure は同値。
- `nonfaithfulness_or_failure_mode`: component-preserving alias transport can miss the target obligation residual and fail semantic repair closure。
- `previous_cycle_delta`: Cycle 84 の missed residual normal form を cross-vocabulary transport criterion へ上げる。
- `rival_stress_test`: component-preserving migration cannot certify semantic closure without target residual lifts。
- `genius_potential`: support node
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: transport-naturality kernel for finite repair-gluing obstruction.

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-alias-classification.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-component-faithfulness.md`
- `research/ideas/g-aat-quality-surface-01-semantic-support-projection-kernel.md`

## 進捗ログ

- 2026-06-22: G1 transport-criterion / genius-support candidate として picked。
- 2026-06-22: Lean 証拠を `SemanticResidualTransportNaturality.lean` に固定し、単体 `lake env lean` と module build が通った。
- 2026-06-22: G4 SCORE 監査で base 80 / final +160 に確定した。
