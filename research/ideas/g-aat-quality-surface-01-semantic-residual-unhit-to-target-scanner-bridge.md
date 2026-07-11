---
status: picked
goal: G-aat-quality-surface-01
exploration_role: source-unhit to target-scanner alarm bridge / repair-hit scanner integration / genius-support convergence
candidate_type: source unhit scanner to generated target scanner bridge / alarm consistency theorem
capability_category: semantic-obstruction / status-drop-scanner / alarm-bridge / mapped-target-scanner / genius-support
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can show source repair witnesses and target scan results separately, but they do not prove that a source unhit scanner witness forces generated target scanner nonempty, nor that target scanner none forces source unhit scanner none.
origin: cycle-105
tags: [quality-surface, semantic-repair, residual-cut, status-drop, scanner, alarm-bridge, mapped-target, genius-support]
created: 2026-06-23
cycle: 105
lean: proved-in-research
planned_report_section: "Cycle 105: Source unhit to generated target scanner bridge"
---

# Source Unhit To Generated Target Scanner Bridge

## 主張

Cycle 104 の source unhit status-drop scanner と、Cycle 103 の generated mapped target scanner を接続する。

source scanner が explicit unhit old status drop を `some` として返すなら、generated mapped target scanner は
`none` ではありえず、実際に `some targetPair` を返す。逆に generated mapped target scanner が `none` なら、
complete source order 上で source unhit scanner も `none` になる。

これは alarm consistency bridge であり、target-wide order completeness、hit sufficiency、repair synthesis、
global minimality、vanishing-to-closure、true `H^1` / Cech / coboundary quotient、ArchMap/tooling correctness、
runtime/UI correctness、whole-codebase quality は主張しない。

## 候補種別

`source unhit scanner to generated target scanner bridge` / `alarm consistency theorem`

## 依拠

- Cycle 103: generated mapped target scanner order。
- Cycle 104: source unhit status-drop scanner exactness。

## 非自明性

source-side red witness と target-side generated scanner を別々の artifact にせず、同じ finite order bridge で接続する。
source unhit `some` と target scanner `none` が同時に成立しないことを Lean theorem として固定した。

## 数学的興味

repair-hit scanner の red/green surface を mapped target scanner surface と整合させる。
これは future semantic repair-gluing obstruction theorem の diagnostic layer で、source witness と target obstruction alarm の整合性を保証する。

## GOAL への前進

source certificate geometry の unhit witness が target generated scanner の nonempty alarm に必ず現れることを示した。
quality surface の scanner 群が互いに矛盾しないことを、proof-level bridge として加えた。

## ライバルに対する有効性

ADL、static analyzer、dashboard、AI summary は source-side repair witness と target scan result を並べられる。
しかし、source unhit scanner hit が generated target scanner hit を強制し、target scanner `none` が source unhit scanner `none` を強制することを証明しない。

## SCORE 見込み

- `score_reason`: Cycle 103/104 の scanner surfaces を alarm bridge として接続し、source red witness と target generated scanner の整合性を証明した。
- `dullness_risk`: 既存 theorem の合成に近い。selected witness と theorem package で proof surface を固定したが、score は support-cycle として抑える。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualUnhitToTargetScannerBridge.lean` で source-to-target scanner bridge を証明する。

## CS / SWE への帰結

repair audit で source unhit witness が見つかった場合、target generated scan が green になることはない。
target generated scan が green なら、complete source order 上では source unhit scanner も green になる。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualUnhitToTargetScannerBridge.lean` に固定した。

- `sourceUnhitScannerSome_forces_mappedTargetScannerNotNone`
- `sourceUnhitScannerSome_gives_mappedTargetScannerHit`
- `mappedTargetScannerNone_forces_sourceUnhitScannerNone`
- `selected_sourceUnhitScannerSome_gives_generatedTargetScannerHit`
- `selected_generatedTargetScanner_not_none`
- `semanticResidualUnhitToTargetScannerBridge_package`

検証実績:

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/SemanticResidualUnhitToTargetScannerBridge.lean`: pass。
- `cd research/lean && lake build ResearchLean.AG.QualitySurface.SemanticResidualUnhitToTargetScannerBridge`: pass。
- `cd research/lean && lake build ResearchLean`: pass。
- `#print axioms`: theorem family は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、complete source order、source unhit scanner `some` / `none`、generated mapped target scanner
`some` / `none` の alarm consistency に限定する。
unchecked: target-wide order completeness、hit sufficiency、repair synthesis、global minimality、vanishing-to-closure、
true H1/cohomology、Cech quotient、coboundary quotient、ArchMap correctness、runtime/UI correctness、whole-codebase quality。

## 審判メモ

- G1: accept。新 obstruction 本体ではないが、source red witness と target generated scanner `none` の同時成立不能性を固定する diagnostic layer として base 70 / final +140 は妥当。
- G2: accept。score range +136 to +144、提案 +140 は妥当。rival は source witness と target scan を並べられても alarm consistency を証明しない。
- genius unlock ではなく、finite semantic repair-gluing obstruction theorem へ向けた support-cycle。

## 追加 required fields

- `mathematical_interest`: source unhit scanner と generated target scanner の alarm consistency を証明する。
- `goal_advancement`: source red witness が target generated scan に現れることを保証する。
- `planned_theorem_names`: `sourceUnhitScannerSome_gives_mappedTargetScannerHit`, `mappedTargetScannerNone_forces_sourceUnhitScannerNone`, `semanticResidualUnhitToTargetScannerBridge_package`
- `visible_projection`: source unhit scanner、generated mapped target scanner、some/non-none/none。
- `protected_structure`: explicit source unhit witness、complete source order、mapped generated target order。
- `exactness_or_minimality_claim`: alarm consistency。minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: target scanner none without complete source order does not certify source unhit scanner none。
- `previous_cycle_delta`: Cycle 104 の source scanner exactness を Cycle 103 の generated target scanner と接続した。
- `rival_stress_test`: rival は二つの scanner result を表示できても相互矛盾不能性を theorem として出さない。
- `genius_potential`: support-cycle。1000 点 unlock ではなく、future finite semantic repair-gluing obstruction theorem の diagnostic consistency layer。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: source red witness と target generated scanner alarm の整合性を保証する。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-unhit-status-drop-scanner.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-mapped-status-drop-scanner-order.md`
- planned report section: `Cycle 105: Source unhit to generated target scanner bridge`

## 進捗ログ

- 2026-06-23: Cycle 105 candidate として source unhit to generated target scanner bridge を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualUnhitToTargetScannerBridge.lean` に固定し、単体
  `lake env lean`、module build、`cd research/lean && lake build ResearchLean`、axiom 監査が通った。
