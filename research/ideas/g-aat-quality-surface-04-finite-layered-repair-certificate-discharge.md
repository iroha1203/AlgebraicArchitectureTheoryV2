---
status: picked
goal: G-aat-quality-surface-04
exploration_role: closer / unifier
candidate_type: target-support
capability_category: semantic-faithfulness-discharge / effective-descent / representation-adequacy / anti-weakening
expected_base_score: 90
expected_evidence_multiplier: 2.0
expected_final_score: 180
evidence_stage: proved-in-research
rival_advantage: ADL, static analysis, conformance checkers, metric dashboards, and AI review can expose local repair signals, but this candidate proves when those local signals are an independent non-hidden adequacy certificate for semantic descent rather than a disguised global-coherence assumption.
genius_potential: no
genius_target: none
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: material premise discharge theorem for LayeredRepairAdequacy
target_progress: support-node
proof_obligation_delta: Replaces Cycle 1's visible `LayeredRepairAdequacy` premise extraction with a finite/local certificate route and non-hiddenness witness.
target_completion_role: checkpoint support; not target completion by itself.
origin: G-04
tracking_issue: 2484
parent_tracking_issue: 2482
tags: [quality-surface, semantic-repair, obstruction-tower, adequacy-discharge, target-support]
created: 2026-06-24
cycle: 2
lean: proved-in-research
---

# Finite Layered Repair Certificate Discharge

## 主張

`FiniteSemanticRepairObstructionTower T` に対し、boundary semantic closure を直接 premise にせず、finite `c0Order` 上の boundary primitive について residual-component coverage と residual-component faithfulness を証明し、その二つから semantic closure を導く finite/local certificate prism を定義する。

その prism から `LayeredRepairAdequacy T` を構成し、`universalSemanticRepairObstructionTower_iff` の adequacy 引数を、未放電の一括 premise ではなく独立 certificate 由来の theorem に置き換える。さらに、certificate prism が `H1Vanishes T`、`ObstructionTowerVanishes T`、`GlobalSemanticRepairCoherent T` を含意しない witness を固定し、anti-weakening rule に対して結論相当 premise を隠していないことを示す。

## 候補種別

`target-support`

## 依拠

- GOAL `G-aat-quality-surface-04` の target theorem / material premise ledger / anti-weakening rule。
- Cycle 1 checkpoint: `research/lean/ResearchLean/AG/QualitySurface/SemanticRepairObstructionTower.lean`
- G-02 weak finite shadow: `research/lean/ResearchLean/AG/QualitySurface/SemanticRepairGluingComplex.lean`
- semantic faithfulness bridge: `SemanticResidualComponentFaithfulness.lean`
- transport bridge: `SemanticResidualTransportNaturality.lean`

## 非自明性

Cycle 1 は `LayeredRepairAdequacy` を tower data から分けたが、sufficiency theorem は依然として `LayeredRepairAdequacy T` を一括引数に取る。今回の候補はその一括引数を、finite boundary certificate と layer-local effectivity certificate から構成し、同時にその certificate が obstruction vanish や global coherence を含まないことを証明対象にする。

単なる structure field の名前替えにしないため、certificate の各 field は finite enumeration、boundary coverage、boundary faithfulness、coverage/faithfulness から closure への局所 bridge だけに限定する。`LayeredRepairAdequacy`、`GlobalSemanticRepairCoherent T`、`ObstructionTowerVanishes T`、`H1Vanishes T`、target equivalence、torsor triviality、stack effectiveness、finite-shadow completeness は field に入れない。

## 数学的興味

obstruction tower の強さは、vanishing と global coherence の同値だけではなく、その同値を支える material premise が結論を隠していないことにある。この候補は adequacy premise を finite/local certificate prism に分解し、proof audit 可能な非循環性を Lean theorem として固定する。

## GOAL への前進

前回 G6 が target-proved を拒否した最大理由である `LayeredRepairAdequacy` の未放電を、独立 certificate からの構成 theorem と非隠蔽 witness へ押し下げる。

## ライバルに対する有効性

ADL、静的解析、conformance checker、metric dashboard、AI review は local repair plan、component pass、visible local coherence を扱える。しかし、それらが semantic repair descent を支える非循環な adequacy certificate であることまでは証明しない。この候補は local signal と global coherence の間に、residual faithfulness / transport / layer effectivity の証明可能な監査面を置く。

## SCORE 見込み

- `score_reason`: G6 blocker を直接減らす target-support。証拠が Lean proof / axiom audit / formalization quality audit まで通れば base 90 / x2.0 を期待する。
- `dullness_risk`: certificate fields が `LayeredRepairAdequacy` の単なる名前替え、`forall primitive, boundary -> primitiveSemanticallyClosed primitive` の直接 field、または `GlobalSemanticRepairCoherent` / `ObstructionTowerVanishes` / `H1Vanishes` の隠し field になると失格。
- `proof_or_evidence_plan`: `FiniteBoundarySemanticClosureCertificate` を coverage / faithfulness / local bridge で定義し、`LayeredRepairDischargePrism` から `LayeredRepairAdequacy` を構成する。`universalSemanticRepairObstructionTower_iff_of_dischargePrism`、G-02 weak shadow instance、そして `dischargePrism_not_h1Vanishes` / `dischargePrism_not_obstructionTowerVanishes` / `dischargePrism_not_globalCoherent` を Lean で証明する。
- `planned_theorem_names`: `FiniteBoundarySemanticClosureCertificate`, `LayeredRepairDischargePrism`, `boundarySemanticClosed_of_finiteBoundaryCertificate`, `layeredRepairAdequacy_of_dischargePrism`, `globalRepairCoherent_of_obstructionTowerVanishes_of_dischargePrism`, `universalSemanticRepairObstructionTower_iff_of_dischargePrism`, `universalSemanticRepairObstructionTower_package_of_dischargePrism`, `finiteGluingComplex_dischargePrism`, `finiteGluingComplex_as_obstructionTower_shadow_of_dischargePrism`, `dischargePrism_not_h1Vanishes`, `dischargePrism_not_obstructionTowerVanishes`, `dischargePrism_not_globalCoherent`

## Target Theorem 寄与

- `target_theorem`: `Universal Semantic Repair Obstruction Tower Theorem`
- `target_support_node`: material premise discharge theorem for `LayeredRepairAdequacy`
- `target_progress`: `support-node`
- `proof_obligation_delta`: `LayeredRepairAdequacy` を visible material premise から finite/local certificate による構成 theorem へ変換する。target theorem を弱めず、completion には true sheaf `H1`、functoriality、nonabelian / higher / stacky witness、finite computable shadow connection がなお必要。
- `target_completion_role`: checkpoint support; G6 が target-proved と判定するにはこの certificate だけでは足りない。

## CS / SWE への帰結

local repair pass、component-level clearance、AI review の自然言語 repair plan は、そのまま descent adequacy ではない。どの local certificate が semantic residual を faithful に閉じ、どの transport/coverage が残り、どの nonabelian / higher / stack layer が effective かを分離することで、tooling や review output を obstruction tower の material premise audit に載せられる。

## 証明・根拠の見込み

Lean では既存 `FiniteSemanticRepairObstructionTower` を拡張せず、別の certificate structure を追加する。構造体に入れるのは次だけにする。

- finite enumeration completeness: `forall primitive, primitive ∈ T.c0Order`
- local coverage predicate and local faithfulness predicate
- listed boundary primitives が coverage / faithfulness を持つこと
- coverage と faithfulness から `primitiveSemanticallyClosed` を導く local bridge

結論相当の `LayeredRepairAdequacy T`、`GlobalSemanticRepairCoherent T`、`ObstructionTowerVanishes T`、`H1Vanishes T`、target equivalence、torsor triviality、stack effectiveness、finite-shadow completeness は structure field に入れない。

非隠蔽 witness は、finite discharge prism を満たすが selected residual が boundary ではない小 tower を構成して示す。これにより、prism が `H1Vanishes`、`ObstructionTowerVanishes`、global coherence を含意しないことを固定する。

## 審判メモ

- 厳密性: G2 A は revise。`boundary -> primitiveSemanticallyClosed` の直接 field ではなく coverage / faithfulness / local bridge から closure を導くこと、かつ prism が `H1Vanishes`、`ObstructionTowerVanishes`、`GlobalSemanticRepairCoherent` を含意しない witness を要求した。
- 厳密性対応: `research/lean/ResearchLean/AG/QualitySurface/SemanticRepairAdequacyDischarge.lean` で `FiniteBoundarySemanticClosureCertificate` を lower-level certificate として実装し、`LayeredRepairDischargePrism` から `LayeredRepairAdequacy` を構成した。non-hiddenness witness は `C0 := Empty` の小 tower として、prism は vacuously 存在するが residual は boundary ではないことを固定した。`focused Lean check: ResearchLean/AG/QualitySurface/SemanticRepairAdequacyDischarge.lean` と `Research module build: ResearchLean.AG.QualitySurface.SemanticRepairAdequacyDischarge` は通過。
- 研究価値: Cycle 1 の target-boundary theorem が依存していた material premise を、結論を含まない certificate 由来の構成 theorem に押し下げた。これは target completion ではなく、G6 blocker を減らす support-node。
- repo 全体価値: G-02 weak finite shadow と G-04 finite tower の接続を `finiteGluingComplex_dischargePrism` / `finiteGluingComplex_as_obstructionTower_shadow_of_dischargePrism` として再利用可能な import に分離した。
- ライバル比較: local repair signal を読むだけの ADL / static analysis / review tooling と違い、local coverage / faithfulness が semantic closure へ至るための非循環な proof obligation を明示する。

## 関連

- Cycle 1 candidate: `g-aat-quality-surface-04-finite-semantic-repair-obstruction-tower-package.md`
- G1 closer / unifier の independent certificate discharge candidate。
- G1 obstruction の residual-fiber faithfulness no-go。

## 進捗ログ

- 2026-06-24: G1 candidate pool から G6 blocker に最も直接対応する candidate として作成。
- 2026-06-24: G2 A revise を受け、prism field を lower-level coverage / faithfulness / local bridge に制限し、非隠蔽 witness 要件を追加。
- 2026-06-24: Lean evidence として `SemanticRepairAdequacyDischarge.lean` を追加し、candidate を picked / lean-proved に更新。
- 2026-06-24: `.tmp/g04_adequacy_discharge_axioms.lean` で今回追加した discharge theorem / witness theorem の `#print axioms` を確認し、全対象が `does not depend on any axioms` であることを確認。
