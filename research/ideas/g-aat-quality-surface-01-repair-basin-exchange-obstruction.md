---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: repair-potential / profile-curvature / certificate-transport / obstruction / quality-surface / traceability
expected_base_score: 78
expected_evidence_multiplier: 2.0
expected_final_score: 156
evidence_stage: proved-in-research
rival_advantage: ADL / conformance surfaces can compare refinement and repair views, but this candidate records when refine-then-repair and repair-then-refine have the same visible local projection while disagreeing on protected repair-basin membership.
origin: G1-cycle68
tags: [quality-surface, repair-basin, cech, refinement, obstruction]
created: 2026-06-21
cycle: 68
genius_potential: no
genius_target: none
genius_support_role: none
---

# Repair-basin exchange obstruction for refine-then-repair versus repair-then-refine

## 主張

Selected finite Cech handoff covers admit a typed repair/refinement exchange cell with
two path fields, `coarsePath` and `refinedPath`, representing the selected finite
`declared repair -> refine` and `refine -> declared repair` readings.  The cell stores
only endpoints, visible projection data, and the two covers; exactness, bases, clearance,
and obstruction are proved below rather than assumed as fields.  The two paths share the
same visible local projection, but differ in protected repair-basin membership.

Here `repair basin` means only selected finite overlap-basis / declared-clearance
membership for the supplied covers and repair predicate.  It does not mean a broad
reachable repair region.  The obstruction is not a global runtime repair synthesis claim:
it is a finite overlap-basis exchange witness inside this selected cell.  For
component-complete declared repairs, common clearance of the exchanged cell is equivalent
to hitting the union of the two selected overlap bases.  A selected trace-only repair plan
clears the coarse trace basin while failing the refined trace-plus-repair-frontier basin,
so visible agreement is not faithful to protected repair-basin exchange.

The claim is relative to selected finite source-ref handoff covers, selected overlap
cocycle data, finite `BridgeComponent` vocabulary, typed repair/refinement cell data, and
declared component-level repair predicates.  It does not assert canonical global
refinement, runtime repair generation, ArchMap correctness, source extraction completeness,
arbitrary route enumeration, global sheaf completeness, or whole-codebase quality.

## 候補種別

`bridge`: repair-potential, Cech overlap basis, and profile-curvature/refinement exchange
are placed in one typed finite cell.

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/HandoffRepairTransversal.lean`
- `research/lean/ResearchLean/AG/QualitySurface/HandoffCechExactness.lean`
- `research/lean/ResearchLean/AG/QualitySurface/OverlapObstructionBasis.lean`
- `research/lean/ResearchLean/AG/QualitySurface/RepairTransportCechCommutatorCurvature.lean`
- `research/lean/ResearchLean/AG/QualitySurface/RepairBasinExchangeObstruction.lean`
- Cycle 64 component-support repair transversal.
- Cycle 65 Cech local-to-global overlap exactness.
- Cycle 66 exact overlap obstruction basis and repair-transversal duality.
- Cycle 67 repair/transport Cech commutator curvature.

## 非自明性

この候補は単なる `union` / hitting-set 補題ではない。要求するのは、同じ typed
repair/refinement exchange cell の中で、`coarsePath` と `refinedPath` を同じ endpoints
と visible projection に束ね、可視 projection は同じだが、coarse basin と refined basin の
protected overlap basis が異なることを cell の field ではなく theorem として固定することである。
さらに positive criterion と finite obstruction witness の両方を要求する。

1. positive criterion: component-complete repair plan が exchanged cell の両側を clear することと、二つの selected overlap bases の union を hit することが同値である。
2. obstruction witness: trace-only repair plan は coarse trace basin を clear するが、refined trace-plus-repair-frontier basin を clear しない。
3. nonfaithfulness: visible repair/refinement projection は、この basin exchange obstruction を復元しない。

## 数学的興味

Repair basin を一点の repair obligation としてではなく、refinement と交換するときの Cech
overlap-basis geometry として読む。これにより、Quality Surface の curvature は path
noncommutativity だけでなく、repair basin membership の交換障害としても観測できる。

## GOAL への前進

この候補は、repair frontier と Cech curvature を「修理してから細分化する」か「細分化してから修理する」かの
protected basin exchange へ持ち上げ、Quality Surface の repair-potential / profile-curvature
/ obstruction 能力を増やす。

## ライバルに対する有効性

ADL、architecture conformance checker、metric dashboard は、refinement view、declared
repair、local conformance surface、mismatch list を扱える。しかし通常は、同じ visible/local
projection の背後で、protected overlap basis が repair basin membership を変えることを theorem
として保持しない。この候補は、ADL が表示できる visible agreement を尊重したうえで、その projection
が faithful でない protected repair-basin exchange obstruction を Lean 証拠として固定する。

## SCORE 見込み

- `score_reason`: Cycle 67 の repair/transport commutator curvature を、selected finite overlap-basis / declared-clearance membership の exchange obstruction へ持ち上げる。positive criterion と finite obstruction witness が両方通れば、通常 rubric の 80-100 点帯に入る。
- `dullness_risk`: 単なる basis union hitting criterion だけに落ちると dull になる。selected typed exchange cell、cell-level visible projection nonfaithfulness、coarse/refined basin gap を Lean statement に入れる必要がある。G2 A/C の指摘に従い、見込み SCORE は 94/188 から 78/156 に下げる。
- `proof_or_evidence_plan`: 実績として `research/lean/ResearchLean/AG/QualitySurface/RepairBasinExchangeObstruction.lean` に selected repair/refinement exchange cell、basis union clearance criterion、trace-only finite obstruction witness、visible projection nonfaithfulness、package theorem を置いた。

## CS / SWE への帰結

同じ可視上の local repair result でも、refinement を挟むと修理すべき protected component
support が増える場合を theorem として区別できる。これは runtime repair synthesis ではなく、有限に与えられた
source-ref handoff / overlap cocycle / declared repair predicate の中で、修理計画が refined basin
を hit しているかを検査するための幾何的 criterion である。

## 証明・根拠の見込み

Lean では Research 側で次を固定した。

- `RepairRefinementBasinCell`: endpoints、visible projection、`coarsePath`、`refinedPath` を同じ typed cell に置く。exactness、basis、clearance、obstruction は field として保存しない。
- `SameVisibleLocalRepairRefinementProjection`: selected cell の `coarsePath` と `refinedPath` が same visible/local projection を共有する。
- `RepairBasinMembership`: selected cover と repair plan の finite overlap-basis / declared-clearance membership predicate。
- `BasinExchangeObstruction`: coarse basin は clear するが refined basin は clear しない selected witness。
- `commonClearance_iff_hits_unionBasis`: component-complete repair plan に対し、coarse/refined common clearance と selected basis union hitting が同値である。
- `repairRefinement_basinMembership_commutes_of_compatible`: union basis を hit する repair plan では selected finite basin membership が交換する。
- `repairRefinement_basinExchangeObstruction`: trace-only repair plan による finite obstruction witness。
- `visibleRepairRefinement_not_faithful_to_basinExchange`: visible/local projection は protected basin exchange obstruction に faithful ではない。
- `repairBasinExchangeObstruction_package`: positive criterion、finite obstruction、nonfaithfulness を束ねる。

検証は次の通り。

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/RepairBasinExchangeObstruction.lean`: pass.
- `lake build ResearchLean`: pass.
- `lake build`: pass. 既存 `Formal/Arch/Extension/FeatureExtensionExamples.lean` の linter warning のみ。
- `#print axioms`: `RepairRefinementBasinCell`、basis definitions、`RepairBasinMembership`、`CommonRepairBasinClearance`、`traceOnlyRepairPlan`、`traceOnlyRepairPlan_misses_repairFrontier`、`BasinExchangeObstruction` は axiom-free。selected cell / basis / common clearance / trace-only clearance/failure は標準 `propext`。same visible/local projection、obstruction package、nonfaithfulness package は標準 `propext` と既存 selected cover/local-exactness witness 由来の `Quot.sound`。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。
- G3 形式化品質監査: pass。cell は endpoints、visible projection、`coarsePath`、`refinedPath` のみを field とし、exactness / basis / clearance / obstruction を field として保存しない。`RepairBasinMembership` は exact selected basis と declared clearance の組であり、単なる list hit ではない。

## 可視 projection

両側の path は selected visible repair/refinement surface では同じ local projection を持つ。projection
は endpoint / visible one-component shape を示すだけで、protected overlap basis の identity や
repair frontier component を保持しない。

## protected structure

Protected structure は、selected finite Cech overlap basis と declared repair support にある。
coarse basin は trace component を、refined basin は trace と repair-frontier component を持つ。
trace-only repair support は visible には十分に見えるが、refined protected basis では repair-frontier
component を hit しない。

## exactness_or_minimality_claim

coarse / refined の各 selected basis は exact overlap obstruction basis として扱う。common
clearance は selected bases の union を hit することに同値である。trace-only witness は refined
basis の repair-frontier component を落とす selected one-component failure witness であり、
形式的な global minimality theorem はこの cycle では主張しない。

## nonfaithfulness_or_failure_mode

visible repair/refinement projection が同じでも、protected repair-basin membership は復元できない。
failure mode は、coarse basin clearance と refined basin clearance の分離である。

## previous_cycle_delta

Cycle 67 は visible/local projection が同じ repair/transport Cech commutator において、flat path と
curved path の overlap basis が分岐することを示した。この cycle は、その curved overlap basis を
repair basin membership の交換障害として読み替え、refine-then-repair と repair-then-refine の
positive criterion / obstruction witness へ進める。

## 審判メモ

- 厳密性: initial `revise`、revision 後 `accept`; base 78; `genius_eligibility: no`。`repair basin` を selected finite overlap-basis / declared-clearance membership に狭め、same-object cell と no conclusion fields を要求。
- 研究価値: `accept`; base 90; `genius_eligibility: no`。Cycle 67 の curvature を repair-basin exchange へ持ち上げる高価値通常候補。
- repo 全体価値: `accept`; base 86; `genius_eligibility: no`。Lean / paper seed 価値は高いが Cycle 66-67 に近く、94 は高め。
- ライバル比較: `accept`; base 90; `genius_eligibility: no`。ADL の visible agreement / conformance view では落ちる protected basin exchange obstruction を固定する。

## G3 監査メモ

- 公理検査: pass。標準 `propext` と一部 `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。finite witness の `traceOnlyRepairPlan` と `traceOnlyRepairPlan_misses_repairFrontier` は axiom-free。
- 形式化品質: pass。nonfaithfulness は一般の `FaithfulToInvariant` 否定ではなく selected finite witness package として表現されているが、候補の claim boundary と一致する。
- resolved revise: `repair basin` を broad repair region ではなく selected finite overlap-basis / declared-clearance membership に限定した。same-object cell は conclusion fields を持たず、証明は theorem 側に置いた。見込み SCORE は 78/156 に下げた。
- unchecked: 任意 cell への一般化、形式的 global minimality / uniqueness theorem。

## 関連

- `g-aat-quality-surface-01-overlap-obstruction-basis.md`
- `g-aat-quality-surface-01-repair-transport-cech-commutator-curvature.md`

## 進捗ログ

- 2026-06-21: Cycle 68 の picked 候補として作成。G2 へ進める。
- 2026-06-21: G2 revise を反映して score 見込みを 78/156 に下げ、G3 Lean 証拠を固定した。
