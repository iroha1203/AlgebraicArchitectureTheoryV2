---
status: picked
goal: G-sft-conway-01
exploration_role: g6-frontier / coherent-family-local-exactness
candidate_type: negative-bridge
capability_category: common-refinement, coherent-family, local-global-boundary, conway-obstruction
expected_base_score: 50
expected_evidence_multiplier: 2.0
expected_final_score: 100
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 14
score_reason: Cycle 12/13 の frontier だった local support はあるが shared span がない failure mode を、現 `CommonRefinementSpan` interface では起こらない blocker theorem として固定する。Sigma-indexed shared span 構成で coherent support iff forkwise support を証明するため base 50。
mathematical_interest: 現 interface の柔軟性が、local fork supports を常に coherent shared span へ assemble できることを明示する。
goal_advancement: coherent family interface の exactness boundary を固定し、次に必要な non-selected refinement / restricted span vocabulary を明確化する。
dullness_risk: 新 obstruction ではなく、現 vocabulary では obstruction が潰れるという negative bridge。
proof_or_evidence_plan: `research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyExactness.lean` に local support predicate、Sigma assembly、coherent iff local、local-but-not-coherent blocker、vanishing interaction を置く。
planned_theorem_names: ForkFamilyHasLocalCommonRefinementSupport, CoherentCommonRefinementSupport.ofEachForkSupport, coherentCommonRefinementSupport_iff_eachForkSupport, ForkFamilyLocalButNotCoherent, no_forkFamilyLocalButNotCoherent, coherentGlobalCommonRefinementVanishes_implies_localSupport, localSupport_and_globalZeroCochain_implies_coherentVanishes, selectedCoherentFamilyExactnessPackage
rival_advantage: owner mismatch dashboard can show mismatch, but this theorem records a precise boundary of the current common-refinement interface: local support cannot witness a shared-span obstruction without restricting span vocabulary.
visible_projection: forkwise local support, Sigma shared span, coherent support equivalence, local/shared blocker.
protected_structure: CommonRefinementSpan, CommonRefinementSupportsFork, CoherentCommonRefinementSupport, SupportForkFamily.
exactness_or_minimality_claim: `ForkFamilyHasCoherentCommonRefinementSupport family` iff every selected fork has local common-refinement support.
nonfaithfulness_or_failure_mode: the attempted local-but-not-coherent obstruction is impossible at the current selected interface.
previous_cycle_delta: turns Cycle 13's next frontier into a precise negative theorem rather than adding another preservation lemma.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, common-refinement, coherent-family, exactness-boundary]
created: 2026-07-04
---

# Coherent family local exactness

## 主張

各 selected fork に local `CommonRefinementSupportsFork` があるなら、それらの local span を Sigma-indexed sum で束ねて
one shared `CommonRefinementSpan` を作れる。したがって現 interface では、
`ForkFamilyHasCoherentCommonRefinementSupport family` は forkwise local support と同値であり、
「local support はあるが shared span が存在しない」failure mode は起こらない。

## 非自明性

これは新 obstruction ではなく blocker theorem である。Cycle 12/13 の自然な次候補だった
local/shared gap を検出しようとしても、現 `CommonRefinementSpan` は任意の local span family を
disjoint union で束ねられるほど柔軟なため、その gap は定義上消える。

## GOAL への前進

Conway common-refinement family interface の exactness boundary を固定する。次に非自明な obstruction を
得るには、non-selected refinement span family、restricted span vocabulary、または arbitrary-cover
naturality blocker が必要であることを示す。

## SCORE 見込み

- `score_reason`: coherent iff local support の Sigma assembly theorem と blocker theorem により base 50。
- `dullness_risk`: obstruction を増やすのではなく、現 vocabulary では obstruction が潰れることを示す negative bridge。
- `proof_or_evidence_plan`: `focused Lean check: ResearchLean/AG/SFT/ConwayCoherentFamilyExactness.lean`、
  `旧Research aggregate build`、`#print axioms` で検証する。

## Lean evidence

- `research/lean/ResearchLean/AG/SFT/ConwayCoherentFamilyExactness.lean`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ForkFamilyHasLocalCommonRefinementSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.CoherentCommonRefinementSupport.ofEachForkSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentCommonRefinementSupport_iff_eachForkSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.ForkFamilyLocalButNotCoherent`
- `ResearchLean.AG.SFT.ConwayTwoTopology.no_forkFamilyLocalButNotCoherent`
- `ResearchLean.AG.SFT.ConwayTwoTopology.coherentGlobalCommonRefinementVanishes_implies_localSupport`
- `ResearchLean.AG.SFT.ConwayTwoTopology.localSupport_and_globalZeroCochain_implies_coherentVanishes`
- `ResearchLean.AG.SFT.ConwayTwoTopology.selectedCoherentFamilyExactnessPackage`

## 審判メモ

- 厳密性: pass。Sigma-indexed shared span at the current selected interface として Lean theorem 化済み。
- 研究価値: base 50。現 interface の exactness boundary を明示する negative bridge。
- repo 全体価値: 次の non-selected / restricted-span frontier を明確にする。
- ライバル比較: mismatch 可視化ではなく、common-refinement vocabulary の限界を theorem として保存する。

## 進捗ログ

- 2026-07-04: 作成。`focused Lean check: ResearchLean/AG/SFT/ConwayCoherentFamilyExactness.lean`、
  module build、`旧Research aggregate build`、full `lake build` が通過。G2 二審判 pass、final score +100。
  `#print axioms` は `Classical.choice` のみ。
