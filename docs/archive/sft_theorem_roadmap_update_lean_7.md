# SFT Roadmap 最終実装指示書 7

## 目的

この指示書 7 は、SFT theorem roadmap の最後の実装指示書である。

指示書 1 から 6 までで、Lean 側には次の surface が入った。

- exact shared-clock `ClockedForecastCone`
- binary local-to-global gluing
- endpoint-level inverse-law constructor
- selected path-level inverse-law constructor
- finite-cover / Cech-style selected descent skeleton
- finite descent failure から typed obstruction witness への bridge
- selected bad obstruction witness から governance cutting への bridge

最後に行うことは、これらを一つの統合 package に束ねて、

```text
bounded evolution is either computably governed,
or it fails with an explicit typed boundary failure witness.
```

という conservative grand theorem surface を Lean 上に置くことである。

ここで重要なのは、`Fundamental Modularity Theorem of Software Evolution` を
無条件の宇宙的定理として証明することではない。Lean で証明するのは、
明示された finite / selected / package assumptions の下で、roadmap の各部品が
一つの最終 conclusion に組み上がる、という checked assembly theorem である。

---

## 現在の claim boundary

まだ次のようには言わない。

```text
All software evolution is computably governed.
All descent failures are completely classified.
All finite covers satisfy descent.
Full Cech cohomology is implemented.
Governance interventions are operationally effective in real repositories.
Closed-loop calibration is empirically correct.
AI agent teams are globally safe or confluent.
The full Fundamental Modularity Theorem is proved without assumptions.
```

この指示書 7 の完了後に言いたいこと:

```text
The SFT roadmap has a checked final assembly theorem package:
under explicit descent, obstruction, minimal-envelope, governance,
calibration, and confluence assumptions, a bounded selected evolution is
computably governed or exposes a typed boundary failure witness.
```

より短く言えば:

```text
The grand theorem now exists as a conservative Lean theorem-package assembly,
not as an unconditional global theorem.
```

---

## Phase 1: final assembly 用の新規ファイルを作る

追加先:

```text
Formal/Arch/Evolution/SFTFundamentalModularity.lean
```

基本 import:

```lean
import Formal.Arch.Evolution.SFTTheoremRoadmap
import Formal.Arch.Evolution.SFTDescentObstruction
```

namespace:

```lean
namespace Formal.Arch
namespace SFTFundamentalModularity
```

このファイルは、既存の定義を再発明しない。目的は、既存 surface を束ねる
final assembly layer を置くことである。

---

## Phase 2: final outcome vocabulary を定義する

最終 theorem は、成功か失敗かを一つの型で読めるようにする。

```lean
inductive FundamentalEvolutionOutcome where
  | computablyGoverned
  | typedBoundaryFailure
  deriving DecidableEq, Repr
```

ただし、実際の theorem conclusion は `Prop` の disjunction としてよい。
`FundamentalEvolutionOutcome` は docs-facing vocabulary として使う。

次に、typed boundary failure の class を定義する。

```lean
inductive FundamentalBoundaryFailureKind where
  | descentFailure
  | obstructionUnclassified
  | governanceUncut
  | reviewEnvelopeMissing
  | calibrationBoundaryExpanded
  | agenticConfluenceMissing
  | theoremFamilyAssumptionMissing
  deriving DecidableEq, Repr
```

failure witness:

```lean
structure TypedComputationBoundaryFailure where
  kind : FundamentalBoundaryFailureKind
  explainsBrokenBoundary : Prop
  evidenceBoundary : Prop
  nonConclusions : Prop
```

ここで `explainsBrokenBoundary` は、現時点では explicit assumption でよい。
全 failure を自動分類する theorem にはしない。

---

## Phase 3: computably governed predicate を定義する

最終 theorem の成功側を、単なる `True` ではなく、構成要素を読める package として置く。

```lean
structure ComputablyGoverned where
  descentAvailable : Prop
  obstructionHandled : Prop
  minimalEnvelopeAvailable : Prop
  governanceCutsBad : Prop
  closedLoopSettles : Prop
  agenticConfluenceAvailable : Prop
  governedBoundary : Prop
  nonConclusions : Prop
```

accessor theorem:

```lean
theorem computablyGoverned_records_governance
    (governed : ComputablyGoverned) :
    governed.governanceCutsBad :=
  governed.governanceCutsBad
```

同様に、必要なら各 field の accessor を追加してよい。

---

## Phase 4: component package を分けて保持する

最終 package に直接大量の field を詰め込むと読みにくくなる。
まず component package を置く。

```lean
structure FundamentalDescentComponent where
  modularityAsDescent : Prop
  forecastConeDescent : Prop
  modularity_iff_descent :
    modularityAsDescent ↔ forecastConeDescent
  descentBoundary : Prop
  nonConclusions : Prop
```

obstruction component:

```lean
structure FundamentalObstructionComponent where
  technicalDebtAsObstruction : Prop
  typedFailureWitnessAvailable : Prop
  obstructionBoundary : Prop
  nonConclusions : Prop
```

review/minimal envelope component:

```lean
structure FundamentalReviewComponent where
  minimalDecisionPreservingEnvelope : Prop
  reviewBoundary : Prop
  nonConclusions : Prop
```

governance component:

```lean
structure FundamentalGovernanceComponent where
  governanceAsObstructionCutting : Prop
  selectedBadWitnessesCut : Prop
  desiredFamiliesPreserved : Prop
  governanceBoundary : Prop
  nonConclusions : Prop
```

closed-loop component:

```lean
structure FundamentalCalibrationComponent where
  boundaryExplicitFixedPoint : Prop
  fixedPointOrBoundaryExpansion : Prop
  calibrationBoundary : Prop
  nonConclusions : Prop
```

agentic component:

```lean
structure FundamentalAgenticComponent where
  agenticConfluence : Prop
  fairInterleavingsConverge : Prop
  agentBoundary : Prop
  nonConclusions : Prop
```

これらは最初は Prop-level component でよい。
後続で既存 theorem package 型により依存させられる箇所だけ依存させる。

---

## Phase 5: existing roadmap package への bridge を置く

既存の `SFTTheoremRoadmap.FundamentalModularityConclusion` と
`SFTTheoremRoadmap.FundamentalModularityTheoremPackage` を捨てない。
final assembly はこれを使って構成する。

目標:

```lean
def toRoadmapConclusion
    (descent : FundamentalDescentComponent)
    (obstruction : FundamentalObstructionComponent)
    (review : FundamentalReviewComponent)
    (governance : FundamentalGovernanceComponent)
    (calibration : FundamentalCalibrationComponent)
    (governed : ComputablyGoverned)
    (failure : TypedComputationBoundaryFailure)
    (hOutcome :
      governed.governedBoundary ∨ failure.explainsBrokenBoundary) :
    SFTTheoremRoadmap.FundamentalModularityConclusion
```

この `def` は、既存 roadmap conclusion の field に component の Prop を詰める。
`computablyGoverned` と `typedBoundaryFailureWitness` は、それぞれ
`governed.governedBoundary` と `failure.explainsBrokenBoundary` に対応させてよい。

注意:

- `hOutcome` は明示前提でよい。
- ここで governance effectiveness を証明しない。
- ここで failure classifier completeness を証明しない。

---

## Phase 6: final hypotheses package を作る

ここが最終指示書の中心である。

```lean
structure FundamentalModularityHypotheses where
  descent : FundamentalDescentComponent
  obstruction : FundamentalObstructionComponent
  review : FundamentalReviewComponent
  governance : FundamentalGovernanceComponent
  calibration : FundamentalCalibrationComponent
  agentic : FundamentalAgenticComponent
  governed : ComputablyGoverned
  failure : TypedComputationBoundaryFailure
  hModularity :
    descent.modularityAsDescent
  hDebt :
    obstruction.technicalDebtAsObstruction
  hReview :
    review.minimalDecisionPreservingEnvelope
  hGovernance :
    governance.governanceAsObstructionCutting
  hLearning :
    calibration.boundaryExplicitFixedPoint
  governed_or_failure :
    governed.governedBoundary ∨ failure.explainsBrokenBoundary
  theoremBoundary : Prop
  nonConclusions : Prop
```

ここで `agentic` component は conclusion に直接入れなくてもよいが、
`ComputablyGoverned.agenticConfluenceAvailable` と対応する theorem を別途置く。

---

## Phase 7: final package constructor を証明する

最終 package を既存 roadmap package に落とす。

```lean
def roadmapConclusion_of_hypotheses
    (h : FundamentalModularityHypotheses) :
    SFTTheoremRoadmap.FundamentalModularityConclusion
```

続いて:

```lean
def roadmapPackage_of_hypotheses
    (h : FundamentalModularityHypotheses) :
    SFTTheoremRoadmap.FundamentalModularityTheoremPackage :=
  SFTTheoremRoadmap.FundamentalModularityTheoremPackage.ofTheoremFamily
    (roadmapConclusion_of_hypotheses h)
    h.hModularity
    h.hDebt
    h.hReview
    h.hGovernance
    h.hLearning
    h.theoremBoundary
```

この段階で、既存 `ofTheoremFamily` を再利用する。

---

## Phase 8: final theorem を置く

中心 theorem:

```lean
theorem fundamental_modularity_final_assembly
    (h : FundamentalModularityHypotheses) :
    h.descent.modularityAsDescent ∧
      h.obstruction.technicalDebtAsObstruction ∧
      h.review.minimalDecisionPreservingEnvelope ∧
      h.governance.governanceAsObstructionCutting ∧
      h.calibration.boundaryExplicitFixedPoint ∧
      (h.governed.governedBoundary ∨
        h.failure.explainsBrokenBoundary)
```

証明方針:

```lean
  exact
    SFTTheoremRoadmap.FundamentalModularityTheoremPackage
      .fundamental_modularity_of_theorem_family
        (roadmapConclusion_of_hypotheses h)
        h.hModularity
        h.hDebt
        h.hReview
        h.hGovernance
        h.hLearning
```

名前空間の都合でこの形が通らない場合は、既存 theorem 名を fully qualified にする。

roadmap-facing package accessor:

```lean
theorem final_bounded_evolution_governed_or_typed_failure
    (h : FundamentalModularityHypotheses) :
    h.governed.governedBoundary ∨ h.failure.explainsBrokenBoundary :=
  h.governed_or_failure
```

modularity/descent accessor:

```lean
theorem final_modularity_iff_forecastConeDescent
    (h : FundamentalModularityHypotheses) :
    (roadmapPackage_of_hypotheses h).modularity ↔
      (roadmapPackage_of_hypotheses h).forecastConeDescent :=
  SFTTheoremRoadmap.FundamentalModularityTheoremPackage
    .fundamental_modularity (roadmapPackage_of_hypotheses h)
```

---

## Phase 9: finite obstruction governance bridge を final component に接続する

指示書 6 の成果を final assembly で読めるようにする。

追加 theorem 候補:

```lean
theorem governanceComponent_of_finiteObstructionGovernance
    {Global Index Local : Type _}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG OperationL : Type _}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteObstructionGovernancePackage model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hBadClassified :
      ∀ witness,
        package.obstructionPackage.classifier.classify failure = some witness ->
        package.governancePackage.target.bad witness) :
    FundamentalGovernanceComponent
```

field の詰め方:

- `governanceAsObstructionCutting` は
  `∃ witness, ... cutsBad ...` にする。
- `selectedBadWitnessesCut` も同じ witness proposition でよい。
- `desiredFamiliesPreserved` は、最初は
  `∀ family, package.governancePackage.target.desiredPreserved family ->
    package.governancePackage.preservesDesired
      package.governancePackage.selectedIntervention family`
  にする。
- `governanceBoundary` は `package.obstructionToGovernanceBoundary`。
- `nonConclusions` は `package.nonConclusions`。

証明には次を使う。

```lean
governance_cuts_obstruction_of_finite_failure
finite_governance_preserves_desired_family
```

これにより、指示書 6 の selected finite bridge が final assembly に接続される。

---

## Phase 10: minimal envelope / calibration / agentic confluence bridge を置く

既存 theorem package を component に読む bridge を追加する。

### Minimal envelope

```lean
def reviewComponent_of_minimalEnvelopePackage
    {ConePath MinimalEnvelope : Type _}
    (package :
      SFTTheoremRoadmap.MinimalConsequenceEnvelopePackage
        ConePath MinimalEnvelope) :
    FundamentalReviewComponent
```

`minimalDecisionPreservingEnvelope` は、
例えば

```lean
∀ (OtherEnvelope : Type _)
  (otherProjection : ConePath -> OtherEnvelope),
  SFTTheoremRoadmap.DecisionSoundProjection
    package.reviewEquivalent otherProjection ->
    ∃ factor : MinimalEnvelope -> OtherEnvelope,
      ∀ path, factor (package.projection path) = otherProjection path
```

を入れる。

### Closed-loop calibration

```lean
def calibrationComponent_of_closedLoopPackage
    {Estimate : Type _} {update : Estimate -> Estimate}
    (package :
      SFTTheoremRoadmap.ClosedLoopCalibrationPackage Estimate update)
    (hMonotone : package.monotone)
    (hEvidence : package.evidencePreserving)
    (hBoundary : package.boundaryExplicit)
    (hNonConclusion : package.nonConclusionPreserving)
    (hError : package.forecastErrorRefining)
    (initial : Estimate) :
    FundamentalCalibrationComponent
```

`fixedPointOrBoundaryExpansion` には
`ClosedLoopCalibrationPackage.closedLoop_calibration_fixedPoint_or_boundary`
の結論を入れる。

### Agentic confluence

```lean
def agenticComponent_of_agenticConfluencePackage
    {Interleaving ConeQuotient : Type _}
    (package :
      SFTTheoremRoadmap.AgenticConfluencePackage
        Interleaving ConeQuotient)
    (hTermination : package.localTermination)
    (hConfluence : package.localConfluence)
    (hDescent : package.forecastConeDescent)
    (hInterface : package.interfaceConstraintsPreserved)
    (hPolicy : package.policiesCommutationInvariant) :
    FundamentalAgenticComponent
```

`fairInterleavingsConverge` には
`AgenticConfluencePackage.agentic_confluence` の結論を入れる。

---

## Phase 11: public entrypoint を更新する

更新先:

```text
Formal.lean
Formal/Arch/Evolution/SFTTheoremPackages.lean
docs/aat/lean_theorem_index.md
docs/aat/proof_obligations.md
docs/sft/sft_theorem_roadmap_and_research_vision.md
```

`Formal.lean` に追加:

```lean
import Formal.Arch.Evolution.SFTFundamentalModularity
```

`SFTTheoremPackages.lean` の representative declarations に追加:

```text
FundamentalEvolutionOutcome
FundamentalBoundaryFailureKind
TypedComputationBoundaryFailure
ComputablyGoverned
FundamentalDescentComponent
FundamentalObstructionComponent
FundamentalReviewComponent
FundamentalGovernanceComponent
FundamentalCalibrationComponent
FundamentalAgenticComponent
FundamentalModularityHypotheses
roadmapConclusion_of_hypotheses
roadmapPackage_of_hypotheses
fundamental_modularity_final_assembly
final_bounded_evolution_governed_or_typed_failure
final_modularity_iff_forecastConeDescent
governanceComponent_of_finiteObstructionGovernance
reviewComponent_of_minimalEnvelopePackage
calibrationComponent_of_closedLoopPackage
agenticComponent_of_agenticConfluencePackage
```

---

## Phase 12: docs の claim boundary を更新する

`docs/aat/lean_theorem_index.md` に新節を追加する。

候補見出し:

```text
## SFT Fundamental Modularity Final Assembly
```

書いてよい表現:

```text
The final assembly theorem packages the selected SFT theorem family into a
conservative governed-or-typed-failure conclusion under explicit assumptions.
```

```text
The theorem is a Lean-checked assembly over selected descent, obstruction,
minimal-envelope, governance, calibration, and agentic-confluence components.
```

まだ書かない表現:

```text
The Fundamental Modularity Theorem is unconditionally proved.
```

```text
All software evolution is governed.
```

```text
All real governance interventions are effective.
```

```text
The implemented theorem proves empirical forecast correctness.
```

`docs/aat/proof_obligations.md` では、既存の
`SFT theorem roadmap / fundamental modularity family` 行を更新する。

更新後の status は次のように読む。

```text
defined only / proved final assembly accessors under explicit package assumptions
```

ただし、future proof obligation として次を残す。

- concrete cochain-level Cech cohomology theorem
- complete descent failure classifier
- operational governance effectiveness over real repositories
- empirical calibration correctness
- global agentic safety / global confluence
- assumption-free Fundamental Modularity theorem

---

## Phase 13: roadmap 文書の Final Vision を更新する

`docs/sft/sft_theorem_roadmap_and_research_vision.md` の Lean 実装計画に、
指示書 7 の完了状態を追記する。

書いてよい表現:

```text
Lean now contains the final conservative assembly surface for the Fundamental
Modularity theorem family: under explicit package assumptions, bounded selected
evolution is governed or exposes a typed boundary failure.
```

書いてはいけない表現:

```text
The full theorem is completely proved for all software systems.
```

---

## Phase 14: 成功条件

この指示書 7 が完了したと言える条件:

1. `Formal/Arch/Evolution/SFTFundamentalModularity.lean` が追加される。
2. `FundamentalEvolutionOutcome` が追加される。
3. `FundamentalBoundaryFailureKind` が追加される。
4. `TypedComputationBoundaryFailure` が追加される。
5. `ComputablyGoverned` が追加される。
6. final component package 群が追加される。
7. `FundamentalModularityHypotheses` が追加される。
8. `roadmapConclusion_of_hypotheses` が追加される。
9. `roadmapPackage_of_hypotheses` が追加される。
10. `fundamental_modularity_final_assembly` が証明される。
11. `final_bounded_evolution_governed_or_typed_failure` が証明される。
12. `final_modularity_iff_forecastConeDescent` が証明される。
13. finite obstruction governance bridge から final governance component を作れる。
14. minimal envelope package から final review component を作れる。
15. closed-loop calibration package から final calibration component を作れる。
16. agentic confluence package から final agentic component を作れる。
17. `Formal.lean` と `SFTTheoremPackages.lean` の public entrypoint が更新される。
18. `docs/aat/lean_theorem_index.md` が更新される。
19. `docs/aat/proof_obligations.md` が更新される。
20. `docs/sft/sft_theorem_roadmap_and_research_vision.md` が更新される。
21. `lake build` が通る。
22. `git diff --check` が通る。
23. hidden / bidirectional Unicode scan が通る。
24. Lean source に `axiom`, `admit`, `sorry`, `unsafe` がない。
25. docs が assumption-free full theorem と誤読されない。

---

## 最終的に言えること

指示書 7 完了後に言えること:

```text
The SFT roadmap now has a Lean-checked final assembly theorem package.
Under explicit finite/selected theorem-package assumptions, bounded selected
software evolution is computably governed or exposes a typed boundary failure.
```

より正確には:

```text
The Fundamental Modularity theorem family is implemented as a conservative
Lean assembly: ForecastCone descent, descent obstruction, minimal review
envelope, obstruction-cutting governance, closed-loop calibration, and
agentic confluence are combined into a governed-or-typed-failure conclusion,
with all non-conclusions and assumption boundaries explicit.
```

まだ残る future proof obligations:

- all finite covers satisfying descent
- complete descent failure classification
- concrete Cech cochain complex and full cohomology theorem
- operational governance effectiveness
- empirical forecast calibration
- global agentic confluence / safety theorem
- assumption-free Fundamental Modularity theorem for all software systems

つまり、これで roadmap の Lean 実装は「最終形の骨格」まで到達する。
ここから先は、骨格の外側にある assumption を一つずつ実定理で discharge していく研究段階になる。

---

## 実装後 status

この指示書に対応して `Formal/Arch/Evolution/SFTFundamentalModularity.lean` を追加した。
Lean 側には次の final assembly surface が入っている。

- `FundamentalEvolutionOutcome`
- `FundamentalBoundaryFailureKind`
- `TypedComputationBoundaryFailure`
- `ComputablyGoverned`
- `FundamentalDescentComponent`
- `FundamentalObstructionComponent`
- `FundamentalReviewComponent`
- `FundamentalGovernanceComponent`
- `FundamentalCalibrationComponent`
- `FundamentalAgenticComponent`
- `FundamentalModularityHypotheses`
- `roadmapConclusion_of_hypotheses`
- `roadmapPackage_of_hypotheses`
- `fundamental_modularity_final_assembly`
- `final_bounded_evolution_governed_or_typed_failure`
- `final_agentic_confluence`
- `final_governed_agenticConfluenceAvailable`
- `final_modularity_iff_forecastConeDescent`

また、finite obstruction governance、minimal envelope、closed-loop calibration、
agentic confluence の既存 package surface を final component として読む bridge を追加した。
`agentic.nonConclusions` は roadmap conclusion の boundary に保存され、`hAgentic` と
`hAgenticAvailable` により agentic confluence component は final assembly conclusion と
governed-side availability に接続される。agentic component bridge は `localConfluence` 単体ではなく、
`AgenticConfluencePackage.agentic_confluence` の conclusion `FairInterleavingsConverge package.landing`
を `agenticConfluence` / `fairInterleavingsConverge` として保持する。
`Formal.lean` と `SFTTheoremPackages.lean` の public entrypoint metadata も更新済みである。

この status で言えることは、次に限られる。

```text
The SFT roadmap has a Lean-checked final assembly theorem package.
Under explicit finite/selected theorem-package assumptions, bounded selected
software evolution is computably governed or exposes a typed boundary failure.
```

まだ言わないことは変わらない。

- all finite covers satisfy descent
- all descent failures are completely classified
- full Cech cohomology theorem is implemented
- operational governance is effective in real repositories
- empirical calibration correctness is proved
- global agentic safety / confluence is proved
- the Fundamental Modularity Theorem is proved without assumptions
