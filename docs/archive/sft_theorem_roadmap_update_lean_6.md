# SFT Roadmap 残タスク実装指示書 6

## 目的

現在の Lean 実装は、ForecastCone descent について次の段階まで到達している。

- binary local-to-global gluing core
- endpoint-level inverse-law constructor
- selected path-level inverse-law constructor
- finite-cover / Cech-style selected descent skeleton

この指示書 6 の目的は、次へ進むこと。

```text
finite descent failure を typed obstruction / cohomology bridge / governance cutting へ接続する
```

ここで狙うのは、まだ full Cech cohomology theorem ではない。まず、finite selected descent が壊れる場合を typed failure として分類し、その failure から obstruction witness を得て、bad witness を governance intervention で切るための checked surface を作る。

---

## 現在の claim boundary

まだ次のようには言わない。

```text
All descent failures are completely classified.
Full Cech cohomology is implemented.
Governance synthesis is operationally effective.
Fundamental Modularity Theorem is fully proved.
```

現在言えること:

```text
Finite-cover ForecastCone descent has a selected Cech-style skeleton under explicit finite gluing and compatibility laws.
```

この指示書 6 の完了後に言いたいこと:

```text
Selected finite descent failures can be mapped to typed obstruction witnesses, and selected bad obstruction witnesses can be linked to governance cutting assumptions.
```

---

## Phase 1: finite descent failure type を定義する

追加先:

```text
Formal/Arch/Evolution/SFTDescentObstruction.lean
```

または最初は:

```text
Formal/Arch/Evolution/SFTFiniteCover.lean
```

推奨は新規ファイル。

```lean
import Formal.Arch.Evolution.SFTFiniteCover
import Formal.Arch.Evolution.SFTTheoremRoadmap

namespace Formal.Arch
```

finite descent で扱う failure を明示する。

```lean
inductive FiniteDescentFailureKind where
  | noGlobalLift
  | localIdentification
  | cechIncompatibility
  | governanceBlocked
  deriving DecidableEq, Repr
```

具体的な failure package:

```lean
structure FiniteDescentFailure
    {Global Index Local : Type _}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG OperationL : Type _}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  kind : FiniteDescentFailureKind
  localFamily :
    Option (FiniteLocalClockedConeFamily cover model source horizon)
  globalLeft :
    Option (ClockedConePoint model.globalSupport model.globalRelation source horizon)
  globalRight :
    Option (ClockedConePoint model.globalSupport model.globalRelation source horizon)
  evidenceBoundary : Prop
  nonConclusions : Prop
```

注意:

- `Option` は failure kind ごとに必要な payload が違うための軽量表現。
- より型安全にするなら inductive payload にしてよい。
- 最初は package surface を優先し、完全な eliminator は後でよい。

---

## Phase 2: obstruction witness を finite failure 用に定義する

既存の `SFTTheoremRoadmap.DescentObstructionWitness` は generic payload を持つ。

finite cover 用に、payload を明示した witness package を追加する。

```lean
structure FiniteDescentObstructionPayload
    {Global Index Local : Type _}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG OperationL : Type _}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  failureKind : FiniteDescentFailureKind
  obstructionClass : String
  affectedIndices : List Index
  classifierBoundary : Prop
  nonConclusions : Prop
```

typed witness:

```lean
abbrev FiniteDescentObstructionWitness
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) :=
  SFTTheoremRoadmap.DescentObstructionWitness
    (FiniteDescentObstructionPayload model source horizon)
```

`String` を避けたい場合は:

```lean
inductive FiniteObstructionClass where
  | missingGlue
  | overlapMismatch
  | hiddenCoupling
  | supportMismatch
  | governanceConflict
  deriving DecidableEq, Repr
```

推奨は `FiniteObstructionClass`。

---

## Phase 3: classifier completeness を明示前提にする

すべての failure を自動分類できるとは主張しない。classifier completeness は明示前提として定義する。

```lean
structure FiniteDescentObstructionClassifier
    {Global Index Local : Type _}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG OperationL : Type _}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  classify :
    FiniteDescentFailure model source horizon ->
      Option (FiniteDescentObstructionWitness model source horizon)
  sound :
    ∀ failure witness,
      classify failure = some witness ->
        witness.kind = SFTTheoremRoadmap.DescentFailureKind.surjectivityFailure ∨
        witness.kind = SFTTheoremRoadmap.DescentFailureKind.injectivityFailure
  completenessBoundary : Prop
  nonConclusions : Prop
```

もし既存 `DescentFailureKind` が finite kind と合わない場合は、finite 独自 witness を使ってよい。

```lean
structure FiniteTypedObstructionWitness ... where
  failureKind : FiniteDescentFailureKind
  payload : FiniteDescentObstructionPayload ...
  evidenceBoundary : Prop
  nonConclusions : Prop
```

重要なのは、classifier を theorem ではなく explicit data として置くこと。

---

## Phase 4: failure から obstruction を得る theorem を追加する

目標:

```lean
theorem finite_descent_obstruction_of_classified_failure
    (classifier : FiniteDescentObstructionClassifier model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hClassified :
      ∃ witness, classifier.classify failure = some witness) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      classifier.classify failure = some witness
```

より便利な package:

```lean
structure FiniteDescentObstructionPackage
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  classifier :
    FiniteDescentObstructionClassifier model source horizon
  everySelectedFailureClassified :
    ∀ failure,
      ∃ witness, classifier.classify failure = some witness
  obstructionBoundary : Prop
  nonConclusions : Prop
```

theorem:

```lean
theorem finite_descent_obstruction_of_failure
    (package : FiniteDescentObstructionPackage model source horizon)
    (failure : FiniteDescentFailure model source horizon) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      package.classifier.classify failure = some witness
```

これは classified selected failure に限る。

---

## Phase 5: cohomology bridge と obstruction witness を接続する

既存:

```lean
FiniteCechDescentCohomologyBridge
```

これに obstruction witness を接続する bridge を追加する。

```lean
structure FiniteCechObstructionBridge
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  cohomology :
    FiniteCechDescentCohomologyBridge model
  obstructionPackage :
    FiniteDescentObstructionPackage model source horizon
  h1_nonzero_witnesses_failure : Prop
  obstruction_reflects_h1_nonzero : Prop
  bridgeBoundary : Prop
  nonConclusions : Prop
```

最初の theorem は accessor でよい。

```lean
theorem finite_obstruction_bridge_records_boundary
    (bridge : FiniteCechObstructionBridge model source horizon) :
    bridge.bridgeBoundary :=
  bridge.bridgeBoundary
```

また、H1 vanishing と finite descent reading の既存 bridge は保持する。

```lean
theorem finite_descent_of_h1_vanishes
    (bridge : FiniteCechObstructionBridge model source horizon)
    (h : bridge.cohomology.H1Vanishes) :
    bridge.cohomology.allCompatibleLocalFuturesGlue :=
  bridge.cohomology.finiteDescent_of_h1_vanishes h
```

claim boundary:

- `H1` の実 cochain complex はまだ実装しない。
- `H1 nonzero -> obstruction` は selected bridge assumption としてよい。
- full cohomology theorem とは言わない。

---

## Phase 6: obstruction を review/minimal envelope に接続する

既存 roadmap には `MinimalEnvelope` と `ReviewSetoid` がある。

finite obstruction witness が review decision を誘導する surface を作る。

```lean
structure FiniteObstructionReviewProjection
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat)
    (Decision : Type _) where
  decide :
    FiniteDescentObstructionWitness model source horizon -> Decision
  soundDecisionBoundary : Prop
  minimalEnvelopeBoundary : Prop
  nonConclusions : Prop
```

theorem は最初は accessor でよい。

```lean
theorem finite_obstruction_review_records_sound_boundary
    (projection : FiniteObstructionReviewProjection model source horizon Decision) :
    projection.soundDecisionBoundary :=
  projection.soundDecisionBoundary
```

ここで言えること:

```text
obstruction witness can feed a selected review decision projection.
```

まだ言わないこと:

```text
review decision is complete, optimal, or operationally correct.
```

---

## Phase 7: governance cutting target を定義する

governance は obstruction witness のうち selected bad witness を切る。

```lean
structure FiniteGovernanceCutTarget
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  bad :
    FiniteDescentObstructionWitness model source horizon -> Prop
  desiredPreserved :
    FiniteLocalClockedConeFamily cover model source horizon -> Prop
  badBoundary : Prop
  desiredBoundary : Prop
  nonConclusions : Prop
```

---

## Phase 8: governance intervention package を finite obstruction に接続する

既存 `SFTTheoremRoadmap.GovernanceSynthesisPackage` を直接使ってもよいが、最初は finite obstruction 向け wrapper を作る。

```lean
structure FiniteGovernanceCuttingPackage
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  target :
    FiniteGovernanceCutTarget model source horizon
  intervention : Type _
  cutsBad :
    intervention ->
      FiniteDescentObstructionWitness model source horizon -> Prop
  preservesDesired :
    intervention ->
      FiniteLocalClockedConeFamily cover model source horizon -> Prop
  selectedIntervention : intervention
  selected_cuts_all_bad :
    ∀ witness, target.bad witness ->
      cutsBad selectedIntervention witness
  selected_preserves_desired :
    ∀ family, target.desiredPreserved family ->
      preservesDesired selectedIntervention family
  governanceBoundary : Prop
  nonConclusions : Prop
```

theorem:

```lean
theorem finite_governance_cuts_bad_obstruction
    (package : FiniteGovernanceCuttingPackage model source horizon)
    (witness : FiniteDescentObstructionWitness model source horizon)
    (hBad : package.target.bad witness) :
    package.cutsBad package.selectedIntervention witness :=
  package.selected_cuts_all_bad witness hBad
```

theorem:

```lean
theorem finite_governance_preserves_desired_family
    (package : FiniteGovernanceCuttingPackage model source horizon)
    (family : FiniteLocalClockedConeFamily cover model source horizon)
    (hDesired : package.target.desiredPreserved family) :
    package.preservesDesired package.selectedIntervention family :=
  package.selected_preserves_desired family hDesired
```

---

## Phase 9: obstruction-to-governance theorem package を作る

ここが指示書 6 の中心。

```lean
structure FiniteObstructionGovernancePackage
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  obstructionPackage :
    FiniteDescentObstructionPackage model source horizon
  governancePackage :
    FiniteGovernanceCuttingPackage model source horizon
  obstructionToGovernanceBoundary : Prop
  nonConclusions : Prop
```

theorem:

```lean
theorem governance_cuts_obstruction_of_finite_failure
    (package : FiniteObstructionGovernancePackage model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hBadClassified :
      ∀ witness,
        package.obstructionPackage.classifier.classify failure = some witness ->
        package.governancePackage.target.bad witness) :
    ∃ witness,
      package.obstructionPackage.classifier.classify failure = some witness ∧
      package.governancePackage.cutsBad
        package.governancePackage.selectedIntervention witness
```

証明方針:

1. `finite_descent_obstruction_of_failure` で witness を取る。
2. `hBadClassified` で bad を得る。
3. `finite_governance_cuts_bad_obstruction` を適用する。

これはかなり通しやすいはず。

---

## Phase 10: roadmap-facing theorem を追加する

追加先:

```text
Formal/Arch/Evolution/SFTTheoremRoadmap.lean
```

候補:

```lean
theorem finite_governance_cuts_obstruction_of_failure
    (package : FiniteObstructionGovernancePackage model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hBadClassified : ...)
    : ∃ witness, ...
```

docstring に必ず書く。

```text
This connects selected finite descent failures to selected governance cutting.
It assumes classifier completeness and selected governance cutting laws.
It is not operational governance effectiveness.
It is not full Fundamental Modularity Theorem.
```

---

## Phase 11: public entrypoint を更新する

更新先:

```text
Formal.lean
Formal/Arch/Evolution/SFTTheoremPackages.lean
```

新規ファイルを作る場合:

```lean
import Formal.Arch.Evolution.SFTDescentObstruction
```

representative declarations に追加:

```text
FiniteDescentFailureKind
FiniteDescentFailure
FiniteObstructionClass
FiniteDescentObstructionPayload
FiniteDescentObstructionClassifier
FiniteDescentObstructionPackage
finite_descent_obstruction_of_failure
FiniteCechObstructionBridge
FiniteObstructionReviewProjection
FiniteGovernanceCutTarget
FiniteGovernanceCuttingPackage
finite_governance_cuts_bad_obstruction
finite_governance_preserves_desired_family
FiniteObstructionGovernancePackage
governance_cuts_obstruction_of_finite_failure
SFTTheoremRoadmap.finite_governance_cuts_obstruction_of_failure
```

---

## Phase 12: docs を更新する

更新先:

```text
docs/aat/lean_theorem_index.md
docs/aat/proof_obligations.md
docs/sft/sft_theorem_roadmap_and_research_vision.md
docs/sft/sft_theorem_roadmap_update_lean_6.md
```

書いてよい表現:

```text
Selected finite descent failures can be classified into typed obstruction witnesses under an explicit classifier package.
```

```text
Selected bad obstruction witnesses can be cut by a governance package under explicit cutting and preservation laws.
```

まだ書かない表現:

```text
All descent failures are completely classified.
```

```text
Governance interventions are operationally effective.
```

```text
Full Cech cohomology theorem is proved.
```

```text
Fundamental Modularity Theorem is fully proved.
```

---

## 成功条件

この指示書 6 が完了したと言える条件:

1. `FiniteDescentFailureKind` が追加される。
2. `FiniteDescentFailure` が追加される。
3. finite obstruction payload / witness が追加される。
4. `FiniteDescentObstructionClassifier` が追加される。
5. `FiniteDescentObstructionPackage` が追加される。
6. `finite_descent_obstruction_of_failure` が証明される。
7. `FiniteCechObstructionBridge` が追加される。
8. `FiniteObstructionReviewProjection` が追加される。
9. `FiniteGovernanceCutTarget` が追加される。
10. `FiniteGovernanceCuttingPackage` が追加される。
11. `finite_governance_cuts_bad_obstruction` が証明される。
12. `finite_governance_preserves_desired_family` が証明される。
13. `FiniteObstructionGovernancePackage` が追加される。
14. `governance_cuts_obstruction_of_finite_failure` が証明される。
15. roadmap-facing accessor theorem が追加される。
16. theorem index / proof obligations / roadmap docs が更新される。
17. `lake build` が通る。
18. `git diff --check` が通る。
19. Lean source に `axiom`, `admit`, `sorry`, `unsafe` がない。
20. docs が governance effectiveness や full cohomology を無条件主張していない。

---

## 完了後に言えること

完了後は、次のように言える。

```text
Selected finite descent failures can be classified into typed obstruction witnesses, and selected bad obstruction witnesses can be cut by explicit governance packages.
```

より正確には:

```text
Finite-cover SFT descent now has a checked bridge from selected descent failure,
to typed obstruction classification, to selected governance cutting, all under
explicit classifier and governance-law assumptions.
```

まだ次は言わない。

```text
Full Cech cohomology theorem is proved.
Governance is operationally effective.
Fundamental Modularity Theorem is fully proved.
```

次の指示書 7 では、closed-loop calibration、minimal envelope、agentic confluence と統合して `FundamentalModularityTheoremPackage` の final assembly に進む。

---

## 実装後ステータス

この指示書 6 の Lean 実装は `Formal/Arch/Evolution/SFTDescentObstruction.lean`,
`Formal/Arch/Evolution/SFTTheoremRoadmap.lean`, `Formal/Arch/Evolution/SFTTheoremPackages.lean`,
`Formal.lean` に反映済み。

追加された surface:

- `FiniteDescentFailureKind`
- `FiniteDescentFailure`
- `FiniteObstructionClass`
- `FiniteDescentObstructionPayload`
- `FiniteTypedObstructionWitness`
- `FiniteDescentObstructionWitness`
- `FiniteDescentObstructionClassifier`
- `FiniteDescentObstructionClassifier.classified_failureKind_eq`
- `FiniteDescentObstructionClassifier.classified_payload_failureKind_eq`
- `finite_descent_obstruction_of_classified_failure`
- `finite_descent_obstruction_of_classified_failure_sound`
- `FiniteDescentObstructionPackage`
- `finite_descent_obstruction_of_failure`
- `finite_descent_obstruction_of_failure_sound`
- `FiniteCechObstructionBridge`
- `FiniteCechObstructionBridge.finite_obstruction_bridge_records_boundary`
- `FiniteCechObstructionBridge.finite_descent_of_h1_vanishes`
- `FiniteObstructionReviewProjection`
- `finite_obstruction_review_records_sound_boundary`
- `FiniteGovernanceCutTarget`
- `FiniteGovernanceCuttingPackage`
- `finite_governance_cuts_bad_obstruction`
- `finite_governance_preserves_desired_family`
- `FiniteObstructionGovernancePackage`
- `governance_cuts_obstruction_of_finite_failure`
- `SFTTheoremRoadmap.finite_governance_cuts_obstruction_of_failure`

言えること:

```text
Selected finite descent failures can be classified into typed obstruction
witnesses, and selected bad obstruction witnesses can be cut by explicit
governance packages.
```

より正確には、finite-cover SFT descent は selected descent failure から typed
obstruction classification へ、さらに selected governance cutting へ接続する checked bridge を持つ。
この bridge は explicit classifier completeness assumption と selected governance cutting /
preservation laws に相対化される。
`FiniteTypedObstructionWitness` は outer failure kind と payload failure kind の一致を
`payload_failureKind_eq` として保持し、classifier soundness も outer / payload の両方が
selected failure kind と一致することを要求する。

まだ言わないこと:

```text
All descent failures are completely classified.
Full Cech cohomology theorem is proved.
Governance interventions are operationally effective.
Fundamental Modularity Theorem is fully proved.
```

残る future proof obligation:

- complete classification of all descent failures
- full Cech cohomology theorem / concrete cochain complex
- operational governance effectiveness
- governance synthesis integrated with actual obstruction cutting without selected package assumptions
- closed-loop calibration over concrete finite-height refinement order
- Fundamental Modularity theorem over one integrated SFT model
