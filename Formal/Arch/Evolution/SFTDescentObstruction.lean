import Formal.Arch.Evolution.SFTCechCohomology

/-!
Finite descent obstruction and governance-cutting surface.

This module connects the finite-cover ForecastCone descent skeleton to typed
failure classification, obstruction witnesses, Cech-style bridge predicates,
review projection, and selected governance cutting.  Classifier completeness
and governance effectiveness remain explicit assumptions.
-/

namespace Formal.Arch

universe u v w x y z

/-- Selected finite descent failure kinds. -/
inductive FiniteDescentFailureKind where
  | noGlobalLift
  | localIdentification
  | cechIncompatibility
  | governanceBlocked
  deriving DecidableEq, Repr

/--
A selected finite descent failure record.

Payload fields are optional because different failure kinds carry different
evidence.  The record is a boundary surface, not a complete classifier.
-/
structure FiniteDescentFailure
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  kind : FiniteDescentFailureKind
  localFamily :
    Option (FiniteLocalClockedConeFamily cover model source horizon)
  globalLeft :
    Option
      (ClockedConePoint model.globalSupport model.globalRelation
        source horizon)
  globalRight :
    Option
      (ClockedConePoint model.globalSupport model.globalRelation
        source horizon)
  evidenceBoundary : Prop
  nonConclusions : Prop

/-- Selected classes for finite descent obstruction witnesses. -/
inductive FiniteObstructionClass where
  | missingGlue
  | overlapMismatch
  | hiddenCoupling
  | supportMismatch
  | governanceConflict
  deriving DecidableEq, Repr

/-- Payload attached to a finite descent obstruction witness. -/
structure FiniteDescentObstructionPayload
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  failureKind : FiniteDescentFailureKind
  obstructionClass : FiniteObstructionClass
  affectedIndices : List Index
  classifierBoundary : Prop
  nonConclusions : Prop

/-- Typed finite obstruction witness. -/
structure FiniteTypedObstructionWitness
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  failureKind : FiniteDescentFailureKind
  payload : FiniteDescentObstructionPayload model source horizon
  payload_failureKind_eq :
    payload.failureKind = failureKind
  evidenceBoundary : Prop
  nonConclusions : Prop

/-- Public finite obstruction witness alias. -/
abbrev FiniteDescentObstructionWitness
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) :=
  FiniteTypedObstructionWitness model source horizon

/--
Explicit finite descent obstruction classifier.

Completeness is not a theorem here; callers provide classification data and
boundary assumptions.
-/
structure FiniteDescentObstructionClassifier
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  classify :
    FiniteDescentFailure model source horizon ->
      Option (FiniteDescentObstructionWitness model source horizon)
  sound :
    ∀ failure witness,
      classify failure = some witness ->
        witness.failureKind = failure.kind ∧
          witness.payload.failureKind = failure.kind
  completenessBoundary : Prop
  nonConclusions : Prop

namespace FiniteDescentObstructionClassifier

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {model : FiniteSFTModel cover OperationG OperationL}
variable {source : Global} {horizon : Nat}

/-- A classified witness has the selected failure kind on its outer tag. -/
theorem classified_failureKind_eq
    (classifier :
      FiniteDescentObstructionClassifier model source horizon)
    {failure : FiniteDescentFailure model source horizon}
    {witness : FiniteDescentObstructionWitness model source horizon}
    (hClassified : classifier.classify failure = some witness) :
    witness.failureKind = failure.kind :=
  (classifier.sound failure witness hClassified).1

/-- A classified witness has the selected failure kind in its payload tag. -/
theorem classified_payload_failureKind_eq
    (classifier :
      FiniteDescentObstructionClassifier model source horizon)
    {failure : FiniteDescentFailure model source horizon}
    {witness : FiniteDescentObstructionWitness model source horizon}
    (hClassified : classifier.classify failure = some witness) :
    witness.payload.failureKind = failure.kind :=
  (classifier.sound failure witness hClassified).2

/-- The witness itself records agreement between outer and payload failure tags. -/
theorem classified_payload_matches_witness_kind
    (classifier :
      FiniteDescentObstructionClassifier model source horizon)
    {failure : FiniteDescentFailure model source horizon}
    {witness : FiniteDescentObstructionWitness model source horizon}
    (_hClassified : classifier.classify failure = some witness) :
    witness.payload.failureKind = witness.failureKind :=
  witness.payload_failureKind_eq

end FiniteDescentObstructionClassifier

/-- A classified selected failure yields its selected obstruction witness. -/
theorem finite_descent_obstruction_of_classified_failure
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (classifier :
      FiniteDescentObstructionClassifier model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hClassified :
      ∃ witness, classifier.classify failure = some witness) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      classifier.classify failure = some witness :=
  hClassified

/--
A classified selected failure yields a witness whose outer and payload failure
tags both match the selected failure kind.
-/
theorem finite_descent_obstruction_of_classified_failure_sound
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (classifier :
      FiniteDescentObstructionClassifier model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hClassified :
      ∃ witness, classifier.classify failure = some witness) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      classifier.classify failure = some witness ∧
        witness.failureKind = failure.kind ∧
          witness.payload.failureKind = failure.kind := by
  rcases hClassified with ⟨witness, hWitness⟩
  exact ⟨witness, hWitness, classifier.sound failure witness hWitness⟩

/-- Package asserting selected finite descent failures are classified. -/
structure FiniteDescentObstructionPackage
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  classifier :
    FiniteDescentObstructionClassifier model source horizon
  everySelectedFailureClassified :
    ∀ failure,
      ∃ witness, classifier.classify failure = some witness
  obstructionBoundary : Prop
  nonConclusions : Prop

/-- A selected finite descent failure yields a typed obstruction witness. -/
theorem finite_descent_obstruction_of_failure
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteDescentObstructionPackage model source horizon)
    (failure : FiniteDescentFailure model source horizon) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      package.classifier.classify failure = some witness :=
  package.everySelectedFailureClassified failure

/--
A selected finite descent failure yields a typed obstruction witness whose
outer and payload failure tags both match the selected failure kind.
-/
theorem finite_descent_obstruction_of_failure_sound
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteDescentObstructionPackage model source horizon)
    (failure : FiniteDescentFailure model source horizon) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      package.classifier.classify failure = some witness ∧
        witness.failureKind = failure.kind ∧
          witness.payload.failureKind = failure.kind :=
  finite_descent_obstruction_of_classified_failure_sound
    package.classifier failure
    (package.everySelectedFailureClassified failure)

/--
A selected classified failure carries all failure-kind soundness equalities:
the witness outer tag, payload tag, and witness-internal payload tag agree.
-/
theorem finite_descent_obstruction_of_classified_failure_sound_complete
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (classifier :
      FiniteDescentObstructionClassifier model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hClassified :
      ∃ witness, classifier.classify failure = some witness) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      classifier.classify failure = some witness ∧
        witness.failureKind = failure.kind ∧
          witness.payload.failureKind = failure.kind ∧
            witness.payload.failureKind = witness.failureKind := by
  rcases hClassified with ⟨witness, hWitness⟩
  exact
    ⟨witness, hWitness,
      FiniteDescentObstructionClassifier.classified_failureKind_eq
        classifier hWitness,
      FiniteDescentObstructionClassifier.classified_payload_failureKind_eq
        classifier hWitness,
      FiniteDescentObstructionClassifier.classified_payload_matches_witness_kind
        classifier hWitness⟩

/--
Finite exact classifier-completeness package.

The completeness theorem remains relative to the selected finite exact model
and the supplied classifier package.  It does not classify all software
failures and does not assert ambient source-observation coverage.
-/
structure FiniteExactFailureClassifierCompleteness
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    (exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance)
    (source : Global) (horizon : Nat) where
  obstructionPackage :
    FiniteDescentObstructionPackage exactModel.descentModel source horizon
  recordsExactCoverBoundary : exactModel.RecordsExactCoverBoundary
  recordsFiniteModelBoundary : exactModel.RecordsFiniteModelBoundary
  selectedFailureBoundary : Prop
  classifierCompletenessBoundary : Prop
  soundnessBoundary : Prop
  nonConclusions : Prop

namespace FiniteExactFailureClassifierCompleteness

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {OperationG : Type x} {OperationL : Type y}
variable {Governance : Type z}
variable {exactModel :
  FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
variable {source : Global} {horizon : Nat}

/-- The finite exact package exposes its selected classifier. -/
def classifier
    (package :
      FiniteExactFailureClassifierCompleteness exactModel source horizon) :
    FiniteDescentObstructionClassifier
      exactModel.descentModel source horizon :=
  package.obstructionPackage.classifier

/-- Completeness is recorded only for the selected finite exact failure universe. -/
def RecordsClassifierCompletenessBoundary
    (package :
      FiniteExactFailureClassifierCompleteness exactModel source horizon) :
    Prop :=
  package.classifierCompletenessBoundary ∧
    package.obstructionPackage.classifier.completenessBoundary

/-- Non-conclusions for classifier completeness remain explicit. -/
def RecordsNonConclusions
    (package :
      FiniteExactFailureClassifierCompleteness exactModel source horizon) :
    Prop :=
  package.nonConclusions ∧ exactModel.RecordsNonConclusions ∧
    package.obstructionPackage.nonConclusions ∧
    package.obstructionPackage.classifier.nonConclusions

/-- Exact-cover boundary assumptions remain explicit. -/
theorem records_exactCoverBoundary
    (package :
      FiniteExactFailureClassifierCompleteness exactModel source horizon) :
    exactModel.RecordsExactCoverBoundary :=
  package.recordsExactCoverBoundary

/-- Finite-model boundary assumptions remain explicit. -/
theorem records_finiteModelBoundary
    (package :
      FiniteExactFailureClassifierCompleteness exactModel source horizon) :
    exactModel.RecordsFiniteModelBoundary :=
  package.recordsFiniteModelBoundary

end FiniteExactFailureClassifierCompleteness

/--
Failure-kind local classifier coverage.

This is a selected finite predicate over the supplied classifier.  It does not
claim that every software failure, repository failure, or extractor output is
classified.
-/
def FiniteFailureKindClassifierCoverage
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (classifier :
      FiniteDescentObstructionClassifier model source horizon)
    (kind : FiniteDescentFailureKind) : Prop :=
  ∀ failure : FiniteDescentFailure model source horizon,
    failure.kind = kind ->
      ∃ witness : FiniteDescentObstructionWitness model source horizon,
        classifier.classify failure = some witness ∧
          witness.failureKind = kind ∧
            witness.payload.failureKind = kind

/-- A package records classifier coverage separately for each selected failure kind. -/
def FiniteFailureKindClassifierCoverageMatrix
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteDescentObstructionPackage model source horizon) : Prop :=
  ∀ kind,
    FiniteFailureKindClassifierCoverage package.classifier kind

/--
Every selected finite exact descent failure is classified by the supplied
classifier package, with outer and payload failure-kind soundness preserved.
-/
theorem finiteExact_failure_classifier_complete
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (package :
      FiniteExactFailureClassifierCompleteness exactModel source horizon)
    (failure :
      FiniteDescentFailure exactModel.descentModel source horizon) :
    ∃ witness :
      FiniteDescentObstructionWitness exactModel.descentModel source horizon,
      package.classifier.classify failure = some witness ∧
        witness.failureKind = failure.kind ∧
          witness.payload.failureKind = failure.kind ∧
            witness.payload.failureKind = witness.failureKind :=
  finite_descent_obstruction_of_classified_failure_sound_complete
    package.classifier failure
    (package.obstructionPackage.everySelectedFailureClassified failure)

/--
Finite exact classifier completeness can be read failure-kind by failure-kind.

The theorem only ranges over failures in the selected finite exact model.
-/
theorem finiteExact_failureKind_classifier_complete
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (package :
      FiniteExactFailureClassifierCompleteness exactModel source horizon)
    (kind : FiniteDescentFailureKind) :
    FiniteFailureKindClassifierCoverage package.classifier kind := by
  intro failure hKind
  rcases finiteExact_failure_classifier_complete package failure with
    ⟨witness, hClassified, hWitnessKind, hPayloadKind, _hPayloadMatches⟩
  exact
    ⟨witness, hClassified, hWitnessKind.trans hKind,
      hPayloadKind.trans hKind⟩

/--
The finite exact package exposes the whole selected failure-kind coverage
matrix.
-/
theorem finiteExact_failureKind_classifier_matrix
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (package :
      FiniteExactFailureClassifierCompleteness exactModel source horizon) :
    FiniteFailureKindClassifierCoverageMatrix package.obstructionPackage :=
  fun kind => finiteExact_failureKind_classifier_complete package kind

/--
Cech-side obstruction witness for a selected finite cone cocycle.

The record keeps the concrete cocycle together with an explicit selected
non-coboundary / obstruction boundary.  It is not a full cohomology theorem.
-/
structure CechCocycleObstruction
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  zero : CechCone0 model source horizon
  one : CechCone1 cover model source horizon
  cocycle : IsCechConeCocycle zero one
  selectedNonCoboundaryBoundary : Prop
  obstructionBoundary : Prop
  nonConclusions : Prop

/--
Bridge between concrete Cech cocycle obstructions and typed finite obstruction
witnesses over the same selected finite exact model.
-/
structure FiniteCechTypedObstructionBridge
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    (exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance)
    (source : Global) (horizon : Nat) where
  classifierCompleteness :
    FiniteExactFailureClassifierCompleteness exactModel source horizon
  witnessToCocycle :
    FiniteDescentObstructionWitness exactModel.descentModel source horizon ->
      CechCocycleObstruction exactModel.descentModel source horizon
  cocycleToFailure :
    CechCocycleObstruction exactModel.descentModel source horizon ->
      FiniteDescentFailure exactModel.descentModel source horizon
  witnessCocycleBoundary : Prop
  cocycleFailureBoundary : Prop
  selectedFiniteBoundary : Prop
  nonConclusions : Prop

namespace FiniteCechTypedObstructionBridge

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {OperationG : Type x} {OperationL : Type y}
variable {Governance : Type z}
variable {exactModel :
  FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
variable {source : Global} {horizon : Nat}

/-- The bridge records its selected finite boundary. -/
def RecordsSelectedFiniteBoundary
    (bridge :
      FiniteCechTypedObstructionBridge exactModel source horizon) : Prop :=
  bridge.selectedFiniteBoundary ∧
    bridge.classifierCompleteness.RecordsClassifierCompletenessBoundary

/-- Non-conclusions remain explicit across Cech and classifier boundaries. -/
def RecordsNonConclusions
    (bridge :
      FiniteCechTypedObstructionBridge exactModel source horizon) : Prop :=
  bridge.nonConclusions ∧
    bridge.classifierCompleteness.RecordsNonConclusions

end FiniteCechTypedObstructionBridge

/--
A typed finite obstruction witness can be read as a selected Cech cocycle
obstruction through the supplied bridge.
-/
def cech_obstruction_of_typed_witness
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (bridge :
      FiniteCechTypedObstructionBridge exactModel source horizon)
    (witness :
      FiniteDescentObstructionWitness exactModel.descentModel source horizon) :
    CechCocycleObstruction exactModel.descentModel source horizon :=
  bridge.witnessToCocycle witness

/--
A selected Cech cocycle obstruction yields a typed finite obstruction witness
through the selected finite exact classifier-completeness bridge.
-/
theorem typed_obstruction_of_cech_cocycle_obstruction
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (bridge :
      FiniteCechTypedObstructionBridge exactModel source horizon)
    (obstruction :
      CechCocycleObstruction exactModel.descentModel source horizon) :
    ∃ witness :
      FiniteDescentObstructionWitness exactModel.descentModel source horizon,
      bridge.classifierCompleteness.classifier.classify
          (bridge.cocycleToFailure obstruction) = some witness ∧
        witness.failureKind = (bridge.cocycleToFailure obstruction).kind ∧
          witness.payload.failureKind =
            (bridge.cocycleToFailure obstruction).kind ∧
            witness.payload.failureKind = witness.failureKind :=
  finiteExact_failure_classifier_complete
    bridge.classifierCompleteness (bridge.cocycleToFailure obstruction)

/--
Cech cocycle obstructions preserve the typed failure-kind alignment supplied by
the selected finite exact classifier bridge.
-/
theorem typed_obstruction_of_cech_cocycle_preserves_failure_kind
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (bridge :
      FiniteCechTypedObstructionBridge exactModel source horizon)
    (obstruction :
      CechCocycleObstruction exactModel.descentModel source horizon) :
    ∃ witness :
      FiniteDescentObstructionWitness exactModel.descentModel source horizon,
      witness.failureKind = (bridge.cocycleToFailure obstruction).kind ∧
        witness.payload.failureKind =
          (bridge.cocycleToFailure obstruction).kind ∧
          witness.payload.failureKind = witness.failureKind := by
  rcases typed_obstruction_of_cech_cocycle_obstruction bridge obstruction with
    ⟨witness, _hClassified, hFailureKind, hPayloadKind, hPayloadMatches⟩
  exact ⟨witness, hFailureKind, hPayloadKind, hPayloadMatches⟩

/-- Cech bridge plus obstruction classifier boundary for finite descent. -/
structure FiniteCechObstructionBridge
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
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

namespace FiniteCechObstructionBridge

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {model : FiniteSFTModel cover OperationG OperationL}
variable {source : Global} {horizon : Nat}

/-- The obstruction/cohomology bridge records its selected boundary. -/
theorem finite_obstruction_bridge_records_boundary
    (bridge : FiniteCechObstructionBridge model source horizon) :
    bridge.bridgeBoundary -> bridge.bridgeBoundary :=
  id

/-- The obstruction/cohomology bridge exposes its selected boundary when supplied. -/
theorem finite_obstruction_bridge_boundary
    (bridge : FiniteCechObstructionBridge model source horizon)
    (hBoundary : bridge.bridgeBoundary) :
    bridge.bridgeBoundary :=
  hBoundary

/-- H1 vanishing still exposes the selected finite descent reading. -/
theorem finite_descent_of_h1_vanishes
    (bridge : FiniteCechObstructionBridge model source horizon)
    (h : bridge.cohomology.H1Vanishes) :
    bridge.cohomology.allCompatibleLocalFuturesGlue :=
  bridge.cohomology.finiteDescent_of_h1_vanishes h

end FiniteCechObstructionBridge

/-- Projection from finite obstruction witnesses to selected review decisions. -/
structure FiniteObstructionReviewProjection
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat)
    (Decision : Type z) where
  decide :
    FiniteDescentObstructionWitness model source horizon -> Decision
  soundDecisionBoundary : Prop
  minimalEnvelopeBoundary : Prop
  nonConclusions : Prop

/-- The review projection exposes its selected soundness boundary. -/
theorem finite_obstruction_review_records_sound_boundary
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat} {Decision : Type z}
    (projection :
      FiniteObstructionReviewProjection model source horizon Decision) :
    projection.soundDecisionBoundary -> projection.soundDecisionBoundary :=
  id

/-- The review projection exposes its selected soundness boundary when supplied. -/
theorem finite_obstruction_review_sound_boundary
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat} {Decision : Type z}
    (projection :
      FiniteObstructionReviewProjection model source horizon Decision)
    (hBoundary : projection.soundDecisionBoundary) :
    projection.soundDecisionBoundary :=
  hBoundary

/-- Governance target for cutting selected bad finite obstruction witnesses. -/
structure FiniteGovernanceCutTarget
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  bad :
    FiniteDescentObstructionWitness model source horizon -> Prop
  desiredPreserved :
    FiniteLocalClockedConeFamily cover model source horizon -> Prop
  badBoundary : Prop
  desiredBoundary : Prop
  nonConclusions : Prop

/-- Selected governance cutting package for finite obstruction witnesses. -/
structure FiniteGovernanceCuttingPackage
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  intervention : Type z
  target :
    FiniteGovernanceCutTarget model source horizon
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

/-- The selected governance intervention cuts a selected bad obstruction. -/
theorem finite_governance_cuts_bad_obstruction
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteGovernanceCuttingPackage model source horizon)
    (witness : FiniteDescentObstructionWitness model source horizon)
    (hBad : package.target.bad witness) :
    package.cutsBad package.selectedIntervention witness :=
  package.selected_cuts_all_bad witness hBad

/-- The selected governance intervention preserves selected desired families. -/
theorem finite_governance_preserves_desired_family
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteGovernanceCuttingPackage model source horizon)
    (family : FiniteLocalClockedConeFamily cover model source horizon)
    (hDesired : package.target.desiredPreserved family) :
    package.preservesDesired package.selectedIntervention family :=
  package.selected_preserves_desired family hDesired

/-- Finite obstruction-to-governance package. -/
structure FiniteObstructionGovernancePackage
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat) where
  obstructionPackage :
    FiniteDescentObstructionPackage model source horizon
  governancePackage :
    FiniteGovernanceCuttingPackage model source horizon
  obstructionToGovernanceBoundary : Prop
  nonConclusions : Prop

/--
Selected finite descent failure, once classified as bad, is cut by the selected
governance package.
-/
theorem governance_cuts_obstruction_of_finite_failure
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteObstructionGovernancePackage model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hBadClassified :
      ∀ witness,
        package.obstructionPackage.classifier.classify failure =
          some witness ->
        package.governancePackage.target.bad witness) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      package.obstructionPackage.classifier.classify failure = some witness ∧
        package.governancePackage.cutsBad
          package.governancePackage.selectedIntervention witness := by
  rcases finite_descent_obstruction_of_failure
      package.obstructionPackage failure with
    ⟨witness, hWitness⟩
  exact
    ⟨witness, hWitness,
      finite_governance_cuts_bad_obstruction
        package.governancePackage witness
        (hBadClassified witness hWitness)⟩

/--
Finite exact governance-cutting soundness package.

The package is relative to a selected finite exact model and a supplied
obstruction/governance package.  It records soundness boundaries for cutting
selected bad witnesses and preserving selected desired local families without
claiming operational effectiveness.
-/
structure FiniteExactGovernanceCuttingSoundness
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    (exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance)
    (source : Global) (horizon : Nat) where
  obstructionGovernance :
    FiniteObstructionGovernancePackage exactModel.descentModel source horizon
  recordsExactCoverBoundary : exactModel.RecordsExactCoverBoundary
  recordsFiniteModelBoundary : exactModel.RecordsFiniteModelBoundary
  badExclusionBoundary : Prop
  desiredPreservationBoundary : Prop
  operationalBoundary : Prop
  nonConclusions : Prop

namespace FiniteExactGovernanceCuttingSoundness

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {OperationG : Type x} {OperationL : Type y}
variable {Governance : Type z}
variable {exactModel :
  FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
variable {source : Global} {horizon : Nat}

/-- The selected governance package used by the soundness bridge. -/
def governancePackage
    (soundness :
      FiniteExactGovernanceCuttingSoundness exactModel source horizon) :
    FiniteGovernanceCuttingPackage exactModel.descentModel source horizon :=
  soundness.obstructionGovernance.governancePackage

/-- The soundness package records bad-exclusion and desired-preservation boundaries. -/
def RecordsSoundnessBoundary
    (soundness :
      FiniteExactGovernanceCuttingSoundness exactModel source horizon) :
    Prop :=
  soundness.badExclusionBoundary ∧
    soundness.desiredPreservationBoundary ∧ soundness.operationalBoundary

/-- Non-conclusions remain explicit for governance soundness. -/
def RecordsNonConclusions
    (soundness :
      FiniteExactGovernanceCuttingSoundness exactModel source horizon) :
    Prop :=
  soundness.nonConclusions ∧ exactModel.RecordsNonConclusions ∧
    soundness.obstructionGovernance.nonConclusions ∧
    soundness.governancePackage.nonConclusions

/-- Exact-cover boundary assumptions remain explicit. -/
theorem records_exactCoverBoundary
    (soundness :
      FiniteExactGovernanceCuttingSoundness exactModel source horizon) :
    exactModel.RecordsExactCoverBoundary :=
  soundness.recordsExactCoverBoundary

/-- Finite-model boundary assumptions remain explicit. -/
theorem records_finiteModelBoundary
    (soundness :
      FiniteExactGovernanceCuttingSoundness exactModel source horizon) :
    exactModel.RecordsFiniteModelBoundary :=
  soundness.recordsFiniteModelBoundary

end FiniteExactGovernanceCuttingSoundness

/--
In a selected finite exact model, a selected bad classified failure is cut by
the selected governance intervention.
-/
theorem finiteExact_governance_cuts_bad_failure
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (soundness :
      FiniteExactGovernanceCuttingSoundness exactModel source horizon)
    (failure :
      FiniteDescentFailure exactModel.descentModel source horizon)
    (hBadClassified :
      ∀ witness,
        soundness.obstructionGovernance.obstructionPackage.classifier.classify
            failure = some witness ->
        soundness.governancePackage.target.bad witness) :
    ∃ witness :
      FiniteDescentObstructionWitness exactModel.descentModel source horizon,
      soundness.obstructionGovernance.obstructionPackage.classifier.classify
          failure = some witness ∧
        soundness.governancePackage.cutsBad
          soundness.governancePackage.selectedIntervention witness :=
  governance_cuts_obstruction_of_finite_failure
    soundness.obstructionGovernance failure hBadClassified

/--
In a selected finite exact model, the selected governance intervention preserves
selected desired local cone families.
-/
theorem finiteExact_governance_preserves_desired_family
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (soundness :
      FiniteExactGovernanceCuttingSoundness exactModel source horizon)
    (family :
      FiniteLocalClockedConeFamily
        exactModel.cover exactModel.descentModel source horizon)
    (hDesired : soundness.governancePackage.target.desiredPreserved family) :
    soundness.governancePackage.preservesDesired
      soundness.governancePackage.selectedIntervention family :=
  finite_governance_preserves_desired_family
    soundness.governancePackage family hDesired

/--
Combined soundness accessor: selected bad obstruction cutting and selected
desired-family preservation hold under the finite exact governance package.
-/
theorem finiteExact_governance_cutting_sound
    {Global : Type u} {Index : Type v} {Local : Type w}
    {OperationG : Type x} {OperationL : Type y}
    {Governance : Type z}
    {exactModel :
      FiniteExactSFTModel Global Index Local OperationG OperationL Governance}
    {source : Global} {horizon : Nat}
    (soundness :
      FiniteExactGovernanceCuttingSoundness exactModel source horizon)
    (failure :
      FiniteDescentFailure exactModel.descentModel source horizon)
    (family :
      FiniteLocalClockedConeFamily
        exactModel.cover exactModel.descentModel source horizon)
    (hBadClassified :
      ∀ witness,
        soundness.obstructionGovernance.obstructionPackage.classifier.classify
            failure = some witness ->
        soundness.governancePackage.target.bad witness)
    (hDesired : soundness.governancePackage.target.desiredPreserved family) :
    (∃ witness :
      FiniteDescentObstructionWitness exactModel.descentModel source horizon,
      soundness.obstructionGovernance.obstructionPackage.classifier.classify
          failure = some witness ∧
        soundness.governancePackage.cutsBad
          soundness.governancePackage.selectedIntervention witness) ∧
      soundness.governancePackage.preservesDesired
        soundness.governancePackage.selectedIntervention family :=
  ⟨finiteExact_governance_cuts_bad_failure
      soundness failure hBadClassified,
    finiteExact_governance_preserves_desired_family
      soundness family hDesired⟩

end Formal.Arch
