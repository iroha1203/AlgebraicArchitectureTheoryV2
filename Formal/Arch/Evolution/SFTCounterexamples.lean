import Formal.Arch.Evolution.SignatureDynamics
import Formal.Arch.Evolution.AttractorEngineering

namespace Formal.Arch

/--
SFT-facing names for counterexample families that support the published
non-conclusion boundaries.
-/
inductive SFTCounterexampleKind where
  | endpointSafeZeroDeltaNotPathSafe
  | acceptedPreservationNotSupportPreservation
  | sameObservedSignatureDifferentFutureSupport
  | sameObservedSignatureDifferentFutureTrajectory
  | coarseSafeNotRefinedHiddenAxisSafe
  deriving DecidableEq, Repr

namespace SFTCounterexamples

/--
SFT-native registry for the existing finite counterexamples.

The fields are theorem proofs, not new model assumptions. This registry is an
entrypoint for SFT documents and future theorem packages; it does not turn the
counterexamples into empirical degradation, incident risk, or global forecast
claims.
-/
structure Package where
  endpointSafeZeroDeltaNotPathSafe :
    EndpointSignatureDelta
        ZeroNetForceNonZeroExcursion.observation
        ZeroNetForceNonZeroExcursion.signedNatDelta
        ZeroNetForceNonZeroExcursion.excursionPlan = 0 ∧
      StateInSafeRegion ZeroNetForceNonZeroExcursion.observation
        ZeroNetForceNonZeroExcursion.safeRegion 0 ∧
      StateInSafeRegion ZeroNetForceNonZeroExcursion.observation
        ZeroNetForceNonZeroExcursion.safeRegion 0 ∧
      ¬ SignatureTrajectoryInSafeRegion
          ZeroNetForceNonZeroExcursion.safeRegion
          (SignatureTrajectory ZeroNetForceNonZeroExcursion.observation
            ZeroNetForceNonZeroExcursion.excursionPlan)
  acceptedPreservationNotSupportPreservation :
    (∃ (t : ArchitectureTransition
        AcceptedPreservationNotSupportPreservation.ExampleState
        AcceptedPreservationNotSupportPreservation.safeState
        AcceptedPreservationNotSupportPreservation.safeState),
      AcceptedPreservationNotSupportPreservation.control.AcceptedStep t ∧
        StepPreservesSafeRegion
          AcceptedPreservationNotSupportPreservation.control.observation
          AcceptedPreservationNotSupportPreservation.control.invariant t) ∧
    (∀ {X Y : AcceptedPreservationNotSupportPreservation.ExampleState}
      (t : ArchitectureTransition
        AcceptedPreservationNotSupportPreservation.ExampleState X Y),
      AcceptedPreservationNotSupportPreservation.control.AcceptedStep t ->
        StepPreservesSafeRegion
          AcceptedPreservationNotSupportPreservation.control.observation
          AcceptedPreservationNotSupportPreservation.control.invariant t) ∧
    (∃ X op,
      AcceptedPreservationNotSupportPreservation.kernel.Supports X op ∧
        ¬ OperationTransitionSemantics.OperationPreservesSafeRegion
            AcceptedPreservationNotSupportPreservation.semantics
            AcceptedPreservationNotSupportPreservation.control.observation
            AcceptedPreservationNotSupportPreservation.control.invariant op) ∧
    DampingControlSchema.RecordsNonConclusions
      AcceptedPreservationNotSupportPreservation.control ∧
    FiniteOperationKernel.RecordsNonConclusions
      AcceptedPreservationNotSupportPreservation.kernel ∧
    OperationTransitionSemantics.RecordsNonConclusions
      AcceptedPreservationNotSupportPreservation.semantics
  sameObservedSignatureDifferentFutureSupport :
    SameObservedSignatureDifferentFutureSupport
      SameSignatureDifferentFuture.observation
      SameSignatureDifferentFuture.kernel
      SameSignatureDifferentFuture.source
      SameSignatureDifferentFuture.target
  sameObservedSignatureDifferentFutureTrajectory :
    SameObservedSignatureDifferentFutureTrajectory
      SameSignatureDifferentFuture.observation
      SameSignatureDifferentFuture.kernel
      SameSignatureDifferentFuture.semantics
      SameSignatureDifferentFuture.leftScript
      SameSignatureDifferentFuture.rightScript
      SameSignatureDifferentFuture.leftPlan
      SameSignatureDifferentFuture.rightPlan
  coarseSafeButRefinedHiddenAxisNonzero :
    StateInSafeRegion ObservabilityExpansionShock.coarseObservation
        ObservabilityExpansionShock.coarseSafe
        ObservabilityExpansionShock.witness ∧
      ObservabilityExpansionShock.HiddenAxisMeasuredNonzero
        ObservabilityExpansionShock.witness
  coarseSafeButNotRefinedSafe :
    StateInSafeRegion ObservabilityExpansionShock.coarseObservation
        ObservabilityExpansionShock.coarseSafe
        ObservabilityExpansionShock.witness ∧
      ¬ StateInSafeRegion ObservabilityExpansionShock.refinedObservation
          ObservabilityExpansionShock.refinedSafe
          ObservabilityExpansionShock.witness
  nonConclusionKinds : List SFTCounterexampleKind
  nonConclusions : Prop
  recordsNonConclusions : nonConclusions

/-- The canonical SFT counterexample registry backed by existing finite proofs. -/
def canonicalPackage : Package where
  endpointSafeZeroDeltaNotPathSafe :=
    ZeroNetForceNonZeroExcursion.endpointSafe_and_zeroDelta_but_not_pathSafe
  acceptedPreservationNotSupportPreservation :=
    AcceptedPreservationNotSupportPreservation.acceptedPreservation_not_supportPreservation_counterexample
  sameObservedSignatureDifferentFutureSupport :=
    SameSignatureDifferentFuture.sameObservedSignature_differentFutureSupport
  sameObservedSignatureDifferentFutureTrajectory :=
    SameSignatureDifferentFuture.sameObservedSignature_differentFutureTrajectory
  coarseSafeButRefinedHiddenAxisNonzero :=
    ObservabilityExpansionShock.coarseSafe_but_refinedHiddenAxis_nonzero
  coarseSafeButNotRefinedSafe :=
    ObservabilityExpansionShock.coarseSafe_but_not_refinedSafe
  nonConclusionKinds :=
    [SFTCounterexampleKind.endpointSafeZeroDeltaNotPathSafe,
     SFTCounterexampleKind.acceptedPreservationNotSupportPreservation,
     SFTCounterexampleKind.sameObservedSignatureDifferentFutureSupport,
     SFTCounterexampleKind.sameObservedSignatureDifferentFutureTrajectory,
     SFTCounterexampleKind.coarseSafeNotRefinedHiddenAxisSafe]
  nonConclusions := True
  recordsNonConclusions := trivial

/-- Endpoint safety plus zero endpoint delta does not imply path safety. -/
theorem endpoint_safe_zero_delta_not_path_safe (package : Package) :
    EndpointSignatureDelta
        ZeroNetForceNonZeroExcursion.observation
        ZeroNetForceNonZeroExcursion.signedNatDelta
        ZeroNetForceNonZeroExcursion.excursionPlan = 0 ∧
      StateInSafeRegion ZeroNetForceNonZeroExcursion.observation
        ZeroNetForceNonZeroExcursion.safeRegion 0 ∧
      StateInSafeRegion ZeroNetForceNonZeroExcursion.observation
        ZeroNetForceNonZeroExcursion.safeRegion 0 ∧
      ¬ SignatureTrajectoryInSafeRegion
          ZeroNetForceNonZeroExcursion.safeRegion
          (SignatureTrajectory ZeroNetForceNonZeroExcursion.observation
            ZeroNetForceNonZeroExcursion.excursionPlan) :=
  package.endpointSafeZeroDeltaNotPathSafe

/-- Accepted-step invariant preservation does not imply support preservation. -/
theorem accepted_preservation_not_support_preservation (package : Package) :
    (∃ (t : ArchitectureTransition
        AcceptedPreservationNotSupportPreservation.ExampleState
        AcceptedPreservationNotSupportPreservation.safeState
        AcceptedPreservationNotSupportPreservation.safeState),
      AcceptedPreservationNotSupportPreservation.control.AcceptedStep t ∧
        StepPreservesSafeRegion
          AcceptedPreservationNotSupportPreservation.control.observation
          AcceptedPreservationNotSupportPreservation.control.invariant t) ∧
    (∀ {X Y : AcceptedPreservationNotSupportPreservation.ExampleState}
      (t : ArchitectureTransition
        AcceptedPreservationNotSupportPreservation.ExampleState X Y),
      AcceptedPreservationNotSupportPreservation.control.AcceptedStep t ->
        StepPreservesSafeRegion
          AcceptedPreservationNotSupportPreservation.control.observation
          AcceptedPreservationNotSupportPreservation.control.invariant t) ∧
    (∃ X op,
      AcceptedPreservationNotSupportPreservation.kernel.Supports X op ∧
        ¬ OperationTransitionSemantics.OperationPreservesSafeRegion
            AcceptedPreservationNotSupportPreservation.semantics
            AcceptedPreservationNotSupportPreservation.control.observation
            AcceptedPreservationNotSupportPreservation.control.invariant op) ∧
    DampingControlSchema.RecordsNonConclusions
      AcceptedPreservationNotSupportPreservation.control ∧
    FiniteOperationKernel.RecordsNonConclusions
      AcceptedPreservationNotSupportPreservation.kernel ∧
    OperationTransitionSemantics.RecordsNonConclusions
      AcceptedPreservationNotSupportPreservation.semantics :=
  package.acceptedPreservationNotSupportPreservation

/-- Same current observation does not imply same future operation support. -/
theorem same_observed_signature_different_future_support
    (package : Package) :
    SameObservedSignatureDifferentFutureSupport
      SameSignatureDifferentFuture.observation
      SameSignatureDifferentFuture.kernel
      SameSignatureDifferentFuture.source
      SameSignatureDifferentFuture.target :=
  package.sameObservedSignatureDifferentFutureSupport

/-- Same current observation does not imply same future signature trajectory. -/
theorem same_observed_signature_different_future_trajectory
    (package : Package) :
    SameObservedSignatureDifferentFutureTrajectory
      SameSignatureDifferentFuture.observation
      SameSignatureDifferentFuture.kernel
      SameSignatureDifferentFuture.semantics
      SameSignatureDifferentFuture.leftScript
      SameSignatureDifferentFuture.rightScript
      SameSignatureDifferentFuture.leftPlan
      SameSignatureDifferentFuture.rightPlan :=
  package.sameObservedSignatureDifferentFutureTrajectory

/-- Coarse safety does not imply refined hidden-axis safety. -/
theorem coarse_safe_not_refined_hidden_axis_safe (package : Package) :
    StateInSafeRegion ObservabilityExpansionShock.coarseObservation
        ObservabilityExpansionShock.coarseSafe
        ObservabilityExpansionShock.witness ∧
      ¬ StateInSafeRegion ObservabilityExpansionShock.refinedObservation
          ObservabilityExpansionShock.refinedSafe
          ObservabilityExpansionShock.witness :=
  package.coarseSafeButNotRefinedSafe

/-- The package exposes the selected SFT non-conclusion list. -/
def nonConclusionList (package : Package) : List SFTCounterexampleKind :=
  package.nonConclusionKinds

/-- The package records SFT counterexample non-conclusions explicitly. -/
theorem records_nonConclusions (package : Package) :
    package.nonConclusions :=
  package.recordsNonConclusions

end SFTCounterexamples

end Formal.Arch
