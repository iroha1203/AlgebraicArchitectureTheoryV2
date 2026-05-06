import Formal.Arch.Evolution.SignatureDynamics

namespace Formal.Arch

universe u v w

/--
The complement of a selected bad region, read as a selected safe region.

This is only a predicate-level wrapper: it does not assert that a review,
tooling, or empirical process can identify or avoid every bad state.
-/
abbrev AvoidsBadRegion {Sig : Type v} (Bad : Sig -> Prop) : SafeRegion Sig :=
  fun sig => ¬ Bad sig

/--
A minimal Attractor Engineering support package.

The package does not introduce a global architecture field. It bundles the
selected observation, finite operation support, bounded transition semantics,
target region, and explicit support-preservation assumption needed to reuse the
existing `SignatureDynamics` safe-trajectory theorem.
-/
structure AttractorEngineeringSupportPackage
    (State : Type u) (Sig : Type v) (OperationId : Type w) where
  observation : SignatureObservation State Sig
  kernel : FiniteOperationKernel State OperationId
  semantics : OperationTransitionSemantics State OperationId
  targetRegion : SafeRegion Sig
  supportPreserves :
    kernel.SupportOperationsPreserveSafeRegion semantics observation targetRegion
  coverageAssumptions : Prop
  measurementBoundary : Prop
  nonConclusions : Prop

namespace AttractorEngineeringSupportPackage

variable {State : Type u} {Sig : Type v} {OperationId : Type w}

/-- The package explicitly records its selected coverage assumptions. -/
def RecordsCoverageAssumptions
    (package : AttractorEngineeringSupportPackage State Sig OperationId) :
    Prop :=
  package.coverageAssumptions

/--
The package explicitly records the measurement boundary: unmeasured axes,
tooling coverage, calibration, and empirical completeness remain outside the
Lean theorem claim.
-/
def RecordsMeasurementBoundary
    (package : AttractorEngineeringSupportPackage State Sig OperationId) :
    Prop :=
  package.measurementBoundary

/-- The package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (package : AttractorEngineeringSupportPackage State Sig OperationId) :
    Prop :=
  package.nonConclusions

/-- The selected target trajectory read by the package observation. -/
def TargetTrajectory
    (package : AttractorEngineeringSupportPackage State Sig OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y) :
    List Sig :=
  SignatureTrajectory package.observation plan

/--
The support-preservation premise stored in the package, exposed as an accessor
theorem for downstream wrappers.
-/
theorem supportPreserves_targetRegion
    (package : AttractorEngineeringSupportPackage State Sig OperationId) :
    package.kernel.SupportOperationsPreserveSafeRegion
      package.semantics package.observation package.targetRegion :=
  package.supportPreserves

/--
If a bounded script is realized by the selected operation semantics, uses only
finite-support operations, and starts inside the target region, then its target
trajectory stays inside that region.

This is the Attractor Engineering reading of
`FiniteOperationKernel.boundedSampledScript_preserves_safeRegion`.
-/
theorem supportPackage_preserves_targetTrajectory
    (package : AttractorEngineeringSupportPackage State Sig OperationId)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart :
      StateInSafeRegion package.observation package.targetRegion X)
    (hRealizes : script.RealizesEvolution package.semantics plan)
    (hSupport :
      package.kernel.ScriptUsesSupport script.operations plan) :
    SignatureTrajectoryInSafeRegion package.targetRegion
      (package.TargetTrajectory plan) :=
  FiniteOperationKernel.boundedSampledScript_preserves_safeRegion
    package.kernel package.semantics package.observation package.targetRegion
    script plan hStart hRealizes hSupport package.supportPreserves

/--
Specialize a support package whose target region is the complement of a bad
region. The conclusion is still a bounded trajectory theorem, not a claim about
global bad-region discovery or empirical guardrail capacity.
-/
theorem supportPackage_avoids_badRegion
    (package : AttractorEngineeringSupportPackage State Sig OperationId)
    (Bad : Sig -> Prop)
    (hTarget : package.targetRegion = AvoidsBadRegion Bad)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart :
      StateInSafeRegion package.observation (AvoidsBadRegion Bad) X)
    (hRealizes : script.RealizesEvolution package.semantics plan)
    (hSupport :
      package.kernel.ScriptUsesSupport script.operations plan) :
    SignatureTrajectoryInSafeRegion (AvoidsBadRegion Bad)
      (package.TargetTrajectory plan) := by
  rw [← hTarget] at hStart ⊢
  exact
    package.supportPackage_preserves_targetTrajectory
      script plan hStart hRealizes hSupport

/--
A direct wrapper for support shaping against a selected bad region, using the
bad-region complement as the safe region.
-/
theorem supportShaping_avoids_badRegion
    (O : SignatureObservation State Sig)
    (kernel : FiniteOperationKernel State OperationId)
    (sem : OperationTransitionSemantics State OperationId)
    (Bad : Sig -> Prop)
    (script : BoundedOperationScript OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y)
    (hStart : StateInSafeRegion O (AvoidsBadRegion Bad) X)
    (hRealizes : script.RealizesEvolution sem plan)
    (hSupport : kernel.ScriptUsesSupport script.operations plan)
    (hPreserves :
      kernel.SupportOperationsPreserveSafeRegion sem O (AvoidsBadRegion Bad)) :
    SignatureTrajectoryInSafeRegion (AvoidsBadRegion Bad)
      (SignatureTrajectory O plan) :=
  FiniteOperationKernel.boundedSampledScript_preserves_safeRegion
    kernel sem O (AvoidsBadRegion Bad) script plan
    hStart hRealizes hSupport hPreserves

end AttractorEngineeringSupportPackage

end Formal.Arch
