import Formal.Arch.Evolution.AttractorEngineering
import Formal.Arch.Evolution.SFTForecastCone

namespace Formal.Arch

universe u v w

/--
SFT-native support-safety package.

The package reuses the checked Attractor Engineering support package as its
safe-region core, while recording the SFT observation / accepted-step /
forecast / non-conclusion boundaries separately. In particular, accepted steps
do not imply support preservation; the stored support-preservation premise in
the underlying package remains the theorem-bearing assumption.
-/
structure SFTSupportSafetyPackage
    (State : Type u) (Sig : Type v) (OperationId : Type w) where
  supportPackage : AttractorEngineeringSupportPackage State Sig OperationId
  observationBoundary : Prop
  acceptedStepBoundary : Prop
  forecastBoundary : Prop
  nonConclusions : Prop

namespace SFTSupportSafetyPackage

variable {State : Type u} {Sig : Type v} {OperationId : Type w}

/-- The selected observation schema used by this SFT support-safety package. -/
def observation
    (package : SFTSupportSafetyPackage State Sig OperationId) :
    SignatureObservation State Sig :=
  package.supportPackage.observation

/-- The selected finite operation support used by this package. -/
def kernel
    (package : SFTSupportSafetyPackage State Sig OperationId) :
    FiniteOperationKernel State OperationId :=
  package.supportPackage.kernel

/-- The selected operation transition semantics used by this package. -/
def semantics
    (package : SFTSupportSafetyPackage State Sig OperationId) :
    OperationTransitionSemantics State OperationId :=
  package.supportPackage.semantics

/-- The selected safe region whose preservation is theorem-bearing. -/
def targetRegion
    (package : SFTSupportSafetyPackage State Sig OperationId) :
    SafeRegion Sig :=
  package.supportPackage.targetRegion

/-- The observed forecast trajectory read through the package observation. -/
def ForecastTrajectory
    (package : SFTSupportSafetyPackage State Sig OperationId)
    {X Y : State} (plan : ArchitectureEvolution State X Y) :
    List Sig :=
  package.supportPackage.TargetTrajectory plan

/-- The package records its observation boundary. -/
def RecordsObservationBoundary
    (package : SFTSupportSafetyPackage State Sig OperationId) : Prop :=
  package.observationBoundary

/--
The package records that accepted-step evidence is not being used as a
substitute for support preservation.
-/
def RecordsAcceptedStepBoundary
    (package : SFTSupportSafetyPackage State Sig OperationId) : Prop :=
  package.acceptedStepBoundary

/--
The package records the forecast boundary: support safety is a selected
trajectory theorem, not forecast correctness or calibration.
-/
def RecordsForecastBoundary
    (package : SFTSupportSafetyPackage State Sig OperationId) : Prop :=
  package.forecastBoundary

/-- The package records its SFT non-conclusion boundary. -/
def RecordsNonConclusions
    (package : SFTSupportSafetyPackage State Sig OperationId) : Prop :=
  package.nonConclusions ∧
    package.supportPackage.RecordsMeasurementBoundary ∧
    package.supportPackage.RecordsNonConclusions

/--
Read the finite kernel as an SFT set-valued operation support.

This is a bridge of vocabulary only. It carries finite-support boundaries and
does not add probabilities, proposal completeness, or extractor completeness.
-/
def operationSupport
    (package : SFTSupportSafetyPackage State Sig OperationId) :
    OperationSupport State OperationId where
  supports := package.kernel.Supports
  coverageAssumptions := package.kernel.coverageAssumptions
  supportBoundary :=
    package.kernel.RecordsWeightSourceBoundary ∧
      package.kernel.RecordsNormalizationBoundary
  nonConclusions := package.kernel.RecordsNonConclusions

/--
Read transition semantics as an SFT step relation by existentially retaining
the realized primitive architecture transition.
-/
def stepRelation
    (package : SFTSupportSafetyPackage State Sig OperationId) :
    StepRelation State OperationId where
  step := fun source op target =>
    ∃ t : ArchitectureTransition State source target,
      package.semantics.Realizes op t
  coverageAssumptions := package.semantics.coverageAssumptions
  theoremBoundary := package.RecordsForecastBoundary
  nonConclusions := package.semantics.RecordsNonConclusions

/-- One architecture transition realized by a supported operation as an SFT step. -/
def supportedArchitectureStep
    (package : SFTSupportSafetyPackage State Sig OperationId)
    (op : OperationId) {X Y : State}
    (step : ArchitectureTransition State X Y)
    (hSupport : package.kernel.Supports X op)
    (hRealizes : package.semantics.Realizes op step) :
    SupportedFieldStep package.operationSupport package.stepRelation X Y where
  operation := op
  supported := hSupport
  realizes := ⟨step, hRealizes⟩

/--
Convert a realized script that uses the selected finite support into an SFT
support-witnessed field path.
-/
def fieldPathOfSupportedScript
    (package : SFTSupportSafetyPackage State Sig OperationId) :
    (operations : List OperationId) ->
      {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
        BoundedOperationScript.ScriptRealizesEvolution
          package.semantics operations plan ->
        package.kernel.ScriptUsesSupport operations plan ->
          FieldPath package.operationSupport package.stepRelation X Y
  | [], _, _, ArchitecturePath.nil X, _hRealizes, _hSupport =>
      ArchitecturePath.nil X
  | [], _, _, ArchitecturePath.cons _step _rest, hRealizes, _hSupport =>
      False.elim hRealizes
  | _op :: _ops, _, _, ArchitecturePath.nil _, hRealizes, _hSupport =>
      False.elim hRealizes
  | op :: ops, _, _, ArchitecturePath.cons step rest, hRealizes, hSupport =>
      ArchitecturePath.cons
        (package.supportedArchitectureStep op step hSupport.1 hRealizes.1)
        (fieldPathOfSupportedScript package ops rest hRealizes.2 hSupport.2)

/-- Script-to-field-path conversion preserves the script operation count. -/
@[simp] theorem fieldPathOfSupportedScript_length
    (package : SFTSupportSafetyPackage State Sig OperationId) :
    (operations : List OperationId) ->
      {X Y : State} -> (plan : ArchitectureEvolution State X Y) ->
        (hRealizes :
          BoundedOperationScript.ScriptRealizesEvolution
            package.semantics operations plan) ->
        (hSupport : package.kernel.ScriptUsesSupport operations plan) ->
          ArchitecturePath.length
            (fieldPathOfSupportedScript package operations plan
              hRealizes hSupport) = operations.length
  | [], _, _, ArchitecturePath.nil _, _hRealizes, _hSupport => rfl
  | [], _, _, ArchitecturePath.cons _step _rest, hRealizes, _hSupport =>
      False.elim hRealizes
  | _op :: _ops, _, _, ArchitecturePath.nil _, hRealizes, _hSupport =>
      False.elim hRealizes
  | _op :: ops, _, _, ArchitecturePath.cons _step rest, hRealizes, hSupport => by
      simp [fieldPathOfSupportedScript, ArchitecturePath.length,
        fieldPathOfSupportedScript_length package ops rest hRealizes.2
          hSupport.2]

/--
An accepted supported trajectory records both accepted-step evidence and support
evidence. The support evidence is the one used by support-safety theorems.
-/
structure AcceptedSupportedTrajectory
    (package : SFTSupportSafetyPackage State Sig OperationId)
    (control : DampingControlSchema State Sig)
    (X Y : State) where
  script : BoundedOperationScript OperationId
  plan : ArchitectureEvolution State X Y
  startsInsideTarget : StateInSafeRegion package.observation package.targetRegion X
  realizes : script.RealizesEvolution package.semantics plan
  usesSupport : package.kernel.ScriptUsesSupport script.operations plan
  accepted : script.AcceptedEvolution control package.semantics plan

namespace AcceptedSupportedTrajectory

variable {package : SFTSupportSafetyPackage State Sig OperationId}
variable {control : DampingControlSchema State Sig}
variable {X Y : State}

/-- The SFT support-witnessed field path induced by the trajectory. -/
def fieldPath
    (trajectory : AcceptedSupportedTrajectory package control X Y) :
    FieldPath package.operationSupport package.stepRelation X Y :=
  fieldPathOfSupportedScript package trajectory.script.operations
    trajectory.plan trajectory.realizes trajectory.usesSupport

/-- The induced SFT field path has exactly the script operation length. -/
@[simp] theorem fieldPath_length
    (trajectory : AcceptedSupportedTrajectory package control X Y) :
    ArchitecturePath.length trajectory.fieldPath =
      trajectory.script.operations.length := by
  simp [fieldPath]

/--
The accepted supported trajectory is a member of the package ForecastCone at the
script-length horizon.
-/
theorem mem_forecastCone
    (trajectory : AcceptedSupportedTrajectory package control X Y) :
    ForecastCone package.operationSupport package.stepRelation X
      trajectory.script.operations.length Y trajectory.fieldPath := by
  simp [ForecastCone, ReachableFieldPath, fieldPath_length]

/--
SFT-native support safety theorem.

If the stored package premise says every supported operation preserves the
selected safe region, then the selected forecast trajectory stays inside that
region. The accepted-step evidence in `trajectory.accepted` is retained as
evidence, but it is not used to derive support preservation.
-/
theorem supportSafety_preserves_forecastTrajectory
    (trajectory : AcceptedSupportedTrajectory package control X Y) :
    SignatureTrajectoryInSafeRegion package.targetRegion
      (package.ForecastTrajectory trajectory.plan) :=
  package.supportPackage.supportPackage_preserves_targetTrajectory
    trajectory.script trajectory.plan trajectory.startsInsideTarget
    trajectory.realizes trajectory.usesSupport

/--
The SFT support-safety theorem also exposes the induced ForecastCone witness
and the bounded safe observed trajectory together.
-/
theorem forecastCone_and_supportSafety
    (trajectory : AcceptedSupportedTrajectory package control X Y) :
    ForecastCone package.operationSupport package.stepRelation X
      trajectory.script.operations.length Y trajectory.fieldPath ∧
    SignatureTrajectoryInSafeRegion package.targetRegion
      (package.ForecastTrajectory trajectory.plan) :=
  ⟨trajectory.mem_forecastCone,
    trajectory.supportSafety_preserves_forecastTrajectory⟩

/--
Accepted evidence is available as an accessor, but it remains distinct from the
support-preservation premise used by `supportSafety_preserves_forecastTrajectory`.
-/
theorem acceptedEvidence
    (trajectory : AcceptedSupportedTrajectory package control X Y) :
    trajectory.script.AcceptedEvolution control package.semantics
      trajectory.plan :=
  trajectory.accepted

end AcceptedSupportedTrajectory

end SFTSupportSafetyPackage

end Formal.Arch
