import Formal.Arch.Evolution.ArchitecturePath

namespace Formal.Arch

universe u v

/--
Selected SFT operation support over a field state space.

The support is a set-valued family. Coverage, finite-sampling, proposal
completeness, probability weights, and empirical extraction remain explicit
boundary propositions rather than consequences of membership in the support.
-/
structure OperationSupport (Field : Type u) (Operation : Type v) where
  supports : Field -> Operation -> Prop
  coverageAssumptions : Prop
  supportBoundary : Prop
  nonConclusions : Prop

namespace OperationSupport

variable {Field : Type u} {Operation : Type v}

/-- The selected operation is in the support at the selected field state. -/
def Supports
    (support : OperationSupport Field Operation)
    (F : Field) (op : Operation) : Prop :=
  support.supports F op

/-- The support package explicitly records its selected coverage assumptions. -/
def RecordsCoverageAssumptions
    (support : OperationSupport Field Operation) : Prop :=
  support.coverageAssumptions

/--
The support package records the boundary for finite sampling, proposal
completeness, weights, and extractor coverage.
-/
def RecordsSupportBoundary
    (support : OperationSupport Field Operation) : Prop :=
  support.supportBoundary

/-- The support package explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (support : OperationSupport Field Operation) : Prop :=
  support.nonConclusions

end OperationSupport

/--
Selected SFT step relation for field evolution.

This relation only says that an operation can realize a transition from one
selected field state to another. It does not claim probability, causal
correctness, calibration, or implementation extractor completeness.
-/
structure StepRelation (Field : Type u) (Operation : Type v) where
  step : Field -> Operation -> Field -> Prop
  coverageAssumptions : Prop
  theoremBoundary : Prop
  nonConclusions : Prop

namespace StepRelation

variable {Field : Type u} {Operation : Type v}

/-- The selected operation realizes this field transition. -/
def Realizes
    (relation : StepRelation Field Operation)
    (source : Field) (op : Operation) (target : Field) : Prop :=
  relation.step source op target

/-- The step relation explicitly records its selected coverage assumptions. -/
def RecordsCoverageAssumptions
    (relation : StepRelation Field Operation) : Prop :=
  relation.coverageAssumptions

/-- The step relation records the theorem/modeling boundary it is relative to. -/
def RecordsTheoremBoundary
    (relation : StepRelation Field Operation) : Prop :=
  relation.theoremBoundary

/-- The step relation explicitly records its non-conclusion boundary. -/
def RecordsNonConclusions
    (relation : StepRelation Field Operation) : Prop :=
  relation.nonConclusions

end StepRelation

/--
One supported SFT field step.

The operation witness is stored in the step, so downstream theorems can inspect
both support membership and transition realization without reconstructing them
from an unannotated state list.
-/
structure SupportedFieldStep
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source target : Field) where
  operation : Operation
  supported : support.Supports source operation
  realizes : relation.Realizes source operation target

/-- A finite SFT field path whose primitive steps are support-witnessed. -/
abbrev FieldPath
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation) :=
  ArchitecturePath (SupportedFieldStep support relation)

/--
A supported field path is reachable from its indexed source within the selected
horizon.

The endpoint is already tracked by the dependent `FieldPath` type. The horizon
bound is a finite path-length bound, not a forecast calibration claim.
-/
def ReachableFieldPath
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source target : Field}
    (horizon : Nat) (path : FieldPath support relation source target) :
    Prop :=
  ArchitecturePath.length path <= horizon

/--
The selected ForecastCone membership predicate.

`ForecastCone support relation source horizon target path` means that `path` is
a finite supported field path from `source` to `target` within `horizon`. It is
not a point prediction, probability distribution, causal proof, or calibrated
empirical forecast.
-/
def ForecastCone
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat)
    (target : Field) (path : FieldPath support relation source target) :
    Prop :=
  ReachableFieldPath horizon path

namespace ForecastCone

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}

/-- ForecastCone membership exposes the finite horizon bound. -/
theorem length_le_horizon
    {source target : Field} {horizon : Nat}
    {path : FieldPath support relation source target}
    (hCone : ForecastCone support relation source horizon target path) :
    ArchitecturePath.length path <= horizon :=
  hCone

/-- The zero-length path belongs to the zero-horizon cone at its source. -/
theorem nil_mem
    (source : Field) :
    ForecastCone support relation source 0 source (ArchitecturePath.nil source) := by
  simp [ForecastCone, ReachableFieldPath, ArchitecturePath.length]

/-- Increasing the selected horizon preserves cone membership. -/
theorem monotone_horizon
    {source target : Field} {horizon₁ horizon₂ : Nat}
    {path : FieldPath support relation source target}
    (hCone : ForecastCone support relation source horizon₁ target path)
    (hLe : horizon₁ <= horizon₂) :
    ForecastCone support relation source horizon₂ target path :=
  Nat.le_trans hCone hLe

/-- The support package coverage assumptions remain an explicit accessor. -/
def RecordsSupportCoverageAssumptions :
    Prop :=
  support.RecordsCoverageAssumptions

/-- The step-relation coverage assumptions remain an explicit accessor. -/
def RecordsStepCoverageAssumptions :
    Prop :=
  relation.RecordsCoverageAssumptions

/-- The support/model boundary remains explicit for downstream cone theorems. -/
def RecordsSupportBoundary :
    Prop :=
  support.RecordsSupportBoundary

/-- The theorem boundary of the selected step relation remains explicit. -/
def RecordsStepTheoremBoundary :
    Prop :=
  relation.RecordsTheoremBoundary

/-- The selected horizon is only a finite path-length bound. -/
def RecordsHorizonBoundary (horizon : Nat) : Prop :=
  ∀ {source target : Field} (path : FieldPath support relation source target),
    ForecastCone support relation source horizon target path ->
      ArchitecturePath.length path <= horizon

/--
ForecastCone non-conclusions combine support and step-relation
non-conclusions. In particular, cone membership does not imply point
prediction, probability, calibration, causal proof, global safety, or extractor
completeness.
-/
def RecordsNonConclusions :
    Prop :=
  support.RecordsNonConclusions ∧ relation.RecordsNonConclusions

end ForecastCone

end Formal.Arch
