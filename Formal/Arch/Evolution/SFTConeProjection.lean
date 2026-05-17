import Formal.Arch.Evolution.SFTForecastCone

namespace Formal.Arch

universe u v

/--
Pointwise inclusion between two selected SFT operation supports.

This is only set-valued support inclusion at each selected field state. It does
not compare probabilities, costs, calibration, or extractor completeness.
-/
def PointwiseSupportInclusion
    {Field : Type u} {Operation : Type v}
    (support₂ support₁ : OperationSupport Field Operation) : Prop :=
  ∀ source operation,
    support₂.Supports source operation ->
      support₁.Supports source operation

/--
Step simulation between two selected SFT step relations, relative to the
narrower support.

Every supported primitive transition in the narrower model is realized by the
wider model with the same source, operation witness, and target. This is not a
global risk-reduction, probability, or calibration theorem.
-/
def StepSimulation
    {Field : Type u} {Operation : Type v}
    (support₂ : OperationSupport Field Operation)
    (relation₂ relation₁ : StepRelation Field Operation) : Prop :=
  ∀ source operation target,
    support₂.Supports source operation ->
      relation₂.Realizes source operation target ->
        relation₁.Realizes source operation target

/--
The same step relation simulates itself for any selected narrower support.

This helper isolates the common support-monotonicity case from the more
general support-inclusion plus step-simulation projection theorem.
-/
def SameRelationStepSimulation
    {Field : Type u} {Operation : Type v}
    (support₂ : OperationSupport Field Operation)
    (relation : StepRelation Field Operation) :
    StepSimulation support₂ relation relation :=
  fun _source _operation _target _hSupported hRealizes => hRealizes

namespace ForecastConeProjection

variable {Field : Type u} {Operation : Type v}
variable {support₁ support₂ : OperationSupport Field Operation}
variable {relation₁ relation₂ : StepRelation Field Operation}

/-- Project one supported field step along support inclusion and step simulation. -/
def projectSupportedFieldStep
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁)
    {source target : Field}
    (step : SupportedFieldStep support₂ relation₂ source target) :
    SupportedFieldStep support₁ relation₁ source target where
  operation := step.operation
  supported := hSupport source step.operation step.supported
  realizes := hStep source step.operation target step.supported step.realizes

/-- Project a support-witnessed field path into the wider support/step model. -/
def projectFieldPath
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁) :
    {source target : Field} ->
      FieldPath support₂ relation₂ source target ->
        FieldPath support₁ relation₁ source target
  | _, _, ArchitecturePath.nil source => ArchitecturePath.nil source
  | _, _, ArchitecturePath.cons step rest =>
      ArchitecturePath.cons
        (projectSupportedFieldStep hSupport hStep step)
        (projectFieldPath hSupport hStep rest)

/-- A path in the wider model is the structural projection of a narrower path. -/
def ProjectedFieldPath
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁)
    {source target : Field}
    (path₂ : FieldPath support₂ relation₂ source target)
    (path₁ : FieldPath support₁ relation₁ source target) : Prop :=
  path₁ = projectFieldPath hSupport hStep path₂

/-- Projecting a zero-length path keeps the zero-length path. -/
@[simp] theorem projectFieldPath_nil
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁)
    (source : Field) :
    projectFieldPath hSupport hStep (ArchitecturePath.nil source) =
      ArchitecturePath.nil source :=
  rfl

/-- Projecting a successor path projects its head step and tail path. -/
@[simp] theorem projectFieldPath_cons
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁)
    {source mid target : Field}
    (step : SupportedFieldStep support₂ relation₂ source mid)
    (rest : FieldPath support₂ relation₂ mid target) :
    projectFieldPath hSupport hStep (ArchitecturePath.cons step rest) =
      ArchitecturePath.cons
        (projectSupportedFieldStep hSupport hStep step)
        (projectFieldPath hSupport hStep rest) :=
  rfl

/-- Path projection preserves finite path length. -/
@[simp] theorem projectFieldPath_length
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁) :
    {source target : Field} ->
      (path : FieldPath support₂ relation₂ source target) ->
        ArchitecturePath.length (projectFieldPath hSupport hStep path) =
          ArchitecturePath.length path
  | _, _, ArchitecturePath.nil _ => rfl
  | _, _, ArchitecturePath.cons _ rest => by
      simp [projectFieldPath, ArchitecturePath.length,
        projectFieldPath_length hSupport hStep rest]

/--
Zero-horizon cone projection is the projected zero-length path at the source.
-/
theorem forecastCone_project_zero
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁)
    (source : Field) :
    ForecastCone support₁ relation₁ source 0 source
      (projectFieldPath hSupport hStep (ArchitecturePath.nil source)) := by
  simpa using
    (ForecastCone.nil_mem (support := support₁) (relation := relation₁) source)

/--
Successor-step projection preserves the projected-path relation after adding a
shared projected head step.
-/
theorem projectedFieldPath_cons
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁)
    {source mid target : Field}
    (step : SupportedFieldStep support₂ relation₂ source mid)
    {path₂ : FieldPath support₂ relation₂ mid target}
    {path₁ : FieldPath support₁ relation₁ mid target}
    (hProjected : ProjectedFieldPath hSupport hStep path₂ path₁) :
    ProjectedFieldPath hSupport hStep
      (ArchitecturePath.cons step path₂)
      (ArchitecturePath.cons
        (projectSupportedFieldStep hSupport hStep step) path₁) := by
  simp [ProjectedFieldPath] at hProjected ⊢
  exact hProjected

/--
Under pointwise support inclusion and step simulation, every path in the
narrower `ForecastCone` projects to a path in the wider `ForecastCone` with the
same horizon bound.
-/
theorem forecastCone_projects_of_supportInclusion_and_stepSimulation
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁)
    {source target : Field} {horizon : Nat}
    {path₂ : FieldPath support₂ relation₂ source target}
    (hCone : ForecastCone support₂ relation₂ source horizon target path₂) :
    ForecastCone support₁ relation₁ source horizon target
      (projectFieldPath hSupport hStep path₂) := by
  simpa [ForecastCone, ReachableFieldPath] using hCone

/--
Cone projection with the projected path witness exposed for downstream theorem
packages.
-/
theorem exists_projected_forecastCone
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    (hStep : StepSimulation support₂ relation₂ relation₁)
    {source target : Field} {horizon : Nat}
    {path₂ : FieldPath support₂ relation₂ source target}
    (hCone : ForecastCone support₂ relation₂ source horizon target path₂) :
    ∃ path₁ : FieldPath support₁ relation₁ source target,
      ProjectedFieldPath hSupport hStep path₂ path₁ ∧
        ForecastCone support₁ relation₁ source horizon target path₁ := by
  refine ⟨projectFieldPath hSupport hStep path₂, ?_, ?_⟩
  · rfl
  · exact forecastCone_projects_of_supportInclusion_and_stepSimulation
      hSupport hStep hCone

/--
Support inclusion alone is enough when both cones use the same selected step
relation: every narrower-support cone path has a structural witness in the
wider-support cone at the same horizon.
-/
theorem forecastCone_projects_of_supportInclusion
    {relation : StepRelation Field Operation}
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    {source target : Field} {horizon : Nat}
    {path₂ : FieldPath support₂ relation source target}
    (hCone : ForecastCone support₂ relation source horizon target path₂) :
    ForecastCone support₁ relation source horizon target
      (projectFieldPath hSupport
        (SameRelationStepSimulation support₂ relation) path₂) :=
  forecastCone_projects_of_supportInclusion_and_stepSimulation
    hSupport (SameRelationStepSimulation support₂ relation) hCone

/--
Existential wrapper for support monotonicity with a shared step relation.

The returned path is a projected witness, so the theorem does not claim that the
original dependent path object can be reused across different support packages.
-/
theorem exists_projected_forecastCone_of_supportInclusion
    {relation : StepRelation Field Operation}
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    {source target : Field} {horizon : Nat}
    {path₂ : FieldPath support₂ relation source target}
    (hCone : ForecastCone support₂ relation source horizon target path₂) :
    ∃ path₁ : FieldPath support₁ relation source target,
      ProjectedFieldPath hSupport
        (SameRelationStepSimulation support₂ relation) path₂ path₁ ∧
        ForecastCone support₁ relation source horizon target path₁ :=
  exists_projected_forecastCone
    hSupport (SameRelationStepSimulation support₂ relation) hCone

/--
Combining support inclusion with horizon extension preserves cone membership
after projecting the dependent path witness.
-/
theorem forecastCone_projects_of_supportInclusion_and_horizon_le
    {relation : StepRelation Field Operation}
    (hSupport : PointwiseSupportInclusion support₂ support₁)
    {source target : Field} {horizon₁ horizon₂ : Nat}
    {path₂ : FieldPath support₂ relation source target}
    (hCone : ForecastCone support₂ relation source horizon₁ target path₂)
    (hHorizon : horizon₁ <= horizon₂) :
    ForecastCone support₁ relation source horizon₂ target
      (projectFieldPath hSupport
        (SameRelationStepSimulation support₂ relation) path₂) :=
  ForecastCone.monotone_horizon
    (forecastCone_projects_of_supportInclusion hSupport hCone) hHorizon

end ForecastConeProjection

end Formal.Arch
