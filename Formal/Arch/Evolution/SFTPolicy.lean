import Formal.Arch.Evolution.SFTConeProjection

namespace Formal.Arch

universe u v

/--
Selected SFT operation policy over an explicit operation support.

The policy can expose selection, preorder-like preference, and cost-order
vocabulary without choosing probability weights or claiming that policy
compliance implies architectural lawfulness or future safety.
-/
structure OperationPolicy
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation) where
  selected : Field -> Operation -> Prop
  noHarderThan : Field -> Operation -> Operation -> Prop
  costBoundary : Prop
  selectionBoundary : Prop
  policyBoundary : Prop
  nonConclusions : Prop

namespace OperationPolicy

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}

/-- The selected operation is selected by the policy at the field state. -/
def Selected
    (policy : OperationPolicy support)
    (source : Field) (operation : Operation) : Prop :=
  policy.selected source operation

/--
Policy preorder vocabulary: the first operation is no harder, no less natural,
or no less preferred than the second under the selected policy reading.
-/
def NoHarderThan
    (policy : OperationPolicy support)
    (source : Field) (operation₁ operation₂ : Operation) : Prop :=
  policy.noHarderThan source operation₁ operation₂

/-- Cost-order assumptions remain explicit boundary data. -/
def RecordsCostBoundary
    (policy : OperationPolicy support) : Prop :=
  policy.costBoundary

/-- Selection assumptions remain explicit boundary data. -/
def RecordsSelectionBoundary
    (policy : OperationPolicy support) : Prop :=
  policy.selectionBoundary

/-- The policy/modeling boundary remains explicit. -/
def RecordsPolicyBoundary
    (policy : OperationPolicy support) : Prop :=
  policy.policyBoundary

/--
Policy non-conclusions stay explicit: policy pass is not architecture
lawfulness, calibrated future safety, empirical risk reduction, or extractor
completeness.
-/
def RecordsNonConclusions
    (policy : OperationPolicy support) : Prop :=
  policy.nonConclusions ∧ support.RecordsNonConclusions

end OperationPolicy

/--
Support transformation induced by a governance step.

The transformation stores boundary data separately from the inclusion predicate
used by cone projection theorems.
-/
structure SupportTransformation
    {Field : Type u} {Operation : Type v}
    (supportBefore supportAfter : OperationSupport Field Operation) where
  transformsSupport : Prop
  supportBoundary : Prop
  policyBoundary : Prop
  nonConclusions : Prop

namespace SupportTransformation

variable {Field : Type u} {Operation : Type v}
variable {supportBefore supportAfter : OperationSupport Field Operation}

/--
The after-support is a restriction of the before-support.

This is the theorem-bearing condition needed by existing ForecastCone
projection results. It does not say the restriction is complete, optimal, or
empirically effective.
-/
def Restricts
    (_transformation : SupportTransformation supportBefore supportAfter) :
    Prop :=
  PointwiseSupportInclusion supportAfter supportBefore

/-- The transformation records that it changes the selected support package. -/
def RecordsSupportTransformation
    (transformation : SupportTransformation supportBefore supportAfter) :
    Prop :=
  transformation.transformsSupport

/-- Support-transformation assumptions remain explicit. -/
def RecordsSupportBoundary
    (transformation : SupportTransformation supportBefore supportAfter) :
    Prop :=
  transformation.supportBoundary

/-- Policy-shaping assumptions remain explicit. -/
def RecordsPolicyBoundary
    (transformation : SupportTransformation supportBefore supportAfter) :
    Prop :=
  transformation.policyBoundary

/-- Support-transformation non-conclusions remain explicit. -/
def RecordsNonConclusions
    (transformation : SupportTransformation supportBefore supportAfter) :
    Prop :=
  transformation.nonConclusions ∧
    supportBefore.RecordsNonConclusions ∧ supportAfter.RecordsNonConclusions

end SupportTransformation

/--
Governance intervention as support and policy transformation.

Review, CI, type checking, architecture rules, AI policy, and runtime guards can
be modeled by choosing before/after supports and policies, plus explicit
observation, feedback, escalation, and non-conclusion boundaries.
-/
structure GovernanceIntervention
    {Field : Type u} {Operation : Type v}
    (supportBefore supportAfter : OperationSupport Field Operation) where
  policyBefore : OperationPolicy supportBefore
  policyAfter : OperationPolicy supportAfter
  supportTransformation : SupportTransformation supportBefore supportAfter
  observationEnrichment : Prop
  feedbackUpdate : Prop
  escalationBoundary : Prop
  interventionBoundary : Prop
  nonConclusions : Prop

namespace GovernanceIntervention

variable {Field : Type u} {Operation : Type v}
variable {supportBefore supportAfter : OperationSupport Field Operation}

/-- The intervention records the selected support transformation. -/
def RecordsSupportTransformation
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.supportTransformation.RecordsSupportTransformation

/-- The intervention records before-policy boundary data. -/
def RecordsPolicyBeforeBoundary
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.policyBefore.RecordsPolicyBoundary

/-- The intervention records after-policy boundary data. -/
def RecordsPolicyAfterBoundary
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.policyAfter.RecordsPolicyBoundary

/-- Observation enrichment is an explicit boundary item, not a completeness theorem. -/
def RecordsObservationEnrichment
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.observationEnrichment

/-- Feedback-update assumptions remain explicit. -/
def RecordsFeedbackUpdate
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.feedbackUpdate

/-- Escalation / deferral assumptions remain explicit. -/
def RecordsEscalationBoundary
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.escalationBoundary

/-- The intervention-level modeling boundary remains explicit. -/
def RecordsInterventionBoundary
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.interventionBoundary

/--
Intervention non-conclusions combine support transformation and policy
non-conclusions. In particular, policy pass does not imply architecture
lawfulness, global future safety, or empirical risk reduction.
-/
def RecordsNonConclusions
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.nonConclusions ∧
    intervention.supportTransformation.RecordsNonConclusions ∧
    intervention.policyBefore.RecordsNonConclusions ∧
    intervention.policyAfter.RecordsNonConclusions

/--
A restrictive intervention removes or blocks selected support by making the
after-support pointwise included in the before-support.
-/
def Restrictive
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.supportTransformation.Restricts

/--
A redirective intervention records policy-shaping boundaries on both sides.
This is cost/selection vocabulary only; it does not prove empirical steering.
-/
def Redirective
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.RecordsPolicyBeforeBoundary ∧
    intervention.RecordsPolicyAfterBoundary ∧
    intervention.supportTransformation.RecordsPolicyBoundary

/--
An instrumenting intervention records additional observation capability.
This does not discharge unmeasured-axis safety or extractor completeness.
-/
def Instrumenting
    (intervention :
      GovernanceIntervention supportBefore supportAfter) : Prop :=
  intervention.RecordsObservationEnrichment

/-- A restrictive intervention exposes the support inclusion needed downstream. -/
theorem restrictive_supportInclusion
    (intervention :
      GovernanceIntervention supportBefore supportAfter)
    (hRestrictive : intervention.Restrictive) :
    PointwiseSupportInclusion supportAfter supportBefore :=
  hRestrictive

/--
Restrictive governance connects to the existing same-relation cone projection:
an after-support cone path projects into the before-support cone at the same
horizon.
-/
theorem restrictive_forecastCone_projects
    (intervention :
      GovernanceIntervention supportBefore supportAfter)
    (hRestrictive : intervention.Restrictive)
    {relation : StepRelation Field Operation}
    {source target : Field} {horizon : Nat}
    {pathAfter : FieldPath supportAfter relation source target}
    (hCone : ForecastCone supportAfter relation source horizon target pathAfter) :
    ForecastCone supportBefore relation source horizon target
      (ForecastConeProjection.projectFieldPath
        (restrictive_supportInclusion intervention hRestrictive)
        (SameRelationStepSimulation supportAfter relation)
        pathAfter) :=
  ForecastConeProjection.forecastCone_projects_of_supportInclusion
    (restrictive_supportInclusion intervention hRestrictive) hCone

/-- Redirective interventions expose policy boundaries without proving safety. -/
theorem redirective_records_policyBoundaries
    (intervention :
      GovernanceIntervention supportBefore supportAfter)
    (hRedirective : intervention.Redirective) :
    intervention.RecordsPolicyBeforeBoundary ∧
      intervention.RecordsPolicyAfterBoundary :=
  ⟨hRedirective.1, hRedirective.2.1⟩

/-- Instrumenting interventions expose observation enrichment as boundary data. -/
theorem instrumenting_records_observationEnrichment
    (intervention :
      GovernanceIntervention supportBefore supportAfter)
    (hInstrumenting : intervention.Instrumenting) :
    intervention.RecordsObservationEnrichment :=
  hInstrumenting

/-- Governance intervention keeps policy-pass non-conclusions available. -/
theorem policy_pass_does_not_discharge_lawfulness
    (intervention :
      GovernanceIntervention supportBefore supportAfter)
    (hNonConclusions : intervention.RecordsNonConclusions) :
    intervention.nonConclusions :=
  hNonConclusions.1

end GovernanceIntervention

end Formal.Arch
