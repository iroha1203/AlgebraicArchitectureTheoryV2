import Formal.Arch.Evolution.SFTForecastCone

namespace Formal.Arch

universe u v w x

/--
A selected candidate update relation for artifact-mediated SFT change.

The relation separates candidate membership from candidate application. It does
not state that candidates are complete, unique, empirically extracted, or
causally correct.
-/
structure CandidateUpdateRelation (Field : Type u) (Update : Type v) where
  candidate : Field -> Update -> Prop
  appliesTo : Field -> Update -> Field -> Prop
  interpretationBoundary : Prop
  updateBoundary : Prop
  nonConclusions : Prop

namespace CandidateUpdateRelation

variable {Field : Type u} {Update : Type v}

/-- The selected update is a candidate at the selected field state. -/
def Candidate
    (relation : CandidateUpdateRelation Field Update)
    (source : Field) (update : Update) : Prop :=
  relation.candidate source update

/-- The selected update can be read as producing the selected target field. -/
def AppliesTo
    (relation : CandidateUpdateRelation Field Update)
    (source : Field) (update : Update) (target : Field) : Prop :=
  relation.appliesTo source update target

/-- Interpretation assumptions remain explicit boundary data. -/
def RecordsInterpretationBoundary
    (relation : CandidateUpdateRelation Field Update) : Prop :=
  relation.interpretationBoundary

/-- Candidate-update assumptions remain explicit boundary data. -/
def RecordsUpdateBoundary
    (relation : CandidateUpdateRelation Field Update) : Prop :=
  relation.updateBoundary

/-- Candidate-update non-conclusions remain explicit. -/
def RecordsNonConclusions
    (relation : CandidateUpdateRelation Field Update) : Prop :=
  relation.nonConclusions

end CandidateUpdateRelation

/--
An artifact-mediated SFT action.

The artifact is read as constraining a set of candidate updates. The action
keeps source artifact, target-component, interpretation, composition,
observable, and non-conclusion boundaries explicit.
-/
structure ArtifactAction
    (Artifact : Type w) (Field : Type u) (Update : Type v) where
  artifact : Artifact
  candidateUpdates : CandidateUpdateRelation Field Update
  targetFieldComponents : Prop
  actionBoundary : Prop
  compositionBoundary : Prop
  observableBoundary : Prop
  nonConclusions : Prop

namespace ArtifactAction

variable {Artifact : Type w} {Field : Type u} {Update : Type v}

/-- Candidate update membership induced by the artifact action. -/
def CandidateUpdate
    (action : ArtifactAction Artifact Field Update)
    (source : Field) (update : Update) : Prop :=
  action.candidateUpdates.Candidate source update

/-- Candidate update application induced by the artifact action. -/
def AppliesTo
    (action : ArtifactAction Artifact Field Update)
    (source : Field) (update : Update) (target : Field) : Prop :=
  action.candidateUpdates.AppliesTo source update target

/-- Target field component assumptions remain explicit. -/
def RecordsTargetFieldComponents
    (action : ArtifactAction Artifact Field Update) : Prop :=
  action.targetFieldComponents

/-- Interpretation assumptions are inherited from the candidate update relation. -/
def RecordsInterpretationBoundary
    (action : ArtifactAction Artifact Field Update) : Prop :=
  action.candidateUpdates.RecordsInterpretationBoundary

/-- Action-level assumptions remain explicit. -/
def RecordsActionBoundary
    (action : ArtifactAction Artifact Field Update) : Prop :=
  action.actionBoundary

/-- Composition assumptions remain explicit. -/
def RecordsCompositionBoundary
    (action : ArtifactAction Artifact Field Update) : Prop :=
  action.compositionBoundary

/-- Observable-boundary assumptions remain explicit. -/
def RecordsObservableBoundary
    (action : ArtifactAction Artifact Field Update) : Prop :=
  action.observableBoundary

/--
Artifact action non-conclusions combine action-level and candidate-relation
non-conclusions. In particular, they do not imply a unique future, causal proof,
market success, human intention, or ambient source-observation coverage.
-/
def RecordsNonConclusions
    (action : ArtifactAction Artifact Field Update) : Prop :=
  action.nonConclusions ∧ action.candidateUpdates.RecordsNonConclusions

end ArtifactAction

/--
A deterministic artifact action is a special case of an artifact action whose
candidate update and applied target are both unique for each source field.
-/
structure DeterministicArtifactAction
    (Artifact : Type w) (Field : Type u) (Update : Type v) where
  action : ArtifactAction Artifact Field Update
  selectedUpdate : Field -> Update
  selectedTarget : Field -> Field
  selectedUpdate_candidate :
    ∀ source, action.CandidateUpdate source (selectedUpdate source)
  selectedUpdate_applies :
    ∀ source, action.AppliesTo source (selectedUpdate source) (selectedTarget source)
  candidate_unique :
    ∀ {source update}, action.CandidateUpdate source update ->
      update = selectedUpdate source
  target_unique :
    ∀ {source update target}, action.CandidateUpdate source update ->
      action.AppliesTo source update target ->
        target = selectedTarget source

namespace DeterministicArtifactAction

variable {Artifact : Type w} {Field : Type u} {Update : Type v}

/-- The selected deterministic update is a candidate for its source field. -/
theorem selected_candidate
    (det : DeterministicArtifactAction Artifact Field Update)
    (source : Field) :
    det.action.CandidateUpdate source (det.selectedUpdate source) :=
  det.selectedUpdate_candidate source

/-- Any candidate update equals the selected deterministic update. -/
theorem candidate_eq_selected
    (det : DeterministicArtifactAction Artifact Field Update)
    {source : Field} {update : Update}
    (hCandidate : det.action.CandidateUpdate source update) :
    update = det.selectedUpdate source :=
  det.candidate_unique hCandidate

/-- Any applied candidate target equals the selected deterministic target. -/
theorem target_eq_selected
    (det : DeterministicArtifactAction Artifact Field Update)
    {source : Field} {update : Update} {target : Field}
    (hCandidate : det.action.CandidateUpdate source update)
    (hApplies : det.action.AppliesTo source update target) :
    target = det.selectedTarget source :=
  det.target_unique hCandidate hApplies

/-- Deterministic actions still preserve the artifact-action non-conclusion boundary. -/
def RecordsNonConclusions
    (det : DeterministicArtifactAction Artifact Field Update) : Prop :=
  det.action.RecordsNonConclusions

end DeterministicArtifactAction

/--
A selected forecast-cone family member after an artifact action.

For a set-valued action, each candidate update and applied updated field can
produce its own cone source. This record stores one such member; it is not a
deterministic future, probability distribution, causal proof, or complete
enumeration of all possible future fields.
-/
structure ForecastConeFamilyAfterAction
    {Artifact : Type w} {Field : Type u} {Update : Type v}
    (action : ArtifactAction Artifact Field Update)
    (Operation : Type x)
    (supportAfter : Field -> OperationSupport Field Operation)
    (relationAfter : Field -> StepRelation Field Operation)
    (source : Field) (horizon : Nat) where
  candidateUpdate : Update
  updatedField : Field
  candidateMember : action.CandidateUpdate source candidateUpdate
  appliesToUpdatedField : action.AppliesTo source candidateUpdate updatedField
  target : Field
  path :
    FieldPath (supportAfter updatedField) (relationAfter updatedField)
      updatedField target
  coneMember :
    ForecastCone (supportAfter updatedField) (relationAfter updatedField)
      updatedField horizon target path
  familyBoundary : Prop
  nonConclusions : Prop

namespace ForecastConeFamilyAfterAction

variable {Artifact : Type w} {Field : Type u} {Update : Type v}
variable {action : ArtifactAction Artifact Field Update}
variable {Operation : Type x}
variable {supportAfter : Field -> OperationSupport Field Operation}
variable {relationAfter : Field -> StepRelation Field Operation}
variable {source : Field} {horizon : Nat}

/-- The stored family member exposes its candidate update membership. -/
theorem candidate_member
    (family :
      ForecastConeFamilyAfterAction action Operation supportAfter relationAfter
        source horizon) :
    action.CandidateUpdate source family.candidateUpdate :=
  family.candidateMember

/-- The stored family member exposes the candidate update application witness. -/
theorem applies_to_updatedField
    (family :
      ForecastConeFamilyAfterAction action Operation supportAfter relationAfter
        source horizon) :
    action.AppliesTo source family.candidateUpdate family.updatedField :=
  family.appliesToUpdatedField

/-- The stored cone member exposes the finite horizon bound for its path. -/
theorem length_le_horizon
    (family :
      ForecastConeFamilyAfterAction action Operation supportAfter relationAfter
        source horizon) :
    ArchitecturePath.length family.path <= horizon :=
  ForecastCone.length_le_horizon family.coneMember

/-- The action-after-cone family keeps its selected modeling boundary explicit. -/
def RecordsFamilyBoundary
    (family :
      ForecastConeFamilyAfterAction action Operation supportAfter relationAfter
        source horizon) : Prop :=
  family.familyBoundary

/--
Action-after-cone non-conclusions combine action-level and family-level
boundaries rather than strengthening a candidate family into a unique future.
-/
def RecordsNonConclusions
    (family :
      ForecastConeFamilyAfterAction action Operation supportAfter relationAfter
        source horizon) : Prop :=
  family.nonConclusions ∧ action.RecordsNonConclusions ∧
    ForecastCone.RecordsNonConclusions
      (support := supportAfter family.updatedField)
      (relation := relationAfter family.updatedField)

end ForecastConeFamilyAfterAction

end Formal.Arch
