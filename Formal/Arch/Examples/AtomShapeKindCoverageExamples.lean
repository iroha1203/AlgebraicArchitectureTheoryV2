import Formal.Arch.Atom.Shape

namespace Formal.Arch.AtomShapeKindCoverageExamples

inductive Component where
  | api
  deriving DecidableEq, Repr

inductive Edge where
  | apiToDatabase
  deriving DecidableEq, Repr

inductive Diagram where
  | requestFlow
  deriving DecidableEq, Repr

/--
One concrete atom for each currently declared `AtomKind`.

This is an AtomShape-layer acceptance fixture: each constructor is a primitive
typed fact shape, not observation metadata or a downstream theorem wrapper.
-/
inductive CoverageAtom where
  | component
  | relation
  | capability
  | dataState
  | effect
  | authority
  | contract
  | semantic
  | runtime
  deriving DecidableEq, Repr

def coveragePredicate :
    CoverageAtom -> AtomPredicate Component Edge Diagram
  | .component => AtomPredicate.component Component.api
  | .relation => AtomPredicate.relation Edge.apiToDatabase
  | .capability => AtomPredicate.capability Component.api "read"
  | .dataState => AtomPredicate.dataState Diagram.requestFlow "request-state"
  | .effect => AtomPredicate.effect Diagram.requestFlow "writes-response"
  | .authority => AtomPredicate.boundaryAuthority Component.api "owner"
  | .contract =>
      AtomPredicate.contractSpecification Diagram.requestFlow "api-contract"
  | .semantic =>
      AtomPredicate.semanticInterpretation Diagram.requestFlow "request-meaning"
  | .runtime =>
      AtomPredicate.runtimeInteraction Edge.apiToDatabase "runtime-call"

/-- Concrete root system whose atoms cover the current AtomKind grammar. -/
def coverageSystem : AtomAxiomSystem where
  Atom := CoverageAtom
  Predicate := AtomPredicate Component Edge Diagram
  kind := fun atom => (coveragePredicate atom).kind
  axis := fun atom => (coveragePredicate atom).axis
  predicate := coveragePredicate
  predicateKind := AtomPredicate.kind
  predicateAxis := AtomPredicate.axis
  predicateKindAligned := by
    intro atom
    cases atom <;> rfl
  predicateAxisAligned := by
    intro atom
    cases atom <;> rfl
  singleFact := fun _ => True
  singleFactEvidence := fun _ => trivial
  predicatePreserving := fun _ => True
  predicatePreservingEvidence := fun _ => trivial
  boundaryIndependent := fun _ => True
  boundaryIndependentEvidence := fun _ => trivial
  lawIndependent := fun _ => True
  lawIndependentEvidence := fun _ => trivial
  noObservationBoundaryCreatesAtoms := True
  noObservationBoundaryCreatesAtomsEvidence := trivial
  noLawCreatesAtoms := True
  noLawCreatesAtomsEvidence := trivial
  noToolOutputCreatesAtoms := True
  noToolOutputCreatesAtomsEvidence := trivial
  noSFTEventCreatesAtoms := True
  noSFTEventCreatesAtomsEvidence := trivial
  openTaxonomyBoundary := True

def coveragePortKind : CoverageAtom -> AtomPortKind
  | .component => AtomPortKind.subject
  | .relation => AtomPortKind.relationSource
  | .capability => AtomPortKind.subject
  | .dataState => AtomPortKind.payload
  | .effect => AtomPortKind.effect
  | .authority => AtomPortKind.authority
  | .contract => AtomPortKind.contract
  | .semantic => AtomPortKind.payload
  | .runtime => AtomPortKind.runtimeSource

def coveragePortName : CoverageAtom -> String
  | .component => "component-subject"
  | .relation => "relation-source"
  | .capability => "capability-subject"
  | .dataState => "data-state-payload"
  | .effect => "effect"
  | .authority => "authority"
  | .contract => "contract"
  | .semantic => "semantic-payload"
  | .runtime => "runtime-source"

def coveragePort (atom : CoverageAtom) : AtomPort where
  name := coveragePortName atom
  kind := coveragePortKind atom
  family := (coveragePredicate atom).kind
  axis := (coveragePredicate atom).axis
  required := False
  acceptsFamily := fun kind => kind = (coveragePredicate atom).kind
  acceptsAxis := fun axis => axis = (coveragePredicate atom).axis

def coverageValence (atom : CoverageAtom) : AtomValence where
  ports := fun port => port = coveragePort atom
  requiredPort := fun _ => False
  requiredPortHasPort := by
    intro _ hRequired
    cases hRequired
  hasPort := ⟨coveragePort atom, rfl⟩

def coverageSubjectName : CoverageAtom -> String
  | .component => "api"
  | .relation => "api-to-database"
  | .capability => "api"
  | .dataState => "request-flow"
  | .effect => "request-flow"
  | .authority => "api"
  | .contract => "request-flow"
  | .semantic => "request-flow"
  | .runtime => "api-to-database"

def coveragePredicateName : CoverageAtom -> String
  | .component => "component"
  | .relation => "relation"
  | .capability => "capability"
  | .dataState => "data-state"
  | .effect => "effect"
  | .authority => "boundary-authority"
  | .contract => "contract-specification"
  | .semantic => "semantic-interpretation"
  | .runtime => "runtime-interaction"

def coverageDirection : CoverageAtom -> AtomDirection
  | .relation => AtomDirection.outgoing
  | .runtime => AtomDirection.outgoing
  | .effect => AtomDirection.outgoing
  | _ => AtomDirection.neutral

def coverageArity : CoverageAtom -> Nat
  | .relation => 2
  | .runtime => 2
  | _ => 1

def coverageShape (atom : CoverageAtom) : AtomShape where
  family := (coveragePredicate atom).kind
  axis := (coveragePredicate atom).axis
  subject := { name := coverageSubjectName atom }
  predicate := coveragePredicateName atom
  objectSlots := fun _ => False
  payloadSlots := fun _ => False
  direction := coverageDirection atom
  arity := coverageArity atom
  valence := coverageValence atom
  singleFactShape := True
  singleFactShapeEvidence := trivial

def coverageShapePresentation :
    AtomShapePresentation coverageSystem where
  shapeOf := coverageShape
  shapeKindAligned := by
    intro atom
    cases atom <;> rfl
  shapeAxisAligned := by
    intro atom
    cases atom <;> rfl
  shapeSingleFact := by
    intro _ _
    trivial

def ShapeKindGeneratedBy (kind : AtomKind) : Prop :=
  ∃ atom : CoverageAtom,
    (AtomShapeOf coverageShapePresentation atom).family = kind

theorem coverage_shape_kind_matches_predicate
    (atom : CoverageAtom) :
    (AtomShapeOf coverageShapePresentation atom).family =
      (coveragePredicate atom).kind := by
  cases atom <;> rfl

theorem coverage_shape_axis_matches_predicate
    (atom : CoverageAtom) :
    (AtomShapeOf coverageShapePresentation atom).axis =
      (coveragePredicate atom).axis := by
  cases atom <;> rfl

theorem coverage_shape_has_valence_port
    (atom : CoverageAtom) :
    (AtomShapeOf coverageShapePresentation atom).valence.ports
      (coveragePort atom) := by
  cases atom <;> rfl

/-- Every current AtomKind constructor appears as an intrinsic AtomShape family. -/
theorem coverage_shape_exists_for_every_atom_kind
    (kind : AtomKind) : ShapeKindGeneratedBy kind := by
  cases kind with
  | existence => exact ⟨CoverageAtom.component, rfl⟩
  | relation => exact ⟨CoverageAtom.relation, rfl⟩
  | capability => exact ⟨CoverageAtom.capability, rfl⟩
  | dataState => exact ⟨CoverageAtom.dataState, rfl⟩
  | effect => exact ⟨CoverageAtom.effect, rfl⟩
  | boundaryAuthority => exact ⟨CoverageAtom.authority, rfl⟩
  | contractSpecification => exact ⟨CoverageAtom.contract, rfl⟩
  | semanticInterpretation => exact ⟨CoverageAtom.semantic, rfl⟩
  | runtimeInteraction => exact ⟨CoverageAtom.runtime, rfl⟩

theorem coverage_shape_single_fact
    (atom : CoverageAtom) : coverageSystem.singleFact atom :=
  coverageShapePresentation.shape_single_fact atom

end Formal.Arch.AtomShapeKindCoverageExamples
