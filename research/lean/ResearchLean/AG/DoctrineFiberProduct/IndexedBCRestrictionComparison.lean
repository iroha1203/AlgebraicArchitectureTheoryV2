import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticAssembly
import ResearchLean.AG.DoctrineFiberProduct.BCPresentationReplacement

/-!
# Restriction of the indexed square action to a pointed BC square

A pointed Beck--Chevalley square is represented by a diagnostic-free
walking-arrow diagram morphism. Its two diagram vertices retain the four
corners of the square, and its unique generating-edge naturality equation is
the authored square equation. This avoids introducing a fictitious base arrow
from the southwest corner to the northeast corner.

The generated indexed covariant square comparison is identified with the
reviewed G-110 comparison. Taking its canonical mate then recovers the actual
G-110 direct/via-base Beck--Chevalley mate.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- The two vertices of the walking-arrow restriction shape. -/
inductive IndexedBCRestrictionVertex : Type u
  | north
  | south
  deriving DecidableEq, Fintype

/-- The unique generating edge of the walking-arrow restriction shape. -/
inductive IndexedBCRestrictionEdge :
    IndexedBCRestrictionVertex → IndexedBCRestrictionVertex → Type u
  | leg : IndexedBCRestrictionEdge .north .south

instance indexedBCRestrictionEdgeFintype
    (i j : IndexedBCRestrictionVertex) :
    Fintype (IndexedBCRestrictionEdge i j) := by
  classical
  cases i <;> cases j
  · exact ⟨∅, fun edge => nomatch edge⟩
  · exact ⟨{IndexedBCRestrictionEdge.leg}, by
      intro edge
      cases edge
      simp⟩
  · exact ⟨∅, fun edge => nomatch edge⟩
  · exact ⟨∅, fun edge => nomatch edge⟩

/-- The diagnostic-free walking-arrow shape; it has no declared 2-cells. -/
abbrev indexedBCRestrictionShape : IndexedBaseTwoShape.{u} where
  Vertex := IndexedBCRestrictionVertex
  vertexFintype := inferInstance
  Edge := IndexedBCRestrictionEdge
  edgeFintype := indexedBCRestrictionEdgeFintype
  TwoCell := ULift.{u} Empty
  twoCellFintype := inferInstance
  twoSource := fun cell => nomatch cell.down
  twoTarget := fun cell => nomatch cell.down
  twoLeft := fun cell => nomatch cell.down
  twoRight := fun cell => nomatch cell.down

/-- The unique edge in the walking-arrow restriction shape. -/
def indexedBCRestrictionEdge :
    IndexedBCRestrictionEdge IndexedBCRestrictionVertex.north
      IndexedBCRestrictionVertex.south :=
  IndexedBCRestrictionEdge.leg

/-- The left column of a semantic BC square as a diagnostic-free diagram. -/
noncomputable def indexedBCRestrictionSourceDiagram
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    IndexedBaseDiagram indexedBCRestrictionShape.{u} U where
  vertex := fun vertex : IndexedBCRestrictionVertex => match vertex with
    | .north => input.square.northwest
    | .south => input.square.southwest
  edge := fun {_ _} edge => match edge with
    | .leg => input.square.left
  relation := fun cell => nomatch cell.down

/-- The right column of a semantic BC square as a diagnostic-free diagram. -/
noncomputable def indexedBCRestrictionTargetDiagram
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    IndexedBaseDiagram indexedBCRestrictionShape.{u} U where
  vertex := fun vertex : IndexedBCRestrictionVertex => match vertex with
    | .north => input.square.northeast
    | .south => input.square.southeast
  edge := fun {_ _} edge => match edge with
    | .leg => input.square.right
  relation := fun cell => nomatch cell.down

/-- The top and bottom arrows form the coherent walking-arrow diagram morphism. -/
noncomputable def indexedBCRestrictionDiagramHom
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    IndexedBaseDiagramHom (indexedBCRestrictionSourceDiagram input)
      (indexedBCRestrictionTargetDiagram input) where
  app := fun vertex : IndexedBCRestrictionVertex => match vertex with
    | .north => input.square.top
    | .south => input.square.bottom
  naturality := fun {_ _} edge => match edge with
    | .leg => input.square.commutes.symm

/-- The restriction edge recovers the semantic BC square as validated indexed syntax. -/
theorem indexedBCRestriction_squareAction_eq_semantic
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    indexedSquareTermAction
        ((indexedBCRestrictionDiagramHom input).validatedEdgeSquare
          indexedBCRestrictionEdge) =
      bcSemanticCoreTransportSquareIso input := by
  rfl

/-- The indexed restriction square action is the reviewed G-110 covariant comparison. -/
theorem indexedBCRestriction_squareAction_eq_g110
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    indexedSquareTermAction
        ((indexedBCRestrictionDiagramHom (toSemanticBC presentation)).validatedEdgeSquare
          indexedBCRestrictionEdge) =
      bcCoreTransportSquareIso presentation := by
  rw [indexedBCRestriction_squareAction_eq_semantic]
  simpa using
    (bcProvenanceCoreTransportSquareIso_eq_semantic
      ({ presentation := presentation, realization_eq := rfl } :
        BCRealizationProvenance (toSemanticBC presentation))).symm

/-- The restriction's direct route: left reindexing followed by indexed top transport. -/
noncomputable def indexedBCRestrictionDirectFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation presentation)) ⋙
    indexedFiberAction
      ((indexedBCRestrictionDiagramHom
        (toSemanticBC presentation)).vertexIndex
          IndexedBCRestrictionVertex.north)

/-- The restriction's via-base route: indexed bottom transport followed by right reindexing. -/
noncomputable def indexedBCRestrictionViaBaseFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  indexedFiberAction
      ((indexedBCRestrictionDiagramHom
        (toSemanticBC presentation)).vertexIndex
          IndexedBCRestrictionVertex.south) ⋙
    selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcRightPresentation presentation))

/-- The generated indexed direct route is definitionally the actual G-110 route. -/
theorem indexedBCRestrictionDirectFunctor_eq_g110
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    indexedBCRestrictionDirectFunctor presentation =
      bcDiagnosticDirectFunctor presentation := by
  rfl

/-- The generated indexed via-base route is definitionally the actual G-110 route. -/
theorem indexedBCRestrictionViaBaseFunctor_eq_g110
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    indexedBCRestrictionViaBaseFunctor presentation =
      bcDiagnosticViaBaseFunctor presentation := by
  rfl

/-- Take the canonical Beck--Chevalley mate of the indexed restriction square. -/
noncomputable def indexedBCRestrictionMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    indexedBCRestrictionDirectFunctor presentation ⟶
      indexedBCRestrictionViaBaseFunctor presentation :=
  (mateEquiv (bcLeftAdjunction presentation) (bcRightAdjunction presentation)
    (indexedSquareTermAction
      ((indexedBCRestrictionDiagramHom
        (toSemanticBC presentation)).validatedEdgeSquare
          indexedBCRestrictionEdge)).hom).natTrans

/-- The indexed restriction mate is the reviewed G-110 direct/via-base mate. -/
theorem indexedBCRestrictionMate_eq_g110
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    indexedBCRestrictionMate presentation =
      coreBeckChevalleyMate presentation := by
  unfold indexedBCRestrictionMate
  rw [indexedBCRestriction_squareAction_eq_g110]
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
