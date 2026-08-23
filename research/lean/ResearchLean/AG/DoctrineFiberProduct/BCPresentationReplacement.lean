import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMateCleavageIndependence
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationReplacement

/-!
# Beck--Chevalley presentation replacement

This module places two finite Beck--Chevalley presentations over one literal
semantic input.  It extracts realization provenance for all four decoded
edges and uses cartesian uniqueness to compare the two selected reindexing
routes.  Thus replacement is indexed by equality of the complete decoded BC
input, rather than equality of the authored finite endpoint codes.

The final section isolates the remaining compatibility law: the canonical
covariant square isomorphism used by `coreBeckChevalleyMate` must agree after
replacement.  The comparison below fixes that square isomorphism at the
reference presentation and proves the complete change-of-cleavage mate square;
no authored comparator or Beck--Chevalley equality is accepted as data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## Realization provenance over one literal BC input -/

/-- A finite BC presentation whose decoder is one fixed literal semantic input. -/
structure BCRealizationProvenance
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCSemanticInput U) where
  /-- The authored finite presentation. -/
  presentation : BCPresentation U
  /-- The presentation decodes to the fixed semantic input. -/
  realization_eq : input = toSemanticBC presentation

namespace BCRealizationProvenance

/-- The first-projection semantic input extracted from the fixed BC square. -/
def leftInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCSemanticInput U) :
    CartSemanticInput U where
  source := input.square.northwest
  target := input.square.southwest
  hom := input.square.left

/-- The second-projection semantic input extracted from the fixed BC square. -/
def topInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCSemanticInput U) :
    CartSemanticInput U where
  source := input.square.northwest
  target := input.square.northeast
  hom := input.square.top

/-- The first cospan-leg semantic input extracted from the fixed BC square. -/
def bottomInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCSemanticInput U) :
    CartSemanticInput U where
  source := input.square.southwest
  target := input.square.southeast
  hom := input.square.bottom

/-- The second cospan-leg semantic input extracted from the fixed BC square. -/
def rightInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCSemanticInput U) :
    CartSemanticInput U where
  source := input.square.northeast
  target := input.square.southeast
  hom := input.square.right

/-- The generated first projection supplies provenance over the literal left input. -/
def leftProvenance {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    CartRealizationProvenance (leftInput input) where
  presentation := (bcLeftPresentation provenance.presentation).toPresentation
  realization_eq := by
    rcases provenance with ⟨presentation, rfl⟩
    rfl

/-- The generated second projection supplies provenance over the literal top input. -/
def topProvenance {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    CartRealizationProvenance (topInput input) where
  presentation := (bcTopPresentation provenance.presentation).toPresentation
  realization_eq := by
    rcases provenance with ⟨presentation, rfl⟩
    rfl

/-- The first cospan leg supplies provenance over the literal bottom input. -/
def bottomProvenance {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    CartRealizationProvenance (bottomInput input) where
  presentation := (bcBottomPresentation provenance.presentation).toPresentation
  realization_eq := by
    rcases provenance with ⟨presentation, rfl⟩
    rfl

/-- The second cospan leg supplies provenance over the literal right input. -/
def rightProvenance {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    CartRealizationProvenance (rightInput input) where
  presentation := (bcRightPresentation provenance.presentation).toPresentation
  realization_eq := by
    rcases provenance with ⟨presentation, rfl⟩
    rfl

end BCRealizationProvenance

/-! ## Direct and via-base route comparison -/

/-- The direct mate route generated from one realization provenance. -/
noncomputable def bcProvenanceDirectRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :=
  selectedCoreFiberReindexFunctor provenance.leftProvenance.toRealizableHom ⋙
    coreFiberTransportFunctor input.square.top

/-- The via-base mate route generated from one realization provenance. -/
noncomputable def bcProvenanceViaBaseRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :=
  coreFiberTransportFunctor input.square.bottom ⋙
    selectedCoreFiberReindexFunctor provenance.rightProvenance.toRealizableHom

/-- The canonical mate normalized onto the fixed literal semantic BC input. -/
noncomputable def bcProvenanceCanonicalMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    bcProvenanceDirectRoute provenance ⟶
      bcProvenanceViaBaseRoute provenance := by
  rcases provenance with ⟨presentation, rfl⟩
  exact coreBeckChevalleyMate presentation

/--
The canonical covariant square isomorphism normalized onto the fixed literal
semantic BC square.
-/
noncomputable def bcProvenanceCoreTransportSquareIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    coreFiberTransportFunctor input.square.top ⋙
        coreFiberTransportFunctor input.square.right ≅
      coreFiberTransportFunctor input.square.left ⋙
        coreFiberTransportFunctor input.square.bottom := by
  rcases provenance with ⟨presentation, rfl⟩
  exact bcCoreTransportSquareIso presentation

/--
The covariant square isomorphism generated directly from the fixed semantic
square, its commutativity equation, and the two G-109 compositors.
-/
noncomputable def bcSemanticCoreTransportSquareIso
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    coreFiberTransportFunctor input.square.top ⋙
        coreFiberTransportFunctor input.square.right ≅
      coreFiberTransportFunctor input.square.left ⋙
        coreFiberTransportFunctor input.square.bottom := by
  exact (coreFiberCompositor input.square.top input.square.right).symm ≪≫
    eqToIso (congrArg coreFiberTransportFunctor input.square.commutes.symm) ≪≫
    coreFiberCompositor input.square.left input.square.bottom

/--
Two presentations of one semantic BC input have canonically isomorphic direct
routes, generated by uniqueness of the selected cartesian lifts.
-/
noncomputable def bcProvenanceDirectRouteComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (first second : BCRealizationProvenance input) :
    bcProvenanceDirectRoute first ≅ bcProvenanceDirectRoute second :=
  Functor.isoWhiskerRight
    (cartRealizationProvenanceComparison first.leftProvenance
      second.leftProvenance)
    (coreFiberTransportFunctor input.square.top)

/--
Two presentations of one semantic BC input have canonically isomorphic
via-base routes, generated by uniqueness of the selected cartesian lifts.
-/
noncomputable def bcProvenanceViaBaseRouteComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (first second : BCRealizationProvenance input) :
    bcProvenanceViaBaseRoute first ≅ bcProvenanceViaBaseRoute second :=
  Functor.isoWhiskerLeft
    (coreFiberTransportFunctor input.square.bottom)
    (cartRealizationProvenanceComparison first.rightProvenance
      second.rightProvenance)

/-! ## The mate with the reference covariant square held fixed -/

/--
The selected left cleavage generated from `replacement`, rebased over the
literal semantic input of `reference`.  Only realization provenance changes.
-/
noncomputable def bcReplacementLeftCleavage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    CoreFiberCartesianCleavage
      (bcLeftInput reference.presentation).semantic := by
  rcases reference with ⟨reference, rfl⟩
  exact selectedCoreFiberCartesianCleavage
    replacement.leftProvenance.toRealizableHom

/--
The selected right cleavage generated from `replacement`, rebased over the
literal semantic input of `reference`.
-/
noncomputable def bcReplacementRightCleavage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    CoreFiberCartesianCleavage
      (bcRightInput reference.presentation).semantic := by
  rcases reference with ⟨reference, rfl⟩
  exact selectedCoreFiberCartesianCleavage
    replacement.rightProvenance.toRealizableHom

/--
The replacement mate with the covariant square isomorphism fixed at the
reference presentation.  Both reindexing functors are generated from the
replacement provenance.
-/
noncomputable def bcRebasedReplacementMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :=
  coreBeckChevalleyCleavageMate reference.presentation
    (bcReplacementLeftCleavage reference replacement)
    (bcReplacementRightCleavage reference replacement)

/--
Changing both presentation-generated cleavages commutes with the canonical
mate while the reference covariant square isomorphism is held fixed.  This is
the complete adjunction/unit/counit part of BC presentation replacement.
-/
theorem coreBeckChevalleyMate_rebasedReplacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    Functor.whiskerRight
          (coreFiberCleavageSelectedComparison
            (bcLeftInput reference.presentation)
            (bcReplacementLeftCleavage reference replacement)).hom
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation reference.presentation))) ≫
        coreBeckChevalleyMate reference.presentation =
      bcRebasedReplacementMate reference replacement ≫
        Functor.whiskerLeft
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation reference.presentation)))
          (coreFiberCleavageSelectedComparison
            (bcRightInput reference.presentation)
            (bcReplacementRightCleavage reference replacement)).hom := by
  exact coreBeckChevalleyCleavageMate_selectedComparison
    reference.presentation
    (bcReplacementLeftCleavage reference replacement)
    (bcReplacementRightCleavage reference replacement)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
