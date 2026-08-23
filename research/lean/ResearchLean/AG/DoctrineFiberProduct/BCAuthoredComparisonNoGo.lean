import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticComparison

/-!
# Residual-isomorphism classification of the authored factorization route

This module records a precise obstruction found while pursuing G-110: whenever
an authored comparison and the canonical comparison are both isomorphisms, the
authored component is necessarily the canonical component followed by an
automorphism of the common target.  For the Cycle 43 universal-factorization
construction, that residual automorphism is exactly the transported initial
raw defect.

These statements are evidence about the attempted authored-factorization
route.  They do not refute K2 globally: a later construction may use additional
structure that is not captured by an invertible postcomposition of the
canonical mate.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-! ## Generic componentwise classification -/

/--
An authored component differs from a canonical component only by an
automorphism of their common target.  This is a componentwise route predicate;
it makes no claim that independently chosen residuals are natural in an index.
-/
def IsCanonicalPostIsoTwist
    {C : Type u} [Category.{v} C] {X Y : C}
    (canonical authored : X ⟶ Y) : Prop :=
  ∃ residual : Y ≅ Y, authored = canonical ≫ residual.hom

/--
The nontrivial form of `IsCanonicalPostIsoTwist`: the residual automorphism is
not the identity.  This records a genuine component mismatch without promoting
it to a global no-go theorem.
-/
def HasNontrivialCanonicalPostIsoResidual
    {C : Type u} [Category.{v} C] {X Y : C}
    (canonical authored : X ⟶ Y) : Prop :=
  ∃ residual : Y ≅ Y,
    authored = canonical ≫ residual.hom ∧ residual.hom ≠ 𝟙 Y

/--
Two invertible parallel components always have the canonical-post-residual
classification.  The residual is `canonical⁻¹ ≫ authored`.
-/
  theorem isCanonicalPostIsoTwist_of_isIso
    {C : Type u} [Category.{v} C] {X Y : C}
    (canonical authored : X ⟶ Y) [IsIso canonical] [IsIso authored] :
    IsCanonicalPostIsoTwist canonical authored := by
  refine ⟨(asIso canonical).symm.trans (asIso authored), ?_⟩
  simp

/--
If two invertible parallel components are unequal, their residual
automorphism can be chosen nonidentity.
-/
theorem hasNontrivialCanonicalPostIsoResidual_of_ne
    {C : Type u} [Category.{v} C] {X Y : C}
    (canonical authored : X ⟶ Y) [IsIso canonical] [IsIso authored]
    (hne : authored ≠ canonical) :
    HasNontrivialCanonicalPostIsoResidual canonical authored := by
  rcases isCanonicalPostIsoTwist_of_isIso canonical authored with
    ⟨residual, authored_eq⟩
  refine ⟨residual, authored_eq, ?_⟩
  intro residual_eq
  apply hne
  rw [authored_eq, residual_eq, Category.comp_id]

/--
The post-residual in the classification is unique.  Thus the residual is not
merely an existential witness: cancellation by the invertible canonical
component recovers it from the authored component.
-/
theorem canonicalPostIsoResidual_unique
    {C : Type u} [Category.{v} C] {X Y : C}
    (canonical authored : X ⟶ Y) [IsIso canonical]
    (first second : Y ≅ Y)
    (hfirst : authored = canonical ≫ first.hom)
    (hsecond : authored = canonical ≫ second.hom) :
    first.hom = second.hom := by
  apply (cancel_epi canonical).1
  exact hfirst.symm.trans hsecond

/-! ## Cycle 43 factorization route -/

/-- The Cycle 43 initial raw defect is invertible in the southwest fiber. -/
theorem authoredInitialRawDefectComponent_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    IsIso (authoredInitialRawDefectComponent input cell) := by
  have component_eq :
      authoredInitialRawDefectComponent input cell =
        authoredRawDefectComponentAtCochain input
          (initialRawDefectCochain input.toTransportData) cell := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    rfl
  rw [component_eq]
  exact (authoredRawDefectComponentIsoAtCochain input
    (initialRawDefectCochain input.toTransportData) cell).isIso_hom

/--
The Cycle 43 transported initial raw-defect component is invertible.  This is
obtained by specializing the arbitrary-cochain result from Cycle 46, rather
than by accepting an external invertibility certificate.
-/
theorem authoredViaBaseRawDefectComponent_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    IsIso (authoredViaBaseRawDefectComponent input cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩,
      lift, endpoint_eq⟩, twoCellBase, authored⟩
  letI : IsIso (authoredInitialRawDefectComponent
      normalizedInput cell.as) :=
    authoredInitialRawDefectComponent_isIso normalizedInput cell.as
  change IsIso
    ((selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcRightPresentation presentation))).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
        (authoredInitialRawDefectComponent normalizedInput cell.as)))
  infer_instance

/--
Every Cycle 43 authored-factorization component is invertible: its reviewed
normal form is the invertible canonical mate followed by the invertible
transported raw defect.
-/
theorem authoredFactorizationComparisonComponent_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    IsIso (authoredFactorizationComparisonComponent input cell) := by
  letI : IsIso (authoredViaBaseRawDefectComponent input cell) :=
    authoredViaBaseRawDefectComponent_isIso input cell
  rw [authoredFactorizationComparisonComponent_eq_canonical_comp_viaRawDefect]
  infer_instance

/--
The exact Cycle 43 residual is the transported initial raw defect.  The
existential packaging is deliberate: it classifies this attempted route while
leaving open authored constructions with genuinely different ingredients.
-/
theorem authoredFactorizationComparisonComponent_has_raw_residual
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    ∃ residual :
        (authoredSupportViaBaseRoute input.context).obj cell ≅
          (authoredSupportViaBaseRoute input.context).obj cell,
      residual.hom = authoredViaBaseRawDefectComponent input cell ∧
        authoredFactorizationComparisonComponent input cell =
          (authoredSupportCanonicalMate input.context).app cell ≫ residual.hom := by
  letI : IsIso (authoredViaBaseRawDefectComponent input cell) :=
    authoredViaBaseRawDefectComponent_isIso input cell
  refine ⟨asIso (authoredViaBaseRawDefectComponent input cell), rfl, ?_⟩
  exact authoredFactorizationComparisonComponent_eq_canonical_comp_viaRawDefect
    input cell

/--
Consequently the Cycle 43 component lies in the generic
canonical-post-isomorphism route class.  This is obstruction evidence for this
factorization route, not a refutation of the fixed G-110 target.
-/
theorem authoredFactorizationComparisonComponent_isCanonicalPostIsoTwist
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    IsCanonicalPostIsoTwist
      ((authoredSupportCanonicalMate input.context).app cell)
      (authoredFactorizationComparisonComponent input cell) := by
  letI : IsIso (authoredFactorizationComparisonComponent input cell) :=
    authoredFactorizationComparisonComponent_isIso input cell
  exact isCanonicalPostIsoTwist_of_isIso
    ((authoredSupportCanonicalMate input.context).app cell)
    (authoredFactorizationComparisonComponent input cell)

/--
Any observed mismatch of the Cycle 43 component from the canonical mate is
therefore witnessed by a nonidentity target automorphism.  The mismatch remains
an explicit hypothesis, so this theorem cannot manufacture a negative K2
witness or overstate the scope of the route obstruction.
-/
theorem authoredFactorizationComparisonComponent_has_nontrivial_residual_of_ne
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category)
    (hne : authoredFactorizationComparisonComponent input cell ≠
      (authoredSupportCanonicalMate input.context).app cell) :
    HasNontrivialCanonicalPostIsoResidual
      ((authoredSupportCanonicalMate input.context).app cell)
      (authoredFactorizationComparisonComponent input cell) := by
  letI : IsIso (authoredFactorizationComparisonComponent input cell) :=
    authoredFactorizationComparisonComponent_isIso input cell
  exact hasNontrivialCanonicalPostIsoResidual_of_ne
    ((authoredSupportCanonicalMate input.context).app cell)
    (authoredFactorizationComparisonComponent input cell) hne

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
