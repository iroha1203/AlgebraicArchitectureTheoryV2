import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticNaturalIsoCompatibility
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPastedRouteCompatibility
import ResearchLean.AG.DoctrineFiberProduct.BCPastingComponentToOuterMate

/-!
# Pasted diagnostic naturality predecessor

This module turns the reviewed horizontal and vertical literal-component-mate
equations into natural isomorphisms acting on the complete G-106 diagnostic
package.  It also joins that comparison with the actual outer direct/via-base
route factorization from `BCDiagnosticPastedRouteCompatibility`.

The resulting direction-specific predecessor packages consume the G-109
component-to-outer alignments and the literal mate equations for package,
edge, comparator, mapped-reselection, and path naturality.  They retain the
actual outer-route factorization in the same output and derive forward
coherence and vanishing on both endpoints.  They do not yet prove that the
successive component-square diagnostic actions commute with the outer action;
that cross-route equation is the remaining K4 obligation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence
open CategoryTheory.NatTrans CategoryTheory.TwoSquare

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 2000000

/-- Conjugating an isomorphism through adjunctions whose units and counits are
isomorphisms again gives an isomorphism. -/
theorem conjugateEquiv_isIso_of_adjunction_isIso
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (transformation : L₂ ⟶ L₁)
    [IsIso adj₁.unit] [IsIso adj₁.counit]
    [IsIso adj₂.unit] [IsIso adj₂.counit]
    [IsIso transformation] :
    IsIso (conjugateEquiv adj₁ adj₂ transformation) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp [conjugateEquiv, mateEquiv]
  infer_instance

/-- The canonical mate attached to any realization provenance is exact. -/
theorem bcProvenanceCanonicalMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    IsIso (bcProvenanceCanonicalMate provenance) := by
  rcases provenance with ⟨presentation, rfl⟩
  exact coreBeckChevalleyMate_isIso presentation

/-! ## Horizontal aligned comparison -/

/-- Literal horizontal component mates after the generated source alignment. -/
noncomputable def horizontalAlignedLiteralComponentMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  horizontalDataMateSourceAlignment data ≫
    ((TwoSquare.mk _ _ _ _
      (coreBeckChevalleyMate data.leftPresentation)) ≫ᵥ
    (TwoSquare.mk _ _ _ _
      (coreBeckChevalleyMate data.rightPresentation))).natTrans

/-- The canonical outer horizontal mate after the generated target alignment. -/
noncomputable def horizontalAlignedOuterCanonicalMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  bcProvenanceCanonicalMate
      (bcPastingNormalizedProvenance (.horizontal data)) ≫
    horizontalOuterMateTargetAlignment data

/-- The Cycle 102 horizontal literal mate equation in named aligned form. -/
theorem horizontalAlignedLiteralComponentMate_eq_outer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalAlignedLiteralComponentMate data =
      horizontalAlignedOuterCanonicalMate data :=
  horizontalLiteralComponentMates_eq_outerCanonicalMate data

/-- The generated horizontal target alignment is pointwise exact. -/
theorem horizontalOuterMateTargetAlignment_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    IsIso (horizontalOuterMateTargetAlignment data) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  dsimp [horizontalOuterMateTargetAlignment]
  infer_instance

/-- Exactness of the aligned outer horizontal mate. -/
theorem horizontalAlignedOuterCanonicalMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    IsIso (horizontalAlignedOuterCanonicalMate data) := by
  letI : IsIso (bcProvenanceCanonicalMate
      (bcPastingNormalizedProvenance (.horizontal data))) :=
    bcProvenanceCanonicalMate_isIso _
  letI : IsIso (horizontalOuterMateTargetAlignment data) :=
    horizontalOuterMateTargetAlignment_isIso data
  unfold horizontalAlignedOuterCanonicalMate
  infer_instance

/-- Exactness of the aligned literal horizontal component mate is derived
from its equality with the exact aligned outer mate. -/
theorem horizontalAlignedLiteralComponentMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    IsIso (horizontalAlignedLiteralComponentMate data) := by
  rw [horizontalAlignedLiteralComponentMate_eq_outer]
  exact horizontalAlignedOuterCanonicalMate_isIso data

/-- The aligned literal horizontal component mate as a natural isomorphism. -/
noncomputable def horizontalAlignedLiteralComponentMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) := by
  letI : IsIso (horizontalAlignedLiteralComponentMate data) :=
    horizontalAlignedLiteralComponentMate_isIso data
  exact asIso (horizontalAlignedLiteralComponentMate data)

/-- The aligned outer horizontal canonical mate as a natural isomorphism. -/
noncomputable def horizontalAlignedOuterCanonicalMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) := by
  letI : IsIso (horizontalAlignedOuterCanonicalMate data) :=
    horizontalAlignedOuterCanonicalMate_isIso data
  exact asIso (horizontalAlignedOuterCanonicalMate data)

/-- The two horizontal natural-isomorphism presentations are equal, so all
downstream diagnostic comparisons use the reviewed outer mate equation. -/
theorem horizontalAlignedLiteralComponentMateIso_eq_outer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalAlignedLiteralComponentMateIso data =
      horizontalAlignedOuterCanonicalMateIso data := by
  apply Iso.ext
  exact horizontalAlignedLiteralComponentMate_eq_outer data

/-! ## Vertical aligned comparison -/

/-- The contravariant right-edge alignment used in the vertical target is
exact because both generated reindex adjunctions are equivalences. -/
theorem verticalNormalizedRightReindexAlignment_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    IsIso (verticalNormalizedRightReindexAlignment data) := by
  let outerAdj := coreTransportReindexAdjunction
    (bcPastingNormalizedProvenance
      (.vertical data)).rightProvenance.toRealizableHom
  let componentAdj := (bcRightAdjunction data.upperPresentation).comp
    (bcRightAdjunction data.lowerPresentation)
  letI : IsIso outerAdj.unit := coreTransportReindexUnit_isIso _
  letI : IsIso outerAdj.counit := coreTransportReindexCounit_isIso _
  letI : IsIso (bcRightAdjunction data.upperPresentation).unit :=
    coreTransportReindexUnit_isIso _
  letI : IsIso (bcRightAdjunction data.upperPresentation).counit :=
    coreTransportReindexCounit_isIso _
  letI : IsIso (bcRightAdjunction data.lowerPresentation).unit :=
    coreTransportReindexUnit_isIso _
  letI : IsIso (bcRightAdjunction data.lowerPresentation).counit :=
    coreTransportReindexCounit_isIso _
  letI : IsIso componentAdj.unit := by
    dsimp only [componentAdj]
    rw [Adjunction.comp_unit]
    infer_instance
  letI : IsIso componentAdj.counit := by
    dsimp only [componentAdj]
    rw [Adjunction.comp_counit]
    infer_instance
  unfold verticalNormalizedRightReindexAlignment
  exact conjugateEquiv_isIso_of_adjunction_isIso outerAdj componentAdj
    (verticalNormalizedRightTransportIso data).inv

/-- The generated vertical target alignment is pointwise exact. -/
theorem verticalMateTargetAlignment_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    IsIso (verticalMateTargetAlignment data) := by
  letI : IsIso (verticalNormalizedRightReindexAlignment data) :=
    verticalNormalizedRightReindexAlignment_isIso data
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  dsimp [verticalMateTargetAlignment]
  infer_instance

/-- Literal vertical component mates after the generated source alignment. -/
noncomputable def verticalAlignedLiteralComponentMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :=
  verticalMateSourceAlignment data ≫
    ((TwoSquare.mk _ _ _ _
      (coreBeckChevalleyMate data.lowerPresentation)) ≫ₕ
    (TwoSquare.mk _ _ _ _
      (coreBeckChevalleyMate data.upperPresentation))).natTrans

/-- The canonical outer vertical mate after the generated target alignment. -/
noncomputable def verticalAlignedOuterCanonicalMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :=
  bcProvenanceCanonicalMate
      (bcPastingNormalizedProvenance (.vertical data)) ≫
    verticalMateTargetAlignment data

/-- The Cycle 102 vertical literal mate equation in named aligned form. -/
theorem verticalAlignedLiteralComponentMate_eq_outer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalAlignedLiteralComponentMate data =
      verticalAlignedOuterCanonicalMate data :=
  verticalLiteralComponentMates_eq_outerCanonicalMate data

/-- Exactness of the aligned outer vertical mate. -/
theorem verticalAlignedOuterCanonicalMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    IsIso (verticalAlignedOuterCanonicalMate data) := by
  letI : IsIso (bcProvenanceCanonicalMate
      (bcPastingNormalizedProvenance (.vertical data))) :=
    bcProvenanceCanonicalMate_isIso _
  letI : IsIso (verticalMateTargetAlignment data) :=
    verticalMateTargetAlignment_isIso data
  unfold verticalAlignedOuterCanonicalMate
  infer_instance

/-- Exactness of the aligned literal vertical component mate is derived from
the reviewed outer equality. -/
theorem verticalAlignedLiteralComponentMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    IsIso (verticalAlignedLiteralComponentMate data) := by
  rw [verticalAlignedLiteralComponentMate_eq_outer]
  exact verticalAlignedOuterCanonicalMate_isIso data

/-- The aligned literal vertical component mate as a natural isomorphism. -/
noncomputable def verticalAlignedLiteralComponentMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) := by
  letI : IsIso (verticalAlignedLiteralComponentMate data) :=
    verticalAlignedLiteralComponentMate_isIso data
  exact asIso (verticalAlignedLiteralComponentMate data)

/-- The aligned outer vertical canonical mate as a natural isomorphism. -/
noncomputable def verticalAlignedOuterCanonicalMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) := by
  letI : IsIso (verticalAlignedOuterCanonicalMate data) :=
    verticalAlignedOuterCanonicalMate_isIso data
  exact asIso (verticalAlignedOuterCanonicalMate data)

/-- The two vertical natural-isomorphism presentations are equal. -/
theorem verticalAlignedLiteralComponentMateIso_eq_outer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalAlignedLiteralComponentMateIso data =
      verticalAlignedOuterCanonicalMateIso data := by
  apply Iso.ext
  exact verticalAlignedLiteralComponentMate_eq_outer data

/-! ## Direction-specific K4 predecessor packages -/

/-- Horizontal G-110(E) predecessor: actual outer-route `(d2)`--`(d6)`
factorization together with aligned-mate diagnostic naturality.  The fields
are deliberately not called K4 compatibility: the equation coupling the
successive component actions to the outer action is not yet present. -/
structure HorizontalPastedBCDiagnosticNaturalityPredecessor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) where
  outerRouteComposition :
    BCDiagnosticCompositionCompatibility incidence.toFiberwise
        (bcDiagnosticDirectFirstFunctor pasting.pastePresentation)
        (bcDiagnosticDirectSecondFunctor pasting.pastePresentation) ∧
      BCDiagnosticCompositionCompatibility incidence.toFiberwise
        (bcDiagnosticViaBaseFirstFunctor pasting.pastePresentation)
        (bcDiagnosticViaBaseSecondFunctor pasting.pastePresentation)
  alignedMateNaturality : FiberwiseDiagnosticNaturalIsoCompatibility
    incidence.toFiberwise _ _ (horizontalAlignedLiteralComponentMateIso pasting)
  alignedMate_eq_outer : horizontalAlignedLiteralComponentMateIso pasting =
    horizontalAlignedOuterCanonicalMateIso pasting

/-- Construct the horizontal naturality predecessor from the ordinary
interpretation and its generated southwest source-fiber incidence. -/
noncomputable def horizontalPastedBCDiagnosticNaturalityPredecessor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) :
    HorizontalPastedBCDiagnosticNaturalityPredecessor
      pasting interpretation incidence where
  outerRouteComposition := horizontalPastedBCDiagnosticCompositionCompatibility
    pasting interpretation incidence
  alignedMateNaturality := fiberwiseDiagnosticNaturalIsoCompatibility
    incidence.toFiberwise _ _ (horizontalAlignedLiteralComponentMateIso pasting)
  alignedMate_eq_outer := horizontalAlignedLiteralComponentMateIso_eq_outer pasting

/-- Vertical G-110(E) predecessor, parallel to the horizontal package. -/
structure VerticalPastedBCDiagnosticNaturalityPredecessor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) where
  outerRouteComposition :
    BCDiagnosticCompositionCompatibility incidence.toFiberwise
        (bcDiagnosticDirectFirstFunctor pasting.pastePresentation)
        (bcDiagnosticDirectSecondFunctor pasting.pastePresentation) ∧
      BCDiagnosticCompositionCompatibility incidence.toFiberwise
        (bcDiagnosticViaBaseFirstFunctor pasting.pastePresentation)
        (bcDiagnosticViaBaseSecondFunctor pasting.pastePresentation)
  alignedMateNaturality : FiberwiseDiagnosticNaturalIsoCompatibility
    incidence.toFiberwise _ _ (verticalAlignedLiteralComponentMateIso pasting)
  alignedMate_eq_outer : verticalAlignedLiteralComponentMateIso pasting =
    verticalAlignedOuterCanonicalMateIso pasting

/-- Construct the vertical naturality predecessor. -/
noncomputable def verticalPastedBCDiagnosticNaturalityPredecessor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) :
    VerticalPastedBCDiagnosticNaturalityPredecessor
      pasting interpretation incidence where
  outerRouteComposition := verticalPastedBCDiagnosticCompositionCompatibility
    pasting interpretation incidence
  alignedMateNaturality := fiberwiseDiagnosticNaturalIsoCompatibility
    incidence.toFiberwise _ _ (verticalAlignedLiteralComponentMateIso pasting)
  alignedMate_eq_outer := verticalAlignedLiteralComponentMateIso_eq_outer pasting

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
