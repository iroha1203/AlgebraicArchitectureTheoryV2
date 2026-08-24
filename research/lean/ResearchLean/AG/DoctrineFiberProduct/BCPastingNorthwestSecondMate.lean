import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingBottomAlignment
import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMate

/-!
# Northwest second-mate alignment for Beck--Chevalley pasting

The canonical outer pullback and the literal pasted pullback have canonically
isomorphic northwest objects.  This module turns the generated inverse
northwest transport comparison into its contravariant mate in both horizontal
and vertical pasting.  The resulting transformations align the outer selected
reindex functor with the component route after northwest transport.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence
open CategoryTheory.NatTrans CategoryTheory.TwoSquare

set_option maxHeartbeats 2000000

/-- The inverse horizontal northwest comparison followed by the component
left edge is the generated outer left edge. -/
theorem horizontalPasteNorthwest_inv_left_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    data.pasteNorthwestIso.inv ≫
        typedPresentationToSemantic
          (bcLeftPresentation data.leftPresentation) =
      typedPresentationToSemantic
        (bcLeftPresentation data.pastePresentation) := by
  have h : data.pasteNorthwestIso.inv ≫ data.nestedSquare.left =
      (toSemanticBC data.pastePresentation).square.left := by
    exact (Iso.inv_comp_eq data.pasteNorthwestIso).2
      data.pasteNorthwestIso_hom_left.symm
  simpa [HorizontalBCPastingData.nestedSquare] using h

/-- Generated covariant alignment square for the horizontal outer left edge. -/
noncomputable def horizontalPasteNorthwestLeftTransportIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    coreFiberTransportFunctor data.pasteNorthwestIso.inv ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcLeftPresentation data.leftPresentation)) ≅
      coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcLeftPresentation data.pastePresentation)) ⋙
        𝟭 (CoreFiber data.southwest.toSemantic) :=
  (coreFiberCompositor data.pasteNorthwestIso.inv
      (typedPresentationToSemantic
        (bcLeftPresentation data.leftPresentation))).symm ≪≫
    coreFiberTransportEqIso (horizontalPasteNorthwest_inv_left_eq data) ≪≫
    (coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcLeftPresentation data.pastePresentation))).rightUnitor.symm

/-- The horizontal covariant alignment as a square between generated
adjunctions. -/
noncomputable def horizontalPasteNorthwestLeftTransportSquare
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  TwoSquare.mk
    (coreFiberTransportFunctor data.pasteNorthwestIso.inv)
    (coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcLeftPresentation data.pastePresentation)))
    (coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcLeftPresentation data.leftPresentation)))
    (𝟭 (CoreFiber data.southwest.toSemantic))
    (horizontalPasteNorthwestLeftTransportIso data).hom

/-- The generated horizontal northwest second mate. -/
noncomputable def horizontalPasteNorthwestReindexAlignment
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.pastePresentation)) ⋙
        coreFiberTransportFunctor data.pasteNorthwestIso.inv ⟶
      (𝟭 (CoreFiber data.southwest.toSemantic)) ⋙
        selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.leftPresentation)) :=
  (mateEquiv
    (bcLeftAdjunction data.pastePresentation)
    (bcLeftAdjunction data.leftPresentation)
    (horizontalPasteNorthwestLeftTransportSquare data)).natTrans

/-- Horizontal northwest reindex alignment with the target identity removed. -/
noncomputable def horizontalPasteNorthwestReindexAlignmentNormalized
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.pastePresentation)) ⋙
        coreFiberTransportFunctor data.pasteNorthwestIso.inv ⟶
      selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation data.leftPresentation)) :=
  horizontalPasteNorthwestReindexAlignment data ≫
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (bcLeftPresentation data.leftPresentation))).leftUnitor.hom

/-- The inverse vertical northwest comparison followed by the literal pasted
left edge is the generated outer left edge. -/
theorem verticalPasteNorthwest_inv_left_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    data.pasteNorthwestIso.inv ≫ data.nestedSquare.left =
      typedPresentationToSemantic
        (bcLeftPresentation data.pastePresentation) := by
  exact (Iso.inv_comp_eq data.pasteNorthwestIso).2
    data.pasteNorthwestIso_hom_left.symm

/-- Generated covariant alignment square for the vertical outer left edge. -/
noncomputable def verticalPasteNorthwestLeftTransportIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    coreFiberTransportFunctor data.pasteNorthwestIso.inv ⋙
        (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcLeftPresentation data.upperPresentation)) ⋙
          coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcLeftPresentation data.lowerPresentation))) ≅
      coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcLeftPresentation data.pastePresentation)) ⋙
        𝟭 (CoreFiber data.southwest.toSemantic) :=
  (Functor.isoWhiskerLeft
      (coreFiberTransportFunctor data.pasteNorthwestIso.inv)
      (coreFiberCompositor
        (typedPresentationToSemantic
          (bcLeftPresentation data.upperPresentation))
        (typedPresentationToSemantic
          (bcLeftPresentation data.lowerPresentation))).symm).trans
    ((coreFiberCompositor data.pasteNorthwestIso.inv
      data.nestedSquare.left).symm.trans
        ((coreFiberTransportEqIso
          (verticalPasteNorthwest_inv_left_eq data)).trans
          (Functor.rightUnitor _).symm))

/-- The vertical covariant alignment as a square between generated
adjunctions. -/
noncomputable def verticalPasteNorthwestLeftTransportSquare
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    TwoSquare
      (coreFiberTransportFunctor data.pasteNorthwestIso.inv)
      (coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcLeftPresentation data.pastePresentation)))
      (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcLeftPresentation data.upperPresentation)) ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcLeftPresentation data.lowerPresentation)))
      (𝟭 (CoreFiber data.southwest.toSemantic)) :=
  TwoSquare.mk _ _ _ _ (verticalPasteNorthwestLeftTransportIso data).hom

/-- The generated vertical northwest second mate. -/
noncomputable def verticalPasteNorthwestReindexAlignment
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.pastePresentation)) ⋙
        coreFiberTransportFunctor data.pasteNorthwestIso.inv ⟶
      𝟭 (CoreFiber data.southwest.toSemantic) ⋙
        (selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcLeftPresentation data.lowerPresentation)) ⋙
          selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcLeftPresentation data.upperPresentation))) :=
  (mateEquiv
    (bcLeftAdjunction data.pastePresentation)
    ((bcLeftAdjunction data.upperPresentation).comp
      (bcLeftAdjunction data.lowerPresentation))
    (verticalPasteNorthwestLeftTransportSquare data)).natTrans

/-- Vertical northwest reindex alignment with the target identity removed. -/
noncomputable def verticalPasteNorthwestReindexAlignmentNormalized
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.pastePresentation)) ⋙
        coreFiberTransportFunctor data.pasteNorthwestIso.inv ⟶
      selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.lowerPresentation)) ⋙
        selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.upperPresentation)) :=
  verticalPasteNorthwestReindexAlignment data ≫
    (Functor.leftUnitor _).hom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
