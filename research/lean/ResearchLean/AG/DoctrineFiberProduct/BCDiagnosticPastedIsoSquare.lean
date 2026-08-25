import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticNaturalIsoSquare
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPastedNaturalIsoCompatibility

/-!
# Split pasted Beck--Chevalley diagnostic squares

The outer direct/via comparison and the successive component comparison are
kept as four separate sides.  Their reviewed mate equation generates a
commutative diagnostic square in both pasting directions.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence
open CategoryTheory.NatTrans CategoryTheory.TwoSquare

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 2000000

/-- Exact canonical mate as a named natural isomorphism. -/
noncomputable def coreBeckChevalleyMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) := by
  letI := coreBeckChevalleyMate_isIso presentation
  exact asIso (coreBeckChevalleyMate presentation)

/-! ## Horizontal four-side square -/

/-- Normalized outer direct route in the horizontal pasted square. -/
noncomputable def horizontalPastedOuterDirectFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
      (bcPastingNormalizedProvenance
        (.horizontal data)).leftProvenance.toRealizableHom ⋙
    coreFiberTransportFunctor
      (normalizedNestedPasteSquare (.horizontal data)).top

/-- Literal successive component direct route. -/
noncomputable def horizontalPastedComponentDirectFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation data.leftPresentation)) ⋙
    (coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcTopPresentation data.leftPresentation)) ⋙
      coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcTopPresentation data.rightPresentation)))

/-- Normalized outer via-base route. -/
noncomputable def horizontalPastedOuterViaFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  coreFiberTransportFunctor
      (normalizedNestedPasteSquare (.horizontal data)).bottom ⋙
    selectedCoreFiberReindexFunctor
      (bcPastingNormalizedProvenance
        (.horizontal data)).rightProvenance.toRealizableHom

/-- Literal successive component via-base route. -/
noncomputable def horizontalPastedComponentViaFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  (coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcBottomPresentation data.leftPresentation)) ⋙
    coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcBottomPresentation data.rightPresentation))) ⋙
    selectedCoreFiberReindexFunctor
      (bcPastingNormalizedProvenance
        (.horizontal data)).rightProvenance.toRealizableHom

/-- Literal horizontal component mates before the source alignment. -/
noncomputable def horizontalLiteralComponentMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalPastedComponentDirectFunctor data ⟶
      horizontalPastedComponentViaFunctor data :=
  ((TwoSquare.mk _ _ _ _
      (coreBeckChevalleyMate data.leftPresentation)) ≫ᵥ
    (TwoSquare.mk _ _ _ _
      (coreBeckChevalleyMate data.rightPresentation))).natTrans

theorem horizontalLiteralComponentMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    IsIso (horizontalLiteralComponentMate data) := by
  letI : IsIso (coreBeckChevalleyMate data.leftPresentation) :=
    coreBeckChevalleyMate_isIso _
  letI : IsIso (coreBeckChevalleyMate data.rightPresentation) :=
    coreBeckChevalleyMate_isIso _
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  let topRight := coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcTopPresentation data.rightPresentation))
  let bottomLeft := coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcBottomPresentation data.leftPresentation))
  letI : IsIso ((coreBeckChevalleyMate data.leftPresentation).app P) :=
    inferInstance
  letI : IsIso (topRight.map
      ((coreBeckChevalleyMate data.leftPresentation).app P)) :=
    inferInstance
  letI : IsIso ((coreBeckChevalleyMate data.rightPresentation).app
      (bottomLeft.obj P)) := inferInstance
  dsimp [horizontalLiteralComponentMate, TwoSquare.vComp,
    topRight, bottomLeft]
  simp only [Category.id_comp, Category.comp_id]
  exact IsIso.comp_isIso' (IsIso.id _)
    (IsIso.comp_isIso' inferInstance inferInstance)

theorem horizontalDataMateSourceAlignment_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    IsIso (horizontalDataMateSourceAlignment data) := by
  letI : IsIso (horizontalLiteralComponentMate data) :=
    horizontalLiteralComponentMate_isIso data
  letI : IsIso (horizontalDataMateSourceAlignment data ≫
      horizontalLiteralComponentMate data) := by
    have heq : horizontalDataMateSourceAlignment data ≫
        horizontalLiteralComponentMate data =
      horizontalAlignedLiteralComponentMate data := rfl
    rw [heq]
    exact horizontalAlignedLiteralComponentMate_isIso data
  exact IsIso.of_isIso_comp_right (horizontalDataMateSourceAlignment data)
    (horizontalLiteralComponentMate data)

noncomputable def horizontalDataMateSourceAlignmentIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalPastedOuterDirectFunctor data ≅
      horizontalPastedComponentDirectFunctor data := by
  letI := horizontalDataMateSourceAlignment_isIso data
  exact asIso (horizontalDataMateSourceAlignment data)

noncomputable def horizontalLiteralComponentMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalPastedComponentDirectFunctor data ≅
      horizontalPastedComponentViaFunctor data := by
  letI := horizontalLiteralComponentMate_isIso data
  exact asIso (horizontalLiteralComponentMate data)

noncomputable def horizontalOuterCanonicalMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalPastedOuterDirectFunctor data ≅
      horizontalPastedOuterViaFunctor data := by
  letI := bcProvenanceCanonicalMate_isIso
    (bcPastingNormalizedProvenance (.horizontal data))
  exact asIso (bcProvenanceCanonicalMate
    (bcPastingNormalizedProvenance (.horizontal data)))

noncomputable def horizontalOuterMateTargetAlignmentIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalPastedOuterViaFunctor data ≅
      horizontalPastedComponentViaFunctor data := by
  letI := horizontalOuterMateTargetAlignment_isIso data
  exact asIso (horizontalOuterMateTargetAlignment data)

/-- The reviewed horizontal mate equation as an exposed four-side square. -/
theorem horizontalPastedMateIsoSquare
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalDataMateSourceAlignmentIso data ≪≫
        horizontalLiteralComponentMateIso data =
      horizontalOuterCanonicalMateIso data ≪≫
        horizontalOuterMateTargetAlignmentIso data := by
  apply Iso.ext
  change horizontalAlignedLiteralComponentMate data =
    horizontalAlignedOuterCanonicalMate data
  exact horizontalAlignedLiteralComponentMate_eq_outer data

/-! ## Vertical four-side square -/

noncomputable def verticalPastedOuterDirectFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
      (bcPastingNormalizedProvenance
        (.vertical data)).leftProvenance.toRealizableHom ⋙
    coreFiberTransportFunctor
      (normalizedNestedPasteSquare (.vertical data)).top

noncomputable def verticalPastedComponentDirectFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :=
  (selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation data.lowerPresentation)) ⋙
    selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation data.upperPresentation))) ⋙
    coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcTopPresentation data.upperPresentation))

noncomputable def verticalPastedOuterViaFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :=
  coreFiberTransportFunctor
      (normalizedNestedPasteSquare (.vertical data)).bottom ⋙
    selectedCoreFiberReindexFunctor
      (bcPastingNormalizedProvenance
        (.vertical data)).rightProvenance.toRealizableHom

noncomputable def verticalPastedComponentViaFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :=
  coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcBottomPresentation data.lowerPresentation)) ⋙
    (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation data.lowerPresentation)) ⋙
      selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation data.upperPresentation)))

noncomputable def verticalLiteralComponentMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalPastedComponentDirectFunctor data ⟶
      verticalPastedComponentViaFunctor data :=
  ((TwoSquare.mk _ _ _ _
      (coreBeckChevalleyMate data.lowerPresentation)) ≫ₕ
    (TwoSquare.mk _ _ _ _
      (coreBeckChevalleyMate data.upperPresentation))).natTrans

/-- The literal horizontal composite of the lower and upper component mates,
constructed directly in the groupoid of functors. -/
noncomputable def verticalLiteralComponentMateIsoGenerated
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalPastedComponentDirectFunctor data ≅
      verticalPastedComponentViaFunctor data :=
  (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcLeftPresentation data.lowerPresentation)))
      (coreBeckChevalleyMateIso data.upperPresentation) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (coreBeckChevalleyMateIso data.lowerPresentation)
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation data.upperPresentation))) ≪≫
    (Functor.associator _ _ _)

theorem verticalLiteralComponentMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    IsIso (verticalLiteralComponentMate data) := by
  have heq : verticalLiteralComponentMate data =
      (verticalLiteralComponentMateIsoGenerated data).hom := rfl
  rw [heq]
  infer_instance

theorem verticalMateSourceAlignment_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    IsIso (verticalMateSourceAlignment data) := by
  letI : IsIso (verticalLiteralComponentMate data) :=
    verticalLiteralComponentMate_isIso data
  letI : IsIso (verticalMateSourceAlignment data ≫
      verticalLiteralComponentMate data) := by
    have heq : verticalMateSourceAlignment data ≫
        verticalLiteralComponentMate data =
      verticalAlignedLiteralComponentMate data := rfl
    rw [heq]
    exact verticalAlignedLiteralComponentMate_isIso data
  exact IsIso.of_isIso_comp_right (verticalMateSourceAlignment data)
    (verticalLiteralComponentMate data)

noncomputable def verticalMateSourceAlignmentIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalPastedOuterDirectFunctor data ≅
      verticalPastedComponentDirectFunctor data := by
  letI := verticalMateSourceAlignment_isIso data
  exact asIso (verticalMateSourceAlignment data)

noncomputable def verticalLiteralComponentMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalPastedComponentDirectFunctor data ≅
      verticalPastedComponentViaFunctor data := by
  exact verticalLiteralComponentMateIsoGenerated data

noncomputable def verticalOuterCanonicalMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalPastedOuterDirectFunctor data ≅
      verticalPastedOuterViaFunctor data := by
  letI := bcProvenanceCanonicalMate_isIso
    (bcPastingNormalizedProvenance (.vertical data))
  exact asIso (bcProvenanceCanonicalMate
    (bcPastingNormalizedProvenance (.vertical data)))

noncomputable def verticalMateTargetAlignmentIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalPastedOuterViaFunctor data ≅
      verticalPastedComponentViaFunctor data := by
  letI := verticalMateTargetAlignment_isIso data
  exact asIso (verticalMateTargetAlignment data)

/-- The reviewed vertical mate equation as an exposed four-side square. -/
theorem verticalPastedMateIsoSquare
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalMateSourceAlignmentIso data ≪≫
        verticalLiteralComponentMateIso data =
      verticalOuterCanonicalMateIso data ≪≫
        verticalMateTargetAlignmentIso data := by
  apply Iso.ext
  change verticalAlignedLiteralComponentMate data =
    verticalAlignedOuterCanonicalMate data
  exact verticalAlignedLiteralComponentMate_eq_outer data

/-! ## Generated diagnostic squares -/

noncomputable def horizontalPastedBCDiagnosticIsoSquareCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) :=
  fiberwiseDiagnosticNaturalIsoSquareCompatibility incidence.toFiberwise
    (horizontalDataMateSourceAlignmentIso pasting)
    (horizontalLiteralComponentMateIso pasting)
    (horizontalOuterCanonicalMateIso pasting)
    (horizontalOuterMateTargetAlignmentIso pasting)
    (horizontalPastedMateIsoSquare pasting)

noncomputable def verticalPastedBCDiagnosticIsoSquareCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) :=
  fiberwiseDiagnosticNaturalIsoSquareCompatibility incidence.toFiberwise
    (verticalMateSourceAlignmentIso pasting)
    (verticalLiteralComponentMateIso pasting)
    (verticalOuterCanonicalMateIso pasting)
    (verticalMateTargetAlignmentIso pasting)
    (verticalPastedMateIsoSquare pasting)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
