import ResearchLean.AG.DoctrineFiberProduct.BCPastingTypedOuterComparisonEquality

/-!
# Component-to-outer Beck--Chevalley mate equations

This module proves that the horizontal and vertical composites of generated
component mates agree with the canonical mate of the independently generated
normalized outer square after the named source and target alignments.

## Implementation notes

The horizontal proof uses a direction-qualified northwest square whose source
is stated directly with `data.pasteNorthwestIso`.  The generic
direction-independent alias is normalized only after component expansion, so
dependent functor endpoints are never rewritten by an ill-typed motive.  A
named compositor-naturality lemma transports the complete top prefix, and a
functorial inverse cancellation closes the bottom alignment.  The vertical
equation then follows from the reviewed vertical outer equality and the
existing mate-composition normal form.  No caller coherence field or whole
adjunction cast is introduced.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence
open CategoryTheory.NatTrans CategoryTheory.TwoSquare

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Mating a square after generated top and bottom whiskering gives the
correspondingly whiskered mate.  This is an API lemma for both outer equations. -/
theorem mateEquiv_whiskerTopBottom_natTrans
    {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    {G G' : C ⥤ E} {H H' : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (w : TwoSquare G L₁ L₂ H)
    (α : G' ⟶ G) (β : H ⟶ H') :
    ((mateEquiv adj₁ adj₂
      ((w.whiskerTop α).whiskerBottom β)).natTrans) =
      Functor.whiskerLeft R₁ α ≫
        (mateEquiv adj₁ adj₂ w).natTrans ≫
        Functor.whiskerRight β R₂ := by
  apply NatTrans.ext
  funext X
  simp [mateEquiv]
  rw [← R₂.map_comp, ← β.naturality, R₂.map_comp]

/-- Top and right whiskering of a `TwoSquare` commute. -/
theorem twoSquare_whiskerTop_whiskerRight
    {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {G G' : A ⥤ C} {H : B ⥤ D}
    {L₁ : A ⥤ B} {L₂ L₃ : C ⥤ D}
    (w : TwoSquare G L₁ L₂ H) (α : G' ⟶ G) (β : L₃ ⟶ L₂) :
    (w.whiskerTop α).whiskerRight β =
      (w.whiskerRight β).whiskerTop α := by
  apply NatTrans.ext
  funext X
  simp

/-- A functor sends a four-arrow cyclic inverse composition to an identity. -/
theorem functor_map_comp4_eq_id
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X₀ X₁ X₂ X₃ : C}
    (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂)
    (f₃ : X₂ ⟶ X₃) (f₄ : X₃ ⟶ X₀)
    (h : f₁ ≫ f₂ ≫ f₃ ≫ f₄ = 𝟙 X₀) :
    F.map f₁ ≫ F.map f₂ ≫ F.map f₃ ≫ F.map f₄ = 𝟙 (F.obj X₀) := by
  simpa only [F.map_comp, F.map_id] using congrArg F.map h

/-- A functor cancels two nested isomorphism inverses against their homs. -/
theorem functor_map_iso_inv_inv_hom_hom
    {C D : Type*} [Category C] [Category D]
    (F : Functor C D) {X₀ X₁ X₂ : C}
    (e₁ : X₀ ≅ X₁) (e₂ : X₁ ≅ X₂) :
    F.map e₂.inv ≫ F.map e₁.inv ≫
        F.map e₁.hom ≫ F.map e₂.hom = 𝟙 _ := by
  apply functor_map_comp4_eq_id
  simp

/-- Pointwise form of nested natural-isomorphism cancellation under a
functor. -/
theorem functor_map_natIso_inv_inv_hom_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : Functor D E) {G₀ G₁ G₂ : Functor C D}
    (e₁ : G₀ ≅ G₁) (e₂ : G₁ ≅ G₂) (X : C) :
    F.map (e₂.inv.app X) ≫ F.map (e₁.inv.app X) ≫
        F.map (e₁.hom.app X) ≫ F.map (e₂.hom.app X) = 𝟙 _ := by
  exact functor_map_iso_inv_inv_hom_hom F (e₁.app X) (e₂.app X)

/-- Equality transport along a symmetric edge equality is the inverse of the
forward transport isomorphism. -/
theorem coreFiberTransportEqIso_symm
    {U : AtomCarrier.{u}} {W X : ExtractionInstance U}
    {first second : W ⟶ X} (edge_eq : first = second) :
    coreFiberTransportEqIso edge_eq.symm =
      (coreFiberTransportEqIso edge_eq).symm := by
  subst edge_eq
  rfl

/-- Target alignment from the normalized horizontal outer mate to the literal
component-mate bottom route. -/
noncomputable def horizontalOuterMateTargetAlignment
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).bottom ⋙
        selectedCoreFiberReindexFunctor
          (bcPastingNormalizedProvenance
            (.horizontal data)).rightProvenance.toRealizableHom ⟶
      (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation data.leftPresentation)) ⋙
        coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation data.rightPresentation))) ⋙
        selectedCoreFiberReindexFunctor
          (bcPastingNormalizedProvenance
            (.horizontal data)).rightProvenance.toRealizableHom :=
  Functor.whiskerRight
    ((coreFiberTransportEqIso
        (horizontalBCPastingNormalizedBottom_eq data)).trans
      (coreFiberCompositor
        (typedPresentationToSemantic
          (bcBottomPresentation data.leftPresentation))
        (typedPresentationToSemantic
          (bcBottomPresentation data.rightPresentation)))).hom
    (selectedCoreFiberReindexFunctor
      (bcPastingNormalizedProvenance
        (.horizontal data)).rightProvenance.toRealizableHom)

/-- Direction-qualified top compositor for horizontal pasted data.  Its public
type uses `data.pasteNorthwestIso` directly. -/
noncomputable def horizontalDataNormalizedTopCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    coreFiberTransportFunctor
        (normalizedNestedPasteSquare (.horizontal data)).top ≅
      coreFiberTransportFunctor data.pasteNorthwestIso.inv ⋙
        coreFiberTransportFunctor
          ((toSemanticBC data.leftPresentation).square.top ≫
            (toSemanticBC data.rightPresentation).square.top) :=
  horizontalBCPastingNormalizedTopCompositor data

/-- Direction-qualified northwest reindex alignment generated by the second
mate on horizontal pasted data. -/
noncomputable def horizontalDataNormalizedNorthwestReindexAlignment
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  ((mateEquiv
    (coreTransportReindexAdjunction
      (bcPastingNormalizedProvenance
        (.horizontal data)).leftProvenance.toRealizableHom)
    (bcLeftAdjunction data.leftPresentation)
    (TwoSquare.mk _ _ _ _
      ((horizontalBCPastingNormalizedLeftCompositor data).inv ≫
        (coreFiberTransportFunctor
          (normalizedNestedPasteSquare
            (.horizontal data)).left).rightUnitor.inv))).natTrans) ≫
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation data.leftPresentation))).leftUnitor.hom

/-- Exact direction-qualified source alignment from the normalized horizontal
outer mate to the literal component-mate source. -/
noncomputable def horizontalDataMateSourceAlignment
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    selectedCoreFiberReindexFunctor
          (bcPastingNormalizedProvenance
            (.horizontal data)).leftProvenance.toRealizableHom ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).top ⟶
      selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.leftPresentation)) ⋙
        (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation data.leftPresentation)) ⋙
          coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation data.rightPresentation))) :=
  Functor.whiskerLeft
      (selectedCoreFiberReindexFunctor
        (bcPastingNormalizedProvenance
          (.horizontal data)).leftProvenance.toRealizableHom)
      (horizontalDataNormalizedTopCompositor data).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (horizontalDataNormalizedNorthwestReindexAlignment data)
      (coreFiberTransportFunctor
        ((toSemanticBC data.leftPresentation).square.top ≫
          (toSemanticBC data.rightPresentation).square.top)) ≫
    Functor.whiskerLeft
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation data.leftPresentation)))
      (coreFiberCompositor
        (typedPresentationToSemantic
          (bcTopPresentation data.leftPresentation))
        (typedPresentationToSemantic
          (bcTopPresentation data.rightPresentation))).hom

/-- The direction-qualified horizontal northwest covariant square, stated on
the exact `data.pasteNorthwestIso` endpoint. -/
noncomputable def horizontalDataNormalizedNorthwestLeftTransportSquare
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    TwoSquare
      (coreFiberTransportFunctor data.pasteNorthwestIso.inv)
      (coreFiberTransportFunctor
        (normalizedNestedPasteSquare (.horizontal data)).left)
      (coreFiberTransportFunctor
        (toSemanticBC data.leftPresentation).square.left)
      (Functor.id (CoreFiber
        (normalizedNestedPasteSquare (.horizontal data)).southwest)) :=
  TwoSquare.mk _ _ _ _
    ((horizontalBCPastingNormalizedLeftCompositor data).inv ≫
      (coreFiberTransportFunctor
        (normalizedNestedPasteSquare (.horizontal data)).left).rightUnitor.inv)

/-- Direction-qualified northwest square pasted with both literal horizontal
component squares. -/
noncomputable def horizontalDataTypedRawComparisonSquare
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  horizontalDataNormalizedNorthwestLeftTransportSquare data ≫ₕ
    ((bcCoreTransportSquareIso data.leftPresentation).hom ≫ₕ
      (bcCoreTransportSquareIso data.rightPresentation).hom)

/-- Direction-qualified horizontal typed outer comparison normal form. -/
noncomputable def horizontalDataTypedOuterComparisonNormalForm
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :=
  ((horizontalDataTypedRawComparisonSquare data).whiskerTop
    (horizontalOuterTopToTypedComponents data)).whiskerBottom
      (horizontalTypedComponentsToOuterBottom data)

/-- The direction-qualified and existing typed horizontal outer normal forms
carry the same natural transformation. -/
theorem horizontalDataTypedOuterComparisonNormalForm_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    (horizontalDataTypedOuterComparisonNormalForm data).natTrans =
      horizontalTypedOuterComparisonNatTrans data := by
  rfl

/-- The direction-qualified horizontal outer normal form equals the reviewed
outer boundary comparison. -/
theorem horizontalDataTypedOuterComparisonNatTrans_eq_outer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    (horizontalDataTypedOuterComparisonNormalForm data).natTrans =
      (horizontalBCPastingOuterBoundaryComparison data).hom := by
  rw [horizontalDataTypedOuterComparisonNormalForm_eq]
  exact horizontalTypedOuterComparisonNatTrans_eq_outer data

/-- The mate of the direction-qualified northwest-plus-component square is
the vertical composition of the generated northwest and component mates. -/
theorem horizontalDataNormalizedNorthwest_mateEquiv_vcomp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    (mateEquiv
      (coreTransportReindexAdjunction
        (bcPastingNormalizedProvenance
          (.horizontal data)).leftProvenance.toRealizableHom)
      (bcRightAdjunction data.rightPresentation)
      (horizontalDataTypedRawComparisonSquare data)) =
      (mateEquiv
        (coreTransportReindexAdjunction
          (bcPastingNormalizedProvenance
            (.horizontal data)).leftProvenance.toRealizableHom)
        (bcLeftAdjunction data.leftPresentation)
        (horizontalDataNormalizedNorthwestLeftTransportSquare data)) ≫ᵥ
      (mateEquiv
        (bcLeftAdjunction data.leftPresentation)
        (bcRightAdjunction data.rightPresentation)
        ((bcCoreTransportSquareIso data.leftPresentation).hom ≫ₕ
          (bcCoreTransportSquareIso data.rightPresentation).hom)) := by
  exact mateEquiv_vcomp _ _ _ _ _

/-- Naturality of the horizontal top compositor on the exact unit followed by
the direction-qualified northwest comparison component. -/
theorem horizontalMateTopCompositor_naturality_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (X : CoreFiber
      (bcPastingNormalizedProvenance
        (.horizontal data)).leftProvenance.toRealizableHom.semantic.target) :
    (coreFiberTransportFunctor
        ((toSemanticBC data.leftPresentation).square.top ≫
          (toSemanticBC data.rightPresentation).square.top)).map
      ((bcLeftAdjunction data.leftPresentation).unit.app
        ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
          ((selectedCoreFiberReindexFunctor
            (bcPastingNormalizedProvenance
              (.horizontal data)).leftProvenance.toRealizableHom).obj X))) ≫
    (coreFiberTransportFunctor
        ((toSemanticBC data.leftPresentation).square.top ≫
          (toSemanticBC data.rightPresentation).square.top)).map
      ((selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation data.leftPresentation))).map
        ((horizontalBCPastingNormalizedLeftCompositor data).inv.app
          ((selectedCoreFiberReindexFunctor
            (bcPastingNormalizedProvenance
              (.horizontal data)).leftProvenance.toRealizableHom).obj X))) ≫
    (coreFiberCompositor
      (typedPresentationToSemantic
        (bcTopPresentation data.leftPresentation))
      (typedPresentationToSemantic
        (bcTopPresentation data.rightPresentation))).hom.app
        ((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.leftPresentation))).obj
          ((coreFiberTransportFunctor
            (bcPastingNormalizedProvenance
              (.horizontal data)).leftProvenance.toRealizableHom.semantic.hom).obj
            ((selectedCoreFiberReindexFunctor
              (bcPastingNormalizedProvenance
                (.horizontal data)).leftProvenance.toRealizableHom).obj X))) =
    (coreFiberCompositor
      (typedPresentationToSemantic
        (bcTopPresentation data.leftPresentation))
      (typedPresentationToSemantic
        (bcTopPresentation data.rightPresentation))).hom.app
        ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
          ((selectedCoreFiberReindexFunctor
            (bcPastingNormalizedProvenance
              (.horizontal data)).leftProvenance.toRealizableHom).obj X)) ≫
    (coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcTopPresentation data.rightPresentation))).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcTopPresentation data.leftPresentation))).map
        ((bcLeftAdjunction data.leftPresentation).unit.app
          ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
            ((selectedCoreFiberReindexFunctor
              (bcPastingNormalizedProvenance
                (.horizontal data)).leftProvenance.toRealizableHom).obj X)))) ≫
    (coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcTopPresentation data.rightPresentation))).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcTopPresentation data.leftPresentation))).map
        ((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.leftPresentation))).map
          ((horizontalBCPastingNormalizedLeftCompositor data).inv.app
            ((selectedCoreFiberReindexFunctor
              (bcPastingNormalizedProvenance
                (.horizontal data)).leftProvenance.toRealizableHom).obj X)))) := by
  rw [← Category.assoc]
  rw [← (coreFiberTransportFunctor
    ((toSemanticBC data.leftPresentation).square.top ≫
      (toSemanticBC data.rightPresentation).square.top)).map_comp]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    (coreFiberCompositor
      (typedPresentationToSemantic
        (bcTopPresentation data.leftPresentation))
      (typedPresentationToSemantic
        (bcTopPresentation data.rightPresentation))).hom.naturality
      ((bcLeftAdjunction data.leftPresentation).unit.app
          ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
            ((selectedCoreFiberReindexFunctor
              (bcPastingNormalizedProvenance
                (.horizontal data)).leftProvenance.toRealizableHom).obj X)) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation data.leftPresentation))).map
          ((horizontalBCPastingNormalizedLeftCompositor data).inv.app
            ((selectedCoreFiberReindexFunctor
              (bcPastingNormalizedProvenance
                (.horizontal data)).leftProvenance.toRealizableHom).obj X)))

/-- The aligned horizontal composite mate equals the canonical mate of the
independently generated normalized outer square. -/
theorem horizontalComponentMate_eq_outerCanonicalMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalDataMateSourceAlignment data ≫
        (mateEquiv
          (bcLeftAdjunction data.leftPresentation)
          (bcRightAdjunction data.rightPresentation)
          ((bcCoreTransportSquareIso data.leftPresentation).hom ≫ₕ
            (bcCoreTransportSquareIso data.rightPresentation).hom)).natTrans =
      bcProvenanceCanonicalMate
          (bcPastingNormalizedProvenance (.horizontal data)) ≫
        horizontalOuterMateTargetAlignment data := by
  rw [horizontalBCPastingOuterCanonicalMate_eq]
  rw [← horizontalDataTypedOuterComparisonNatTrans_eq_outer]
  unfold horizontalDataTypedOuterComparisonNormalForm
  rw [mateEquiv_whiskerTopBottom_natTrans]
  have hright :
      coreTransportReindexAdjunction
          (bcPastingNormalizedProvenance
            (.horizontal data)).rightProvenance.toRealizableHom =
        bcRightAdjunction data.rightPresentation := by
    rfl
  have hraw := horizontalDataNormalizedNorthwest_mateEquiv_vcomp data
  have hrawOuter :
      (mateEquiv
        (coreTransportReindexAdjunction
          (bcPastingNormalizedProvenance
            (.horizontal data)).leftProvenance.toRealizableHom)
        (coreTransportReindexAdjunction
          (bcPastingNormalizedProvenance
            (.horizontal data)).rightProvenance.toRealizableHom)
        (horizontalDataTypedRawComparisonSquare data)) =
      (mateEquiv
        (coreTransportReindexAdjunction
          (bcPastingNormalizedProvenance
            (.horizontal data)).leftProvenance.toRealizableHom)
        (bcLeftAdjunction data.leftPresentation)
        (horizontalDataNormalizedNorthwestLeftTransportSquare data)) ≫ᵥ
      (mateEquiv
        (bcLeftAdjunction data.leftPresentation)
        (bcRightAdjunction data.rightPresentation)
        ((bcCoreTransportSquareIso data.leftPresentation).hom ≫ₕ
          (bcCoreTransportSquareIso data.rightPresentation).hom)) := by
    simpa only [hright] using hraw
  rw [congrArg TwoSquare.natTrans hrawOuter]
  unfold horizontalOuterMateTargetAlignment
  apply NatTrans.ext
  funext X
  unfold horizontalDataMateSourceAlignment
  unfold horizontalDataNormalizedTopCompositor
  unfold horizontalDataNormalizedNorthwestReindexAlignment
  rw [horizontalOuterTopToTypedComponents_eq]
  rw [horizontalTypedComponentsToOuterBottom_eq]
  rw [coreFiberTransportEqIso_symm
    (horizontalBCPastingNormalizedBottom_eq data)]
  have hcancel := functor_map_natIso_inv_inv_hom_hom
    (selectedCoreFiberReindexFunctor
      (bcPastingNormalizedProvenance
        (.horizontal data)).rightProvenance.toRealizableHom)
    (coreFiberTransportEqIso
      (horizontalBCPastingNormalizedBottom_eq data))
    (coreFiberCompositor
      (typedPresentationToSemantic
        (bcBottomPresentation data.leftPresentation))
      (typedPresentationToSemantic
        (bcBottomPresentation data.rightPresentation))) X
  simp
  simp only [bcPastingNorthwestIso]
  simp [horizontalDataNormalizedNorthwestLeftTransportSquare]
  slice_lhs 1 3 =>
    rw [horizontalMateTopCompositor_naturality_app]
  rw [hcancel]
  simp

/-- The literal mate of the vertically composed generated component squares,
named so downstream alignment theorems do not repeatedly normalize its
dependent functor boundary. -/
noncomputable def verticalComponentMateNatTrans
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :=
  (mateEquiv
    ((bcLeftAdjunction data.upperPresentation).comp
      (bcLeftAdjunction data.lowerPresentation))
    ((bcRightAdjunction data.upperPresentation).comp
      (bcRightAdjunction data.lowerPresentation))
    ((TwoSquare.mk _ _ _ _
      (bcCoreTransportSquareIso data.upperPresentation).hom) ≫ᵥ
    (TwoSquare.mk _ _ _ _
      (bcCoreTransportSquareIso data.lowerPresentation).hom))).natTrans

/-- The generated vertical bottom transport and the mutually inverse
right-adjoint conjugates cancel before component expansion. -/
theorem verticalMateTargetCancellation
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    Functor.whiskerRight
        (coreFiberTransportEqIso
          (verticalNormalizedBottom_eq data)).inv
        (selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcRightPresentation data.lowerPresentation)) ⋙
          selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcRightPresentation data.upperPresentation))) ≫
      Functor.whiskerRight
        (coreFiberTransportEqIso
          (verticalNormalizedBottom_eq data)).hom
        (selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcRightPresentation data.lowerPresentation)) ⋙
          selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcRightPresentation data.upperPresentation))) ≫
      Functor.whiskerLeft
        (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation data.lowerPresentation)))
        ((conjugateEquiv
          ((bcRightAdjunction data.upperPresentation).comp
            (bcRightAdjunction data.lowerPresentation))
          (coreTransportReindexAdjunction
            (bcPastingNormalizedProvenance
              (.vertical data)).rightProvenance.toRealizableHom))
          (verticalNormalizedRightTransportIso data).hom) ≫
      Functor.whiskerLeft
        (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcBottomPresentation data.lowerPresentation)))
        ((conjugateEquiv
          (coreTransportReindexAdjunction
            (bcPastingNormalizedProvenance
              (.vertical data)).rightProvenance.toRealizableHom)
          ((bcRightAdjunction data.upperPresentation).comp
            (bcRightAdjunction data.lowerPresentation)))
          (verticalNormalizedRightTransportIso data).inv) = 𝟙 _ := by
  have hrightCancel :
      (conjugateEquiv
          ((bcRightAdjunction data.upperPresentation).comp
            (bcRightAdjunction data.lowerPresentation))
          (coreTransportReindexAdjunction
            (bcPastingNormalizedProvenance
              (.vertical data)).rightProvenance.toRealizableHom)
          (verticalNormalizedRightTransportIso data).hom) ≫
        (conjugateEquiv
          (coreTransportReindexAdjunction
            (bcPastingNormalizedProvenance
              (.vertical data)).rightProvenance.toRealizableHom)
          ((bcRightAdjunction data.upperPresentation).comp
            (bcRightAdjunction data.lowerPresentation))
          (verticalNormalizedRightTransportIso data).inv) = 𝟙 _ := by
    apply conjugateEquiv_comm
    exact (verticalNormalizedRightTransportIso data).inv_hom_id
  rw [← Category.assoc, ← Functor.whiskerRight_comp]
  simp only [Iso.inv_hom_id]
  rw [← Functor.whiskerLeft_comp, hrightCancel]
  simp

/-- The mate-law normal form obtained from the typed vertical outer square,
before the external source and target alignments are cancelled. -/
noncomputable def verticalDecomposedOuterMateNatTrans
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :=
  Functor.whiskerLeft
      (selectedCoreFiberReindexFunctor
        (bcPastingNormalizedProvenance
          (.vertical data)).leftProvenance.toRealizableHom)
      (verticalBCPastingNormalizedTopCompositor data).hom ≫
    ((((mateEquiv
          (coreTransportReindexAdjunction
            (bcPastingNormalizedProvenance
              (.vertical data)).leftProvenance.toRealizableHom)
          ((bcLeftAdjunction data.upperPresentation).comp
            (bcLeftAdjunction data.lowerPresentation))
          (verticalNormalizedNorthwestLeftTransportSquare data)) ≫ᵥ
        (mateEquiv
          ((bcLeftAdjunction data.upperPresentation).comp
            (bcLeftAdjunction data.lowerPresentation))
          ((bcRightAdjunction data.upperPresentation).comp
            (bcRightAdjunction data.lowerPresentation))
          ((TwoSquare.mk _ _ _ _
            (bcCoreTransportSquareIso data.upperPresentation).hom) ≫ᵥ
          (TwoSquare.mk _ _ _ _
            (bcCoreTransportSquareIso data.lowerPresentation).hom)))).whiskerBottom
        ((conjugateEquiv
          ((bcRightAdjunction data.upperPresentation).comp
            (bcRightAdjunction data.lowerPresentation))
          (coreTransportReindexAdjunction
            (bcPastingNormalizedProvenance
              (.vertical data)).rightProvenance.toRealizableHom))
          (verticalNormalizedRightTransportIso data).hom)).natTrans ≫
      Functor.whiskerRight
        ((Functor.leftUnitor
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation data.lowerPresentation)))).hom ≫
          (coreFiberTransportEqIso
            (verticalNormalizedBottom_eq data)).inv)
        (selectedCoreFiberReindexFunctor
          (bcPastingNormalizedProvenance
            (.vertical data)).rightProvenance.toRealizableHom))

/-- The vertical source and target alignments cancel around the decomposed
outer mate.  This isolates categorical coherence from the mate-law rewrite. -/
theorem verticalDecomposedMateAlignment
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalMateSourceAlignment data ≫
        verticalComponentMateNatTrans data =
      verticalDecomposedOuterMateNatTrans data ≫
        verticalMateTargetAlignment data := by
  unfold verticalComponentMateNatTrans
  unfold verticalDecomposedOuterMateNatTrans
  have htailCancel := verticalMateTargetCancellation data
  simp only [verticalMateSourceAlignment,
    verticalNormalizedNorthwestReindexAlignment,
    verticalMateTargetAlignment,
    verticalNormalizedRightReindexAlignment,
    TwoSquare.whiskerBottom,
    TwoSquare.vComp,
    Category.assoc,
    Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp_whiskerRight_assoc]
  rw [htailCancel]
  simp only [Category.comp_id]
  apply NatTrans.ext
  funext X
  simp
  rfl

/-- Mate laws identify the typed vertical outer mate with the named
decomposed mate normal form, independently of external alignments. -/
theorem verticalTypedOuterMate_eq_decomposed
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    (mateEquiv
        (coreTransportReindexAdjunction
          (bcPastingNormalizedProvenance
            (.vertical data)).leftProvenance.toRealizableHom)
        (coreTransportReindexAdjunction
          (bcPastingNormalizedProvenance
            (.vertical data)).rightProvenance.toRealizableHom)
        (verticalTypedOuterComparisonNormalForm data)).natTrans =
      verticalDecomposedOuterMateNatTrans data := by
  unfold verticalDecomposedOuterMateNatTrans
  rw [verticalTypedOuterComparisonNormalForm_eq]
  rw [twoSquare_whiskerTop_whiskerRight]
  rw [mateEquiv_whiskerTopBottom_natTrans]
  have hright := mateEquiv_conjugateEquiv_vcomp
    (coreTransportReindexAdjunction
      (bcPastingNormalizedProvenance
        (.vertical data)).leftProvenance.toRealizableHom)
    ((bcRightAdjunction data.upperPresentation).comp
      (bcRightAdjunction data.lowerPresentation))
    (coreTransportReindexAdjunction
      (bcPastingNormalizedProvenance
        (.vertical data)).rightProvenance.toRealizableHom)
    (verticalTypedRawComparisonSquare data)
    (verticalNormalizedRightTransportIso data).hom
  rw [congrArg TwoSquare.natTrans hright]
  have hraw := verticalNormalizedNorthwest_mateEquiv_vcomp data
  have hrawWhiskered := congrArg
    (fun w => w.whiskerBottom
      ((conjugateEquiv
        ((bcRightAdjunction data.upperPresentation).comp
          (bcRightAdjunction data.lowerPresentation))
        (coreTransportReindexAdjunction
          (bcPastingNormalizedProvenance
            (.vertical data)).rightProvenance.toRealizableHom))
          (verticalNormalizedRightTransportIso data).hom)) hraw
  rw [congrArg TwoSquare.natTrans hrawWhiskered]

/-- The aligned vertical component mate equals the mate of the typed outer
normal form.  This is the algebraic core of the canonical-outer equation. -/
theorem verticalComponentMate_eq_typedOuterNormalFormMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalMateSourceAlignment data ≫
        verticalComponentMateNatTrans data =
      (mateEquiv
          (coreTransportReindexAdjunction
            (bcPastingNormalizedProvenance
              (.vertical data)).leftProvenance.toRealizableHom)
          (coreTransportReindexAdjunction
            (bcPastingNormalizedProvenance
              (.vertical data)).rightProvenance.toRealizableHom)
          (verticalTypedOuterComparisonNormalForm data)).natTrans ≫
        verticalMateTargetAlignment data := by
  rw [verticalDecomposedMateAlignment]
  rw [verticalTypedOuterMate_eq_decomposed]

/-- The aligned vertical composite mate equals the canonical mate of the
independently generated normalized outer square. -/
theorem verticalComponentMate_eq_outerCanonicalMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalMateSourceAlignment data ≫
        verticalComponentMateNatTrans data =
      bcProvenanceCanonicalMate
          (bcPastingNormalizedProvenance (.vertical data)) ≫
        verticalMateTargetAlignment data := by
  rw [verticalBCPastingOuterCanonicalMate_eq]
  rw [← verticalTypedOuterComparisonNormalForm_eq_outer]
  exact verticalComponentMate_eq_typedOuterNormalFormMate data

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
