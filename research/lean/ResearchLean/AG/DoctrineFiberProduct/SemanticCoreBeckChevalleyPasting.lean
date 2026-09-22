import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreBeckChevalleyCleavage
import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreBeckChevalleyFactorization

/-! Pasting of semantic Beck--Chevalley squares. -/

namespace AAT.AG.DoctrineFiberProduct

universe u
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory
open CategoryTheory.Functor CategoryTheory.NatTrans
open AtomFoundation CrossStageCoherence
open CategoryTheory.TwoSquare

set_option maxHeartbeats 3000000

/-- Two horizontally composable exact pointed squares. -/
structure SemanticHorizontalPasting (U : AtomCarrier.{u}) where
  northwest : ExtractionInstance U
  northmiddle : ExtractionInstance U
  northeast : ExtractionInstance U
  southwest : ExtractionInstance U
  southmiddle : ExtractionInstance U
  southeast : ExtractionInstance U
  topLeft : northwest ⟶ northmiddle
  topRight : northmiddle ⟶ northeast
  bottomLeft : southwest ⟶ southmiddle
  bottomRight : southmiddle ⟶ southeast
  left : northwest ⟶ southwest
  middle : northmiddle ⟶ southmiddle
  right : northeast ⟶ southeast
  leftCommutes : topLeft ≫ middle = left ≫ bottomLeft
  rightCommutes : topRight ≫ right = middle ≫ bottomRight

namespace SemanticHorizontalPasting

def first {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    ExtInstSquare U where
  northwest := data.northwest
  northeast := data.northmiddle
  southwest := data.southwest
  southeast := data.southmiddle
  top := data.topLeft
  left := data.left
  right := data.middle
  bottom := data.bottomLeft
  commutes := data.leftCommutes.symm

def second {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    ExtInstSquare U where
  northwest := data.northmiddle
  northeast := data.northeast
  southwest := data.southmiddle
  southeast := data.southeast
  top := data.topRight
  left := data.middle
  right := data.right
  bottom := data.bottomRight
  commutes := data.rightCommutes.symm

def outer {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    ExtInstSquare U where
  northwest := data.northwest
  northeast := data.northeast
  southwest := data.southwest
  southeast := data.southeast
  top := data.topLeft ≫ data.topRight
  left := data.left
  right := data.right
  bottom := data.bottomLeft ≫ data.bottomRight
  commutes := by
    symm
    calc
      (data.topLeft ≫ data.topRight) ≫ data.right =
          data.topLeft ≫ (data.topRight ≫ data.right) := Category.assoc _ _ _
      _ = data.topLeft ≫ (data.middle ≫ data.bottomRight) :=
        congrArg (data.topLeft ≫ ·) data.rightCommutes
      _ = (data.topLeft ≫ data.middle) ≫ data.bottomRight :=
        (Category.assoc _ _ _).symm
      _ = (data.left ≫ data.bottomLeft) ≫ data.bottomRight :=
        congrArg (· ≫ data.bottomRight) data.leftCommutes
      _ = data.left ≫ (data.bottomLeft ≫ data.bottomRight) :=
        Category.assoc _ _ _

/-- Generic covariant horizontal pasting, aligned with the independently
generated outer square. -/
theorem transport_square_pasting
    {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    indexedHorizontalComponentRoute
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.leftCommutes.symm : IndexedBaseSquareTerm U
            data.topLeft data.left data.middle data.bottomLeft))
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.rightCommutes.symm : IndexedBaseSquareTerm U
            data.topRight data.middle data.right data.bottomRight)) =
      semanticCoreTransportSquareIso data.outer := by
  let first : ValidatedIndexedBaseSquare U
      data.topLeft data.left data.middle data.bottomLeft :=
    .ofTerm (.leaf data.leftCommutes.symm)
  let second : ValidatedIndexedBaseSquare U
      data.topRight data.middle data.right data.bottomRight :=
    .ofTerm (.leaf data.rightCommutes.symm)
  have h := indexedHorizontalPastingCoherence first second
  change indexedHorizontalComponentRoute first second =
    semanticCoreTransportSquareIso data.outer at h
  exact h

/-- The normalized mate of the pasted squares is the canonical mate of the
outer semantic square. -/
theorem mate_normalized_outer
    {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    (mateEquiv
      (semanticCoreTransportReindexAdjunction
        ⟨data.northwest, data.southwest, data.left⟩)
      (semanticCoreTransportReindexAdjunction
        ⟨data.northeast, data.southeast, data.right⟩)
      (indexedHorizontalComponentRoute
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.leftCommutes.symm : IndexedBaseSquareTerm U
            data.topLeft data.left data.middle data.bottomLeft))
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.rightCommutes.symm : IndexedBaseSquareTerm U
            data.topRight data.middle data.right data.bottomRight))).hom).natTrans =
      semanticCoreBeckChevalleyMate data.outer := by
  rw [transport_square_pasting]
  rfl

/-- The mate of the horizontal composite of covariant semantic squares is
the vertical composite of their generated mates. -/
theorem mate_pasting
    {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    (mateEquiv
      (semanticCoreTransportReindexAdjunction
        ⟨data.northwest, data.southwest, data.left⟩)
      (semanticCoreTransportReindexAdjunction
        ⟨data.northeast, data.southeast, data.right⟩)
      ((semanticCoreTransportSquareIso data.first).hom ≫ₕ
        (semanticCoreTransportSquareIso data.second).hom)) =
      (TwoSquare.mk _ _ _ _ (semanticCoreBeckChevalleyMate data.first)) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (semanticCoreBeckChevalleyMate data.second)) := by
  simpa only [semanticCoreBeckChevalleyMate] using
    mateEquiv_vcomp
      (semanticCoreTransportReindexAdjunction
        ⟨data.northwest, data.southwest, data.left⟩)
      (semanticCoreTransportReindexAdjunction
        ⟨data.northmiddle, data.southmiddle, data.middle⟩)
      (semanticCoreTransportReindexAdjunction
        ⟨data.northeast, data.southeast, data.right⟩)
      (semanticCoreTransportSquareIso data.first).hom
      (semanticCoreTransportSquareIso data.second).hom

/-- Mates commute with changing the top covariant functor. -/
private theorem mateEquiv_whiskerTop
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D]
    [Category.{v₃} E] [Category.{v₄} F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G G' : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (w : TwoSquare G' L₁ L₂ H) (change : G ⟶ G') :
    mateEquiv adj₁ adj₂ (w.whiskerTop change) =
      (mateEquiv adj₁ adj₂ w).whiskerRight change := by
  ext d
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerRight,
    TwoSquare.natTrans, Functor.comp_obj, Functor.comp_map,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightUnitor_inv_app, associator_hom_app, associator_inv_app,
    leftUnitor_hom_app, Functor.map_comp, Category.id_comp,
    Category.assoc]
  have hUnit : adj₂.unit.app (G.obj (R₁.obj d)) ≫
      R₂.map (L₂.map (change.app (R₁.obj d))) =
      change.app (R₁.obj d) ≫ adj₂.unit.app (G'.obj (R₁.obj d)) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (adj₂.unit.naturality (change.app (R₁.obj d))).symm
  simp only [← Category.assoc, hUnit]

/-- Mates commute with changing the bottom covariant functor. -/
private theorem mateEquiv_whiskerBottom
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D]
    [Category.{v₃} E] [Category.{v₄} F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H H' : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (w : TwoSquare G L₁ L₂ H) (change : H ⟶ H') :
    mateEquiv adj₁ adj₂ (w.whiskerBottom change) =
      (mateEquiv adj₁ adj₂ w).whiskerLeft change := by
  ext d
  simp only [mateEquiv_apply, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.natTrans, Functor.comp_obj, Functor.comp_map,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightUnitor_inv_app, associator_hom_app, associator_inv_app,
    leftUnitor_hom_app, Functor.map_comp, Category.id_comp,
    Category.assoc]
  have hChange : R₂.map (change.app (L₁.obj (R₁.obj d))) ≫
      R₂.map (H'.map (adj₁.counit.app d)) =
      R₂.map (H.map (adj₁.counit.app d)) ≫
        R₂.map (change.app d) := by
    simpa only [← Functor.map_comp] using
      congrArg R₂.map (change.naturality (adj₁.counit.app d)).symm
  simp only [← Category.assoc, hChange]
  simp [Category.assoc]

/-- The pasted mate is the composite of the component mates after the
transport compositors align the two-step and direct outer routes. -/
theorem mate_pasting_normalized
    {U : AtomCarrier.{u}} (data : SemanticHorizontalPasting U) :
    semanticCoreBeckChevalleyMate data.outer =
      (TwoSquare.whiskerLeft
        (TwoSquare.whiskerRight
          (TwoSquare.mk _ _ _ _ (semanticCoreBeckChevalleyMate data.first) ≫ᵥ
            TwoSquare.mk _ _ _ _ (semanticCoreBeckChevalleyMate data.second))
          (coreFiberCompositor data.topLeft data.topRight).hom)
        (coreFiberCompositor data.bottomLeft data.bottomRight).inv).natTrans := by
  let first := (semanticCoreTransportSquareIso data.first).hom
  let second := (semanticCoreTransportSquareIso data.second).hom
  let topComparison := (coreFiberCompositor data.topLeft data.topRight).hom
  let bottomComparison := (coreFiberCompositor data.bottomLeft data.bottomRight).inv
  let leftAdj := semanticCoreTransportReindexAdjunction
    (⟨data.northwest, data.southwest, data.left⟩ : CartSemanticInput U)
  let rightAdj := semanticCoreTransportReindexAdjunction
    (⟨data.northeast, data.southeast, data.right⟩ : CartSemanticInput U)
  let raw := first ≫ₕ second
  have firstAction : indexedSquareTermAction
      (ValidatedIndexedBaseSquare.ofTerm
        (.leaf data.leftCommutes.symm : IndexedBaseSquareTerm U
          data.topLeft data.left data.middle data.bottomLeft)) =
      semanticCoreTransportSquareIso data.first := by
    rfl
  have secondAction : indexedSquareTermAction
      (ValidatedIndexedBaseSquare.ofTerm
        (.leaf data.rightCommutes.symm : IndexedBaseSquareTerm U
          data.topRight data.middle data.right data.bottomRight)) =
      semanticCoreTransportSquareIso data.second := by
    rfl
  have houter : (semanticCoreTransportSquareIso data.outer).hom =
      (indexedHorizontalComponentRoute
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.leftCommutes.symm : IndexedBaseSquareTerm U
            data.topLeft data.left data.middle data.bottomLeft))
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.rightCommutes.symm : IndexedBaseSquareTerm U
            data.topRight data.middle data.right data.bottomRight))).hom :=
    congrArg Iso.hom (transport_square_pasting data).symm
  have hroute :
      (indexedHorizontalComponentRoute
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.leftCommutes.symm : IndexedBaseSquareTerm U
            data.topLeft data.left data.middle data.bottomLeft))
        (ValidatedIndexedBaseSquare.ofTerm
          (.leaf data.rightCommutes.symm : IndexedBaseSquareTerm U
            data.topRight data.middle data.right data.bottomRight))).hom =
      (raw.whiskerTop topComparison).whiskerBottom bottomComparison := by
    simp only [indexedHorizontalComponentRoute, firstAction, secondAction,
      Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      TwoSquare.mk, TwoSquare.natTrans, raw, first, second,
      topComparison, bottomComparison]
    simp only [SemanticHorizontalPasting.first, SemanticHorizontalPasting.second,
      Iso.symm_hom, Category.assoc]
  have normalized : (semanticCoreTransportSquareIso data.outer).hom =
      (raw.whiskerTop topComparison).whiskerBottom
        bottomComparison := by
    exact Eq.trans houter hroute
  have hmate := congrArg
    (fun square => (mateEquiv leftAdj rightAdj square).natTrans) normalized
  have hbottom := mateEquiv_whiskerBottom leftAdj rightAdj
    (raw.whiskerTop topComparison) bottomComparison
  have htop := mateEquiv_whiskerTop leftAdj rightAdj raw topComparison
  have halign : mateEquiv leftAdj rightAdj
        ((raw.whiskerTop topComparison).whiskerBottom bottomComparison) =
      TwoSquare.whiskerLeft
        ((mateEquiv leftAdj rightAdj raw).whiskerRight topComparison)
        bottomComparison :=
    hbottom.trans (congrArg (fun mate => mate.whiskerLeft bottomComparison) htop)
  have hraw : mateEquiv leftAdj rightAdj raw =
      TwoSquare.mk _ _ _ _ (semanticCoreBeckChevalleyMate data.first) ≫ᵥ
        TwoSquare.mk _ _ _ _ (semanticCoreBeckChevalleyMate data.second) :=
    mate_pasting data
  change (mateEquiv leftAdj rightAdj
      (semanticCoreTransportSquareIso data.outer).hom).natTrans = _
  calc
    _ = (mateEquiv leftAdj rightAdj
        ((raw.whiskerTop topComparison).whiskerBottom
          bottomComparison)).natTrans := hmate
    _ = (TwoSquare.whiskerLeft
        ((mateEquiv leftAdj rightAdj raw).whiskerRight topComparison)
        bottomComparison).natTrans :=
      congrArg TwoSquare.natTrans halign
    _ = _ := congrArg (fun mate =>
      ((mate.whiskerRight topComparison).whiskerLeft bottomComparison).natTrans) hraw


end SemanticHorizontalPasting

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
