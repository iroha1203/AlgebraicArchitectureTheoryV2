import Formal.SHIGURE.Part2.Schemes.FppfDescentBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Iterated base change for fppf descent data

The two descriptions of a composite base change use different pullback
schemes. This file compares those actual charts and the induced descent
functors; no effectivity assumption is needed.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {X Y Z : Scheme.{u}} (cover : FppfCover.{u,v} X)
  (g : Y ⟶ X) (h : Z ⟶ Y)

/-- The iterated pullback chart and the pullback along the composite. -/
def compositeBaseChangeChart (i : cover.I₀) :
    ((cover.pullback₁ g).pullback₁ h).X i ≅ (cover.pullback₁ (h ≫ g)).X i :=
  pullbackRightPullbackFstIso g (cover.f i) h

private theorem compositeBaseChangeChart_square (i : cover.I₀) :
    (compositeBaseChangeChart cover g h i).hom ≫ (cover.pullback₁ (h ≫ g)).f i =
      ((cover.pullback₁ g).pullback₁ h).f i ≫ 𝟙 Z :=
  (pullbackRightPullbackFstIso_hom_fst g (cover.f i) h).trans (Category.comp_id _).symm

/-- Reindex descent data along the canonical isomorphisms of the charts. -/
def compositeBaseChangeCharts :
    FppfModuleDescentData (cover.pullback₁ (h ≫ g)) ⥤
      FppfModuleDescentData ((cover.pullback₁ g).pullback₁ h) :=
  DescentData.pullFunctor Q (p := 𝟙 Z) (α := id)
    (p' := fun i => (compositeBaseChangeChart cover g h i).hom)
    (compositeBaseChangeChart_square cover g h)

/-- Identifying the two charts is an equivalence of their descent categories. -/
theorem compositeBaseChangeCharts_isEquivalence :
    (compositeBaseChangeCharts cover g h).IsEquivalence := by
  let inverseSquare (i : cover.I₀) :
      (compositeBaseChangeChart cover g h i).inv ≫ ((cover.pullback₁ g).pullback₁ h).f i =
        (cover.pullback₁ (h ≫ g)).f i ≫ 𝟙 Z :=
    (pullbackRightPullbackFstIso_inv_fst g (cover.f i) h).trans (Category.comp_id _).symm
  let e := DescentData.pullFunctorEquivalence Q (Iso.refl Z) (α := id)
    (p' := fun i => (compositeBaseChangeChart cover g h i).hom)
    (compositeBaseChangeChart_square cover g h) (β := id)
    (q' := fun i => (compositeBaseChangeChart cover g h i).inv) inverseSquare
  exact e.isEquivalence_functor

set_option maxHeartbeats 725000 in
/-- The functor restricting data twice is naturally isomorphic to restriction
along the composite followed by the canonical chart equivalence. -/
def fppfDescentBaseChange_composite :
    fppfDescentBaseChange cover g ⋙ fppfDescentBaseChange (cover.pullback₁ g) h ≅
      fppfDescentBaseChange cover (h ≫ g) ⋙ compositeBaseChangeCharts cover g h := by
  let iterated (i : cover.I₀) :=
    Scheme.Cover.pullbackHom (cover.pullback₁ g) h i ≫ cover.pullbackHom g i
  have agree (i : cover.I₀) :
      (compositeBaseChangeChart cover g h i).hom ≫ cover.pullbackHom (h ≫ g) i =
        iterated i :=
    pullbackRightPullbackFstIso_hom_snd g (cover.f i) h
  let a := DescentData.pullFunctorCompIso Q (cover.pullbackHom_map g)
    (Scheme.Cover.pullbackHom_map (cover.pullback₁ g) h) (h ≫ g)
    (r' := iterated) rfl (fun _ => rfl)
  let b := DescentData.pullFunctorCompIso Q (cover.pullbackHom_map (h ≫ g))
    (compositeBaseChangeChart_square cover g h) (h ≫ g)
    (r' := iterated) (Category.id_comp _) agree
  exact a ≪≫ b.symm

/-- Both chart presentations give the same comparison for a global module. -/
def compositeBaseChangeCharts_comparison :
    fppfModuleComparison (cover.pullback₁ (h ≫ g)) ⋙ compositeBaseChangeCharts cover g h ≅
      fppfModuleComparison ((cover.pullback₁ g).pullback₁ h) :=
  DescentData.toDescentDataCompPullFunctorIso Q (compositeBaseChangeChart_square cover g h) ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (Q.mapId (.mk (op Z)))) _ ≪≫
      Functor.leftUnitor _

end

end SHIGURE.SchemeDescent
