import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-! # Canonical Cartesian arrows and their vertical factors -/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v a b

variable {S : Type u} [Category.{v} S]
  (F : Pseudofunctor (LocallyDiscrete Sᵒᵖ) Cat.{a,b})

/-- The canonical lift of an identity is the vertical unit comparison. -/
theorem cartesianLift_identity {X : S} (M : F.obj (.mk (op X))) :
    CoGrothendieck.cartesianLift M (𝟙 X) =
      (CoGrothendieck.ι F X).map ((F.mapId (.mk (op X))).hom.toNatTrans.app M) := by
  refine CoGrothendieck.Hom.ext _ _ ?_ ?_
  · rfl
  · simp only [eqToHom_refl, Category.comp_id, CoGrothendieck.ι_map_fiber]
    exact (Iso.hom_inv_id_app (Cat.Hom.toNatIso (F.mapId (.mk (op X)))) M).symm

/-- Every morphism to a pulled-back object gives a vertical factor of
the corresponding morphism to its original object. -/
theorem vertical_cartesianLift {X Y : S} (f : X ⟶ Y)
    {M : F.obj (.mk (op X))} (N : F.obj (.mk (op Y)))
    (a : M ⟶ (F.map f.op.toLoc).toFunctor.obj N) :
    (CoGrothendieck.ι F X).map a ≫ CoGrothendieck.cartesianLift N f =
      (⟨f, a⟩ : (⟨X, M⟩ : CoGrothendieck F) ⟶ ⟨Y, N⟩) := by
  apply CoGrothendieck.Hom.ext _ _ (Category.id_comp f)
  simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso,
    PrelaxFunctor.map₂_eqToHom, ← Cat.Hom₂.comp_app]

/-- A vertical arrow after a canonical lift acts by its actual pullback. -/
theorem cartesianLift_vertical {X Y : S} (f : X ⟶ Y)
    {M N : F.obj (.mk (op Y))} (a : M ⟶ N) :
    CoGrothendieck.cartesianLift M f ≫ (CoGrothendieck.ι F Y).map a =
      (⟨f, (F.map f.op.toLoc).toFunctor.map a⟩ :
        CoGrothendieck.domainCartesianLift M f ⟶ ⟨Y, N⟩) := by
  apply CoGrothendieck.Hom.ext _ _ (Category.comp_id f)
  simp [F.mapComp_id_left_inv_app, Strict.leftUnitor_eqToIso,
    PrelaxFunctor.map₂_eqToHom, ← Functor.map_comp_assoc, ← Cat.Hom₂.comp_app]

/-- Composition of Cartesian lifts has the component of the actual
pseudofunctor composition isomorphism. -/
theorem cartesianLift_comp {X Y Z : S} (f : Y ⟶ Z) (g : X ⟶ Y)
    (N : F.obj (.mk (op Z))) :
    CoGrothendieck.cartesianLift ((F.map f.op.toLoc).toFunctor.obj N) g ≫
      CoGrothendieck.cartesianLift N f =
    (⟨g ≫ f, (F.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app N⟩ :
      CoGrothendieck.domainCartesianLift ((F.map f.op.toLoc).toFunctor.obj N) g ⟶ ⟨Z, N⟩) := by
  refine CoGrothendieck.Hom.ext _ _ ?_ ?_
  · rfl
  · simp

end

end SHIGURE.SchemeDescent
