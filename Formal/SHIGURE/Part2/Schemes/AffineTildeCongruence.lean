import Formal.SHIGURE.Part2.Schemes.TildeBaseChange
import Formal.SHIGURE.Part2.Descent.ScalarChangeProjection

/-! # Affine pullback respects equality of coefficient maps -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {R S : CommRingCat.{u}} {f g : R ⟶ S} (h : f = g) (M : ModuleCat.{u} R)

/-- Rewriting a coefficient homomorphism commutes with affine associated-module pullback. -/
theorem tildePullbackIso_congr_at :
    (pullbackCongr (congrArg (fun k : R ⟶ S => Spec.map k) h)).hom.app ((tilde.functor R).obj M) ≫
      (tildePullbackIso g).hom.app M =
    (tildePullbackIso f).hom.app M ≫ (tilde.functor S).map
      ((extensionAlongCongruence (congrArg (fun k : R ⟶ S => k.hom) h)).hom.app M) := by
  subst g
  simp only [pullbackCongr, extensionAlongCongruence, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  let G := tilde.functor S
  let N := (ModuleCat.extendScalars f.hom).obj M
  let k := (tildePullbackIso f).hom.app M
  have identity : G.map (𝟙 N) = 𝟙 (G.obj N) := G.map_id N
  exact ((congrArg (k ≫ ·) identity).trans (Category.comp_id k)).symm

end

end SHIGURE.SchemeDescent
