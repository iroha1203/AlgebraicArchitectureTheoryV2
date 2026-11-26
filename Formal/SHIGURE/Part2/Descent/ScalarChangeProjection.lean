import Formal.SHIGURE.Part2.Descent.ScalarCocycle

/-! # Rewriting the coefficient map of a scalar extension -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory ModuleCat

noncomputable section

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The scalar extension along equal coefficient maps uses the same functor. -/
def extensionAlongCongruence {f g : R →+* S} (h : f = g) :
    extendScalars.{u,u,u} f ≅ extendScalars.{u,u,u} g := eqToIso (congrArg _ h)

/-- Changing the formula of the coefficient map preserves the extension unit. -/
theorem extensionAlongCongruence_unit {f g : R →+* S} (h : f = g) (M : ModuleCat.{u} R) (x : M) :
    (extensionAlongCongruence h).hom.app M ((extendRestrictScalarsAdj f).unit.app M x) =
      (extendRestrictScalarsAdj g).unit.app M x := by
  subst g
  rfl

/-- Pull a double comparison to the two specified projections of the same
triple overlap, using their coefficient map equalities. -/
def scalarExtensionPullHomAt (f₀ f₁ : R →+* S) (g : S →+* T) {r₀ r₁ : R →+* T}
    (e₀ : g.comp f₀ = r₀) (e₁ : g.comp f₁ = r₁) {M N : ModuleCat.{u} R}
    (m : (extendScalars f₀).obj M ⟶ (extendScalars f₁).obj N) :
    (extendScalars r₀).obj M ⟶ (extendScalars r₁).obj N :=
  (extensionAlongCongruence e₀).inv.app M ≫ scalarExtensionPullHom f₀ f₁ g m ≫
    (extensionAlongCongruence e₁).hom.app N

/-- In the coefficient comparison for Lemma B.4, reflexive formulas for the
composite maps simplify to ordinary pullback of the overlap map. -/
@[simp]
theorem scalarExtensionPullHomAt_comp (f₀ f₁ : R →+* S) (g : S →+* T) {M N : ModuleCat.{u} R}
    (m : (extendScalars f₀).obj M ⟶ (extendScalars f₁).obj N) :
    scalarExtensionPullHomAt f₀ f₁ g rfl rfl m = scalarExtensionPullHom f₀ f₁ g m := by
  simp [scalarExtensionPullHomAt, extensionAlongCongruence]

end

end SHIGURE.CoefficientDescent
