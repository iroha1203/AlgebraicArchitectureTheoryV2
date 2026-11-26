import Formal.SHIGURE.Part2.Descent.ScalarExtensionCoordinates

/-! # The inner extension inside a composite scalar chart -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory ModuleCat

noncomputable section

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T) {r : R →+* T} (w : g.comp f = r)
  {M : ModuleCat.{u} R} {V : ModuleCat.{u} T}

/-- Insert a section of an inner coefficient extension into the chosen
presentation of the outer extension. -/
def scalarExtensionInsert (e : (extendScalars r).obj M ≅ V) :
    (extendScalars f).obj M ⟶ (restrictScalars g).obj V :=
  (extendRestrictScalarsAdj g).unit.app ((extendScalars f).obj M) ≫
    (restrictScalars g).map ((extendScalarsComp f g).inv.app M ≫
      (extensionAlongCongruence w).hom.app M ≫ e.hom)

/-- Inner units are sent to the unit of the specified composite extension. -/
theorem scalarExtensionInsert_unit (e : (extendScalars r).obj M ≅ V) (x : M) :
    scalarExtensionInsert f g w e ((extendRestrictScalarsAdj f).unit.app M x) =
      e.hom ((extendRestrictScalarsAdj r).unit.app M x) := by
  let a := (extendScalarsComp f g).app M
  let b := (extensionAlongCongruence w).app M
  let u := (extendRestrictScalarsAdj (g.comp f)).unit.app M x
  let t := (extendRestrictScalarsAdj g).unit.app ((extendScalars f).obj M)
    ((extendRestrictScalarsAdj f).unit.app M x)
  have left : a.hom u = t := extendScalarsComp_hom_app_one_tmul f g M x
  have inverse : a.inv (a.hom u) = u :=
    congrArg (fun k : (extendScalars (g.comp f)).obj M ⟶ (extendScalars (g.comp f)).obj M => k u) a.hom_inv_id
  have comp : b.hom u = (extendRestrictScalarsAdj r).unit.app M x :=
    extensionAlongCongruence_unit w M x
  change e.hom (b.hom (a.inv t)) = _
  rw [← left, inverse, comp]

set_option maxHeartbeats 600000 in
/-- To compute the pulled comparison on the generating unit, apply the
original comparison and insert the result in the target coefficient chart. -/
theorem scalarExtensionPullHomAt_on_unit (f₀ : R →+* S) {r₀ : R →+* T}
    (w₀ : g.comp f₀ = r₀) {N : ModuleCat.{u} R}
    (δ : (extendScalars f₀).obj N ⟶ (extendScalars f).obj M)
    (e : (extendScalars r).obj M ≅ V) (x : N) :
    e.hom (scalarExtensionPullHomAt f₀ f g w₀ w δ ((extendRestrictScalarsAdj r₀).unit.app N x)) =
      scalarExtensionInsert f g w e (δ ((extendRestrictScalarsAdj f₀).unit.app N x)) := by
  subst r₀
  let c := (extensionAlongCongruence w).app M
  let a := (extendScalarsComp f g).app M
  let A := (extendScalars f).obj M
  let v₀ := (extendRestrictScalarsAdj (g.comp f₀)).unit.app N x
  let y := δ ((extendRestrictScalarsAdj f₀).unit.app N x)
  let v₁ := (extendRestrictScalarsAdj g).unit.app A y
  have compute := scalarExtensionPullHom_unit f₀ f g δ x
  have normalized :
      scalarExtensionPullHomAt f₀ f g rfl w δ =
        scalarExtensionPullHom f₀ f g δ ≫ c.hom := by
    simp only [scalarExtensionPullHomAt, extensionAlongCongruence, eqToIso_refl,
      Iso.refl_inv, NatTrans.id_app, Category.id_comp, c]
    rfl
  have result := congrArg (fun m : (extendScalars (g.comp f₀)).obj N ⟶ (extendScalars r).obj M => m v₀) normalized
  change scalarExtensionPullHomAt f₀ f g rfl w δ v₀ = c.hom (scalarExtensionPullHom f₀ f g δ v₀) at result
  change e.hom (scalarExtensionPullHomAt f₀ f g rfl w δ v₀) = e.hom (c.hom (a.inv v₁))
  rw [result, compute]
  rfl

end

end SHIGURE.CoefficientDescent
