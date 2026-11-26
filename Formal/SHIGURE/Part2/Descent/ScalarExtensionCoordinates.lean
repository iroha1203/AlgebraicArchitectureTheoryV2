import Formal.SHIGURE.Part2.Descent.ScalarChangeProjection

/-! # Presenting a scalar extension in tensor coordinates -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory ModuleCat

noncomputable section

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {M N : ModuleCat.{u} R} {U V : ModuleCat.{u} T}

/-- Use a tensor coordinate over an equal presentation of its scalar map. -/
def scalarExtensionCoordinateAt {f g : R →+* T} (h : f = g) (e : (extendScalars f).obj M ≅ U) :
    (extendScalars g).obj M ≅ U :=
  (extensionAlongCongruence h.symm).app M ≪≫ e

/-- Changing the ring presentation does not change a coordinate on the extension units. -/
theorem scalarExtensionCoordinateAt_unit {f g : R →+* T} (h : f = g) (e : (extendScalars f).obj M ≅ U) (x : M) :
    (scalarExtensionCoordinateAt h e).hom ((extendRestrictScalarsAdj g).unit.app M x) =
      e.hom ((extendRestrictScalarsAdj f).unit.app M x) := by
  change e.hom ((extensionAlongCongruence h.symm).hom.app M ((extendRestrictScalarsAdj g).unit.app M x)) = _
  rw [extensionAlongCongruence_unit]

private theorem scalarExtensionCoordinateAt_refl (f : R →+* T) (e : (extendScalars f).obj M ≅ U) :
    scalarExtensionCoordinateAt (rfl : f = f) e = e := by
  unfold scalarExtensionCoordinateAt extensionAlongCongruence
  rw [eqToIso_refl]
  change Iso.refl _ ≪≫ e = e
  exact Iso.refl_trans _

set_option maxHeartbeats 675000 in
/-- Pulling a comparison in a different presentation of the pair and projection maps
gives the same morphism between the specified coefficient coordinates. -/
theorem scalarExtensionCoordinateAt_pullHom (f₀ f₁ : R →+* S) {g k : S →+* T} (h : g = k)
    {r₀ r₁ : R →+* T} (h₀ : k.comp f₀ = r₀) (h₁ : k.comp f₁ = r₁)
    (m : (extendScalars f₀).obj M ⟶ (extendScalars f₁).obj N)
    (a : (extendScalars (g.comp f₀)).obj M ≅ U) (b : (extendScalars (g.comp f₁)).obj N ≅ V)
    (v : U ⟶ V) (comm : scalarExtensionPullHom f₀ f₁ g m ≫ b.hom = a.hom ≫ v) :
    scalarExtensionPullHomAt f₀ f₁ k h₀ h₁ m ≫
      (scalarExtensionCoordinateAt (M := N) (U := V) ((congrArg (fun p : S →+* T => p.comp f₁) h).trans h₁) b).hom =
    (scalarExtensionCoordinateAt (M := M) (U := U) ((congrArg (fun p : S →+* T => p.comp f₀) h).trans h₀) a).hom ≫ v := by
  subst k
  subst r₀
  subst r₁
  simpa only [scalarExtensionPullHomAt_comp, scalarExtensionCoordinateAt_refl] using comm

/-- A linear coordinate on an extension is uniquely determined by its unit values. -/
theorem scalarExtensionCoordinate_ext (f : R →+* T) (a b : (extendScalars f).obj M ≅ U)
    (h : ∀ x : M, a.hom ((extendRestrictScalarsAdj f).unit.app M x) =
      b.hom ((extendRestrictScalarsAdj f).unit.app M x)) : a = b := by
  apply Iso.ext
  exact ExtendScalars.hom_ext h
/-- Tensor coordinates agree along a shared coefficient projection if they
give the same tensor for every original module element. -/
theorem scalarExtensionCoordinateAt_agrees (hf : f = r) (hg : g = r)
    (a : (extendScalars f).obj M ≅ U) (b : (extendScalars g).obj M ≅ U)
    (units : ∀ x : M, a.hom ((extendRestrictScalarsAdj f).unit.app M x) =
      b.hom ((extendRestrictScalarsAdj g).unit.app M x)) :
    scalarExtensionCoordinateAt hf a = scalarExtensionCoordinateAt hg b := by
  apply scalarExtensionCoordinate_ext r
  intro x
  rw [scalarExtensionCoordinateAt_unit, scalarExtensionCoordinateAt_unit]
  exact units x


end

end SHIGURE.CoefficientDescent
