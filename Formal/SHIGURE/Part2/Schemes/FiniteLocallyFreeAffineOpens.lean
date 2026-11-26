import Formal.SHIGURE.Part2.Schemes.FiniteLocallyFreeSheaf

/-! # Finite local freeness is affine local -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules TopologicalSpace TensorProduct
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {X : Scheme.{u}} {M : X.Modules}

/-- Finite locally free presentations restrict to smaller affine opens. -/
theorem HasFiniteLocallyFreeOn.restrict {U V : X.Opens} {hU : IsAffineOpen U} {hV : IsAffineOpen V}
    (inside : V ≤ U) (h : HasFiniteLocallyFreeOn M hU) : HasFiniteLocallyFreeOn M hV := by
  obtain ⟨N, finite, ⟨e⟩⟩ := h
  let f := X.presheaf.map (homOfLE inside).op
  exact ⟨(ModuleCat.extendScalars f.hom).obj N, finiteLocallyFree_extendScalars f N finite,
    ⟨restrictTildePresentationIso (hV := hV) inside e⟩⟩

/-- The section ring and its principal localization identify the local
coefficient module with the one obtained from the smaller tilde chart. -/
private theorem finiteLocallyFree_of_basicOpenPresentation {U : X.Opens}
    (affine : IsAffineOpen U) (N : ModuleCat.{u} Γ(X, U))
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict affine.fromSpec)
    (f : Γ(X, U)) (localFree : HasFiniteLocallyFreeOn M (affine.basicOpen f)) :
    FiniteLocallyFree (Localization.Away f) (LocalizedModule (Submonoid.powers f) N) := by
  let V := X.basicOpen f
  let a := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
  letI : Algebra Γ(X, U) Γ(X, V) := a.hom.toAlgebra
  letI : IsLocalization.Away f Γ(X, V) := affine.isLocalization_basicOpen f
  obtain ⟨P, finite, ⟨k⟩⟩ := localFree
  let w := restrictTildePresentationIso (hV := affine.basicOpen f) (X.basicOpen_le f) e
  let comparison := (tilde.fullyFaithfulFunctor (R := Γ(X, V))).preimageIso (k ≪≫ w.symm)
  let N₀ := (ModuleCat.extendScalars a.hom).obj N
  have finite₀ : FiniteLocallyFree (Γ(X, V)) N₀ := finiteLocallyFree_of_moduleIso comparison finite
  let L := CommRingCat.of (Localization.Away f)
  let j := IsLocalization.algEquiv (Submonoid.powers f) (Γ(X, V)) L
  let b : Γ(X, V) ⟶ L := CommRingCat.ofHom j.toRingEquiv.toRingHom
  have equal : b.hom.comp a.hom = algebraMap (Γ(X, U)) L := by
    ext z
    exact j.commutes z
  let composed := ((ModuleCat.extendScalarsComp a.hom b.hom).app N).symm
  let changeRing := eqToIso (congrArg (fun a' : Γ(X, U) →+* L =>
    (ModuleCat.extendScalars a').obj N) equal)
  let tensor := extendScalarsTensorIso (B := L) N
  let localized := (LocalizedModule.equivTensorProduct (Submonoid.powers f) N).symm.toModuleIso
  exact finiteLocallyFree_of_moduleIso (composed ≪≫ changeRing ≪≫ tensor ≪≫ localized)
    (finiteLocallyFree_extendScalars b N₀ finite₀)

/-- On every affine open, a finite locally free sheaf admits a finite locally
free coefficient presentation. -/
theorem isFiniteLocallyFreeModule_iff_on_affineOpens : IsFiniteLocallyFreeModule M ↔
    ∀ U : X.affineOpens, HasFiniteLocallyFreeOn M U.property := by
  refine ⟨?_, fun localFree => ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, localFree⟩⟩
  intro h V
  have coherent := h.quasiCoherent
  obtain ⟨ι, U, cover, presentations⟩ := h
  apply of_affine_open_cover (P := fun W => HasFiniteLocallyFreeOn M W.property) U cover V _ _ presentations
  · intro W f localFree
    exact localFree.restrict (X.basicOpen_le f)
  · intro W s spans localFree
    classical
    obtain ⟨N, ⟨e⟩⟩ := coherent W
    refine ⟨N, ?_, ⟨e⟩⟩
    exact finiteLocallyFree_of_localizationSpan s spans
      (fun f => finiteLocallyFree_of_basicOpenPresentation W.property N e f.val (localFree f))

end

end SHIGURE.SchemeDescent
