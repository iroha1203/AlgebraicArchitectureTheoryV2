import Formal.SHIGURE.Part2.Schemes.QuasiCoherentModules

/-! # Reading the actual sections of an affine module restriction

The affine chart of an affine open uses its section ring as coefficient
ring. An associated-module presentation on that chart therefore makes
its principal-open restrictions localizations of the original sections.

## Implementation notes

The restrictions are compared using the chart's structure-sheaf
isomorphisms and the actual image opens. This gives linear maps over
the affine section ring and identifies the original restriction map.
An equality on underlying carriers alone would leave the scalar actions
unverified.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

noncomputable section

universe u

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

private theorem image_le (W : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ W ≤ U :=
  (hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le

private theorem affine_inverse_top :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (hU.fromSpec.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv =
      X.presheaf.map (homOfLE (image_le hU ⊤)).op := by
  let g := hU.fromSpec
  let S := Spec Γ(X, U)
  let j : op U ⟶ op (g ''ᵁ (⊤ : S.Opens)) := (homOfLE (image_le hU ⊤)).op
  change (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (g.appIso (⊤ : S.Opens)).inv = X.presheaf.map j
  apply (cancel_mono (g.appIso (⊤ : S.Opens)).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, g.appIso_hom', g.map_appLE]
  change (Scheme.ΓSpecIso Γ(X, U)).inv = g.app U ≫ S.presheaf.map _
  rw [hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (Category.comp_id _).symm.trans (congrArg ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ ·)
    ((S.presheaf.map_id _).symm.trans (congrArg S.presheaf.map (Subsingleton.elim _ _))))

private theorem affine_inverse_open (W : (Spec Γ(X, U)).Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec Γ(X, U)).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op ≫
      (hU.fromSpec.appIso W).inv = X.presheaf.map (homOfLE (image_le hU W)).op := by
  rw [hU.fromSpec.appIso_inv_naturality, ← Category.assoc, affine_inverse_top, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

private def affineRead (M : X.Modules) (W : (Spec Γ(X, U)).Opens) {V : X.Opens}
    (image : hU.fromSpec ''ᵁ W = V) (inside : V ≤ U) :
    (modulesSpecToSheaf.obj (M.restrict hU.fromSpec)).val.obj (op W) ≅
      (ModuleCat.restrictScalars (X.presheaf.map (homOfLE inside).op).hom).obj (M.val.obj (op V)) := by
  subst V
  let A := (modulesSpecToSheaf.obj (M.restrict hU.fromSpec)).val.obj (op W)
  let B := (ModuleCat.restrictScalars (X.presheaf.map (homOfLE inside).op).hom).obj
    (M.val.obj (op (hU.fromSpec ''ᵁ W)))
  change A ≅ B
  refine LinearEquiv.toModuleIso (X₁ := A) (X₂ := B)
    { AddEquiv.refl _ with map_smul' := fun r x => ?_ }
  let y : Γ(M, hU.fromSpec ''ᵁ W) := x
  change (hU.fromSpec.appIso W).inv
      ((Spec Γ(X, U)).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op
        ((Scheme.ΓSpecIso Γ(X, U)).inv r)) • y =
    (X.presheaf.map (homOfLE inside).op r) • y
  exact congrArg (fun a : Γ(X, hU.fromSpec ''ᵁ W) => a • y)
    (congrArg (fun m : Γ(X, U) ⟶ Γ(X, hU.fromSpec ''ᵁ W) => m r) (affine_inverse_open hU W))

private theorem affineRead_apply (M : X.Modules) (W : (Spec Γ(X, U)).Opens) {V : X.Opens}
    (image : hU.fromSpec ''ᵁ W = V) (inside : V ≤ U)
    (x : (modulesSpecToSheaf.obj (M.restrict hU.fromSpec)).val.obj (op W)) :
    (affineRead hU M W image inside).hom x = M.presheaf.map (eqToHom image.symm).op x := by
  subst V
  change x = M.presheaf.map (𝟙 _) x
  rw [M.presheaf.map_id]
  rfl

/-- An affine tilde presentation localizes the module's original restriction
map from that affine open to each principal open inside it. -/
theorem affineSections_localize (M : X.Modules) (presentation : HasTildeOn M hU) (r : Γ(X, U)) :
    IsLocalizedModule (Submonoid.powers r) (M.val.map (homOfLE (X.basicOpen_le r)).op).hom := by
  let g := hU.fromSpec
  let Z := Spec Γ(X, U)
  let N := M.restrict g
  let F := (modulesSpecToSheaf.obj N).val
  let W : Z.Opens := PrimeSpectrum.basicOpen r
  let V := X.basicOpen r
  let topIncl : op (⊤ : Z.Opens) ⟶ op W := (homOfLE le_top).op
  let openIncl : op U ⟶ op V := (homOfLE (X.basicOpen_le r)).op
  have topImage : g ''ᵁ (⊤ : Z.Opens) = U :=
    g.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have openImage : g ''ᵁ W = V := hU.fromSpec_image_basicOpen r
  let e₀ := affineRead hU M ⊤ topImage le_rfl
  let e₁ := affineRead hU M W openImage (X.basicOpen_le r)
  let topRes := X.presheaf.map (homOfLE (le_rfl : U ≤ U)).op
  have identity : topRes.hom = RingHom.id Γ(X, U) := by
    simp [topRes]
  let e := e₀ ≪≫ ModuleCat.restrictScalarsId'App topRes.hom identity (M.val.obj (op U))
  let p := F.map topIncl
  let q := M.val.map openIncl
  have equation : e.hom ≫ q = p ≫ e₁.hom := by
    ext x
    change M.presheaf.map openIncl (e₀.hom x) = e₁.hom (p x)
    rw [show e₀.hom x = M.presheaf.map (eqToHom topImage.symm).op x from
      affineRead_apply hU M ⊤ topImage le_rfl x,
      show e₁.hom (p x) = M.presheaf.map (eqToHom openImage.symm).op (p x) from
        affineRead_apply hU M W openImage (X.basicOpen_le r) (p x)]
    change M.presheaf.map openIncl (M.presheaf.map (eqToHom topImage.symm).op x) =
      M.presheaf.map (eqToHom openImage.symm).op (M.presheaf.map (g.opensFunctor.op.map topIncl) x)
    have maps : M.presheaf.map ((eqToHom topImage.symm).op ≫ openIncl) =
        M.presheaf.map (g.opensFunctor.op.map topIncl ≫ (eqToHom openImage.symm).op) :=
      congrArg M.presheaf.map (Subsingleton.elim _ _)
    simp only [Functor.map_comp] at maps
    exact congrArg (fun m => m x) maps
  have comparison : q = e.inv ≫ p ≫ e₁.hom := by
    apply (cancel_epi e.hom).1
    simpa only [Iso.hom_inv_id_assoc] using equation
  haveI : IsLocalizedModule (Submonoid.powers r) p.hom :=
    (principalLocalizations_iff_tilde N).2 presentation r
  change IsLocalizedModule (Submonoid.powers r) q.hom
  rw [comparison]
  haveI : IsLocalizedModule (Submonoid.powers r) (p.hom.comp e.symm.toLinearEquiv.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers r) p.hom e.symm.toLinearEquiv
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
    (p.hom.comp e.symm.toLinearEquiv.toLinearMap) e₁.toLinearEquiv

end

end SHIGURE.SchemeDescent
