import Formal.SHIGURE.Part2.Schemes.TensorPullback
import Formal.SHIGURE.Part2.Schemes.TensorAffine
import Formal.SHIGURE.Part2.Schemes.AffineBaseChangeCoherence

/-! # Affine and pullback comparisons for module-sheaf tensors

For quasi-coherent inputs the canonical pullback tensor map is invertible.
The proof compares it with scalar extension on affine charts, compares open
pullback with actual restriction, and detects invertibility on the resulting
cover. Its map is fixed by the pullback-adjunction unit normalization.

## Implementation notes

The local normalization lemmas are proved for arbitrary morphisms before
substituting the canonical affine comparison. This avoids expanding the
left-adjoint uniqueness construction while checking sectionwise equations.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

variable {X Y Z : Scheme.{u}}

/-- Tensor products of quasi-coherent module sheaves are quasi-coherent.
This supplies the carrier needed when primitive operations are descended
as morphisms by the existing quasi-coherent-module descent equivalence. -/
theorem tensorModule_isQuasiCoherent {M N : X.Modules}
    (hM : IsQuasiCoherentModule M) (hN : IsQuasiCoherentModule N) :
    IsQuasiCoherentModule (tensorModule M N) := by
  intro U
  obtain ⟨M₀, ⟨eM⟩⟩ := hM U
  obtain ⟨N₀, ⟨eN⟩⟩ := hN U
  let g := U.property.fromSpec
  let e := tildeTensorIso Γ(X, U.1)
  refine ⟨M₀ ⊗ N₀, ⟨?_⟩⟩
  exact (e.app (M₀, N₀)).symm ≪≫ tensorModuleIso eM eN ≪≫
    (restrictTensorModuleIso g M N).symm

/-- Scalar restriction preserves the underlying function of a module morphism. -/
private lemma restrictScalars_map_hom_apply {R S : CommRingCat.{u}} (a : R ⟶ S)
    {M N : ModuleCat.{u} S} (k : M ⟶ N) (x : M) :
    ((ModuleCat.restrictScalars a.hom).map k).hom x = k.hom x := rfl

/-- The global-sections functor evaluates the original sheaf morphism at the top open. -/
private lemma moduleSpecΓ_map_hom_apply {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (k : M ⟶ N) (x : (moduleSpecΓFunctor (R := R)).obj M) :
    ((moduleSpecΓFunctor (R := R)).map k).hom x = k.val.app (.op ⊤) x := rfl

/-- The tilde adjunction unit is the canonical map to global sections. -/
private lemma tilde_unit_hom_apply {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (m : M) :
    ((tilde.adjunction (R := R)).unit.app M).hom m = StructureSheaf.toOpenₗ R M ⊤ m := rfl

/-- The affine pushforward comparison preserves the underlying global section. -/
private lemma moduleSpecΓPushforwardIso_hom_apply {R S : CommRingCat.{u}} (a : R ⟶ S)
    (K : (Spec S).Modules) (x : (moduleSpecΓFunctor (R := R)).obj ((pushforward (Spec.map a)).obj K)) :
    ((moduleSpecΓPushforwardIso a).hom.app K).hom x = x := rfl

/-- Evaluating the affine adjunction unit equation recovers its sectionwise normalization. -/
private lemma affineUnit_section_eq {R S : CommRingCat.{u}} (a : R ⟶ S)
    (M : ModuleCat.{u} R) (P : (Spec S).Modules)
    (k : tilde ((ModuleCat.extendScalars a.hom).obj M) ⟶ P)
    (η : tilde M ⟶ (pushforward (Spec.map a)).obj P)
    (h : ((tilde.adjunction (R := R)).unit.app M ≫
        (moduleSpecΓFunctor (R := R)).map η) ≫ (moduleSpecΓPushforwardIso a).hom.app P =
      ((ModuleCat.extendRestrictScalarsAdj a.hom).unit.app M ≫
        (ModuleCat.restrictScalars a.hom).map
          ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars a.hom).obj M))) ≫
        (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars a.hom).map k)
    (m : M) :
    k.val.app (.op ⊤)
      (StructureSheaf.toOpenₗ S ((ModuleCat.extendScalars a.hom).obj M) ⊤
        ((1 : S) ⊗ₜ[R, a.hom] m)) =
      η.val.app (.op ⊤) (StructureSheaf.toOpenₗ R M ⊤ m) := by
  have heval := congr($(h).hom m)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.comp_map,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply, tilde_unit_hom_apply] at heval
  erw [restrictScalars_map_hom_apply a, restrictScalars_map_hom_apply a] at heval
  erw [moduleSpecΓ_map_hom_apply η, moduleSpecΓ_map_hom_apply k,
    moduleSpecΓPushforwardIso_hom_apply a] at heval
  exact heval.symm

/-- An inverse normalization determines the forward component of a module-sheaf isomorphism. -/
private lemma moduleIso_hom_apply_of_inv {S : CommRingCat.{u}} {P Q : (Spec S).Modules}
    (e : P ≅ Q) (x : P.val.obj (.op ⊤)) (y : Q.val.obj (.op ⊤))
    (h : e.inv.val.app (.op ⊤) y = x) : e.hom.val.app (.op ⊤) x = y := by
  have t := congr($(e.inv_hom_id).val.app (.op ⊤) y)
  exact (congrArg (fun z => e.hom.val.app (.op ⊤) z) h.symm).trans t

/-- The affine pullback comparison takes pullback-unit images of coefficient
sections to the coefficient scalar-extension unit. -/
private theorem tildePullbackIso_unit_top {R S : CommRingCat.{u}} (a : R ⟶ S)
    (M : ModuleCat.{u} R) (m : M) :
    ((tildePullbackIso a).hom.app M).val.app (.op ⊤)
      (((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde M)).val.app (.op ⊤)
        (StructureSheaf.toOpenₗ R M ⊤ m)) =
      StructureSheaf.toOpenₗ S ((ModuleCat.extendScalars a.hom).obj M) ⊤
        ((1 : S) ⊗ₜ[R, a.hom] m) := by
  have h := unit_conjugateEquiv
    ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map a)))
    ((ModuleCat.extendRestrictScalarsAdj a.hom).comp (tilde.adjunction (R := S)))
    (tildePullbackIso a).inv M
  rw [conjugateEquiv_tildePullbackIso_inv] at h
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  have hinv := affineUnit_section_eq a M _ ((tildePullbackIso a).inv.app M)
    ((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde M)) h m
  exact moduleIso_hom_apply_of_inv ((tildePullbackIso a).app M) _ _ hinv

/-- Mathlib scalar extension distributes over the coefficient tensor product. -/
private def affineCoefficientTensorIso {R S : CommRingCat.{u}} (a : R ⟶ S)
    (M N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars a.hom).obj (M ⊗ N) ≅
      (ModuleCat.extendScalars a.hom).obj M ⊗ (ModuleCat.extendScalars a.hom).obj N := by
  letI : Algebra R S := a.hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N).toModuleIso

/-- The coefficient scalar-extension comparison sends unit pure tensors to unit pure tensors. -/
private lemma affineCoefficientTensorIso_tmul {R S : CommRingCat.{u}} (a : R ⟶ S)
    (M N : ModuleCat.{u} R) (m : M) (n : N) :
    (affineCoefficientTensorIso a M N).hom ((1 : S) ⊗ₜ[R, a.hom] (m ⊗ₜ[R] n)) =
      ((1 : S) ⊗ₜ[R, a.hom] m) ⊗ₜ[S] ((1 : S) ⊗ₜ[R, a.hom] n) := rfl

/-- The affine tensor comparison has the prescribed normalization at the top open. -/
private lemma tildeTensorMap_toOpen_top {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)
    (m : M) (n : N) :
    (tildeTensorMap R M N).val.app (.op ⊤)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.val)).unit.app
        (tensorPresheaf (tilde M) (tilde N))).app (.op ⊤)
        (StructureSheaf.toOpenₗ R M ⊤ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N ⊤ n)) =
      StructureSheaf.toOpenₗ R (M ⊗[R] N) ⊤ (m ⊗ₜ[R] n) := by
  have h := tildeTensorMap_toOpen R M N m n (1 : R)
  erw [PrimeSpectrum.basicOpen_one] at h
  exact h

/-- A forward normalization determines the inverse component of a module-sheaf isomorphism. -/
private lemma moduleIso_inv_apply_of_hom {S : CommRingCat.{u}} {P Q : (Spec S).Modules}
    (e : P ≅ Q) (x : P.val.obj (.op ⊤)) (y : Q.val.obj (.op ⊤))
    (h : e.hom.val.app (.op ⊤) x = y) : e.inv.val.app (.op ⊤) y = x := by
  have t := congr($(e.hom_inv_id).val.app (.op ⊤) x)
  exact (congrArg (fun z => e.inv.val.app (.op ⊤) z) h.symm).trans t

/-- An affine tensor comparison with its coefficient normalization detects morphism equality. -/
private lemma tensorTilde_hom_ext_aux {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)
    (e : tensorModule (tilde M) (tilde N) ≅ tilde (M ⊗ N))
    (he : ∀ (m : M) (n : N), e.hom.val.app (.op ⊤)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.val)).unit.app
        (tensorPresheaf (tilde M) (tilde N))).app (.op ⊤)
        (StructureSheaf.toOpenₗ R M ⊤ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N ⊤ n)) =
      StructureSheaf.toOpenₗ R (M ⊗[R] N) ⊤ (m ⊗ₜ[R] n))
    {K : (Spec R).Modules} {f g : tensorModule (tilde M) (tilde N) ⟶ K}
    (h : ∀ (m : M) (n : N),
      (tensorModuleHomEquiv _ _ _ f).app (.op ⊤)
          (StructureSheaf.toOpenₗ R M ⊤ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N ⊤ n) =
        (tensorModuleHomEquiv _ _ _ g).app (.op ⊤)
          (StructureSheaf.toOpenₗ R M ⊤ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N ⊤ n)) : f = g := by
  apply (cancel_epi e.inv).1
  apply ((tilde.adjunction (R := R)).homEquiv (M ⊗ N) K).injective
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  have hi := moduleIso_inv_apply_of_hom e _ _ (he m n)
  change f.val.app (.op ⊤) (e.inv.val.app (.op ⊤)
      (StructureSheaf.toOpenₗ R (M ⊗[R] N) ⊤ (m ⊗ₜ[R] n))) =
    g.val.app (.op ⊤) (e.inv.val.app (.op ⊤)
      (StructureSheaf.toOpenₗ R (M ⊗[R] N) ⊤ (m ⊗ₜ[R] n)))
  rw [hi]
  exact h m n

/-- Maps from the tensor of associated sheaves are determined by global coefficient pure tensors. -/
private lemma tensorTilde_hom_ext {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)
    {K : (Spec R).Modules} {f g : tensorModule (tilde M) (tilde N) ⟶ K}
    (h : ∀ (m : M) (n : N),
      (tensorModuleHomEquiv _ _ _ f).app (.op ⊤)
          (StructureSheaf.toOpenₗ R M ⊤ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N ⊤ n) =
        (tensorModuleHomEquiv _ _ _ g).app (.op ⊤)
          (StructureSheaf.toOpenₗ R M ⊤ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N ⊤ n)) : f = g :=
  tensorTilde_hom_ext_aux M N ((tildeTensorIso R).app (M, N))
    (tildeTensorMap_toOpen_top M N) h

/-- The tensor universal map followed by an associated-module map evaluates on coefficient tensors. -/
private lemma tensorTilde_homEquiv_comp_top {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)
    {K : (Spec R).Modules} (q : tilde (M ⊗ N) ⟶ K) (m : M) (n : N) :
    (tensorModuleHomEquiv _ _ _ (tildeTensorMap R M N ≫ q)).app (.op ⊤)
        (StructureSheaf.toOpenₗ R M ⊤ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N ⊤ n) =
      q.val.app (.op ⊤) (StructureSheaf.toOpenₗ R (M ⊗[R] N) ⊤ (m ⊗ₜ[R] n)) := by
  rw [tensorModuleHomEquiv_comp]
  change q.val.app (.op ⊤) ((tildeTensorMap R M N).val.app (.op ⊤)
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec R).ringCatSheaf.val)).unit.app
      (tensorPresheaf (tilde M) (tilde N))).app (.op ⊤)
      (StructureSheaf.toOpenₗ R M ⊤ m ⊗ₜ[_] StructureSheaf.toOpenₗ R N ⊤ n))) = _
  rw [tildeTensorMap_toOpen_top M N]

/-- Associated-sheaf maps commute with the canonical maps to global sections. -/
private lemma tilde_map_toOpen_top {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}
    (q : M ⟶ N) (m : M) :
    (tilde.map q).val.app (.op ⊤) (StructureSheaf.toOpenₗ R M ⊤ m) =
      StructureSheaf.toOpenₗ R N ⊤ (q m) :=
  congr($(tilde.toOpen_map_app q ⊤).hom m)

/-- The canonical pullback tensor map followed by a sheaf map evaluates on the two pullback-unit sections. -/
private lemma pullbackTensorMap_comp_homEquiv_app_tmul {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M N : X.Modules) {K : Y.Modules}
    (q : tensorModule ((pullback f).obj M) ((pullback f).obj N) ⟶ K)
    (U : X.Opensᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (tensorModuleHomEquiv M N ((pushforward f).obj K)
      ((pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackTensorMap f M N ≫ q))).app U
        (m ⊗ₜ[X.presheaf.obj U] n) =
      (tensorModuleHomEquiv _ _ K q).app ((Opens.map f.base).op.obj U)
        (((pullbackPushforwardAdjunction f).unit.app M).val.app U m ⊗ₜ[_]
         ((pullbackPushforwardAdjunction f).unit.app N).val.app U n) := by
  rw [Adjunction.homEquiv_naturality_right, tensorModuleHomEquiv_comp]
  change ((pushforward f).map q).val.app U
      ((tensorModuleHomEquiv M N _
        ((pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackTensorMap f M N))).app U
          (m ⊗ₜ[X.presheaf.obj U] n)) = _
  rw [pullbackTensorMap_homEquiv_app_tmul]
  rfl

/-- A normalized affine pullback comparison identifies the canonical tensor map with scalar-extension tensor comparison. -/
private lemma affine_pullbackTensorMap_comparison_aux {R S : CommRingCat.{u}} (a : R ⟶ S)
    (M N : ModuleCat.{u} R)
    (p : tilde.functor R ⋙ pullback (Spec.map a) ≅ ModuleCat.extendScalars a.hom ⋙ tilde.functor S)
    (hp : ∀ (L : ModuleCat.{u} R) (m : L), (p.hom.app L).val.app (.op ⊤)
      (((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde L)).val.app (.op ⊤)
        (StructureSheaf.toOpenₗ R L ⊤ m)) =
      StructureSheaf.toOpenₗ S ((ModuleCat.extendScalars a.hom).obj L) ⊤
        ((1 : S) ⊗ₜ[R, a.hom] m)) :
    pullbackTensorMap (Spec.map a) (tilde M) (tilde N) ≫
      tensorModuleMap (p.hom.app M) (p.hom.app N) ≫
      tildeTensorMap S ((ModuleCat.extendScalars a.hom).obj M) ((ModuleCat.extendScalars a.hom).obj N) =
    (pullback (Spec.map a)).map (tildeTensorMap R M N) ≫
      p.hom.app (M ⊗ N) ≫
      tilde.map (affineCoefficientTensorIso a M N).hom := by
  apply ((pullbackPushforwardAdjunction (Spec.map a)).homEquiv _ _).injective
  apply tensorTilde_hom_ext M N
  intro m n
  erw [pullbackTensorMap_comp_homEquiv_app_tmul (Spec.map a) (tilde M) (tilde N)
    (tensorModuleMap (p.hom.app M) (p.hom.app N) ≫
      tildeTensorMap S ((ModuleCat.extendScalars a.hom).obj M) ((ModuleCat.extendScalars a.hom).obj N))
    (.op ⊤) (StructureSheaf.toOpenₗ R M ⊤ m) (StructureSheaf.toOpenₗ R N ⊤ n)]
  rw [Adjunction.homEquiv_naturality_left, tensorTilde_homEquiv_comp_top]
  change (tensorModuleHomEquiv _ _ _
      (tensorModuleMap (p.hom.app M) (p.hom.app N) ≫
        tildeTensorMap S ((ModuleCat.extendScalars a.hom).obj M) ((ModuleCat.extendScalars a.hom).obj N))).app (.op ⊤)
      ((((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde M)).val.app (.op ⊤)
        (StructureSheaf.toOpenₗ R M ⊤ m)) ⊗ₜ[_]
       (((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde N)).val.app (.op ⊤)
        (StructureSheaf.toOpenₗ R N ⊤ n))) = _
  rw [tensorModuleHomEquiv_map_comp]
  change (tensorModuleHomEquiv _ _ _
      (tildeTensorMap S ((ModuleCat.extendScalars a.hom).obj M) ((ModuleCat.extendScalars a.hom).obj N))).app (.op ⊤)
      (((p.hom.app M).val.app (.op ⊤)
        ((((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde M)).val.app (.op ⊤)
          (StructureSheaf.toOpenₗ R M ⊤ m)))) ⊗ₜ[_]
       ((p.hom.app N).val.app (.op ⊤)
        ((((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde N)).val.app (.op ⊤)
          (StructureSheaf.toOpenₗ R N ⊤ n))))) = _
  erw [hp M m, hp N n]
  change (tildeTensorMap S ((ModuleCat.extendScalars a.hom).obj M) ((ModuleCat.extendScalars a.hom).obj N)).val.app (.op ⊤)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec S).ringCatSheaf.val)).unit.app
        (tensorPresheaf (tilde ((ModuleCat.extendScalars a.hom).obj M)) (tilde ((ModuleCat.extendScalars a.hom).obj N)))).app (.op ⊤)
        (StructureSheaf.toOpenₗ S ((ModuleCat.extendScalars a.hom).obj M) ⊤ ((1 : S) ⊗ₜ[R, a.hom] m) ⊗ₜ[_]
         StructureSheaf.toOpenₗ S ((ModuleCat.extendScalars a.hom).obj N) ⊤ ((1 : S) ⊗ₜ[R, a.hom] n))) = _
  rw [tildeTensorMap_toOpen_top]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  change _ = (tilde.map (affineCoefficientTensorIso a M N).hom).val.app (.op ⊤)
    ((p.hom.app (M ⊗ N)).val.app (.op ⊤)
      (((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde (M ⊗ N))).val.app (.op ⊤)
        (StructureSheaf.toOpenₗ R (M ⊗[R] N) ⊤ (m ⊗ₜ[R] n))))
  erw [hp (M ⊗ N) (m ⊗ₜ[R] n), tilde_map_toOpen_top,
    affineCoefficientTensorIso_tmul]
  rfl

/-- The normalized affine scalar-extension comparison proves the canonical pullback tensor map invertible. -/
private theorem affine_pullbackTensorMap_isIso_aux {R S : CommRingCat.{u}} (a : R ⟶ S)
    (M N : ModuleCat.{u} R)
    (p : tilde.functor R ⋙ pullback (Spec.map a) ≅ ModuleCat.extendScalars a.hom ⋙ tilde.functor S)
    (hp : ∀ (L : ModuleCat.{u} R) (m : L), (p.hom.app L).val.app (.op ⊤)
      (((pullbackPushforwardAdjunction (Spec.map a)).unit.app (tilde L)).val.app (.op ⊤)
        (StructureSheaf.toOpenₗ R L ⊤ m)) =
      StructureSheaf.toOpenₗ S ((ModuleCat.extendScalars a.hom).obj L) ⊤
        ((1 : S) ⊗ₜ[R, a.hom] m)) :
    IsIso (pullbackTensorMap (Spec.map a) (tilde M) (tilde N)) := by
  letI : IsIso (tensorModuleMap (p.hom.app M) (p.hom.app N)) :=
    (tensorModuleIso (p.app M) (p.app N)).isIso_hom
  letI : IsIso (tilde.map (affineCoefficientTensorIso a M N).hom) :=
    (tilde.functor S).map_isIso (affineCoefficientTensorIso a M N).hom
  exact IsIso.of_isIso_fac_right (affine_pullbackTensorMap_comparison_aux a M N p hp)

/-- For a morphism of affine schemes the canonical pullback tensor map is
invertible on associated modules. -/
theorem affine_pullbackTensorMap_isIso {R S : CommRingCat.{u}} (a : R ⟶ S)
    (M N : ModuleCat.{u} R) :
    IsIso (pullbackTensorMap (Spec.map a) (tilde M) (tilde N)) :=
  affine_pullbackTensorMap_isIso_aux a M N (tildePullbackIso a) (tildePullbackIso_unit_top a)

/-- The actual restriction–pullback constraint carries the restriction
adjunction unit to the pullback adjunction unit. API for the B.3 comparison. -/
private theorem restrictFunctorIsoPullback_unit (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) :
    (restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map ((restrictFunctorIsoPullback f).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ _

/-- The restriction/sheafification comparison on a generating section
is the original restriction to the image of its inverse-image open, followed
by the sheafification unit. This is the section API for the existing comparison. -/
private theorem restrictModuleSheafificationIso_homEquiv_app
    (f : Y ⟶ X) [IsOpenImmersion f] (P : X.PresheafOfModules)
    (U : X.Opensᵒᵖ) (m : P.obj U) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).comp
      (restrictAdjunction f)).homEquiv P _
        ((restrictModuleSheafificationIso f).hom.app P)).app U m =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
        ((restrictModulePresheafFunctor f).obj P)).app
        ((TopologicalSpace.Opens.map f.base).op.obj U)
        (P.map (homOfLE (f.image_preimage_le U.unop)).op m) := by
  unfold restrictModuleSheafificationIso
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

/-- The actual restriction tensor isomorphism has the canonical
adjunction-unit normalization of B.3. The comparison is derived from the
presheaf tensor ring-isomorphism and sheafification, with no extra premise. -/
private theorem restrictTensorModuleIso_homEquiv (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) :
    (restrictAdjunction f).homEquiv _ _ (restrictTensorModuleIso f M N).hom =
      tensorModuleMap ((restrictAdjunction f).unit.app M) ((restrictAdjunction f).unit.app N) ≫
        pushforwardTensorMap f (M.restrict f) (N.restrict f) := by
  let q := restrictTensorPresheafIso f M N
  let S := PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)
  let k := S.map q.hom
  have hk : (restrictTensorModuleIso f M N).hom ≫ k =
      (restrictModuleSheafificationIso f).hom.app (tensorPresheaf M N) := by
    change ((restrictModuleSheafificationIso f).hom.app (tensorPresheaf M N) ≫
      S.map q.inv) ≫ S.map q.hom = _
    rw [Category.assoc, ← Functor.map_comp, q.inv_hom_id, S.map_id]
    exact Category.comp_id _
  apply (cancel_mono ((Scheme.Modules.pushforward f).map k)).1
  rw [← Adjunction.homEquiv_naturality_right, hk]
  apply (tensorModuleHomEquiv M N _).injective
  rw [tensorModuleHomEquiv_comp, tensorModuleHomEquiv_map_comp]
  simp only [Functor.comp_obj]
  erw [pushforwardTensorMap_homEquiv f (M.restrict f) (N.restrict f)]
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  trans ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
      ((restrictModulePresheafFunctor f).obj (tensorPresheaf M N))).app
      ((TopologicalSpace.Opens.map f.base).op.obj U)
      ((tensorPresheaf M N).map (homOfLE (f.image_preimage_le U.unop)).op (m ⊗ₜ[X.presheaf.obj U] n))
  · have h := restrictModuleSheafificationIso_homEquiv_app f (tensorPresheaf M N) U
      (m ⊗ₜ[X.presheaf.obj U] n)
    rw [Adjunction.comp_homEquiv] at h
    exact h
  · let V := (TopologicalSpace.Opens.map f.base).op.obj U
    let m' : (M.restrict f).val.obj V := M.val.map (homOfLE (f.image_preimage_le U.unop)).op m
    let n' : (N.restrict f).val.obj V := N.val.map (homOfLE (f.image_preimage_le U.unop)).op n
    have hq := (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.naturality q.hom
    change q.hom ≫ _ = _ ≫ k.val at hq
    exact congrArg (fun a => a.app V (m' ⊗ₜ[Y.presheaf.obj V] n')) hq

/-- Transport a tensor comparison with its adjunction normalization
across the actual restriction–pullback constraint. The normalization premise
is supplied by `restrictTensorModuleIso_homEquiv` in the final comparison theorem. -/
private theorem pullbackTensorMap_eq_of_restrict_normalization (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules)
    (h : (restrictAdjunction f).homEquiv _ _ (restrictTensorModuleIso f M N).hom =
      tensorModuleMap ((restrictAdjunction f).unit.app M) ((restrictAdjunction f).unit.app N) ≫
        pushforwardTensorMap f (M.restrict f) (N.restrict f)) :
    (restrictFunctorIsoPullback f).hom.app (tensorModule M N) ≫ pullbackTensorMap f M N =
      (restrictTensorModuleIso f M N).hom ≫
        tensorModuleMap ((restrictFunctorIsoPullback f).hom.app M)
          ((restrictFunctorIsoPullback f).hom.app N) := by
  apply ((restrictAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right, h]
  rw [Adjunction.homEquiv_unit, restrictFunctorIsoPullback_unit]
  rw [← Adjunction.homEquiv_unit, pullbackTensorMap_homEquiv]
  rw [Category.assoc, ← pushforwardTensorMap_naturality]
  rw [← Category.assoc, ← tensorModuleMap_comp]
  rw [restrictFunctorIsoPullback_unit, restrictFunctorIsoPullback_unit]

/-- The actual open-restriction tensor isomorphism agrees with the
canonical pullback comparison after the actual restriction–pullback constraint. -/
theorem pullbackTensorMap_restrict (f : Y ⟶ X) [IsOpenImmersion f] (M N : X.Modules) :
    (restrictFunctorIsoPullback f).hom.app (tensorModule M N) ≫ pullbackTensorMap f M N =
      (restrictTensorModuleIso f M N).hom ≫
        tensorModuleMap ((restrictFunctorIsoPullback f).hom.app M)
          ((restrictFunctorIsoPullback f).hom.app N) :=
  pullbackTensorMap_eq_of_restrict_normalization f M N (restrictTensorModuleIso_homEquiv f M N)

/-- The canonical tensor comparison is invertible for an open immersion,
for arbitrary actual module sheaves. No quasi-coherence premise is needed. -/
theorem pullbackTensorMap_isIso_of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) : IsIso (pullbackTensorMap f M N) := by
  let e := (moduleTensorFunctor Y).mapIso (Iso.prod
    ((restrictFunctorIsoPullback f).app M) ((restrictFunctorIsoPullback f).app N))
  haveI : IsIso (tensorModuleMap ((restrictFunctorIsoPullback f).hom.app M)
      ((restrictFunctorIsoPullback f).hom.app N)) := e.isIso_hom
  exact IsIso.of_isIso_fac_left (pullbackTensorMap_restrict f M N)

/-- Invertibility of the canonical tensor comparison is preserved by isomorphisms of its inputs. -/
private theorem tensorMap_isIso_of_iso (f : Y ⟶ X) {M N M' N' : X.Modules}
    (e : M ≅ M') (k : N ≅ N') (h : IsIso (pullbackTensorMap f M N)) :
    IsIso (pullbackTensorMap f M' N') := by
  letI := h
  letI : IsIso (tensorModuleMap e.hom k.hom) := (tensorModuleIso e k).isIso_hom
  letI : IsIso (tensorModuleMap ((pullback f).map e.hom) ((pullback f).map k.hom)) :=
    (tensorModuleIso ((pullback f).mapIso e) ((pullback f).mapIso k)).isIso_hom
  exact IsIso.of_isIso_fac_left (pullbackTensorMap_naturality f e.hom k.hom)

/-- Invertibility of the two canonical tensor comparisons implies invertibility for their composite morphism. -/
private theorem tensorMap_comp_isIso (f : Y ⟶ X) (g : Z ⟶ Y) (M N : X.Modules)
    (hf : IsIso (pullbackTensorMap f M N))
    (hg : IsIso (pullbackTensorMap g ((pullback f).obj M) ((pullback f).obj N))) :
    IsIso (pullbackTensorMap (g ≫ f) M N) := by
  letI := hf
  letI := hg
  letI : IsIso (tensorModuleMap ((pullbackComp g f).hom.app M)
      ((pullbackComp g f).hom.app N)) :=
    (tensorModuleIso ((pullbackComp g f).app M) ((pullbackComp g f).app N)).isIso_hom
  exact IsIso.of_isIso_fac_left (pullbackTensorMap_comp f g M N).symm

/-- Composition coherence detects invertibility after pulling back a canonical tensor comparison. -/
private theorem tensorMap_pullback_isIso_of_comp (f : Y ⟶ X) (g : Z ⟶ Y) (M N : X.Modules)
    (hcomp : IsIso (pullbackTensorMap (g ≫ f) M N))
    (hg : IsIso (pullbackTensorMap g ((pullback f).obj M) ((pullback f).obj N))) :
    IsIso ((pullback g).map (pullbackTensorMap f M N)) := by
  letI := hcomp
  letI := hg
  letI : IsIso (tensorModuleMap ((pullbackComp g f).hom.app M)
      ((pullbackComp g f).hom.app N)) :=
    (tensorModuleIso ((pullbackComp g f).app M) ((pullbackComp g f).app N)).isIso_hom
  exact IsIso.of_isIso_fac_right (pullbackTensorMap_comp f g M N)

/-- Invertibility of module-sheaf maps is detected on affine neighborhoods through their stalks. -/
private theorem isIso_of_affineNeighborhoods {M N : X.Modules} (a : M ⟶ N)
    (localIso : ∀ x : X, ∃ V : X.affineOpens,
      x ∈ V.1 ∧ IsIso ((restrictFunctor V.property.fromSpec).map a)) : IsIso a := by
  let F : TopCat.Sheaf Ab.{u} X := ⟨M.presheaf, M.isSheaf⟩
  let G : TopCat.Sheaf Ab.{u} X := ⟨N.presheaf, N.isSheaf⟩
  let m : F ⟶ G := ⟨a.mapPresheaf⟩
  haveI : IsIso m := (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso m).2 fun x => by
    obtain ⟨V, hx, hV⟩ := localIso x
    have range : x ∈ Set.range V.property.fromSpec := by
      rw [V.property.range_fromSpec]
      exact hx
    obtain ⟨z, rfl⟩ := range
    letI := hV
    exact (NatIso.isIso_map_iff (restrictStalkNatIso V.property.fromSpec z) a).1
      (Functor.map_isIso (toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} z)
        ((restrictFunctor V.property.fromSpec).map a))
  haveI : IsIso ((toPresheaf X).map a) := (TopCat.Sheaf.forget Ab.{u} _).map_isIso m
  exact isIso_of_reflects_iso a (toPresheaf X)

/-- Affine scalar extension and open restriction determine the canonical comparison on quasi-coherent inputs. -/
private theorem tensorMap_isIso_of_affine_and_open
    (openIso : ∀ {A B : Scheme.{u}} (g : B ⟶ A) [IsOpenImmersion g] (M N : A.Modules),
      IsIso (pullbackTensorMap g M N))
    (affineIso : ∀ {R S : CommRingCat.{u}} (a : R ⟶ S) (M N : ModuleCat.{u} R),
      IsIso (pullbackTensorMap (Spec.map a) (tilde M) (tilde N)))
    (f : Y ⟶ X) {M N : X.Modules}
    (hM : IsQuasiCoherentModule M) (hN : IsQuasiCoherentModule N) :
    IsIso (pullbackTensorMap f M N) := by
  apply isIso_of_affineNeighborhoods
  intro y
  obtain ⟨U, hfy⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top X).ge (Set.mem_univ (f y)))
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hfy (f ⁻¹ᵁ U.1).isOpen
  let a := f.appLE U.1 V hVU
  let g := hV.fromSpec
  let j := U.property.fromSpec
  have square : Spec.map a ≫ j = g ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec f U.property hV hVU
  obtain ⟨M₀, ⟨eM⟩⟩ := hM U
  obtain ⟨N₀, ⟨eN⟩⟩ := hN U
  let eM' := eM ≪≫ (restrictFunctorIsoPullback j).app M
  let eN' := eN ≪≫ (restrictFunctorIsoPullback j).app N
  have ha : IsIso (pullbackTensorMap (Spec.map a) ((pullback j).obj M) ((pullback j).obj N)) :=
    tensorMap_isIso_of_iso (Spec.map a) eM' eN' (affineIso a M₀ N₀)
  have hj : IsIso (pullbackTensorMap j M N) := openIso j M N
  have composite : IsIso (pullbackTensorMap (g ≫ f) M N) := by
    rw [← square]
    exact tensorMap_comp_isIso j (Spec.map a) M N hj ha
  have hg : IsIso (pullbackTensorMap g ((pullback f).obj M) ((pullback f).obj N)) :=
    openIso g _ _
  have pulled : IsIso ((pullback g).map (pullbackTensorMap f M N)) :=
    tensorMap_pullback_isIso_of_comp f g M N composite hg
  exact ⟨⟨V, hV⟩, hyV,
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback g) (pullbackTensorMap f M N)).2 pulled⟩

/-- The canonical comparison for an arbitrary scheme morphism is an
isomorphism on quasi-coherent inputs, by the affine scalar tensor comparison
and detection after open restriction. -/
theorem pullbackTensorMap_isIso (f : Y ⟶ X) {M N : X.Modules}
    (hM : IsQuasiCoherentModule M) (hN : IsQuasiCoherentModule N) :
    IsIso (pullbackTensorMap f M N) :=
  tensorMap_isIso_of_affine_and_open pullbackTensorMap_isIso_of_isOpenImmersion
    affine_pullbackTensorMap_isIso f hM hN

/-- The canonical pullback tensor isomorphism used to pull back (6.1).
Its map is fixed by the adjunction normalization of `pullbackTensorMap`,
so no arbitrary selection of a tensor isomorphism is involved. -/
def quasiCoherentPullbackTensorIso (f : Y ⟶ X) {M N : X.Modules}
    (hM : IsQuasiCoherentModule M) (hN : IsQuasiCoherentModule N) :
    (pullback f).obj (tensorModule M N) ≅
      tensorModule ((pullback f).obj M) ((pullback f).obj N) := by
  letI := pullbackTensorMap_isIso f hM hN
  exact asIso (pullbackTensorMap f M N)

end
end SHIGURE.SchemeDescent
