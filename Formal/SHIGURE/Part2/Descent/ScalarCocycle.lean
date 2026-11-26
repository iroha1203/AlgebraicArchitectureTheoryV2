import Formal.SHIGURE.Part2.Descent.Overlap
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Computing the coefficient cocycle on the unit tensors -/

namespace SHIGURE.CoefficientDescent

open TensorProduct

noncomputable section

universe u

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

attribute [local instance] doubleModule

variable (θ : OverlapIso A B N)

private def insertMiddle (b : B) : (B ⊗[A] N) →ₗ[A] B ⊗[A] (B ⊗[A] N) :=
  ((TensorProduct.comm A N B).toLinearMap.lTensor B).comp
    ((TensorProduct.assoc A B N B).toLinearMap.comp ((TensorProduct.mk A (B ⊗[A] N) B).flip b))

omit [Module B N] [IsScalarTower A B N] in
private theorem insertMiddle_tmul (b x : B) (n : N) :
    insertMiddle b (x ⊗ₜ[A] n) = x ⊗ₜ[A] (b ⊗ₜ[A] n) := rfl

private def outputScale (b c : B) : (B ⊗[A] (B ⊗[A] N)) →ₗ[A] B ⊗[A] (B ⊗[A] N) :=
  (doubleAction (b ⊗ₜ[A] c) : Module.End A (B ⊗[A] N)).lTensor B

private theorem outputScale_tmul (b c x : B) (z : B ⊗[A] N) :
    outputScale b c (x ⊗ₜ[A] z) = x ⊗ₜ[A] ((b ⊗ₜ[A] c) • z) := rfl

private theorem move12_scale (b c : B) (z : B ⊗[A] N) :
    move12 θ ((((1 : B) ⊗ₜ[A] b) • z) ⊗ₜ[A] c) =
      outputScale b c (move12 θ (z ⊗ₜ[A] (1 : B))) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, zero_tmul, map_zero]
  | add a b ha hb => rw [smul_add, add_tmul, map_add, ha, hb, add_tmul, map_add, map_add]
  | tmul x n =>
    rw [double_smul, one_smul]
    have comparison : θ ((b • n) ⊗ₜ[A] c) = (b ⊗ₜ[A] c) • θ (n ⊗ₜ[A] (1 : B)) := by
      have := θ.map_smul (b ⊗ₜ[A] c) (n ⊗ₜ[A] (1 : B))
      rwa [double_smul, smul_eq_mul, mul_one] at this
    change x ⊗ₜ[A] θ ((b • n) ⊗ₜ[A] c) =
      outputScale b c (x ⊗ₜ[A] θ (n ⊗ₜ[A] (1 : B)))
    rw [comparison, outputScale_tmul]

private theorem move02_tmul (n : N) (b c : B) :
    move02 θ ((n ⊗ₜ[A] b) ⊗ₜ[A] c) = insertMiddle b (θ (n ⊗ₜ[A] c)) := rfl

private theorem insertMiddle_scale (b c : B) (z : B ⊗[A] N) :
    insertMiddle b ((((1 : B) ⊗ₜ[A] c) • z)) =
      outputScale b c (insertMiddle (1 : B) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, map_add]
  | tmul x n =>
    rw [double_smul, one_smul, insertMiddle_tmul, insertMiddle_tmul, outputScale_tmul, double_smul,
      smul_eq_mul, mul_one]

/-- The entire coefficient cocycle follows from its values on tensors with
the two unaffected coefficient factors equal to one. -/
theorem coefficientCocycle_of_unit_tensors
    (cocycle : ∀ n : N, move12 θ (move01 θ ((n ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B))) =
      move02 θ ((n ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B))) :
    (move12 θ).comp (move01 θ) = move02 θ := by
  apply TensorProduct.ext_threefold
  intro n b c
  have θunit (s : B) :
      θ (n ⊗ₜ[A] s) = ((1 : B) ⊗ₜ[A] s) • θ (n ⊗ₜ[A] (1 : B)) := by
    have h := θ.map_smul ((1 : B) ⊗ₜ[A] s) (n ⊗ₜ[A] (1 : B))
    rwa [double_smul, one_smul, smul_eq_mul, mul_one] at h
  change move12 θ (θ (n ⊗ₜ[A] b) ⊗ₜ[A] c) = move02 θ ((n ⊗ₜ[A] b) ⊗ₜ[A] c)
  rw [move02_tmul, θunit b, θunit c, move12_scale, insertMiddle_scale]
  apply congrArg (outputScale b c)
  exact (cocycle n).trans (move02_tmul θ n 1 1)

section Extension

open CategoryTheory ModuleCat
open scoped ChangeOfRings

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f₁ f₂ : R →+* S) (g : S →+* T) {M N : ModuleCat.{u} R}

/-- Extend a double-overlap module map and compare the two iterated
extensions with the extensions along the corresponding composite maps. -/
def scalarExtensionPullHom
    (m : (extendScalars f₁).obj M ⟶ (extendScalars f₂).obj N) :
    (extendScalars (g.comp f₁)).obj M ⟶ (extendScalars (g.comp f₂)).obj N :=
  (extendScalarsComp f₁ g).hom.app M ≫ (extendScalars g).map m ≫
    (extendScalarsComp f₂ g).inv.app N

/-- On the unit tensor the pulled overlap comparison is computed by the
original comparison and the unit of scalar extension along the pair map. -/
theorem scalarExtensionPullHom_unit
    (m : (extendScalars f₁).obj M ⟶ (extendScalars f₂).obj N) (x : M) :
    scalarExtensionPullHom f₁ f₂ g m ((extendRestrictScalarsAdj (g.comp f₁)).unit.app M x) =
      (extendScalarsComp f₂ g).inv.app N
        ((extendRestrictScalarsAdj g).unit.app ((extendScalars f₂).obj N)
          (m ((extendRestrictScalarsAdj f₁).unit.app M x))) := by
  change (extendScalarsComp f₂ g).inv.app N
      ((extendScalars g).map m
        ((extendScalarsComp f₁ g).hom.app M
          ((1 : T) ⊗ₜ[R,g.comp f₁] x))) = _
  rw [extendScalarsComp_hom_app_one_tmul, ExtendScalars.map_tmul]
  rfl

/-- A two-step scalar comparison acts on a unit tensor by applying the
given map between the two extension units. -/
theorem scalarExtensionComp_map_unit (f : R →+* S) (g : S →+* T)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (h : (ModuleCat.extendScalars f).obj M ⟶ N) (m : M) :
    (ModuleCat.extendScalars g).map h
      ((ModuleCat.extendScalarsComp f g).hom.app M
        ((ModuleCat.extendRestrictScalarsAdj (g.comp f)).unit.app M m)) =
    (ModuleCat.extendRestrictScalarsAdj g).unit.app N
      (h ((ModuleCat.extendRestrictScalarsAdj f).unit.app M m)) := by
  let η := (ModuleCat.extendRestrictScalarsAdj g).unit
  let k := (ModuleCat.extendRestrictScalarsAdj f).unit.app M m
  have unit : (ModuleCat.extendScalarsComp f g).hom.app M
      ((ModuleCat.extendRestrictScalarsAdj (g.comp f)).unit.app M m) =
      η.app ((ModuleCat.extendScalars f).obj M) k :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m
  rw [unit]
  exact (congrArg (fun z : (ModuleCat.extendScalars f).obj M ⟶ _ => z k) (η.naturality h)).symm

/-- Replacing the two overlap modules by isomorphic modules commutes with
extending the overlap comparison. -/
theorem scalarExtensionPullHom_rechart (f₁ f₂ : R →+* S) (g : S →+* T)
    {M N : ModuleCat.{u} R} {U V : ModuleCat.{u} S}
    (δ : (ModuleCat.extendScalars f₁).obj M ⟶ (ModuleCat.extendScalars f₂).obj N)
    (e₁ : (ModuleCat.extendScalars f₁).obj M ≅ U)
    (e₂ : (ModuleCat.extendScalars f₂).obj N ≅ V) :
    scalarExtensionPullHom f₁ f₂ g δ ≫
      ((ModuleCat.extendScalarsComp f₂ g).app N ≪≫ (ModuleCat.extendScalars g).mapIso e₂).hom =
    ((ModuleCat.extendScalarsComp f₁ g).app M ≪≫ (ModuleCat.extendScalars g).mapIso e₁).hom ≫
      (ModuleCat.extendScalars g).map (e₁.inv ≫ δ ≫ e₂.hom) := by
  let E := ModuleCat.extendScalars g
  let a := (ModuleCat.extendScalarsComp f₁ g).app M
  let b := (ModuleCat.extendScalarsComp f₂ g).app N
  change (a.hom ≫ E.map δ ≫ b.inv) ≫ (b.hom ≫ E.map e₂.hom) =
    (a.hom ≫ E.map e₁.hom) ≫ E.map (e₁.inv ≫ δ ≫ e₂.hom)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← E.map_comp, ← E.map_comp, e₁.hom_inv_id_assoc]

end Extension

end

end SHIGURE.CoefficientDescent
