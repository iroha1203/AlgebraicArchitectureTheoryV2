import Formal.SHIGURE.Part2.Descent.Overlap
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Scalar extensions in tensor coordinates -/

namespace SHIGURE.CoefficientDescent

open TensorProduct CategoryTheory ModuleCat
open scoped ChangeOfRings

noncomputable section

universe u

section ModuleAction

variable {A B C X Y : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
  [AddCommGroup Y] [Module A Y] [Module C Y] [IsScalarTower A C Y]

/-- The tensor of the two scalar actions for independent coefficient algebras. -/
def tensorModuleAction : B ⊗[A] C →ₐ[A] Module.End A (X ⊗[A] Y) :=
  (Module.endTensorEndAlgHom (R := A) (S := A) (A := A) (M := X) (N := Y)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul A A X : B →ₐ[A] Module.End A X)
      (Algebra.lsmul A A Y : C →ₐ[A] Module.End A Y))

/-- The coefficient algebra acts independently on the two slots. This action
lets scalar extension be compared with tensor coordinates in the specified order. -/
def tensorProductModule : Module (B ⊗[A] C) (X ⊗[A] Y) :=
  Module.compHom _ (tensorModuleAction (A := A) (B := B) (C := C) (X := X) (Y := Y)).toRingHom

attribute [local instance] tensorProductModule

/-- On pure tensors, the actions are the two original scalar multiplications. -/
@[simp]
theorem tensorProductModule_smul (b : B) (c : C) (x : X) (y : Y) :
    (b ⊗ₜ[A] c) • (x ⊗ₜ[A] y) = (b • x) ⊗ₜ[A] (c • y) := by
  change tensorModuleAction (b ⊗ₜ[A] c) (x ⊗ₜ[A] y) = _
  rw [tensorModuleAction, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Module.endTensorEndAlgHom_apply]
  rfl

/-- Restriction to the common base algebra gives the original tensor action. -/
instance tensorProductModule_tower : IsScalarTower A (B ⊗[A] C) (X ⊗[A] Y) :=
  IsScalarTower.of_algebraMap_smul (fun a v => by
    change tensorModuleAction (algebraMap A (B ⊗[A] C) a) v = a • v
    rw [AlgHom.commutes]
    rfl)

end ModuleAction

section Left
variable {A B C N : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- The first scalar embedding of the tensor product of algebras. -/
abbrev firstMixedEmbedding (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] :
    B →+* B ⊗[A] C :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C).toRingHom

local notation "D" => B ⊗[A] C
local notation "left" => firstMixedEmbedding A B C
local notation "Extended" => ModuleCat.ExtendScalars.obj' (firstMixedEmbedding A B C) (ModuleCat.of B N)

private abbrev leftTensor (d : D) (n : N) : Extended :=
  d ⊗ₜ[B,left] n

omit [Module A N] [IsScalarTower A B N] in
private theorem leftTensor_move (b : B) (d : D) (n : N) :
    leftTensor d (b • n) = leftTensor (left b * d) n := by
  let d' : (ModuleCat.restrictScalars left).obj (ModuleCat.of D D) := d
  exact (TensorProduct.smul_tmul (R := B) b d' n).symm

omit [Module A N] [IsScalarTower A B N] in
private theorem leftTensor_add_left (d e : D) (n : N) :
    leftTensor (d + e) n = leftTensor d n + leftTensor e n := by
  let d' : (ModuleCat.restrictScalars left).obj (ModuleCat.of D D) := d
  let e' : (ModuleCat.restrictScalars left).obj (ModuleCat.of D D) := e
  exact TensorProduct.add_tmul d' e' n

attribute [local instance] tensorProductModule

private def leftOverlapInsert :
    ModuleCat.of B N ⟶ (ModuleCat.restrictScalars left).obj (ModuleCat.of D (N ⊗[A] C)) := by
  letI : Module B (N ⊗[A] C) := Module.compHom _ left
  exact ModuleCat.ofHom {
    toFun n := n ⊗ₜ[A] (1 : C)
    map_add' n m := TensorProduct.add_tmul _ _ _
    map_smul' b n := by
      change (b • n) ⊗ₜ[A] (1 : C) = (b ⊗ₜ[A] (1 : C)) • (n ⊗ₜ[A] (1 : C))
      rw [tensorProductModule_smul, one_smul]
  }

private def mixedLeftExtension : Extended ⟶ ModuleCat.of D (N ⊗[A] C) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars left leftOverlapInsert

private theorem mixedLeftExtension_tmul (d : D) (n : N) :
    (mixedLeftExtension (A := A) (B := B) (C := C) (N := N)) (leftTensor d n) =
      d • (n ⊗ₜ[A] (1 : C)) := by
  letI : Module B (N ⊗[A] C) := Module.compHom _ left
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  rfl

private def leftOverlapReturn : letI : Module A Extended := Module.compHom _ (algebraMap A D)
    (N ⊗[A] C) →ₗ[A] Extended := by
  letI : Module A Extended := Module.compHom _ (algebraMap A D)
  refine TensorProduct.lift {
    toFun n := {
      toFun c := leftTensor ((1 : B) ⊗ₜ[A] c) n
      map_add' c c' := by rw [tmul_add, leftTensor_add_left]
      map_smul' a c := by
        change leftTensor ((1 : B) ⊗ₜ[A] (a • c)) n =
          leftTensor (algebraMap A D a * ((1 : B) ⊗ₜ[A] c)) n
        rw [← Algebra.smul_def, tmul_smul] }
    map_add' n n' := by
      ext c
      exact tmul_add _ _ _
    map_smul' a n := by
      ext c
      change leftTensor ((1 : B) ⊗ₜ[A] c) (a • n) =
        leftTensor (algebraMap A D a * ((1 : B) ⊗ₜ[A] c)) n
      rw [← IsScalarTower.algebraMap_smul B a n, leftTensor_move]
      have h : left (algebraMap A B a) = algebraMap A D a :=
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] D).commutes a
      rw [h]
  }

private theorem leftOverlapReturn_tmul (n : N) (c : C) :
    leftOverlapReturn (n ⊗ₜ[A] c) = (leftTensor ((1 : B) ⊗ₜ[A] c) n : Extended) := rfl

private theorem mixedLeftExtension_bijective :
    Function.Bijective (mixedLeftExtension (A := A) (B := B) (C := C) (N := N)) := by
  letI : Module A Extended := Module.compHom _ (algebraMap A D)
  refine ⟨?_, ?_⟩
  · apply Function.LeftInverse.injective (g := leftOverlapReturn)
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul d n =>
      rw [mixedLeftExtension_tmul]
      change D at d
      induction d using TensorProduct.induction_on with
      | zero => rw [zero_smul, map_zero, zero_tmul]
      | add x y hx hy => rw [add_smul, map_add, add_tmul, hx, hy]
      | tmul b c =>
        have product : left b * ((1 : B) ⊗ₜ[A] c) = b ⊗ₜ[A] c := by
          change ((b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c)) = b ⊗ₜ[A] c
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [tensorProductModule_smul, smul_eq_mul, mul_one, leftOverlapReturn_tmul, leftTensor_move, product]
  · intro z
    refine ⟨leftOverlapReturn z, ?_⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul n c =>
      rw [leftOverlapReturn_tmul, mixedLeftExtension_tmul, tensorProductModule_smul, one_smul, smul_eq_mul, mul_one]

/-- The first scalar extension is the tensor of the given module with the second coefficient algebra. -/
def mixedLeftExtensionIso : Extended ≅ ModuleCat.of D (N ⊗[A] C) :=
  (LinearEquiv.ofBijective (mixedLeftExtension (A := A) (B := B) (C := C) (N := N)).hom
    mixedLeftExtension_bijective).toModuleIso

/-- The first comparison sends the unit tensor to the chart as a pure tensor. -/
theorem mixedLeftExtensionIso_unit (n : N) :
    (mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := N)).hom
      ((ModuleCat.extendRestrictScalarsAdj left).unit.app (ModuleCat.of B N) n) =
      n ⊗ₜ[A] (1 : C) := by
  change mixedLeftExtension (leftTensor (1 : D) n) = _
  rw [mixedLeftExtension_tmul, one_smul]


end Left

section Right

variable {A B C N : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower A C N]

/-- The second scalar embedding of the tensor product of algebras. -/
abbrev secondMixedEmbedding (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] : C →+* B ⊗[A] C :=
  (Algebra.TensorProduct.comm A C B).toRingHom.comp (firstMixedEmbedding A C B)

/-- Normalize evaluation of the second embedding to a pure tensor with unit on the left. -/
@[simp]
theorem secondMixedEmbedding_apply (c : C) :
    secondMixedEmbedding A B C c = (1 : B) ⊗ₜ[A] c := rfl

local notation "D" => B ⊗[A] C
local notation "otherLeft" => firstMixedEmbedding A C B

attribute [local instance] tensorProductModule

private def mixedSwapModules :
    (ModuleCat.restrictScalars (Algebra.TensorProduct.comm A C B).symm.toRingHom).obj
      (ModuleCat.of (C ⊗[A] B) (N ⊗[A] B)) ≅ ModuleCat.of D (B ⊗[A] N) :=
  LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars (Algebra.TensorProduct.comm A C B).symm.toRingHom).obj
      (ModuleCat.of (C ⊗[A] B) (N ⊗[A] B)))
    (X₂ := ModuleCat.of D (B ⊗[A] N)) {
    __ := (TensorProduct.comm A N B).toAddEquiv
    map_smul' d x := by
      change N ⊗[A] B at x
      change TensorProduct.comm A N B ((Algebra.TensorProduct.comm A C B).symm d • x) =
        d • TensorProduct.comm A N B x
      induction d using TensorProduct.induction_on with
      | zero => rw [map_zero, zero_smul, map_zero, zero_smul]
      | add d e hd he => rw [map_add, add_smul, map_add, hd, he, add_smul]
      | tmul b c =>
        change TensorProduct.comm A N B ((c ⊗ₜ[A] b) • x) =
          (b ⊗ₜ[A] c) • TensorProduct.comm A N B x
        induction x using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | add y z hy hz => rw [smul_add, map_add, hy, hz, map_add, smul_add]
        | tmul n x =>
          rw [tensorProductModule_smul, TensorProduct.comm_tmul, TensorProduct.comm_tmul, tensorProductModule_smul]
  }

/-- Extension of scalars along a ring equivalence is restriction along its inverse. -/
def scalarExtensionEquivIso {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    ModuleCat.extendScalars e.toRingHom ≅ ModuleCat.restrictScalars e.symm.toRingHom :=
  (ModuleCat.extendRestrictScalarsAdj e.toRingHom).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

/-- The second scalar extension is the tensor of the first coefficient algebra with the given module. -/
def mixedRightExtensionIso :
    (ModuleCat.extendScalars (secondMixedEmbedding A B C)).obj (ModuleCat.of C N) ≅
      ModuleCat.of D (B ⊗[A] N) := by
  let e := (Algebra.TensorProduct.comm A C B).toRingEquiv
  let base := ModuleCat.of C N
  let leftModule := ModuleCat.of (C ⊗[A] B) (N ⊗[A] B)
  let composition := (ModuleCat.extendScalarsComp otherLeft e.toRingHom).app base
  let swapScalars := (scalarExtensionEquivIso e).app leftModule
  exact composition ≪≫ (ModuleCat.extendScalars e.toRingHom).mapIso mixedLeftExtensionIso ≪≫
    swapScalars ≪≫ mixedSwapModules

/-- The scalar comparison sends each unit tensor to its original element. -/
theorem scalarExtensionEquivIso_unit {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u} R) (x : M) :
    (scalarExtensionEquivIso e).hom.app M
      ((ModuleCat.extendRestrictScalarsAdj e.toRingHom).unit.app M x) = x := by
  let a := ModuleCat.extendRestrictScalarsAdj e.toRingHom
  let b := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction
  have equal := Adjunction.unit_leftAdjointUniq_hom_app a b M
  exact congrArg (fun m : M ⟶ _ => m x) equal

/-- The second comparison sends the unit tensor to the chart at the second position. -/
theorem mixedRightExtensionIso_unit (n : N) :
    (mixedRightExtensionIso (A := A) (B := B) (C := C) (N := N)).hom
      ((ModuleCat.extendRestrictScalarsAdj (secondMixedEmbedding A B C)).unit.app (ModuleCat.of C N) n) =
      (1 : B) ⊗ₜ[A] n := by
  let e := (Algebra.TensorProduct.comm A C B).toRingEquiv
  let M := ModuleCat.of C N
  let LM := ModuleCat.of (C ⊗[A] B) (N ⊗[A] B)
  let extend := ModuleCat.extendScalars e.toRingHom
  let x := mixedLeftExtensionIso (A := A) (B := C) (C := B) (N := N)
  let y := mixedSwapModules (A := A) (B := B) (C := C) (N := N)
  let z := (scalarExtensionEquivIso e).app LM
  let m₁ := (ModuleCat.extendRestrictScalarsAdj otherLeft).unit.app M n
  let u := (ModuleCat.extendRestrictScalarsAdj e.toRingHom).unit
  let comp := (ModuleCat.extendScalarsComp otherLeft e.toRingHom).hom.app M
  let m₂ := (ModuleCat.extendRestrictScalarsAdj (secondMixedEmbedding A B C)).unit.app M n
  have h₁ : comp m₂ = u.app _ m₁ :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul otherLeft e.toRingHom M n
  have h₂ : (extend.map x.hom) (u.app _ m₁) = u.app LM (x.hom m₁) := by
    have natural := u.naturality x.hom
    exact congrArg (fun m : (ModuleCat.extendScalars otherLeft).obj M ⟶ _ => m m₁) natural |>.symm
  have h₃ : z.hom (u.app LM (x.hom m₁)) = x.hom m₁ :=
    scalarExtensionEquivIso_unit e LM (x.hom m₁)
  change y.hom (z.hom ((extend.map x.hom) (comp m₂))) = _
  rw [h₁, h₂, h₃]
  have leftEq : x.hom m₁ = n ⊗ₜ[A] (1 : B) := mixedLeftExtensionIso_unit n
  rw [leftEq]
  change TensorProduct.comm A N B (n ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] n
  rw [TensorProduct.comm_tmul]

end Right

section Maps

variable {A B C X₁ X₂ Y₁ Y₂ : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [AddCommGroup X₁] [Module A X₁] [Module B X₁] [IsScalarTower A B X₁]
  [AddCommGroup X₂] [Module A X₂] [Module B X₂] [IsScalarTower A B X₂]
  [AddCommGroup Y₁] [Module A Y₁] [Module C Y₁] [IsScalarTower A C Y₁]
  [AddCommGroup Y₂] [Module A Y₂] [Module C Y₂] [IsScalarTower A C Y₂]

attribute [local instance] tensorProductModule

/-- Tensoring two module maps gives a map over the tensor product algebra. -/
def tensorProductModuleMap (f : X₁ →ₗ[B] X₂) (g : Y₁ →ₗ[C] Y₂) :
    (X₁ ⊗[A] Y₁) →ₗ[B ⊗[A] C] (X₂ ⊗[A] Y₂) where
  toFun := TensorProduct.map (f.restrictScalars A) (g.restrictScalars A)
  map_add' := map_add _
  map_smul' d v := by
    change TensorProduct.map (f.restrictScalars A) (g.restrictScalars A) (d • v) =
      d • TensorProduct.map (f.restrictScalars A) (g.restrictScalars A) v
    induction d using TensorProduct.induction_on with
    | zero => simp only [zero_smul, map_zero]
    | add d e hd he => rw [add_smul, map_add, hd, he, add_smul]
    | tmul b c =>
      induction v using TensorProduct.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
      | tmul x y =>
        rw [tensorProductModule_smul, map_tmul, map_tmul, tensorProductModule_smul,
          LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, map_smul, map_smul,
          LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply]

/-- On pure tensors the tensor product map acts on each slot. -/
theorem tensorProductModuleMap_tmul (f : X₁ →ₗ[B] X₂) (g : Y₁ →ₗ[C] Y₂) (x : X₁) (y : Y₁) :
    tensorProductModuleMap f g (x ⊗ₜ[A] y) = f x ⊗ₜ[A] g y := rfl

end Maps

section Naturality

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

attribute [local instance] tensorProductModule

/-- Extending scalars along the first embedding acts on the first tensor slot. -/
theorem mixedLeftExtensionIso_natural {M N : ModuleCat.{u} B}
    [Module A M] [Module A N] [IsScalarTower A B M] [IsScalarTower A B N] (f : M ⟶ N) :
    (ModuleCat.extendScalars (firstMixedEmbedding A B C)).map f ≫
      (mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := N)).hom =
    (mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := M)).hom ≫
      ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := C) f.hom (LinearMap.id (R := C) (M := C))) := by
  let ext := ModuleCat.extendScalars (firstMixedEmbedding A B C)
  let unit := (ModuleCat.extendRestrictScalarsAdj (firstMixedEmbedding A B C)).unit
  let l := mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := M)
  let r := mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := N)
  let m := tensorProductModuleMap (A := A) (B := B) (C := C) f.hom (LinearMap.id (R := C) (M := C))
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change r.hom (ext.map f (unit.app M x)) = m (l.hom (unit.app M x))
  have h : ext.map f (unit.app M x) = unit.app N (f x) :=
    (congrArg (fun z : M ⟶ _ => z x) (unit.naturality f)).symm
  rw [h]
  have hx := mixedLeftExtensionIso_unit (A := A) (B := B) (C := C) (N := M) x
  have hy := mixedLeftExtensionIso_unit (A := A) (B := B) (C := C) (N := N) (f x)
  change r.hom (unit.app N (f x)) = m (l.hom (unit.app M x))
  rw [show r.hom (unit.app N (f x)) = _ from hy, show l.hom (unit.app M x) = _ from hx]
  exact (tensorProductModuleMap_tmul (A := A) (B := B) (C := C) f.hom (LinearMap.id (R := C) (M := C)) x (1 : C)).symm

/-- Extending scalars along the second embedding acts on the second tensor slot. -/
theorem mixedRightExtensionIso_natural {M N : ModuleCat.{u} C}
    [Module A M] [Module A N] [IsScalarTower A C M] [IsScalarTower A C N] (f : M ⟶ N) :
    (ModuleCat.extendScalars (secondMixedEmbedding A B C)).map f ≫
      (mixedRightExtensionIso (A := A) (B := B) (C := C) (N := N)).hom =
    (mixedRightExtensionIso (A := A) (B := B) (C := C) (N := M)).hom ≫
      ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := C) (LinearMap.id (R := B) (M := B)) f.hom) := by
  let ext := ModuleCat.extendScalars (secondMixedEmbedding A B C)
  let unit := (ModuleCat.extendRestrictScalarsAdj (secondMixedEmbedding A B C)).unit
  let l := mixedRightExtensionIso (A := A) (B := B) (C := C) (N := M)
  let r := mixedRightExtensionIso (A := A) (B := B) (C := C) (N := N)
  let m := tensorProductModuleMap (A := A) (B := B) (C := C) (LinearMap.id (R := B) (M := B)) f.hom
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change r.hom (ext.map f (unit.app M x)) = m (l.hom (unit.app M x))
  have h : ext.map f (unit.app M x) = unit.app N (f x) :=
    (congrArg (fun z : M ⟶ _ => z x) (unit.naturality f)).symm
  rw [h]
  have hx := mixedRightExtensionIso_unit (A := A) (B := B) (C := C) (N := M) x
  have hy := mixedRightExtensionIso_unit (A := A) (B := B) (C := C) (N := N) (f x)
  rw [show r.hom (unit.app N (f x)) = _ from hy, show l.hom (unit.app M x) = _ from hx]
  exact (tensorProductModuleMap_tmul (A := A) (B := B) (C := C) (LinearMap.id (R := B) (M := B)) f.hom (1 : B) x).symm

end Naturality


section Association

variable {A B C D X Y Z : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
  [AddCommGroup Y] [Module A Y] [Module C Y] [IsScalarTower A C Y]
  [AddCommGroup Z] [Module A Z] [Module D Z] [IsScalarTower A D Z]

attribute [local instance] tensorProductModule

local notation "L" => (B ⊗[A] C) ⊗[A] D
local notation "R" => B ⊗[A] (C ⊗[A] D)
local notation "ML" => (X ⊗[A] Y) ⊗[A] Z
local notation "MR" => X ⊗[A] (Y ⊗[A] Z)

/-- The associator on three tensor factors respects the actions of the
three ordered coefficient rings. -/
def tensorProductModuleAssocIso :
    (ModuleCat.restrictScalars (Algebra.TensorProduct.assoc A A A B C D).symm.toRingHom).obj
      (ModuleCat.of L ML) ≅ ModuleCat.of R MR :=
  LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars (Algebra.TensorProduct.assoc A A A B C D).symm.toRingHom).obj
      (ModuleCat.of L ML))
    (X₂ := ModuleCat.of R MR) {
    __ := (TensorProduct.assoc A X Y Z).toAddEquiv
    map_smul' d v := by
      change ML at v
      let E := Algebra.TensorProduct.assoc A A A B C D
      let T := TensorProduct.assoc A X Y Z
      change T (E.symm d • v) = d • T v
      induction d using TensorProduct.induction_on with
      | zero => simp only [map_zero, zero_smul]
      | add d e hd he => simp only [map_add, add_smul, hd, he]
      | tmul b cd =>
        induction cd using TensorProduct.induction_on with
        | zero => simp only [tmul_zero, map_zero, zero_smul]
        | add s t hs ht => simp only [tmul_add, map_add, add_smul, hs, ht]
        | tmul c d =>
          change T (((b ⊗ₜ[A] c) ⊗ₜ[A] d) • v) = (b ⊗ₜ[A] (c ⊗ₜ[A] d)) • T v
          induction v using TensorProduct.induction_on with
          | zero => simp only [smul_zero, map_zero]
          | add v w hv hw => simp only [smul_add, map_add, hv, hw]
          | tmul xy z =>
            induction xy using TensorProduct.induction_on with
            | zero => simp only [zero_tmul, smul_zero, map_zero]
            | add x y hx hy => simp only [add_tmul, smul_add, map_add, hx, hy]
            | tmul x y =>
              dsimp only [T]
              simp only [tensorProductModule_smul, TensorProduct.assoc_tmul]
  }

end Association

section SwapLast

variable {A B C D X Y Z : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
  [AddCommGroup Y] [Module A Y] [Module C Y] [IsScalarTower A C Y]
  [AddCommGroup Z] [Module A Z] [Module D Z] [IsScalarTower A D Z]

attribute [local instance] tensorProductModule

local notation "L" => B ⊗[A] (C ⊗[A] D)
local notation "R" => B ⊗[A] (D ⊗[A] C)
local notation "ML" => X ⊗[A] (Y ⊗[A] Z)
local notation "MR" => X ⊗[A] (Z ⊗[A] Y)
local notation "swap" => Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) (Algebra.TensorProduct.comm A C D)

/-- Interchanging the last two tensor factors also interchanges the corresponding
coefficient actions. -/
def tensorProductModuleSwapLastIso :
    (ModuleCat.restrictScalars (AlgEquiv.symm swap).toRingHom).obj
      (ModuleCat.of L ML) ≅ ModuleCat.of R MR :=
  LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars (AlgEquiv.symm swap).toRingHom).obj (ModuleCat.of L ML))
    (X₂ := ModuleCat.of R MR) {
    __ := (TensorProduct.congr (LinearEquiv.refl A X) (TensorProduct.comm A Y Z)).toAddEquiv
    map_smul' d m := by
      change ML at m
      let e := swap
      let v := TensorProduct.congr (LinearEquiv.refl A X) (TensorProduct.comm A Y Z)
      change v (e.symm d • m) = d • v m
      induction d using TensorProduct.induction_on with
      | zero => rw [map_zero, zero_smul, map_zero, zero_smul]
      | add a b ha hb => rw [map_add, add_smul, map_add, ha, hb, add_smul]
      | tmul b dc =>
        induction dc using TensorProduct.induction_on with
        | zero => simp only [tmul_zero, map_zero, zero_smul]
        | add s t hs ht => simp only [tmul_add, map_add, add_smul, hs, ht]
        | tmul d c =>
          change v ((b ⊗ₜ[A] (c ⊗ₜ[A] d)) • m) = (b ⊗ₜ[A] (d ⊗ₜ[A] c)) • v m
          induction m using TensorProduct.induction_on with
          | zero => simp only [smul_zero, map_zero]
          | add y z hy hz => simp only [smul_add, map_add, hy, hz]
          | tmul x yz =>
            induction yz using TensorProduct.induction_on with
            | zero => simp only [tmul_zero, smul_zero, map_zero]
            | add y z hy hz => simp only [tmul_add, smul_add, map_add, hy, hz]
            | tmul y z =>
              dsimp only [v]
              simp only [tensorProductModule_smul, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
                TensorProduct.comm_tmul]
  }


end SwapLast

section EqualCoefficients

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

attribute [local instance] doubleModule

/-- The first scalar embedding of the double tensor algebra. -/
abbrev firstScalarEmbedding (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    B →+* B ⊗[A] B :=
  firstMixedEmbedding A B B

/-- Interchange the two coefficient factors of the double overlap. -/
abbrev overlapCoefficientSwap (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (B ⊗[A] B) ≃ₐ[A] (B ⊗[A] B) :=
  Algebra.TensorProduct.comm A B B

/-- The second scalar embedding of the double tensor algebra. -/
abbrev secondScalarEmbedding (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    B →+* B ⊗[A] B :=
  secondMixedEmbedding A B B

/-- Normalize evaluation of the second overlap embedding to a pure tensor with unit on the left. -/
@[simp]
theorem secondScalarEmbedding_apply (b : B) :
    secondScalarEmbedding A B b = (1 : B) ⊗ₜ[A] b := rfl

/-- The first scalar extension in the ordered coefficient descent coordinates. -/
abbrev leftOverlapExtensionIso :
    (ModuleCat.extendScalars (firstScalarEmbedding A B)).obj (ModuleCat.of B N) ≅
      ModuleCat.of (B ⊗[A] B) (N ⊗[A] B) :=
  mixedLeftExtensionIso (A := A) (B := B) (C := B) (N := N)

/-- The second scalar extension in the ordered coefficient descent coordinates. -/
abbrev rightOverlapExtensionIso :
    (ModuleCat.extendScalars (secondScalarEmbedding A B)).obj (ModuleCat.of B N) ≅
      ModuleCat.of (B ⊗[A] B) (B ⊗[A] N) :=
  mixedRightExtensionIso (A := A) (B := B) (C := B) (N := N)

/-- In the first overlap module the unit tensor has the coefficient on the right. -/
theorem leftOverlapExtensionIso_unit (n : N) :
    (leftOverlapExtensionIso (A := A) (B := B) (N := N)).hom
      ((ModuleCat.extendRestrictScalarsAdj (firstScalarEmbedding A B)).unit.app (ModuleCat.of B N) n) =
      n ⊗ₜ[A] (1 : B) :=
  mixedLeftExtensionIso_unit (A := A) (B := B) (C := B) (N := N) n

/-- In the second overlap module the unit tensor has the coefficient on the left. -/
theorem rightOverlapExtensionIso_unit (n : N) :
    (rightOverlapExtensionIso (A := A) (B := B) (N := N)).hom
      ((ModuleCat.extendRestrictScalarsAdj (secondScalarEmbedding A B)).unit.app (ModuleCat.of B N) n) =
      (1 : B) ⊗ₜ[A] n :=
  mixedRightExtensionIso_unit (A := A) (B := B) (C := B) (N := N) n

end EqualCoefficients

section RingEquivalence

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (e : S ≃+* T)

/-- Extension along a composite with a ring equivalence is the original
extension with the scalar action transported to the new ring. -/
def scalarExtensionEquivCompIso :
    ModuleCat.extendScalars (e.toRingHom.comp f) ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars e.symm.toRingHom :=
  ModuleCat.extendScalarsComp f e.toRingHom ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f) (scalarExtensionEquivIso e)

/-- The composite comparison preserves the unit tensor under transport of scalars. -/
theorem scalarExtensionEquivCompIso_unit (M : ModuleCat.{u} R) (m : M) :
    (scalarExtensionEquivCompIso f e).hom.app M
      ((ModuleCat.extendRestrictScalarsAdj (e.toRingHom.comp f)).unit.app M m) =
    (ModuleCat.extendRestrictScalarsAdj f).unit.app M m := by
  let N := (ModuleCat.extendScalars f).obj M
  let x := (ModuleCat.extendRestrictScalarsAdj f).unit.app M m
  let y := (ModuleCat.extendRestrictScalarsAdj (e.toRingHom.comp f)).unit.app M m
  let comp := (ModuleCat.extendScalarsComp f e.toRingHom).hom.app M
  let last := (scalarExtensionEquivIso e).hom.app N
  have fact : comp y = (ModuleCat.extendRestrictScalarsAdj e.toRingHom).unit.app N x :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul f e.toRingHom M m
  change last (comp y) = x
  rw [fact]
  exact scalarExtensionEquivIso_unit e N x

end RingEquivalence

end

end SHIGURE.CoefficientDescent
