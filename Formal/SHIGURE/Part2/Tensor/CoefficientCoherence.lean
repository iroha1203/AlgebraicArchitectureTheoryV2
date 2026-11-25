import Formal.SHIGURE.Part2.Tensor.CoefficientFunctor
import Formal.SHIGURE.Part2.Tensor.ScalarChange

/-!
# Unit and tower comparisons of scalar extension

The module comparisons preserve every extended primitive operation.
Their naturality and the three-stage identity are checked on the
underlying carrier families.
-/

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
variable {sig : Signature.{u}}

/-- A structure-preserving arrow that is invertible on the carriers gives a structured isomorphism. -/
def structureIsoOfCarrierEquiv {A B : TensorStructure k sig} (f : TensorStructure.Hom A B)
    (e : ∀ s, A.carrier s ≃ₗ[k] B.carrier s) (he : ∀ s, f.onSort s = (e s).toLinearMap) : A ≅ B where
  hom := f
  inv :=
    { onSort := fun s => (e s).symm.toLinearMap
      preservesTotal := fun op xs => by
        apply (e _).injective
        have hw := f.preservesTotal op (fun i => (e i.1).symm (xs i))
        simpa only [he, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hw.symm
      preservesQuantity := fun q xs => by
        apply (e _).injective
        have hw := f.preservesQuantity q (fun i => (e i.1).symm (xs i))
        simpa only [he, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hw.symm }
  hom_inv_id := TensorStructure.Hom.ext (funext fun s => LinearMap.ext fun x => by
    change (e s).symm (f.onSort s x) = x
    rw [he, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply])
  inv_hom_id := TensorStructure.Hom.ext (funext fun s => LinearMap.ext fun x => by
    change f.onSort s ((e s).symm x) = x
    rw [he, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])

/-- The scalar unit comparison commutes with the value of each primitive. -/
private theorem scalarUnit_operation {K : Type u} {Γ : List K} {M : K → ModuleCat.{u} k}
    {N : ModuleCat.{u} k} (op : MultilinearMap k (fun i : TensorPosition Γ => M i.1) N)
    (x : ∀ i : TensorPosition Γ, extendCarriers k M k i.1) :
    scalarUnit (extendOperation k M k op x) = op (fun i => scalarUnit (x i)) := by
  have h :
      scalarUnit.toLinearMap.compMultilinearMap (extendOperation k M k op) =
        op.compLinearMap (fun _ => scalarUnit.toLinearMap) := by
    apply multilinear_ext_unit k M k (P := N)
    intro xs
    change scalarUnit (extendOperation k M k op (fun i => (1 : k) ⊗ₜ[k] xs i)) =
      op (fun i => scalarUnit ((1 : k) ⊗ₜ[k] xs i))
    simp only [extendOperation_unit, scalarUnit_tmul, one_smul]
  exact MultilinearMap.congr_fun h x

/-- The unit of scalar extension is an isomorphism of primitive structures. -/
def structureScalarUnit (A : TensorStructure k sig) : extendStructure k k A ≅ A :=
  structureIsoOfCarrierEquiv
    { onSort := fun _ => scalarUnit.toLinearMap
      preservesTotal := fun op x => scalarUnit_operation (A.total op) x
      preservesQuantity := fun q x => scalarUnit_operation (A.quantity q) x }
    (fun _ => scalarUnit) (fun _ => rfl)

/-- The unit of scalar extension is natural in the original realization. -/
def scalarUnitNatIso (k : Type u) [CommRing k] (sig : Signature.{u}) :
    extendStructureFunctor k k sig ≅ 𝟭 (TensorStructure k sig) :=
  NatIso.ofComponents structureScalarUnit (by
    intro A B f
    exact TensorStructure.Hom.ext (funext fun _ => scalarUnit_natural _))

section Tower

variable [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]

/-- The scalar tower comparison commutes with the iterated extension of a primitive. -/
private theorem scalarTower_operation {K : Type u} {Γ : List K} {M : K → ModuleCat.{u} k}
    {N : ModuleCat.{u} k} (op : MultilinearMap k (fun i : TensorPosition Γ => M i.1) N)
    (x : ∀ i : TensorPosition Γ, extendCarriers R (extendCarriers k M R) S i.1) :
    scalarTower (k := k) (R := R) (S := S)
      (extendOperation R (extendCarriers k M R) S
        (N := ModuleCat.of R (R ⊗[k] N)) (extendOperation k M R op) x) =
        extendOperation k M S op (fun i => scalarTower (k := k) (R := R) (S := S) (x i)) := by
  have h :
      ((scalarTower (k := k) (R := R) (S := S) (M := N)).toLinearMap.compMultilinearMap
        (extendOperation R (extendCarriers k M R) S
          (N := ModuleCat.of R (R ⊗[k] N)) (extendOperation k M R op))).compLinearMap
          (fun _ => (scalarTower (k := k) (R := R) (S := S)).symm.toLinearMap) =
        extendOperation k M S op := by
    apply multilinear_ext_unit k M S (P := ModuleCat.of S (S ⊗[k] N))
    intro xs
    have hp (i : TensorPosition Γ) :
        (scalarTower (k := k) (R := R) (S := S)).symm ((1 : S) ⊗ₜ[k] xs i) =
          (1 : S) ⊗ₜ[R] ((1 : R) ⊗ₜ[k] xs i) := by
      apply (scalarTower (k := k) (R := R) (S := S)).injective
      rw [LinearEquiv.apply_symm_apply, scalarTower_tmul, one_smul]
    change scalarTower (k := k) (R := R) (S := S)
        (extendOperation R (extendCarriers k M R) S (N := ModuleCat.of R (R ⊗[k] N))
          (extendOperation k M R op)
          (fun i => (scalarTower (k := k) (R := R) (S := S)).symm ((1 : S) ⊗ₜ[k] xs i))) =
      extendOperation k M S op (fun i => (1 : S) ⊗ₜ[k] xs i)
    rw [funext hp, extendOperation_unit, extendOperation_unit, extendOperation_unit,
      scalarTower_tmul, one_smul]
  have hw := MultilinearMap.congr_fun h
    (fun i => scalarTower (k := k) (R := R) (S := S) (x i))
  change scalarTower (k := k) (R := R) (S := S)
      (extendOperation R (extendCarriers k M R) S (N := ModuleCat.of R (R ⊗[k] N))
        (extendOperation k M R op)
        (fun i => (scalarTower (k := k) (R := R) (S := S)).symm
          (scalarTower (k := k) (R := R) (S := S) (x i)))) = _ at hw
  simpa only [LinearEquiv.symm_apply_apply] using hw

/-- The tower comparison is an isomorphism of primitive structures. -/
def structureScalarTower (A : TensorStructure k sig) :
    extendStructure R S (extendStructure k R A) ≅ extendStructure k S A :=
  structureIsoOfCarrierEquiv
    { onSort := fun _ => (scalarTower (k := k) (R := R) (S := S)).toLinearMap
      preservesTotal := fun op x => scalarTower_operation (A.total op) x
      preservesQuantity := fun q x => scalarTower_operation (A.quantity q) x }
    (fun _ => scalarTower (k := k) (R := R) (S := S)) (fun _ => rfl)

/-- The tower comparison is natural in the original realization. -/
def scalarTowerNatIso (sig : Signature.{u}) :
    extendStructureFunctor k R sig ⋙ extendStructureFunctor R S sig ≅ extendStructureFunctor k S sig :=
  NatIso.ofComponents structureScalarTower (by
    intro A B f
    exact TensorStructure.Hom.ext (funext fun _ => scalarTower_natural _))

variable {T : Type u} [CommRing T] [Algebra k T] [Algebra R T] [Algebra S T]
variable [IsScalarTower k R T] [IsScalarTower k S T] [IsScalarTower R S T]

/-- Both comparisons for three successive coefficient changes give the same arrow. -/
theorem structureScalarTower_three (A : TensorStructure k sig) :
    (extendStructureFunctor S T sig).map (structureScalarTower (R := R) (S := S) A).hom ≫
      (structureScalarTower (R := S) (S := T) A).hom =
    (structureScalarTower (R := S) (S := T) (extendStructure k R A)).hom ≫
      (structureScalarTower (R := R) (S := T) A).hom :=
  TensorStructure.Hom.ext (funext fun _ => scalarTower_three)

end Tower

end SHIGURE.TensorRealization
