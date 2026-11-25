import Formal.SHIGURE.Part2.Tensor.DomainNativeMaps
import Mathlib.Data.ZMod.Basic

/-!
# A unary tensor operation with a specified domain

The two domain choices and two value maps give equal carrier reducts.
The diagram arrows check both that the input lies in the target domain
and that the value in that domain commutes with the output map.
-/

open CategoryTheory SHIGURE.TensorRealization
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorDomainStructure

/-- A single carrier and unary partial operation. -/
private def unaryPartialSignature : Signature.{u} where
  SortType := PUnit
  Total := PEmpty
  Rel := PEmpty
  Partial := PUnit
  Quantity := PEmpty
  totalArity n := nomatch n
  relInputs n := nomatch n
  partialArity _ := ⟨[PUnit.unit], PUnit.unit⟩
  quantityArity n := nomatch n

variable (k : Type u) [CommRing k]

/-- The input tensor of the unary scalar example. -/
private abbrev unaryInput := InputTensor k (fun _ : PUnit.{u + 1} => ModuleCat.of k k) [PUnit.unit]

/-- Read the product of the carrier entries in the unary tensor. -/
private def unaryRead : unaryInput k →ₗ[k] k := by
  letI : Fintype (TensorPosition [(PUnit.unit : PUnit.{u + 1})]) := Fintype.ofFinite _
  exact PiTensorProduct.lift (MultilinearMap.mkPiAlgebra k _ k)

/-- The input tuple with value one. -/
private def unaryOne : unaryInput k := PiTensorProduct.tprod k (fun _ => (1 : k))

private theorem unaryRead_one : unaryRead k (unaryOne k) = 1 := by
  simp [unaryRead, unaryOne, MultilinearMap.mkPiAlgebra_apply]

/-- The unary operation has a selected input submodule and a scalar multiple of the unary reading. -/
private def unaryModel (large : Bool) (value : k) : Diagrams k unaryPartialSignature.{u} where
  toTensorStructure := {
    carrier := fun _ => ModuleCat.of k k
    total f := nomatch f
    quantity q := nomatch q }
  rel r := nomatch r
  dom _ := if large then ⊤ else ⊥
  partialValue _ := value • (unaryRead k).comp (if large then ⊤ else ⊥ : Submodule k (unaryInput k)).subtype

/-- Both selected domains split, so their partial operations extend over every coefficient algebra. -/
theorem unaryModel_admitsBaseChange (large : Bool) (value : k) : (unaryModel k large value).AdmitsBaseChange := by
  intro p
  cases large with
  | false =>
    change UniversallyInjective (⊥ : Submodule k (unaryInput k)).subtype
    refine universallyInjective_of_retraction _ 0 ?_
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (show x.val = 0 from x.property).symm
  | true =>
    change UniversallyInjective (⊤ : Submodule k (unaryInput k)).subtype
    refine universallyInjective_of_retraction _ (Submodule.topEquiv.symm.toLinearMap) ?_
    apply LinearMap.ext
    intro x
    exact Submodule.topEquiv.symm_apply_apply x

/-- The identity on the carrier cannot take the whole declared domain into the zero domain. -/
theorem unaryModel_identity_changesDomain [Nontrivial k] :
    ¬ ∃ f : unaryModel k true 0 ⟶ unaryModel k false 0, (f.val PUnit.unit).hom = (LinearMap.id : k →ₗ[k] k) := by
  rintro ⟨f, f_id⟩
  let x : (unaryModel k true 0).dom PUnit.unit := ⟨unaryOne k, Submodule.mem_top⟩
  have h := (readLinearArrow f).domain PUnit.unit x
  have eq : inputMap (forgetHom f) [PUnit.unit] x.val = unaryOne k := by
    have carrierMap : (fun i : TensorPosition [(PUnit.unit : PUnit.{u + 1})] =>
        (f.val i.1).hom) = fun _ => (LinearMap.id : k →ₗ[k] k) := by
      funext i
      have hs : i.1 = PUnit.unit := Subsingleton.elim _ _
      simpa only [hs] using f_id
    change PiTensorProduct.map (fun i : TensorPosition [(PUnit.unit : PUnit.{u + 1})] =>
      (f.val i.1).hom) (unaryOne k) = _
    rw [carrierMap, PiTensorProduct.map_id]
    rfl
  change inputMap (forgetHom f) [PUnit.unit] x.val ∈ (⊥ : Submodule k (unaryInput k)) at h
  rw [eq] at h
  have v := congrArg (unaryRead k) (show unaryOne k = 0 from h)
  rw [unaryRead_one, map_zero] at v
  exact one_ne_zero v

/-- Even on equal domains, the identity on the carrier must preserve the partial value. -/
theorem unaryModel_identity_changesValue [Nontrivial k] :
    ¬ ∃ f : unaryModel k true 1 ⟶ unaryModel k true 0, (f.val PUnit.unit).hom = (LinearMap.id : k →ₗ[k] k) := by
  rintro ⟨f, f_id⟩
  let x : (unaryModel k true 1).dom PUnit.unit := ⟨unaryOne k, Submodule.mem_top⟩
  have h := (readLinearArrow f).value PUnit.unit x
  change (f.val PUnit.unit).hom ((1 : k) • unaryRead k (unaryOne k)) = (0 : k) • _ at h
  rw [f_id] at h
  change (1 : k) • unaryRead k (unaryOne k) = (0 : k) • _ at h
  rw [one_smul, zero_smul, unaryRead_one] at h
  exact one_ne_zero h

/-- The even multiples of the unary input generator give a selected integral submodule. -/
private def twiceUnary : ℤ →ₗ[ℤ] unaryInput ℤ :=
  (2 : ℤ) • LinearMap.toSpanSingleton ℤ (unaryInput ℤ) (unaryOne ℤ)

private theorem twiceUnary_injective : Function.Injective twiceUnary := by
  intro a b h
  have hv := congrArg (unaryRead ℤ) h
  have nat (x : ℤ) : unaryRead ℤ (twiceUnary x) = 2 * x := by
    rw [twiceUnary, LinearMap.smul_apply, LinearMap.toSpanSingleton_apply, map_smul, map_smul,
      unaryRead_one, smul_eq_mul, smul_eq_mul, mul_one]
  rw [nat, nat] at hv
  omega

/-- The unary operation is defined on the even part of the integral input tensor. -/
private def evenUnaryModel : Diagrams ℤ unaryPartialSignature.{0} where
  toTensorStructure := (unaryModel ℤ true 0).toTensorStructure
  rel r := nomatch r
  dom _ := LinearMap.range twiceUnary
  partialValue _ := 0

/-- The even submodule inclusion loses injectivity after scalar extension modulo two. -/
theorem evenUnaryModel_not_admitsBaseChange : ¬ evenUnaryModel.AdmitsBaseChange := by
  intro h
  let e := LinearEquiv.ofInjective twiceUnary twiceUnary_injective
  let z : ZMod 2 ⊗[ℤ] LinearMap.range twiceUnary := (1 : ZMod 2) ⊗ₜ[ℤ] e 1
  have hz : z ≠ 0 := by
    intro eq
    have v := congrArg (fun t => extendScalarSort (k := ℤ) (ZMod 2)
      ((e.symm.toLinearMap.baseChange (ZMod 2)) t)) eq
    change extendScalarSort (k := ℤ) (ZMod 2)
        ((e.symm.toLinearMap.baseChange (ZMod 2)) ((1 : ZMod 2) ⊗ₜ[ℤ] e 1)) =
        extendScalarSort (k := ℤ) (ZMod 2) ((e.symm.toLinearMap.baseChange (ZMod 2)) 0) at v
    rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      extendScalarSort_tmul, one_smul, map_zero, map_zero] at v
    exact one_ne_zero v
  apply hz ((h PUnit.unit (ZMod 2)) ?_)
  change (((LinearMap.range twiceUnary).subtype).baseChange (ZMod 2)) z = _
  rw [map_zero]
  change (((LinearMap.range twiceUnary).subtype).baseChange (ZMod 2)) ((1 : ZMod 2) ⊗ₜ[ℤ] e 1) = 0
  rw [LinearMap.baseChange_tmul]
  change (1 : ZMod 2) ⊗ₜ[ℤ] twiceUnary 1 = 0
  rw [twiceUnary, LinearMap.smul_apply, LinearMap.toSpanSingleton_apply, one_smul, ← TensorProduct.smul_tmul]
  have two : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  rw [two, TensorProduct.zero_tmul]

end SHIGURE.TensorDomainStructure
