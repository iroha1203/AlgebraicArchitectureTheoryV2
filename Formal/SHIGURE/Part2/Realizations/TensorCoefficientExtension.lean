import Formal.SHIGURE.Part2.Realizations.TensorDeclarations
import Formal.SHIGURE.Part2.AffineBaseChange

/-!
# Coefficient extension of finite tensor operations

Construction 4.8 uses the actual tensor product of the modules at the
variable positions of a finite arity. The unit case and decomposition into
the first position and remaining positions give scalar extension by
recursion on the typed context.
-/

open CategoryTheory TensorProduct PiTensorProduct
open scoped TensorProduct BigOperators

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {K : Type u}
variable (k : Type u) [CommRing k] (M : K → ModuleCat.{u} k)

variable (R : Type u) [CommRing R] [Algebra k R]

/-- The carrier family extended to a new coefficient algebra. -/
def extendCarriers (s : K) : ModuleCat.{u} R :=
  ModuleCat.of R (R ⊗[k] M s)

/-- Coefficient extension distributes over the input tensor of any finite typed arity. -/
def inputTensorBaseChange : (Γ : List K) →
    (R ⊗[k] InputTensor k M Γ) ≃ₗ[R] InputTensor R (extendCarriers k M R) Γ
  | [] => (inputTensorUnit k M).baseChange k R _ _ ≪≫ₗ
      AlgebraTensorModule.rid k R R ≪≫ₗ (inputTensorUnit R (extendCarriers k M R)).symm
  | s :: Γ => (inputTensorCons k M s Γ).baseChange k R _ _ ≪≫ₗ baseChangeTensor R ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl R _) (inputTensorBaseChange Γ) ≪≫ₗ
      (inputTensorCons R (extendCarriers k M R) s Γ).symm

/-- A pure tensor with unit coefficient maps to the tuple of unit-coefficient factors. -/
@[simp]
theorem inputTensorBaseChange_unit_tprod (Γ : List K)
    (x : ∀ i : TensorPosition Γ, M i.1) :
    inputTensorBaseChange k M R Γ ((1 : R) ⊗ₜ[k] tprod k x) =
      tprod R (fun i => (1 : R) ⊗ₜ[k] x i) := by
  induction Γ with
  | nil =>
    let y (i : TensorPosition ([] : List K)) : extendCarriers k M R i.1 := (1 : R) ⊗ₜ[k] x i
    change _ = tprod R y
    apply (inputTensorUnit R (extendCarriers k M R)).injective
    simp only [inputTensorBaseChange, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      inputTensorUnit_tprod, LinearEquiv.apply_symm_apply, AlgebraTensorModule.rid_tmul, one_smul]
  | cons s Γ ih =>
    let y (i : TensorPosition (s :: Γ)) : extendCarriers k M R i.1 := (1 : R) ⊗ₜ[k] x i
    change _ = tprod R y
    apply (inputTensorCons R (extendCarriers k M R) s Γ).injective
    simp only [inputTensorBaseChange, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      inputTensorCons_tprod, baseChangeTensor_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply, ih]
    exact (inputTensorCons R (extendCarriers k M R) s Γ).apply_symm_apply _

variable {N : ModuleCat.{u} k}

/-- Extend an operation through the actual scalar extension of its input tensor. -/
def extendOperation {Γ : List K} (op : MultilinearMap k (fun i : TensorPosition Γ => M i.1) N) :
    MultilinearMap R (fun i : TensorPosition Γ => extendCarriers k M R i.1) (R ⊗[k] N) :=
  (((PiTensorProduct.lift op).baseChange R).comp
    (inputTensorBaseChange k M R Γ).symm.toLinearMap).compMultilinearMap (tprod R)

/-- The changed operation takes unit-coefficient inputs to the unit tensor of its original value. -/
@[simp]
theorem extendOperation_unit {Γ : List K}
    (op : MultilinearMap k (fun i : TensorPosition Γ => M i.1) N)
    (x : ∀ i : TensorPosition Γ, M i.1) :
    extendOperation k M R op (fun i => (1 : R) ⊗ₜ[k] x i) = (1 : R) ⊗ₜ[k] op x := by
  let y (i : TensorPosition Γ) : extendCarriers k M R i.1 := (1 : R) ⊗ₜ[k] x i
  change (PiTensorProduct.lift op).baseChange R ((inputTensorBaseChange k M R Γ).symm (tprod R y)) = _
  have hy : tprod R y = inputTensorBaseChange k M R Γ ((1 : R) ⊗ₜ[k] tprod k x) :=
    (inputTensorBaseChange_unit_tprod k M R Γ x).symm
  rw [hy, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul, PiTensorProduct.lift.tprod]

/-- Equation (4.3) on pure tensors with arbitrary scalar coefficients. -/
theorem extendOperation_tprod {Γ : List K}
    (op : MultilinearMap k (fun i : TensorPosition Γ => M i.1) N)
    (x : ∀ i : TensorPosition Γ, M i.1) (r : TensorPosition Γ → R) :
    letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
    extendOperation k M R op (fun i => r i ⊗ₜ[k] x i) = (∏ i, r i) ⊗ₜ[k] op x := by
  letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
  let y (i : TensorPosition Γ) : extendCarriers k M R i.1 := (1 : R) ⊗ₜ[k] x i
  have h : (fun i : TensorPosition Γ => r i ⊗ₜ[k] x i) = fun i => r i • y i := by
    funext i
    change r i ⊗ₜ[k] x i = r i • ((1 : R) ⊗ₜ[k] x i)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, MultilinearMap.map_smul_univ]
  change (∏ i, r i) • extendOperation k M R op y = _
  rw [extendOperation_unit, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The unit-coefficient tuples determine a multilinear map on the extended carriers. -/
theorem multilinear_ext_unit {Γ : List K} {P : ModuleCat.{u} R}
    {f g : MultilinearMap R (fun i : TensorPosition Γ => extendCarriers k M R i.1) P}
    (h : ∀ x : (i : TensorPosition Γ) → M i.1,
      f (fun i => (1 : R) ⊗ₜ[k] x i) = g (fun i => (1 : R) ⊗ₜ[k] x i)) : f = g := by
  let e := inputTensorBaseChange k M R Γ
  apply PiTensorProduct.lift.injective
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  let f' := (PiTensorProduct.lift f).comp e.toLinearMap
  let g' := (PiTensorProduct.lift g).comp e.toLinearMap
  change f' = g'
  have hgen (x : ∀ i : TensorPosition Γ, M i.1) :
      f' ((1 : R) ⊗ₜ[k] tprod k x) = g' ((1 : R) ⊗ₜ[k] tprod k x) := by
    let y (i : TensorPosition Γ) : extendCarriers k M R i.1 := (1 : R) ⊗ₜ[k] x i
    have he : e ((1 : R) ⊗ₜ[k] tprod k x) = tprod R y :=
      inputTensorBaseChange_unit_tprod k M R Γ x
    change PiTensorProduct.lift f (e _) = PiTensorProduct.lift g (e _)
    rw [he, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    exact h x
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul r x =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a x =>
      rw [← TensorProduct.smul_tmul (R := k) (R' := k) a r (tprod k x)]
      have hr : (a • r) ⊗ₜ[k] tprod k x = (a • r) • ((1 : R) ⊗ₜ[k] tprod k x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hr, map_smul, map_smul, hgen x]
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

/-- Extend every carrier, total operation and quantity of a given structure. -/
def extendStructure {sig : Signature.{u}} (A : TensorStructure k sig) : TensorStructure R sig where
  carrier := extendCarriers k A.carrier R
  total op := extendOperation k A.carrier R (A.total op)
  quantity q := extendOperation k A.carrier R (A.quantity q)

/-- The general coefficient rule extended from the given structure and its finite-arity operations. -/
def coefficientRule (sig : Signature.{u}) : TensorCoefficientRule sig where
  change {R S} f A :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    extendStructure R.Carrier S.Carrier A
  carrierIso {R S} f A s :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    LinearEquiv.refl S.Carrier (S.Carrier ⊗[R.Carrier] A.carrier s)
  total_unit {R S} f A op :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    extendOperation_unit R.Carrier A.carrier S.Carrier (A.total op)
  quantity_unit {R S} f A q :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    extendOperation_unit R.Carrier A.carrier S.Carrier (A.quantity q)

end SHIGURE.TensorRealization

namespace SHIGURE

/-- The tensor realization mode defined using actual scalar extension on every carrier and primitive. -/
def tensorMode {sig : Signature.{u}} (base : CoefficientRing.{u}) {L : Type u}
    (T : TensorTheory base sig L) : CoefficientRealizationMode base T.presentation :=
  tensorModeWithRule base T (TensorRealization.coefficientRule sig)

/-- The selected tensor declarations with scalar extension of their actual primitive structure. -/
def TensorDeclarationContext.mode {base : CoefficientRing.{u}} {P : PrimitivePresentation.{u}}
    {D : TensorLawDeclarations base P} (U : TensorDeclarationContext D) :
    CoefficientRealizationMode base U.presentation :=
  U.modeWithRule (TensorRealization.coefficientRule U.presentation.signature)

end SHIGURE
