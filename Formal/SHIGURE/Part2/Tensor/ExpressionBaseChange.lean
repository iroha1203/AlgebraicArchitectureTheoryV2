import Formal.SHIGURE.Part2.Realizations.TensorCoefficientExtension
import Formal.SHIGURE.Part2.Tensor.ScalarChange

/-!
# Coefficient change of typed tensor expressions

The tensor products specified by a written shape have a canonical scalar
extension comparison. A map between two shapes is transported along those
comparisons.

## Implementation notes

Transporting evaluated maps along the shape equivalences gives one map for
each pair of shapes. We prove the transport formula on unit-coefficient
generators, then use the fixed syntax of the expression to include the
coherence maps, tensor products, sums and scalar literals.
-/

open CategoryTheory TensorProduct
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
variable {sig : Signature.{u}}

/-- The module of a written shape commutes with scalar extension. -/
def shapeBaseChange (A : TensorStructure k sig) : (X : TensorShape sig.SortType) →
    (R ⊗[k] X.module A) ≃ₗ[R] X.module (extendStructure k R A)
  | .unit => extendScalarSort R
  | .sort _ => LinearEquiv.refl R _
  | .arguments Γ => inputTensorBaseChange k A.carrier R Γ
  | .tensor X Y => baseChangeTensor R ≪≫ₗ
      TensorProduct.congr (shapeBaseChange A X) (shapeBaseChange A Y)

/-- The unit comparison sends a scalar tensor to its scalar product. -/
theorem shapeBaseChange_unit (A : TensorStructure k sig) (r : R) (a : k) :
    shapeBaseChange (R := R) A .unit (r ⊗ₜ[k] a) = a • r :=
  extendScalarSort_tmul r a

/-- On a tensor shape, the coefficient of a pure tensor can be put in its first factor. -/
theorem shapeBaseChange_tensor_tmul (A : TensorStructure k sig)
    (X Y : TensorShape sig.SortType) (r : R) (x : X.module A) (y : Y.module A) :
    shapeBaseChange A (.tensor X Y) (r ⊗ₜ[k] (x ⊗ₜ[k] y)) =
      (shapeBaseChange A X (r ⊗ₜ[k] x)) ⊗ₜ[R] (shapeBaseChange A Y ((1 : R) ⊗ₜ[k] y)) := by
  change TensorProduct.congr (shapeBaseChange A X) (shapeBaseChange A Y)
    (baseChangeTensor R (r ⊗ₜ[k] (x ⊗ₜ[k] y))) = _
  rw [baseChangeTensor_tmul, TensorProduct.congr_tmul]

/-- Transport a linear map to the same written shapes after scalar extension. -/
def extendShapeMap (A : TensorStructure k sig) {X Y : TensorShape sig.SortType}
    (f : X.module A →ₗ[k] Y.module A) :
    X.module (extendStructure k R A) →ₗ[R] Y.module (extendStructure k R A) :=
  (shapeBaseChange A Y).toLinearMap.comp ((f.baseChange R).comp (shapeBaseChange A X).symm.toLinearMap)

/-- Evaluate a transported map on a unit tensor by applying the native map. -/
@[simp]
theorem extendShapeMap_unit (A : TensorStructure k sig) {X Y : TensorShape sig.SortType}
    (f : X.module A →ₗ[k] Y.module A) (x : X.module A) :
    extendShapeMap A f (shapeBaseChange A X ((1 : R) ⊗ₜ[k] x)) =
      shapeBaseChange A Y ((1 : R) ⊗ₜ[k] f x) := by
  simp [extendShapeMap]

/-- A comparison square for the image of unit tensors determines the transported map. -/
theorem eq_extendShapeMap_of_unit (A : TensorStructure k sig) {X Y : TensorShape sig.SortType}
    (f : X.module A →ₗ[k] Y.module A)
    (g : X.module (extendStructure k R A) →ₗ[R] Y.module (extendStructure k R A))
    (h : ∀ x, g (shapeBaseChange A X ((1 : R) ⊗ₜ[k] x)) = shapeBaseChange A Y ((1 : R) ⊗ₜ[k] f x)) :
    g = extendShapeMap A f := by
  letI := Module.compHom (Y.module (extendStructure k R A)) (algebraMap k R)
  letI : IsScalarTower k R (Y.module (extendStructure k R A)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  apply (LinearMap.cancel_right (g := (shapeBaseChange A X).toLinearMap) (shapeBaseChange A X).surjective).mp
  apply AlgebraTensorModule.ext
  intro r x
  change g (shapeBaseChange A X (r ⊗ₜ[k] x)) = extendShapeMap A f (shapeBaseChange A X (r ⊗ₜ[k] x))
  have hr : r ⊗ₜ[k] x = r • ((1 : R) ⊗ₜ[k] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hr]
  simp only [map_smul, h, extendShapeMap_unit]

/-- Transport through a sequence of typed tensor maps is computed by composition. -/
theorem extendShapeMap_comp (A : TensorStructure k sig) {X Y Z : TensorShape sig.SortType}
    (f : X.module A →ₗ[k] Y.module A) (g : Y.module A →ₗ[k] Z.module A) :
    (extendShapeMap (R := R) A g).comp (extendShapeMap A f) = extendShapeMap A (g.comp f) := by
  apply eq_extendShapeMap_of_unit
  intro x
  simp only [LinearMap.comp_apply, extendShapeMap_unit]

/-- Transport through a sum of maps is computed by the sum of the transported maps. -/
theorem extendShapeMap_add (A : TensorStructure k sig) {X Y : TensorShape sig.SortType}
    (f g : X.module A →ₗ[k] Y.module A) :
    extendShapeMap (R := R) A f + extendShapeMap A g = extendShapeMap A (f + g) := by
  apply eq_extendShapeMap_of_unit
  intro x
  simp only [LinearMap.add_apply, extendShapeMap_unit, tmul_add, map_add]

/-- A scalar multiple of a map is transported using the changed scalar. -/
theorem extendShapeMap_smul (A : TensorStructure k sig) {X Y : TensorShape sig.SortType}
    (r : k) (f : X.module A →ₗ[k] Y.module A) :
    algebraMap k R r • extendShapeMap (R := R) A f = extendShapeMap A (r • f) := by
  apply eq_extendShapeMap_of_unit
  intro x
  simp only [LinearMap.smul_apply, extendShapeMap_unit, ← TensorProduct.smul_tmul]
  rw [Algebra.smul_def, mul_one, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Tensor products of maps are transported through the shape comparisons. -/
theorem extendShapeMap_tensor (A : TensorStructure k sig) {X X' Y Y' : TensorShape sig.SortType}
    (f : X.module A →ₗ[k] X'.module A) (g : Y.module A →ₗ[k] Y'.module A) :
    TensorProduct.map (extendShapeMap (R := R) A f) (extendShapeMap A g) =
      extendShapeMap A (X := .tensor X Y) (Y := .tensor X' Y') (TensorProduct.map f g) := by
  apply eq_extendShapeMap_of_unit A (X := .tensor X Y) (Y := .tensor X' Y') (TensorProduct.map f g)
  intro z
  change TensorProduct.map (extendShapeMap A f) (extendShapeMap A g)
    (shapeBaseChange A (.tensor X Y) ((1 : R) ⊗ₜ[k] z)) =
      shapeBaseChange A (.tensor X' Y') ((1 : R) ⊗ₜ[k] TensorProduct.map f g z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [shapeBaseChange_tensor_tmul, TensorProduct.map_tmul, extendShapeMap_unit]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- Extension of a multilinear primitive is transport of its linearization. -/
theorem lift_extendOperation (A : TensorStructure k sig) {Γ : List sig.SortType} {s : sig.SortType}
    (f : MultilinearMap k (fun i : TensorPosition Γ => A.carrier i.1) (A.carrier s)) :
    PiTensorProduct.lift (extendOperation k A.carrier R f) =
      extendShapeMap A (X := .arguments Γ) (Y := .sort s) (PiTensorProduct.lift f) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change PiTensorProduct.lift (extendOperation k A.carrier R f) (PiTensorProduct.tprod R x) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- The interchange of tensor factors commutes with coefficient extension. -/
theorem extendShapeMap_swap (A : TensorStructure k sig) (X Y : TensorShape sig.SortType) :
    (TensorProduct.comm R (X.module (extendStructure k R A)) (Y.module (extendStructure k R A))).toLinearMap =
      extendShapeMap A (X := .tensor X Y) (Y := .tensor Y X)
        (TensorProduct.comm k (X.module A) (Y.module A)).toLinearMap := by
  apply eq_extendShapeMap_of_unit A (X := .tensor X Y) (Y := .tensor Y X)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [shapeBaseChange_tensor_tmul]
    change (shapeBaseChange A Y ((1 : R) ⊗ₜ[k] y)) ⊗ₜ[R] (shapeBaseChange A X ((1 : R) ⊗ₜ[k] x)) =
      shapeBaseChange A (.tensor Y X) ((1 : R) ⊗ₜ[k] (y ⊗ₜ[k] x))
    rw [shapeBaseChange_tensor_tmul]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- Reassociation commutes with coefficient extension. -/
theorem extendShapeMap_assoc (A : TensorStructure k sig) (X Y Z : TensorShape sig.SortType) :
    (TensorProduct.assoc R (X.module (extendStructure k R A)) (Y.module (extendStructure k R A))
      (Z.module (extendStructure k R A))).toLinearMap =
      extendShapeMap A (X := .tensor (.tensor X Y) Z) (Y := .tensor X (.tensor Y Z))
        (TensorProduct.assoc k (X.module A) (Y.module A) (Z.module A)).toLinearMap := by
  apply eq_extendShapeMap_of_unit A (X := .tensor (.tensor X Y) Z) (Y := .tensor X (.tensor Y Z))
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul xy z =>
    induction xy using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [shapeBaseChange_tensor_tmul]
      change (shapeBaseChange A X ((1 : R) ⊗ₜ[k] x)) ⊗ₜ[R]
        ((shapeBaseChange A Y ((1 : R) ⊗ₜ[k] y)) ⊗ₜ[R] (shapeBaseChange A Z ((1 : R) ⊗ₜ[k] z))) =
          shapeBaseChange A (.tensor X (.tensor Y Z)) ((1 : R) ⊗ₜ[k] (x ⊗ₜ[k] (y ⊗ₜ[k] z)))
      simp only [shapeBaseChange_tensor_tmul]
    | add x y hx hy => simp only [add_tmul, tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- A commuting shape comparison also commutes with the inverse isomorphism. -/
theorem extendShapeMap_inverse {A : TensorStructure k sig} {X Y : TensorShape sig.SortType}
    (e : X.module A ≃ₗ[k] Y.module A)
    (d : X.module (extendStructure k R A) ≃ₗ[R] Y.module (extendStructure k R A))
    (h : d.toLinearMap = extendShapeMap A e.toLinearMap) :
    d.symm.toLinearMap = extendShapeMap A e.symm.toLinearMap := by
  apply eq_extendShapeMap_of_unit
  intro y
  apply d.injective
  rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  change _ = d.toLinearMap (shapeBaseChange A X ((1 : R) ⊗ₜ[k] e.symm y))
  rw [h, extendShapeMap_unit, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- The left unit comparison is transported with its written source and target. -/
theorem extendShapeMap_leftUnit (A : TensorStructure k sig) (X : TensorShape sig.SortType) :
    (TensorProduct.lid R (X.module (extendStructure k R A))).toLinearMap =
      extendShapeMap A (X := .tensor .unit X) (Y := X) (TensorProduct.lid k (X.module A)).toLinearMap := by
  apply eq_extendShapeMap_of_unit A (X := .tensor .unit X) (Y := X)
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [shapeBaseChange_tensor_tmul, shapeBaseChange_unit, Algebra.smul_def, mul_one]
    change algebraMap k R (show k from a) • shapeBaseChange A X ((1 : R) ⊗ₜ[k] x) =
      shapeBaseChange A X ((1 : R) ⊗ₜ[k] ((show k from a) • x))
    rw [← TensorProduct.smul_tmul]
    rw [Algebra.smul_def, mul_one, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- The right unit comparison is transported with its written source and target. -/
theorem extendShapeMap_rightUnit (A : TensorStructure k sig) (X : TensorShape sig.SortType) :
    (TensorProduct.rid R (X.module (extendStructure k R A))).toLinearMap =
      extendShapeMap A (X := .tensor X .unit) (Y := X) (TensorProduct.rid k (X.module A)).toLinearMap := by
  apply eq_extendShapeMap_of_unit A (X := .tensor X .unit) (Y := X)
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [shapeBaseChange_tensor_tmul, shapeBaseChange_unit, Algebra.smul_def, mul_one]
    change algebraMap k R (show k from a) • shapeBaseChange A X ((1 : R) ⊗ₜ[k] x) =
      shapeBaseChange A X ((1 : R) ⊗ₜ[k] ((show k from a) • x))
    rw [← TensorProduct.smul_tmul]
    rw [Algebra.smul_def, mul_one, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- The empty input of a scalar is that scalar times the empty pure tensor. -/
private theorem emptyInput_ofScalar {K : Type u} (M : K → ModuleCat.{u} k) (a : k) :
    (inputTensorUnit k M).symm a = a • PiTensorProduct.tprod k (fun i => nomatch i.2) := by
  apply (inputTensorUnit k M).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, inputTensorUnit_tprod, smul_eq_mul, mul_one]

/-- Changing coefficients preserves the comparison from scalar units to empty inputs. -/
theorem extendShapeMap_emptyArguments (A : TensorStructure k sig) :
    ((inputTensorUnit R (extendCarriers k A.carrier R)).symm).toLinearMap =
      extendShapeMap A (X := .unit) (Y := .arguments []) (inputTensorUnit k A.carrier).symm.toLinearMap := by
  apply eq_extendShapeMap_of_unit A (X := .unit) (Y := .arguments [])
  intro a
  let b : k := a
  let z : InputTensor k A.carrier [] := PiTensorProduct.tprod k (fun i => nomatch i.2)
  change (inputTensorUnit R (extendCarriers k A.carrier R)).symm (b • (1 : R)) =
    inputTensorBaseChange k A.carrier R [] ((1 : R) ⊗ₜ[k] (inputTensorUnit k A.carrier).symm b)
  rw [emptyInput_ofScalar, emptyInput_ofScalar, ← TensorProduct.smul_tmul,
    Algebra.smul_def, mul_one]
  have hz : (algebraMap k R b) ⊗ₜ[k] z = (algebraMap k R b) • ((1 : R) ⊗ₜ[k] z) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hgen := inputTensorBaseChange_unit_tprod k A.carrier R [] (fun i => nomatch i.2)
  change inputTensorBaseChange k A.carrier R [] ((1 : R) ⊗ₜ[k] z) = _ at hgen
  change _ = inputTensorBaseChange k A.carrier R [] ((algebraMap k R b) ⊗ₜ[k] z)
  rw [hz, map_smul, hgen]
  congr 2
  funext i
  exact nomatch i.2

/-- A one-slot argument tensor is the pure tensor of its single displayed entry. -/
private theorem singleArgumentEquiv_symm_tprod {K : Type u} (M : K → ModuleCat.{u} k) (s : K)
    (a : M s) : (singleArgumentEquiv M s).symm a = PiTensorProduct.tprod k
      (fun | ⟨_, Var.here⟩ => a) := by
  apply (singleArgumentEquiv M s).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (singleArgumentEquiv_tprod M s (fun | ⟨_, Var.here⟩ => a)).symm

/-- Changing coefficients preserves the comparison from a sort to a singleton input. -/
theorem extendShapeMap_singleArgument (A : TensorStructure k sig) (s : sig.SortType) :
    (singleArgumentEquiv (extendCarriers k A.carrier R) s).symm.toLinearMap =
      extendShapeMap A (X := .sort s) (Y := .arguments [s]) (singleArgumentEquiv A.carrier s).symm.toLinearMap := by
  apply eq_extendShapeMap_of_unit A (X := .sort s) (Y := .arguments [s])
  intro a
  change (singleArgumentEquiv (extendCarriers k A.carrier R) s).symm ((1 : R) ⊗ₜ[k] a) =
    inputTensorBaseChange k A.carrier R [s] ((1 : R) ⊗ₜ[k] (singleArgumentEquiv A.carrier s).symm a)
  rw [singleArgumentEquiv_symm_tprod, singleArgumentEquiv_symm_tprod, inputTensorBaseChange_unit_tprod]
  congr 1
  funext i
  rcases i with ⟨_, i⟩
  cases i with
  | here => rfl
  | there i => exact nomatch i

/-- The inverse empty-input comparison is preserved along with its forward isomorphism. -/
theorem extendShapeMap_emptyArgumentsInv (A : TensorStructure k sig) :
    (inputTensorUnit R (extendCarriers k A.carrier R)).toLinearMap =
      extendShapeMap A (X := .arguments []) (Y := .unit) (inputTensorUnit k A.carrier).toLinearMap :=
  extendShapeMap_inverse (X := .unit) (Y := .arguments [])
    (inputTensorUnit k A.carrier).symm (inputTensorUnit R (extendCarriers k A.carrier R)).symm
    (extendShapeMap_emptyArguments A)

/-- The inverse singleton comparison is preserved along with its forward isomorphism. -/
theorem extendShapeMap_singleArgumentInv (A : TensorStructure k sig) (s : sig.SortType) :
    (singleArgumentEquiv (extendCarriers k A.carrier R) s).toLinearMap =
      extendShapeMap A (X := .arguments [s]) (Y := .sort s) (singleArgumentEquiv A.carrier s).toLinearMap :=
  extendShapeMap_inverse (X := .sort s) (Y := .arguments [s])
    (singleArgumentEquiv A.carrier s).symm (singleArgumentEquiv (extendCarriers k A.carrier R) s).symm
    (extendShapeMap_singleArgument A s)

/-- The identity comparison on each written shape is preserved by scalar extension. -/
theorem extendShapeMap_id (A : TensorStructure k sig) (X : TensorShape sig.SortType) :
    (LinearMap.id : X.module (extendStructure k R A) →ₗ[R] X.module (extendStructure k R A)) =
      extendShapeMap A (X := X) (Y := X) LinearMap.id := by
  apply eq_extendShapeMap_of_unit A
  intro x
  rfl

/-- The zero map on each pair of written shapes is preserved by scalar extension. -/
theorem extendShapeMap_zero (A : TensorStructure k sig) (X Y : TensorShape sig.SortType) :
    (0 : X.module (extendStructure k R A) →ₗ[R] Y.module (extendStructure k R A)) =
      extendShapeMap A (X := X) (Y := Y) 0 := by
  apply eq_extendShapeMap_of_unit A
  intro x
  simp

/-- Inserting a scalar multiple in a unit-coefficient tensor moves the scalar to the new ring. -/
private theorem unit_tmul_smul {M : Type u} [AddCommMonoid M] [Module k M] (a : k) (x : M) :
    (1 : R) ⊗ₜ[k] (a • x) = algebraMap k R a • ((1 : R) ⊗ₜ[k] x) := by
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- A typed entry can be transported before or after inserting the unit coefficient. -/
private theorem cast_unitAlongSort (A : TensorStructure k sig) {s t : sig.SortType} (h : s = t)
    (x : A.carrier s) :
    cast (congrArg (fun b => (extendCarriers k A.carrier R b : Type u)) h) ((1 : R) ⊗ₜ[k] x) =
      (1 : R) ⊗ₜ[k] cast (congrArg (fun b => (A.carrier b : Type u)) h) x := by
  cases h
  rfl

/-- The canonical change of coefficients preserves every sort-preserving permutation. -/
theorem extendShapeMap_permuteArguments (A : TensorStructure k sig) {Γ Δ : List sig.SortType}
    (e : TensorPosition Γ ≃ TensorPosition Δ) (sorts : ∀ i, i.1 = (e i).1) :
    (TensorExpression.permuteArguments e sorts).eval (extendStructure k R A) =
      extendShapeMap A ((TensorExpression.permuteArguments e sorts).eval A) := by
  apply eq_extendShapeMap_of_unit A
  let native := (TensorExpression.permuteArguments e sorts).eval A
  let extended := (TensorExpression.permuteArguments e sorts).eval (extendStructure k R A)
  intro z
  change extended (inputTensorBaseChange k A.carrier R Γ ((1 : R) ⊗ₜ[k] z)) =
    inputTensorBaseChange k A.carrier R Δ ((1 : R) ⊗ₜ[k] native z)
  have pure (x : ∀ i : TensorPosition Γ, A.carrier i.1) :
      extended (inputTensorBaseChange k A.carrier R Γ ((1 : R) ⊗ₜ[k] PiTensorProduct.tprod k x)) =
      inputTensorBaseChange k A.carrier R Δ ((1 : R) ⊗ₜ[k] native (PiTensorProduct.tprod k x)) := by
    change extended (inputTensorBaseChange k A.carrier R Γ ((1 : R) ⊗ₜ[k] PiTensorProduct.tprod k x)) =
      inputTensorBaseChange k A.carrier R Δ ((1 : R) ⊗ₜ[k] native (PiTensorProduct.tprod k x))
    rw [inputTensorBaseChange_unit_tprod]
    dsimp only [native, extended]
    let xs (i : TensorPosition Γ) : (extendStructure k R A).carrier i.1 := (1 : R) ⊗ₜ[k] x i
    change (TensorExpression.permuteArguments e sorts).eval (extendStructure k R A)
      (PiTensorProduct.tprod R xs) = _
    rw [TensorExpression.eval_permuteArguments_tprod (extendStructure k R A) e sorts xs,
      TensorExpression.eval_permuteArguments_tprod A e sorts x, inputTensorBaseChange_unit_tprod]
    congr 1
    funext j
    exact cast_unitAlongSort A ((sorts (e.symm j)).trans (congrArg Sigma.fst (e.apply_symm_apply j))) _

  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    rw [map_smul, unit_tmul_smul, unit_tmul_smul, map_smul, map_smul, map_smul, pure]
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]

/-- The canonical change of coefficients preserves concatenation of typed input blocks. -/
theorem extendShapeMap_combineArguments (A : TensorStructure k sig) {Γ Δ Θ : List sig.SortType}
    (e : TensorPosition Γ ⊕ TensorPosition Δ ≃ TensorPosition Θ)
    (sorts : ∀ i, Sum.elim Sigma.fst Sigma.fst i = (e i).1) :
    (combineArgumentsEquiv (extendStructure k R A) e sorts).toLinearMap =
      extendShapeMap A (X := .tensor (.arguments Γ) (.arguments Δ)) (Y := .arguments Θ)
        (combineArgumentsEquiv A e sorts).toLinearMap := by
  apply eq_extendShapeMap_of_unit A (X := .tensor (.arguments Γ) (.arguments Δ)) (Y := .arguments Θ)
  let X := TensorShape.tensor (.arguments Γ) (.arguments Δ)
  let native := (combineArgumentsEquiv A e sorts).toLinearMap
  let extended := (combineArgumentsEquiv (extendStructure k R A) e sorts).toLinearMap
  intro z
  change extended (shapeBaseChange A X ((1 : R) ⊗ₜ[k] z)) =
    inputTensorBaseChange k A.carrier R Θ ((1 : R) ⊗ₜ[k] native z)
  have pure (x : ∀ i : TensorPosition Γ, A.carrier i.1) (y : ∀ i : TensorPosition Δ, A.carrier i.1) :
      extended (shapeBaseChange A X ((1 : R) ⊗ₜ[k] (PiTensorProduct.tprod k x ⊗ₜ[k] PiTensorProduct.tprod k y))) =
      inputTensorBaseChange k A.carrier R Θ
        ((1 : R) ⊗ₜ[k] native (PiTensorProduct.tprod k x ⊗ₜ[k] PiTensorProduct.tprod k y)) := by
    change combineArgumentsEquiv (extendStructure k R A) e sorts
        (shapeBaseChange A (.tensor (.arguments Γ) (.arguments Δ))
          ((1 : R) ⊗ₜ[k] (PiTensorProduct.tprod k x ⊗ₜ[k] PiTensorProduct.tprod k y))) =
      inputTensorBaseChange k A.carrier R Θ ((1 : R) ⊗ₜ[k]
        combineArgumentsEquiv A e sorts (PiTensorProduct.tprod k x ⊗ₜ[k] PiTensorProduct.tprod k y))
    rw [shapeBaseChange_tensor_tmul]
    change combineArgumentsEquiv (extendStructure k R A) e sorts
        (inputTensorBaseChange k A.carrier R Γ ((1 : R) ⊗ₜ[k] PiTensorProduct.tprod k x) ⊗ₜ[R]
          inputTensorBaseChange k A.carrier R Δ ((1 : R) ⊗ₜ[k] PiTensorProduct.tprod k y)) = _
    rw [inputTensorBaseChange_unit_tprod, inputTensorBaseChange_unit_tprod]
    let xs (i : TensorPosition Γ) : (extendStructure k R A).carrier i.1 := (1 : R) ⊗ₜ[k] x i
    let ys (i : TensorPosition Δ) : (extendStructure k R A).carrier i.1 := (1 : R) ⊗ₜ[k] y i
    change combineArgumentsEquiv (extendStructure k R A) e sorts
      (PiTensorProduct.tprod R xs ⊗ₜ[R] PiTensorProduct.tprod R ys) = _
    rw [combineArgumentsEquiv_tprod (extendStructure k R A) e sorts xs ys,
      combineArgumentsEquiv_tprod A e sorts x y, inputTensorBaseChange_unit_tprod]
    congr 1
    funext j
    have h (i : TensorPosition Γ ⊕ TensorPosition Δ) :
        Sum.rec (motive := fun i =>
          (extendStructure k R A).carrier (Sum.elim Sigma.fst Sigma.fst i))
          (fun a => (1 : R) ⊗ₜ[k] x a) (fun b => (1 : R) ⊗ₜ[k] y b) i =
        (1 : R) ⊗ₜ[k] Sum.rec (motive := fun i => A.carrier (Sum.elim Sigma.fst Sigma.fst i)) x y i := by
      cases i <;> rfl
    dsimp only [xs, ys]
    rw [h]
    exact cast_unitAlongSort A ((sorts (e.symm j)).trans (congrArg Sigma.fst (e.apply_symm_apply j))) _
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, tmul_add, ha, hb]
  | tmul a b =>
    induction a using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [add_tmul, tmul_add, map_add, hx, hy]
    | smul_tprod a x =>
      rw [← TensorProduct.smul_tmul', map_smul, unit_tmul_smul, unit_tmul_smul,
        map_smul, map_smul, map_smul]
      congr 1
      induction b using PiTensorProduct.induction_on with
      | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
      | smul_tprod b y =>
        rw [TensorProduct.tmul_smul, map_smul, unit_tmul_smul, unit_tmul_smul,
          map_smul, map_smul, map_smul, pure]

/-- Splitting the input blocks is also preserved, since it is the inverse comparison. -/
theorem extendShapeMap_splitArguments (A : TensorStructure k sig) {Γ Δ Θ : List sig.SortType}
    (e : TensorPosition Γ ⊕ TensorPosition Δ ≃ TensorPosition Θ)
    (sorts : ∀ i, Sum.elim Sigma.fst Sigma.fst i = (e i).1) :
    (combineArgumentsEquiv (extendStructure k R A) e sorts).symm.toLinearMap =
      extendShapeMap A (X := .arguments Θ) (Y := .tensor (.arguments Γ) (.arguments Δ))
        (combineArgumentsEquiv A e sorts).symm.toLinearMap :=
  extendShapeMap_inverse (X := .tensor (.arguments Γ) (.arguments Δ)) (Y := .arguments Θ)
    (combineArgumentsEquiv A e sorts) (combineArgumentsEquiv (extendStructure k R A) e sorts)
    (extendShapeMap_combineArguments A e sorts)

/-- Evaluating a written tensor expression after changing coefficients gives its transported native map. -/
theorem eval_mapScalars_eq_extendShapeMap (A : TensorStructure k sig)
    {X Y : TensorShape sig.SortType} (e : TensorExpression k sig X Y) :
    (e.mapScalars (algebraMap k R)).eval (extendStructure k R A) =
      extendShapeMap A (e.eval A) := by
  induction e with
  | id X => exact extendShapeMap_id A X
  | zero X Y => exact extendShapeMap_zero A X Y
  | total f => exact lift_extendOperation A (A.total f)
  | quantity q => exact lift_extendOperation A (A.quantity q)
  | swap X Y => exact extendShapeMap_swap A X Y
  | assoc X Y Z => exact extendShapeMap_assoc A X Y Z
  | assocInv X Y Z =>
    exact extendShapeMap_inverse (X := .tensor (.tensor X Y) Z) (Y := .tensor X (.tensor Y Z))
      (TensorProduct.assoc k (X.module A) (Y.module A) (Z.module A))
      (TensorProduct.assoc R (X.module (extendStructure k R A)) (Y.module (extendStructure k R A))
        (Z.module (extendStructure k R A))) (extendShapeMap_assoc A X Y Z)
  | leftUnit X => exact extendShapeMap_leftUnit A X
  | leftUnitInv X =>
    exact extendShapeMap_inverse (X := .tensor .unit X) (Y := X) (TensorProduct.lid k (X.module A))
      (TensorProduct.lid R (X.module (extendStructure k R A))) (extendShapeMap_leftUnit A X)
  | rightUnit X => exact extendShapeMap_rightUnit A X
  | rightUnitInv X =>
    exact extendShapeMap_inverse (X := .tensor X .unit) (Y := X) (TensorProduct.rid k (X.module A))
      (TensorProduct.rid R (X.module (extendStructure k R A))) (extendShapeMap_rightUnit A X)
  | emptyArguments => exact extendShapeMap_emptyArguments A
  | emptyArgumentsInv => exact extendShapeMap_emptyArgumentsInv A
  | singleArgument s => exact extendShapeMap_singleArgument A s
  | singleArgumentInv s => exact extendShapeMap_singleArgumentInv A s
  | permuteArguments e sorts => exact extendShapeMap_permuteArguments A e sorts
  | combineArguments e sorts => exact extendShapeMap_combineArguments A e sorts
  | splitArguments e sorts => exact extendShapeMap_splitArguments A e sorts
  | comp f g hf hg =>
    simpa only [TensorExpression.mapScalars, TensorExpression.eval, hf, hg] using
      extendShapeMap_comp (R := R) A (f.eval A) (g.eval A)
  | tensor f g hf hg =>
    simpa only [TensorExpression.mapScalars, TensorExpression.eval, hf, hg] using
      extendShapeMap_tensor (R := R) A (f.eval A) (g.eval A)
  | add f g hf hg =>
    simpa only [TensorExpression.mapScalars, TensorExpression.eval, hf, hg] using
      extendShapeMap_add (R := R) A (f.eval A) (g.eval A)
  | smul a f hf =>
    simpa only [TensorExpression.mapScalars, TensorExpression.eval, hf] using
      extendShapeMap_smul (R := R) A a (f.eval A)

/-- Both sides of a tensor Law are transported by the same comparisons, so equality is preserved. -/
theorem tensorLaw_holds_baseChange {A : TensorStructure k sig} {law : TensorLaw k sig}
    (h : law.holds A) : (law.mapScalars (algebraMap k R)).holds (extendStructure k R A) := by
  change _ = _ at h
  change (law.left.mapScalars (algebraMap k R)).eval _ = (law.right.mapScalars (algebraMap k R)).eval _
  rw [eval_mapScalars_eq_extendShapeMap, eval_mapScalars_eq_extendShapeMap, h]

end SHIGURE.TensorRealization
