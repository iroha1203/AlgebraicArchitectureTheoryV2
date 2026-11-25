import Formal.SHIGURE.Part2.Tensor.CoefficientCoherence

/-!
# Coefficient changes on the states of tensor realizations

The state map of Construction 4.8 is semilinear along the coefficient map.
When two scalar extensions are composed, the structured tower comparison
identifies the state map into the staged extension with the direct one.

## Implementation notes

The semilinear map uses the ordinary linear tensor map over the base ring.
The scalar tower for a pair of coefficient maps comes from their composite.
The same tower comparison preserves the primitives and computes the state map.
-/

open CategoryTheory TensorProduct
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

section Maps

variable {k R S T M : Type u} [CommRing k] [CommRing R] [CommRing S] [CommRing T]
  [Algebra k R] [Algebra k S] [Algebra k T] [AddCommGroup M] [Module k M]

/-- Apply a coefficient algebra homomorphism to the coefficient of a realized state. -/
def mapCoefficients (f : R →ₐ[k] S) : R ⊗[k] M →ₛₗ[f.toRingHom] S ⊗[k] M where
  toFun := f.toLinearMap.rTensor M
  map_add' := map_add _
  map_smul' a x := by
    change f.toLinearMap.rTensor M (a • x) = f a • f.toLinearMap.rTensor M x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul]
      exact congrArg (fun b : S => b ⊗ₜ[k] m) (map_mul f a r)
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The direct map sends a pure tensor to the tensor with its coefficient changed. -/
@[simp]
theorem mapCoefficients_tmul (f : R →ₐ[k] S) (r : R) (m : M) :
    mapCoefficients f (r ⊗ₜ[k] m) = f r ⊗ₜ[k] m :=
  LinearMap.rTensor_tmul M f.toLinearMap m r

/-- Changing by the identity fixes every realized state. -/
theorem mapCoefficients_id (x : R ⊗[k] M) : mapCoefficients (AlgHom.id k R) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul r m => exact mapCoefficients_tmul (AlgHom.id k R) r m
  | add x y hx hy => rw [map_add, hx, hy]

/-- Two direct changes of realized states compose along the composite algebra homomorphism. -/
theorem mapCoefficients_comp (f : R →ₐ[k] S) (g : S →ₐ[k] T) (x : R ⊗[k] M) :
    mapCoefficients g (mapCoefficients f x) = mapCoefficients (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simp only [mapCoefficients_tmul, AlgHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- On the scalar sort, the direct change of realized states is the original algebra homomorphism. -/
theorem extendScalarSort_mapCoefficients (f : R →ₐ[k] S) (x : R ⊗[k] k) :
    extendScalarSort S (mapCoefficients f x) = f (extendScalarSort R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => rw [mapCoefficients_tmul, extendScalarSort_tmul, extendScalarSort_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Maps

section Units

variable {k R M : Type u} [CommRing k] [CommRing R] [Algebra k R] [AddCommGroup M] [Module k M]

/-- If the first coefficient map is the identity, the tower comparison extends the scalar unit. -/
theorem scalarTower_leftUnit :
    (scalarTower (k := k) (R := k) (S := R) (M := M)).toLinearMap =
      (scalarUnit (k := k) (M := M)).toLinearMap.baseChange R := by
  apply AlgebraTensorModule.ext
  intro r x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    change scalarTower (k := k) (R := k) (S := R) (r ⊗ₜ[k] (a ⊗ₜ[k] m)) =
      ((scalarUnit (k := k) (M := M)).toLinearMap.baseChange R) (r ⊗ₜ[k] (a ⊗ₜ[k] m))
    rw [scalarTower_tmul, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, scalarUnit_tmul,
      TensorProduct.smul_tmul]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- If the second coefficient map is the identity, the tower comparison is the scalar unit. -/
theorem scalarTower_rightUnit :
    (scalarTower (k := k) (R := R) (S := R) (M := M)).toLinearMap =
      (scalarUnit (k := R) (M := R ⊗[k] M)).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro r x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    change scalarTower (k := k) (R := R) (S := R) (r ⊗ₜ[R] (a ⊗ₜ[k] m)) =
      scalarUnit (r ⊗ₜ[R] (a ⊗ₜ[k] m))
    rw [scalarTower_tmul, scalarUnit_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_comm a r]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- The unit on the first coefficient change commutes with the structured tower comparison. -/
theorem structureScalarTower_leftUnit {sig : Signature.{u}} (A : TensorStructure k sig) :
    (structureScalarTower (R := k) (S := R) A).hom =
      extendStructureMap R (structureScalarUnit A).hom :=
  TensorStructure.Hom.ext (funext fun _ => scalarTower_leftUnit)

/-- The unit on the second coefficient change commutes with the structured tower comparison. -/
theorem structureScalarTower_rightUnit {sig : Signature.{u}} (A : TensorStructure k sig) :
    (structureScalarTower (R := R) (S := R) A).hom =
      (structureScalarUnit (extendStructure k R A)).hom :=
  TensorStructure.Hom.ext (funext fun _ => scalarTower_rightUnit)

end Units

/-- The public coefficient rule and its structured tower comparison give the direct state map. -/
theorem coefficientRule_changeState_direct {base S : CoefficientRing.{u}} {sig : Signature.{u}}
    (R : CoefficientAlgebra base) (f : R.scalars.Hom S) (A : TensorAt base sig) (s : sig.SortType) :
    letI := base.ring
    letI := R.scalars.ring
    letI := S.ring
    letI : Algebra base.Carrier R.scalars.Carrier := R.fromBase.toAlgebra
    letI : Algebra base.Carrier S.Carrier := (f.comp R.fromBase).toAlgebra
    letI : Algebra R.scalars.Carrier S.Carrier := f.toAlgebra
    letI : IsScalarTower base.Carrier R.scalars.Carrier S.Carrier := ringHom_scalarTower R.fromBase f
    let F : R.scalars.Carrier →ₐ[base.Carrier] S.Carrier := ⟨f, fun _ => rfl⟩
    ∀ x : R.scalars.Carrier ⊗[base.Carrier] A.carrier s,
      (structureScalarTower (R := R.scalars.Carrier) (S := S.Carrier) A).hom.onSort s
        ((coefficientRule sig).changeState f ((coefficientRule sig).change R.fromBase A) s x) =
      mapCoefficients F x := by
  letI := base.ring
  letI := R.scalars.ring
  letI := S.ring
  letI : Algebra base.Carrier R.scalars.Carrier := R.fromBase.toAlgebra
  letI : Algebra base.Carrier S.Carrier := (f.comp R.fromBase).toAlgebra
  letI : Algebra R.scalars.Carrier S.Carrier := f.toAlgebra
  letI : IsScalarTower base.Carrier R.scalars.Carrier S.Carrier := ringHom_scalarTower R.fromBase f
  intro F x
  change scalarTower (k := base.Carrier) (R := R.scalars.Carrier) (S := S.Carrier)
      ((1 : S.Carrier) ⊗ₜ[R.scalars.Carrier] x) = mapCoefficients F x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    rw [scalarTower_tmul, mapCoefficients_tmul]
    change (f r * 1) ⊗ₜ[base.Carrier] m = f r ⊗ₜ[base.Carrier] m
    rw [mul_one]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

end SHIGURE.TensorRealization
