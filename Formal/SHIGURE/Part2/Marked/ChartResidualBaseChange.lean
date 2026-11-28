import Formal.SHIGURE.Part2.Marked.UniversalOperations
import Formal.SHIGURE.Part2.Descent.ExpressionNaturality
import Formal.SHIGURE.Part2.Tensor.ExpressionBaseChange
import Formal.SHIGURE.Part2.Tensor.CoefficientCoherence

/-! # Actual scalar extension of the free chart operations

The coefficient specializations of Construction 6.4 are compared with
the original tensor scalar extension. Naturality of all tensor expressions
then follows from the existing structural naturality and scalar-extension
theorems, including all argument permutation and splitting constructors.

## Implementation notes

The carrier comparison is the coordinate equivalence of the base-changed
standard basis. The structured comparison is proved first on multilinear
basis inputs, retaining the actual extended operations throughout.
-/

universe u

namespace SHIGURE.RealizationFamilies.Marked

open Module CategoryTheory SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

variable {sig : Signature.{u}} (rank : sig.SortType → ℕ)
variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-- Actual scalar extension of the standard finite free carrier, read in
the base-changed standard basis. -/
def freeCarrierBaseChange (s : sig.SortType) :
    (R ⊗[A] (Fin (rank s) → A)) ≃ₗ[R] (Fin (rank s) → R) :=
  ((freeBasis rank A s).baseChange R).equivFun

/-- On unit tensors the carrier comparison applies the actual coefficient map. -/
theorem freeCarrierBaseChange_unit (s : sig.SortType) (x : Fin (rank s) → A) :
    freeCarrierBaseChange rank s ((1 : R) ⊗ₜ[A] x) = fun j => algebraMap A R (x j) := by
  funext j
  simp [freeCarrierBaseChange, Basis.equivFun_apply, Basis.baseChange_repr_tmul,
    freeBasis, Algebra.smul_def]

/-- The actual extended basis vector maps to the new standard basis vector. -/
theorem freeCarrierBaseChange_basis (s : sig.SortType) (j : Fin (rank s)) :
    freeCarrierBaseChange rank s ((1 : R) ⊗ₜ[A] freeBasis rank A s j) = freeBasis rank R s j := by
  classical
  rw [freeCarrierBaseChange_unit]
  funext b
  simp [freeBasis, Pi.single_apply]

/-- Every primitive multilinear operation is preserved by the actual
free-carrier scalar-extension comparison. -/
theorem freeCarrierBaseChange_operation (a : Arity sig.SortType)
    (c : Fin (rank a.output) → (∀ i : TensorPosition a.inputs, Fin (rank i.1)) → A)
    (x : ∀ i : TensorPosition a.inputs, R ⊗[A] (Fin (rank i.1) → A)) :
    freeCarrierBaseChange rank a.output
        (extendOperation A (fun s => ModuleCat.of A (Fin (rank s) → A)) R
          (N := ModuleCat.of A (Fin (rank a.output) → A))
          (operationOfCoefficients rank A a c) x) =
      operationOfCoefficients rank R a (fun b v => algebraMap A R (c b v))
        (fun i => freeCarrierBaseChange rank i.1 (x i)) := by
  let left := (freeCarrierBaseChange rank a.output).toLinearMap.compMultilinearMap
    (extendOperation A (fun s => ModuleCat.of A (Fin (rank s) → A)) R
      (N := ModuleCat.of A (Fin (rank a.output) → A))
      (operationOfCoefficients rank A a c))
  let right : MultilinearMap R
      (fun i : TensorPosition a.inputs => R ⊗[A] (Fin (rank i.1) → A))
      (Fin (rank a.output) → R) :=
    (operationOfCoefficients rank R a (fun b v => algebraMap A R (c b v))).compLinearMap
      (fun i => (freeCarrierBaseChange (A := A) (R := R) rank i.1).toLinearMap)
  have eq : left = right := by
    apply Module.Basis.ext_multilinear
      (fun i : TensorPosition a.inputs => (freeBasis rank A i.1).baseChange R)
    intro v
    change freeCarrierBaseChange rank a.output
        (extendOperation A (fun s => ModuleCat.of A (Fin (rank s) → A)) R
          (N := ModuleCat.of A (Fin (rank a.output) → A))
          (operationOfCoefficients rank A a c)
          (fun i => (freeBasis rank A i.1).baseChange R (v i))) = _
    simp only [Basis.baseChange_apply, right, MultilinearMap.compLinearMap_apply,
      LinearEquiv.coe_coe]
    rw [extendOperation_unit A (fun s => ModuleCat.of A (Fin (rank s) → A)) R
      (N := ModuleCat.of A (Fin (rank a.output) → A))
      (operationOfCoefficients rank A a c) (fun i => freeBasis rank A i.1 (v i))]
    simp only [freeCarrierBaseChange_basis]
    rw [freeCarrierBaseChange_unit]
    funext b
    rw [operationOfCoefficients_basis, operationOfCoefficients_basis]
  exact MultilinearMap.congr_fun eq x

/-- The actual tensor-structure morphism from scalar extension to the
free structure whose independent coefficients are extended. -/
def freeStructureBaseChangeHom (c : OperationCoordinate sig rank → A) :
    extendStructure A R (freeStructure rank A c) ⟶
      freeStructure rank R (fun z => algebraMap A R (c z)) where
  onSort s := (freeCarrierBaseChange rank s).toLinearMap
  preservesTotal f x := freeCarrierBaseChange_operation rank (sig.totalArity f)
    (fun b v => c ⟨.inl f, b, v⟩) x
  preservesQuantity q x := freeCarrierBaseChange_operation rank (sig.quantityArity q)
    (fun b v => c ⟨.inr q, b, v⟩) x

/-- All carriers of the comparison are actual linear equivalences, so the
preserving morphism is an isomorphism of tensor structures. -/
def freeStructureBaseChangeIso (c : OperationCoordinate sig rank → A) :
    extendStructure A R (freeStructure rank A c) ≅
      freeStructure rank R (fun z => algebraMap A R (c z)) :=
  structureIsoOfCarrierEquiv (freeStructureBaseChangeHom rank c)
    (fun s => freeCarrierBaseChange rank s) (fun _ => rfl)

/-- Extend a written shape and then use the structured free-carrier comparison. -/
def freeShapeBaseChange (c : OperationCoordinate sig rank → A) (X : TensorShape sig.SortType) :
    (R ⊗[A] X.module (freeStructure rank A c)) ≃ₗ[R]
      X.module (freeStructure rank R (fun z => algebraMap A R (c z))) :=
  shapeBaseChange (freeStructure rank A c) X ≪≫ₗ
    X.equivSorts (U := extendStructure A R (freeStructure rank A c))
      (V := freeStructure rank R (fun z => algebraMap A R (c z)))
      (fun s => freeCarrierBaseChange rank s)

/-- Full tensor-expression evaluation commutes with the actual shape
comparison, by existing structural naturality and scalar extension. -/
theorem freeShapeBaseChange_eval (c : OperationCoordinate sig rank → A)
    {X Y : TensorShape sig.SortType} (t : TensorExpression A sig X Y)
    (x : X.module (freeStructure rank A c)) :
    freeShapeBaseChange rank c Y ((1 : R) ⊗ₜ[A] t.eval (freeStructure rank A c) x) =
      (t.mapScalars (algebraMap A R)).eval
        (freeStructure rank R (fun z => algebraMap A R (c z)))
          (freeShapeBaseChange rank c X ((1 : R) ⊗ₜ[A] x)) := by
  let D := freeStructure rank A c
  let h := freeStructureBaseChangeHom (R := R) rank c
  have square := (t.mapScalars (algebraMap A R)).eval_natural h
  have point := LinearMap.congr_fun square
    (shapeBaseChange (R := R) D X ((1 : R) ⊗ₜ[A] x))
  rw [eval_mapScalars_eq_extendShapeMap, LinearMap.comp_apply, extendShapeMap_unit,
    LinearMap.comp_apply] at point
  have shapes (Z : TensorShape sig.SortType) (z : Z.module (extendStructure A R D)) :
      Z.mapSorts h.onSort z =
        Z.equivSorts (U := extendStructure A R D)
          (V := freeStructure rank R (fun z => algebraMap A R (c z)))
          (fun s => freeCarrierBaseChange rank s) z :=
    LinearMap.congr_fun (TensorShape.equivSorts_toLinearMap
      (U := extendStructure A R D)
      (V := freeStructure rank R (fun z => algebraMap A R (c z)))
      (fun s => freeCarrierBaseChange rank s) Z).symm z
  rw [shapes, shapes] at point
  exact point

end

end SHIGURE.RealizationFamilies.Marked
