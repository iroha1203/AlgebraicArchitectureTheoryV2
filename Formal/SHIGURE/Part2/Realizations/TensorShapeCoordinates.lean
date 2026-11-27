import Formal.SHIGURE.Part2.Tensor.ExpressionBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Ideal.Maps

/-! # Bases of the actual modules interpreting written tensor shapes -/

namespace SHIGURE.RealizationFamilies

open Module TensorProduct SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {sig : Signature.{u}} (rank : sig.SortType → ℕ)

private def argumentIndices : List sig.SortType → Type
  | [] => PUnit
  | s :: tail => (Fin (rank s)) × argumentIndices tail

/-- An input or output basis of a tensor shape is indexed by its original factors. -/
def tensorShapeIndices : TensorShape sig.SortType → Type
  | .unit => PUnit
  | .sort s => Fin (rank s)
  | .arguments Γ => argumentIndices rank Γ
  | .tensor U V => tensorShapeIndices U × tensorShapeIndices V

variable (A : TensorStructure R sig) (b : ∀ s, Basis (Fin (rank s)) R (A.carrier s))

private def argumentBasis : (Γ : List sig.SortType) →
    Basis (argumentIndices rank Γ) R (InputTensor R A.carrier Γ)
  | [] => (Basis.singleton PUnit R).map (inputTensorUnit R A.carrier).symm
  | s :: Γ => ((b s).tensorProduct (argumentBasis Γ)).map (inputTensorCons R A.carrier s Γ).symm

/-- Choose the genuine tensor basis in every written shape over the frame. -/
def tensorShapeBasis : (U : TensorShape sig.SortType) →
    Basis (tensorShapeIndices rank U) R (U.module A)
  | .unit => Basis.singleton PUnit R
  | .sort s => b s
  | .arguments Γ => argumentBasis rank A b Γ
  | .tensor U V => (tensorShapeBasis U).tensorProduct (tensorShapeBasis V)

/-- The transported bases are the native scalar extension of the basis of each shape. -/
def extendShapeBasis {I : Type*} {U : TensorShape sig.SortType} (d : Basis I R (U.module A)) :
    Basis I S (U.module (extendStructure R S A)) :=
  (d.baseChange S).map (shapeBaseChange A U)

variable {W Z : TensorShape sig.SortType} {I J : Type*}
  (d : Basis I R (W.module A)) (e : Basis J R (Z.module A))
  (g : W.module A →ₗ[R] Z.module A)

/-- In the scalar-extended bases, every matrix entry of the actual
transported map is the image of the original matrix entry. -/
theorem extendShapeMap_entry (i : I) (j : J) :
    (extendShapeBasis (S := S) A e).repr
      (extendShapeMap A g (extendShapeBasis (S := S) A d i)) j =
      algebraMap R S (e.repr (g (d i)) j) := by
  have basisVector : extendShapeBasis (S := S) A d i =
      shapeBaseChange A W ((1 : S) ⊗ₜ[R] d i) := by
    rw [extendShapeBasis, Basis.map_apply, Basis.baseChange_apply]
  rw [basisVector, extendShapeMap_unit]
  change (e.baseChange S).repr
    ((shapeBaseChange A Z).symm (shapeBaseChange A Z ((1 : S) ⊗ₜ[R] g (d i)))) j = _
  rw [LinearEquiv.symm_apply_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

section Residual

variable {A rank} (d₀ : ∀ s, Basis (Fin (rank s)) R (A.carrier s))

/-- The coefficient ideal uses all actual entries of the tensor difference in the chosen bases. -/
def tensorLawResidualIdeal (law : TensorLaw R sig) : Ideal R :=
  Ideal.span (Set.range fun ij : tensorShapeIndices rank law.source × tensorShapeIndices rank law.target =>
    (tensorShapeBasis rank A d₀ law.target).repr
      ((law.left.eval A - law.right.eval A) (tensorShapeBasis rank A d₀ law.source ij.1)) ij.2)

private theorem extendShapeMap_sub {W Z : TensorShape sig.SortType}
    (f g : W.module A →ₗ[R] Z.module A) :
    extendShapeMap (R := S) A (f - g) = extendShapeMap A f - extendShapeMap A g := by
  symm
  apply eq_extendShapeMap_of_unit
  intro x
  rw [LinearMap.sub_apply, extendShapeMap_unit, extendShapeMap_unit, LinearMap.sub_apply,
    TensorProduct.tmul_sub, map_sub]

private theorem tensorLinearMap_eq_zero_iff {I J : Type*} {W Z : TensorShape sig.SortType}
    (d : Basis I R (W.module A)) (e : Basis J R (Z.module A)) (r : W.module A →ₗ[R] Z.module A) :
    r = 0 ↔ ∀ i j, e.repr (r (d i)) j = 0 := by
  constructor
  · rintro rfl i j
    simp only [LinearMap.zero_apply, map_zero, Finsupp.zero_apply]
  · intro h
    apply d.ext
    intro i
    apply e.repr.injective
    ext j
    simpa only [LinearMap.zero_apply, map_zero, Finsupp.zero_apply] using h i j

/-- Killing the original tensor residual entries is precisely satisfaction of
the written tensor Law by the actual scalar-extended realization. -/
theorem tensorLawResidualIdeal_le_ker_iff (law : TensorLaw R sig) :
    tensorLawResidualIdeal d₀ law ≤ RingHom.ker (algebraMap R S) ↔
      (law.mapScalars (algebraMap R S)).holds (extendStructure R S A) := by
  let d := tensorShapeBasis rank A d₀ law.source
  let e := tensorShapeBasis rank A d₀ law.target
  let r := law.left.eval A - law.right.eval A
  have entries : tensorLawResidualIdeal d₀ law ≤ RingHom.ker (algebraMap R S) ↔
      ∀ i j, algebraMap R S (e.repr (r (d i)) j) = 0 := by
    rw [tensorLawResidualIdeal, Ideal.span_le]
    constructor
    · intro h i j
      exact h ⟨(i, j), rfl⟩
    · rintro h _ ⟨⟨i, j⟩, rfl⟩
      exact h i j
  have extended :
      ∀ i j, (extendShapeBasis (S := S) A e).repr
        (extendShapeMap A r (extendShapeBasis (S := S) A d i)) j =
          algebraMap R S (e.repr (r (d i)) j) :=
    extendShapeMap_entry (S := S) A d e r
  have tensorLaw : (law.mapScalars (algebraMap R S)).holds (extendStructure R S A) ↔
      extendShapeMap (R := S) A r = 0 := by
    change (law.left.mapScalars (algebraMap R S)).eval (extendStructure R S A) =
        (law.right.mapScalars (algebraMap R S)).eval (extendStructure R S A) ↔ _
    rw [eval_mapScalars_eq_extendShapeMap, eval_mapScalars_eq_extendShapeMap, ← sub_eq_zero, extendShapeMap_sub]
  have compare : (∀ i j, algebraMap R S (e.repr (r (d i)) j) = 0) ↔
      ∀ i j, (extendShapeBasis (S := S) A e).repr
        (extendShapeMap A r (extendShapeBasis (S := S) A d i)) j = 0 :=
    forall_congr' fun i => forall_congr' fun j => Iff.of_eq (congrArg (· = 0) (extended i j).symm)
  exact entries.trans (compare.trans
    ((tensorLinearMap_eq_zero_iff (extendShapeBasis (S := S) A d)
      (extendShapeBasis (S := S) A e) (extendShapeMap A r)).symm.trans tensorLaw.symm))

end Residual

end

end SHIGURE.RealizationFamilies
