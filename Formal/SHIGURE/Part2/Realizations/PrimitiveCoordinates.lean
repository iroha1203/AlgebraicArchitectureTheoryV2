import Formal.SHIGURE.Part2.Tensor.CoefficientCoherence
import Formal.SHIGURE.Part2.Realizations.PolynomialTerms
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Coefficients of primitive operations on free charts -/

namespace SHIGURE.RealizationFamilies

open Module CategoryTheory

noncomputable section

universe u

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {n : I → ℕ} {r : ℕ}
  {M : I → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  {N : Type u} [AddCommGroup N] [Module R N]

/-- Read every coefficient of the original multilinear operation. -/
def multilinearCoefficients (b : ∀ i, Basis (Fin (n i)) R (M i)) (d : Basis (Fin r) R N)
    (op : MultilinearMap R M N) : (∀ i, Fin (n i)) → Fin r → R :=
  fun a j => d.repr (op (fun i => b i (a i))) j

open Classical in
/-- Rebuild a multilinear operation from the independent coefficients of a free chart. -/
def multilinearOfCoefficients (b : ∀ i, Basis (Fin (n i)) R (M i)) (d : Basis (Fin r) R N)
    (c : (∀ i, Fin (n i)) → Fin r → R) : MultilinearMap R M N :=
  ∑ a : (∀ i, Fin (n i)), (MultilinearMap.mkPiRing R I (d.equivFun.symm (c a))).compLinearMap
    (fun i => (b i).coord (a i))

/-- The reconstructed operation has its specified value on each tuple of basis vectors. -/
theorem multilinearOfCoefficients_basis (b : ∀ i, Basis (Fin (n i)) R (M i)) (d : Basis (Fin r) R N)
    (c : (∀ i, Fin (n i)) → Fin r → R) (a : ∀ i, Fin (n i)) :
    multilinearOfCoefficients b d c (fun i => b i (a i)) = d.equivFun.symm (c a) := by
  classical
  rw [multilinearOfCoefficients, MultilinearMap.sum_apply]
  simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply]
  have product (v : ∀ i, Fin (n i)) :
      (∏ i, (b i).coord (v i) (b i (a i))) = if v = a then (1 : R) else 0 := by
    by_cases equal : v = a
    · subst v
      simp [Basis.coord_apply]
    · rw [if_neg equal]
      obtain ⟨i, different⟩ : ∃ i, v i ≠ a i := Function.ne_iff.mp equal
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne different]
  simp only [product, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The reconstructed coefficients are exactly the original coefficient array. -/
theorem multilinearCoefficients_ofCoefficients (b : ∀ i, Basis (Fin (n i)) R (M i))
    (d : Basis (Fin r) R N) (c : (∀ i, Fin (n i)) → Fin r → R) :
    multilinearCoefficients b d (multilinearOfCoefficients b d c) = c := by
  funext a j
  rw [multilinearCoefficients, multilinearOfCoefficients_basis, ← Basis.equivFun_apply]
  exact congrFun (d.equivFun.apply_symm_apply (c a)) j

/-- The multiplications by coordinates and the finite sum recover an arbitrary
original operation in those coordinates. -/
theorem multilinearOfCoefficients_coefficients (b : ∀ i, Basis (Fin (n i)) R (M i))
    (d : Basis (Fin r) R N) (op : MultilinearMap R M N) :
    multilinearOfCoefficients b d (multilinearCoefficients b d op) = op := by
  classical
  apply MultilinearMap.ext
  intro x
  rw [multilinearOfCoefficients, MultilinearMap.sum_apply]
  simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply]
  let y (i : I) (j : Fin (n i)) : M i := (b i).repr (x i) j • b i j
  have he : (fun i => ∑ j, y i j) = x := funext fun i => (b i).sum_repr (x i)
  rw [← he]
  rw [op.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  have repr : d.equivFun.symm (multilinearCoefficients b d op a) = op (fun i => b i (a i)) := by
    apply d.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [repr]
  have evaluate (i : I) : (∑ t, y i t) = x i := congrFun he i
  simp only [evaluate, Basis.coord_apply]
  exact (op.map_smul_univ (fun i => (b i).repr (x i) (a i)) (fun i => b i (a i))).symm

/-- Reading an output coordinate of a reconstructed operation gives the
sum over the original basis tuples. -/
theorem multilinearOfCoefficients_coordinates
    (c : (∀ i, Fin (n i)) → Fin r → R) (x : ∀ i, Fin (n i) → R) (j : Fin r) :
    letI : DecidableEq I := Classical.decEq I
    multilinearOfCoefficients (fun i => Pi.basisFun R (Fin (n i))) (Pi.basisFun R (Fin r)) c x j =
      ∑ a : (∀ i, Fin (n i)), c a j * ∏ i, x i (a i) := by
  classical
  rw [multilinearOfCoefficients, MultilinearMap.sum_apply, Finset.sum_apply]
  simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply,
    Pi.basisFun_equivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    Basis.coord_apply, ← Basis.equivFun_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]

/-- A free chart specifies one coefficient per input tuple and output basis vector. -/
def multilinearCoefficientsEquiv (b : ∀ i, Basis (Fin (n i)) R (M i))
    (d : Basis (Fin r) R N) :
    MultilinearMap R M N ≃ ((∀ i, Fin (n i)) → Fin r → R) where
  toFun := multilinearCoefficients b d
  invFun := multilinearOfCoefficients b d
  left_inv := multilinearOfCoefficients_coefficients b d
  right_inv := multilinearCoefficients_ofCoefficients b d

section PrimitiveCoordinates

open SHIGURE.TensorRealization

variable (sig : Signature.{u}) (rank : sig.SortType → ℕ)

/-- The free carrier at a sort has one coordinate for each of its basis vectors. -/
abbrev freeCarrier (R : Type u) [CommRing R] (s : sig.SortType) : ModuleCat.{u} R :=
  ModuleCat.of R (Fin (rank s) → R)

/-- The universal chart carries one coefficient per primitive and basis tuple. -/
@[ext]
structure PrimitiveCoefficients (R : Type u) where
  total (e : sig.Total) :
    (∀ i : TensorPosition (sig.totalArity e).inputs, Fin (rank i.1)) → Fin (rank (sig.totalArity e).output) → R
  quantity (q : sig.Quantity) :
    (∀ i : TensorPosition (sig.quantityArity q).inputs, Fin (rank i.1)) → Fin (rank (sig.quantityArity q).output) → R

/-- Reconstruct the actual tensor realization in the fixed free carriers. -/
def PrimitiveCoefficients.toTensor (c : PrimitiveCoefficients sig rank R) : TensorStructure R sig where
  carrier := freeCarrier sig rank R
  total e :=
    letI : Fintype (TensorPosition (sig.totalArity e).inputs) := Fintype.ofFinite _
    multilinearOfCoefficients (fun _ => Pi.basisFun _ _) (Pi.basisFun _ _) (c.total e)
  quantity q :=
    letI : Fintype (TensorPosition (sig.quantityArity q).inputs) := Fintype.ofFinite _
    multilinearOfCoefficients (fun _ => Pi.basisFun _ _) (Pi.basisFun _ _) (c.quantity q)

/-- Read the coefficients of an arbitrary realization with specified free bases. -/
def PrimitiveCoefficients.ofTensor (A : TensorStructure R sig)
    (b : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) : PrimitiveCoefficients sig rank R where
  total e :=
    letI : Fintype (TensorPosition (sig.totalArity e).inputs) := Fintype.ofFinite _
    multilinearCoefficients (fun i => b i.1) (b _) (A.total e)
  quantity q :=
    letI : Fintype (TensorPosition (sig.quantityArity q).inputs) := Fintype.ofFinite _
    multilinearCoefficients (fun i => b i.1) (b _) (A.quantity q)

/-- Reading the chart coefficients after reconstruction recovers the exact array. -/
theorem PrimitiveCoefficients.ofTensor_toTensor (c : PrimitiveCoefficients sig rank R) :
    PrimitiveCoefficients.ofTensor sig rank (PrimitiveCoefficients.toTensor sig rank c)
      (fun _ => Pi.basisFun _ _) = c := by
  apply PrimitiveCoefficients.ext
  · funext e
    letI : Fintype (TensorPosition (sig.totalArity e).inputs) := Fintype.ofFinite _
    exact multilinearCoefficients_ofCoefficients _ _ (c.total e)
  · funext q
    letI : Fintype (TensorPosition (sig.quantityArity q).inputs) := Fintype.ofFinite _
    exact multilinearCoefficients_ofCoefficients _ _ (c.quantity q)



/-- The coordinate equivalences on the carriers transport an original operation to
the operation reconstructed from its coefficients. -/
theorem multilinearOfCoefficients_free_apply
    (b : ∀ i, Basis (Fin (n i)) R (M i)) (d : Basis (Fin r) R N)
    (op : MultilinearMap R M N) (x : ∀ i, M i) :
    multilinearOfCoefficients (fun i => Pi.basisFun R (Fin (n i))) (Pi.basisFun R (Fin r))
      (multilinearCoefficients b d op) (fun i => (b i).equivFun (x i)) = d.equivFun (op x) := by
  classical
  have transported : (multilinearOfCoefficients (fun i => Pi.basisFun R (Fin (n i)))
      (Pi.basisFun R (Fin r)) (multilinearCoefficients b d op)).compLinearMap
      (fun i => (b i).equivFun.toLinearMap) = d.equivFun.toLinearMap.compMultilinearMap op := by
    apply (multilinearCoefficientsEquiv b (Pi.basisFun R (Fin r))).injective
    funext a j
    change (Pi.basisFun R (Fin r)).repr
      (multilinearOfCoefficients (fun i => Pi.basisFun R (Fin (n i))) (Pi.basisFun R (Fin r))
        (multilinearCoefficients b d op) (fun i => (b i).equivFun (b i (a i)))) j =
      (Pi.basisFun R (Fin r)).repr (d.equivFun (op (fun i => b i (a i)))) j
    have coord (i : I) : (b i).equivFun (b i (a i)) = Pi.basisFun R (Fin (n i)) (a i) := by
      ext l
      simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [funext coord, multilinearOfCoefficients_basis, Pi.basisFun_equivFun, LinearEquiv.refl_symm]
    rfl
  exact MultilinearMap.congr_fun transported x

set_option maxHeartbeats 420000 in
/-- The coordinates in a chosen basis form a structure-preserving arrow. -/
def PrimitiveCoefficients.tensorHomOfBasis (A : TensorStructure R sig)
    (b : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) :
    A ⟶ (PrimitiveCoefficients.ofTensor sig rank A b).toTensor sig rank where
  onSort s := (b s).equivFun.toLinearMap
  preservesTotal e x := by
    letI : Fintype (TensorPosition (sig.totalArity e).inputs) := Fintype.ofFinite _
    have h := multilinearOfCoefficients_free_apply (fun i => b i.1) (b (sig.totalArity e).output)
      (A.total e) x
    change (b (sig.totalArity e).output).equivFun (A.total e x) =
      multilinearOfCoefficients (fun _ => Pi.basisFun R _) (Pi.basisFun R _)
        (multilinearCoefficients (fun i => b i.1) (b (sig.totalArity e).output) (A.total e))
        (fun i => (b i.1).equivFun (x i))
    exact h.symm
  preservesQuantity q x := by
    letI : Fintype (TensorPosition (sig.quantityArity q).inputs) := Fintype.ofFinite _
    have h := multilinearOfCoefficients_free_apply (fun i => b i.1) (b (sig.quantityArity q).output)
      (A.quantity q) x
    change (b (sig.quantityArity q).output).equivFun (A.quantity q x) =
      multilinearOfCoefficients (fun _ => Pi.basisFun R _) (Pi.basisFun R _)
        (multilinearCoefficients (fun i => b i.1) (b (sig.quantityArity q).output) (A.quantity q))
        (fun i => (b i.1).equivFun (x i))
    exact h.symm

/-- The tensor reconstructed from any basis has the actual original structure via the coordinate maps. -/
def PrimitiveCoefficients.tensorIsoOfBasis (A : TensorStructure R sig)
    (b : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) :
    A ≅ (PrimitiveCoefficients.ofTensor sig rank A b).toTensor sig rank :=
  structureIsoOfCarrierEquiv (PrimitiveCoefficients.tensorHomOfBasis sig rank A b)
    (fun s => (b s).equivFun) (fun _ => rfl)

end PrimitiveCoordinates

section CoordinateVariables

open SHIGURE.TensorRealization

variable (sig : Signature.{u}) (rank : sig.SortType → ℕ)

/-- Each primitive coefficient records its operation, input basis tuple and output row. -/
inductive PrimitiveCoordinate : Type u
  | total (e : sig.Total) (input : ∀ i : TensorPosition (sig.totalArity e).inputs, Fin (rank i.1))
      (output : Fin (rank (sig.totalArity e).output))
  | quantity (q : sig.Quantity) (input : ∀ i : TensorPosition (sig.quantityArity q).inputs, Fin (rank i.1))
      (output : Fin (rank (sig.quantityArity q).output))

/-- A coefficient array is a value at each primitive coordinate. -/
def PrimitiveCoefficients.valuesEquiv : PrimitiveCoefficients sig rank R ≃ (PrimitiveCoordinate sig rank → R) where
  toFun c
    | .total e a j => c.total e a j
    | .quantity q a j => c.quantity q a j
  invFun values := ⟨fun e a j => values (.total e a j), fun q a j => values (.quantity q a j)⟩
  left_inv c := by cases c; rfl
  right_inv values := funext fun c => by cases c <;> rfl

end CoordinateVariables

end

end SHIGURE.RealizationFamilies
