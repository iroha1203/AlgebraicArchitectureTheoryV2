import ResearchLean.AG.UniformInvariance.ExecutableRationalRank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-!
# Input-generated rational Gram projections

Position: GOAL G-135 E, finite image/kernel/quotient coordinates. This module
constructs maximal column families from the accepted G-107 rational rank
search, not from a supplied basis or expected rank. Each accepted family spans
the same literal range as the original rational table.

## Implementation notes

The inverse is rational determinant inverse times adjugate, so its data body
is executable; mathlib's noncomputable matrix inverse is used only to prove
correctness. All maximal Gram-good families are retained. The downstream
image projector averages their projections, avoiding arbitrary pivot choice
and treating the empty rank uniformly. Semantic rank and choice occur only
in correctness proofs. Supplying homology bases or inverse certificates was
rejected because E requires their generation from original entries. These
are general linear algebra APIs; original P/R/tau transports remain separate
obligations and are not replaced with an arbitrary intermediate complex.
-/

namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates

open Matrix
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra

universe u v
variable {m : Type u} {n : Type v}

/-- E executable inverse API: determinant inverse times adjugate. Finite
square indices supply determinant arithmetic; no invertibility is input data. -/
def adjugateInverse {k : Type*} [Fintype k] [DecidableEq k]
    (A : Matrix k k ℚ) : Matrix k k ℚ := A.det⁻¹ • A.adjugate

/-- Owner correctness API connects the executable formula to mathlib's
nonsingular inverse, including singular and empty matrices. -/
theorem adjugateInverse_eq_inverse {k : Type*} [Fintype k] [DecidableEq k]
    (A : Matrix k k ℚ) : adjugateInverse A = A⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

/-- Owner cancellation API; the nonzero determinant is proved for Gram-good
families, never stored as an input certificate. -/
theorem adjugateInverse_mul {k : Type*} [Fintype k] [DecidableEq k]
    (A : Matrix k k ℚ) (h : A.det ≠ 0) : adjugateInverse A * A = 1 := by
  rw [adjugateInverse_eq_inverse]
  exact Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr h)

/-- Owner right cancellation API with the same generated Gram premise. -/
theorem mul_adjugateInverse {k : Type*} [Fintype k] [DecidableEq k]
    (A : Matrix k k ℚ) (h : A.det ≠ 0) : A * adjugateInverse A = 1 := by
  rw [adjugateInverse_eq_inverse]
  exact Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr h)

/-- Owner transpose API for the rational executable inverse, used to prove
symmetry of the generated image projection. -/
theorem adjugateInverse_transpose {k : Type*} [Fintype k] [DecidableEq k]
    (A : Matrix k k ℚ) : (adjugateInverse A)ᵀ = adjugateInverse Aᵀ := by
  simp only [adjugateInverse_eq_inverse, Matrix.transpose_nonsing_inv]

variable [Fintype m] [Fintype n]

/-- E finite selection producer: all families of computed rank with a
nonzero Gram determinant. The body reads only rational entries and the
accepted executable rank; no semantic basis/rank is supplied. -/
def maximalGramSelections (A : Matrix m n ℚ) :
    Finset (Fin (rationalMatrixRank A) → n) :=
  Finset.univ.filter fun s => selectionIndependent A s = true

/-- Owner membership API relates the finite producer to the original Gram
predicate. Its finite premises come from the input matrix indices. -/
theorem mem_maximalGramSelections_iff (A : Matrix m n ℚ)
    (s : Fin (rationalMatrixRank A) → n) :
    s ∈ maximalGramSelections A ↔ (columnGram A s).det ≠ 0 := by
  simp only [maximalGramSelections, Finset.mem_filter, Finset.mem_univ, true_and,
    selectionIndependent, decide_eq_true_eq]

/-- E maximal-family existence is generated from accepted rank correctness;
rank zero has the empty family, so no nonempty input premise is introduced. -/
theorem maximalGramSelections_nonempty (A : Matrix m n ℚ) :
    (maximalGramSelections A).Nonempty := by
  have h : hasNonzeroGramMinor A (rationalMatrixRank A) = true :=
    (hasNonzeroGramMinor_eq_true_iff A _).2
      (by rw [rationalMatrixRank_eq_rank])
  obtain ⟨s, hs⟩ := (hasNonzeroGramMinor_eq_true_iff_exists A _).1 h
  exact ⟨s, (mem_maximalGramSelections_iff A s).2
    ((columnGram_det_ne_zero_iff A s).2 hs)⟩

/-- Every generated maximal family spans the actual original matrix range.
Inclusion is the original column-selection API; equality uses proved rank
correctness and finite dimensionality, rather than a spanning certificate. -/
theorem maximalGramSelections_range (A : Matrix m n ℚ)
    (s : Fin (rationalMatrixRank A) → n) (hs : s ∈ maximalGramSelections A) :
    LinearMap.range (selectedColumns A s).mulVecLin =
      LinearMap.range A.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq (selectedColumns_range_le A s)
  change (selectedColumns A s).rank = A.rank
  rw [selectedColumns_rank_eq A s
    ((columnGram_det_ne_zero_iff A s).1
      ((mem_maximalGramSelections_iff A s).1 hs)), rationalMatrixRank_eq_rank]

/-- E selected-family projection formula. It has no rank or invertibility
field; correctness is proved separately for families produced above. -/
def gramProjection (A : Matrix m n ℚ) {k : ℕ} (s : Fin k → n) :
    Matrix m m ℚ :=
  selectedColumns A s * adjugateInverse (columnGram A s) * (selectedColumns A s)ᵀ

omit [Fintype n] in
/-- Owner evaluation API: every output is an actual original selected-column
combination, with the explicit inverse-Gram coefficients. -/
theorem gramProjection_mulVec (A : Matrix m n ℚ) {k : ℕ}
    (s : Fin k → n) (x : m → ℚ) :
    gramProjection A s *ᵥ x = selectedColumns A s *ᵥ
      (adjugateInverse (columnGram A s) *ᵥ ((selectedColumns A s)ᵀ *ᵥ x)) := by
  simp only [gramProjection, Matrix.mulVec_mulVec, Matrix.mul_assoc]

omit [Fintype n] in
/-- Owner fixing API: a Gram-good projection fixes every selected column.
The determinant premise is generated by maximalGramSelections membership. -/
theorem gramProjection_mul_selectedColumns (A : Matrix m n ℚ) {k : ℕ}
    (s : Fin k → n) (hs : (columnGram A s).det ≠ 0) :
    gramProjection A s * selectedColumns A s = selectedColumns A s := by
  calc
    _ = selectedColumns A s *
        (adjugateInverse (columnGram A s) * columnGram A s) := by
      simp only [gramProjection, columnGram_eq_transpose_mul, Matrix.mul_assoc]
    _ = selectedColumns A s := by rw [adjugateInverse_mul _ hs, Matrix.mul_one]

/-- Owner range-fixing API: generated maximal-family projection acts as the
identity on every element of the same original matrix range. -/
theorem gramProjection_fixes_range (A : Matrix m n ℚ)
    (s : Fin (rationalMatrixRank A) → n) (hs : s ∈ maximalGramSelections A)
    (x : m → ℚ) (hx : x ∈ LinearMap.range A.mulVecLin) :
    gramProjection A s *ᵥ x = x := by
  rw [← maximalGramSelections_range A s hs] at hx
  obtain ⟨y, rfl⟩ := hx
  change gramProjection A s *ᵥ (selectedColumns A s *ᵥ y) = selectedColumns A s *ᵥ y
  rw [Matrix.mulVec_mulVec, gramProjection_mul_selectedColumns A s
    ((mem_maximalGramSelections_iff A s).1 hs)]

omit [Fintype n] in
/-- Owner transpose API: the Gram projection is symmetric even when the
family is singular. Finite rational dot-product Gram matrices are symmetric. -/
theorem gramProjection_transpose (A : Matrix m n ℚ) {k : ℕ}
    (s : Fin k → n) : (gramProjection A s)ᵀ = gramProjection A s := by
  have hg : (columnGram A s)ᵀ = columnGram A s := by
    simp only [columnGram_eq_transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [gramProjection, Matrix.transpose_mul, Matrix.transpose_transpose,
    adjugateInverse_transpose, hg, Matrix.mul_assoc]

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.adjugateInverse
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.adjugateInverse_eq_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.adjugateInverse_mul
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.mul_adjugateInverse
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.adjugateInverse_transpose
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.maximalGramSelections
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.mem_maximalGramSelections_iff
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.maximalGramSelections_nonempty
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.maximalGramSelections_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.gramProjection
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.gramProjection_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.gramProjection_mul_selectedColumns
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.gramProjection_fixes_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.gramProjection_transpose

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.adjugateInverse.congr_simp

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
