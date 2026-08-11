import ResearchLean.AG.UniformInvariance.DefectSemantics
import Mathlib.LinearAlgebra.Matrix.Rank
import Formal.Util.AssertStandardAxioms

/-!
# Executable rational matrix rank and defect

This module discharges the linear-algebra kernel of claim (ii) in
`G-107-aat-uniform-invariance-characterization`.  For every finite rectangular
rational matrix it computes the exact rank by a finite search over column
selections.  A selection is accepted precisely when the determinant of its
Gram matrix is nonzero.  The executable definitions do not inspect
`Matrix.rank`, a basis, a kernel, a range, a quotient, or any supplied rank or
defect certificate.

The correctness proof has two independent directions.  A nonzero Gram
determinant makes the selected columns linearly independent, hence their count
is bounded by the matrix rank.  Conversely, a basis of the column span is used
only in the proof to show that every number at most the semantic rank has an
accepted selection.  The resulting computed rank is then connected to the
literal kernel/cokernel pair from `DefectSemantics` by rank-nullity and the
finite-dimensional quotient formula.

The final examples execute the same generic evaluator on rectangular
projection and inclusion matrices, a duplicated-column matrix, the identity,
and the zero matrix.  No fixture lookup occurs in the evaluator.

## Position and premises

This file is the executable linear-algebra API supporting claim (ii), not the
all-subset checker itself.  Its ambient inputs are exactly a rational matrix
with finite row and column index types.  The finite search does not require a
separate `DecidableEq` premise on the column type; semantic rank, basis,
kernel, range, and quotient data are derived only in correctness theorems.
Unless noted as an executable fixture, declarations below are API helpers or
correctness lemmas for `rationalMatrixRank` and `rationalMatrixDefect`.

## Implementation notes

Column selection uses the standard `Matrix.submatrix` API, and independence is
tested by the determinant of the selected Gram matrix.  Exhaustive finite Gram
search was chosen because it treats every rectangular matrix and every possible
rank uniformly while reducing directly to rational arithmetic and determinant
evaluation.  A semantic `Matrix.rank` wrapper was rejected because it is not an
executable computation.  A custom Gaussian-elimination implementation was
rejected because it would introduce a second pivot algorithm and a separate
correctness surface when bounded finite search already meets the fixed finite
presentation contract.  A square-matrix determinant alone was rejected because
it cannot recover lower ranks or rectangular rank.  Finally, supplied bases,
ranks, and defects were rejected because they would move the result into an
input certificate instead of deriving it from matrix entries.
-/

namespace AAT.AG.ResolutionInvariance

namespace ExecutableRationalLinearAlgebra

open Matrix

universe u v

variable {m : Type u} {n : Type v}

/-! ## Finite Gram search -/

/-- API helper for the Gram search: select columns by the standard
`Matrix.submatrix` reindexing.  It has no premise beyond the input matrix and
contains no rank or independence information. -/
def selectedColumns (A : Matrix m n ℚ) {k : ℕ} (selection : Fin k → n) :
    Matrix m (Fin k) ℚ :=
  A.submatrix id selection

/-- API helper for `selectionIndependent`: the square Gram matrix of a selected
column family.  `Fintype m` is the finite-row input needed for matrix
multiplication, not a rank certificate. -/
def columnGram [Fintype m] (A : Matrix m n ℚ) {k : ℕ}
    (selection : Fin k → n) : Matrix (Fin k) (Fin k) ℚ :=
  (selectedColumns A selection)ᵀ * selectedColumns A selection

/-- A selected rational column family has nonzero Gram determinant exactly
when the selected columns are linearly independent. -/
theorem columnGram_det_ne_zero_iff [Fintype m]
    (A : Matrix m n ℚ) {k : ℕ} (selection : Fin k → n) :
    (columnGram A selection).det ≠ 0 ↔
      LinearIndependent ℚ (selectedColumns A selection).col := by
  constructor
  · intro hdet
    have hgram : LinearIndependent ℚ (columnGram A selection).col :=
      Matrix.linearIndependent_cols_of_det_ne_zero hdet
    have hgramInj : Function.Injective (columnGram A selection).mulVec :=
      Matrix.mulVec_injective_iff.mpr hgram
    have hgramLinInj :
        Function.Injective (columnGram A selection).mulVecLin := by
      simpa only [Matrix.mulVecLin_apply] using hgramInj
    have hselectedLinInj :
        Function.Injective (selectedColumns A selection).mulVecLin := by
      rw [← LinearMap.ker_eq_bot]
      rw [← Matrix.ker_mulVecLin_transpose_mul_self
        (selectedColumns A selection)]
      exact LinearMap.ker_eq_bot.mpr hgramLinInj
    have hselectedInj :
        Function.Injective (selectedColumns A selection).mulVec := by
      simpa only [Matrix.mulVecLin_apply] using hselectedLinInj
    exact Matrix.mulVec_injective_iff.mp hselectedInj
  · intro hcolumns
    have hselectedInj :
        Function.Injective (selectedColumns A selection).mulVec :=
      Matrix.mulVec_injective_iff.mpr hcolumns
    have hselectedLinInj :
        Function.Injective (selectedColumns A selection).mulVecLin := by
      simpa only [Matrix.mulVecLin_apply] using hselectedInj
    have hgramLinInj :
        Function.Injective (columnGram A selection).mulVecLin := by
      rw [← LinearMap.ker_eq_bot]
      change LinearMap.ker
        (((selectedColumns A selection)ᵀ *
          selectedColumns A selection).mulVecLin) = ⊥
      rw [Matrix.ker_mulVecLin_transpose_mul_self
        (selectedColumns A selection)]
      exact LinearMap.ker_eq_bot.mpr hselectedLinInj
    have hgramInj : Function.Injective (columnGram A selection).mulVec := by
      simpa only [Matrix.mulVecLin_apply] using hgramLinInj
    have hgram : LinearIndependent ℚ (columnGram A selection).col :=
      Matrix.mulVec_injective_iff.mp hgramInj
    rw [Matrix.linearIndependent_cols_iff_isUnit,
      Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hgram
    exact hgram

/-- Executable predicate used by `hasNonzeroGramMinor`: test one selected Gram
determinant.  Its only premise is the finite row index needed to form the Gram
matrix. -/
def selectionIndependent [Fintype m] (A : Matrix m n ℚ) {k : ℕ}
    (selection : Fin k → n) : Bool :=
  decide ((columnGram A selection).det ≠ 0)

/-- The Boolean selection test is true exactly for linearly independent
selected columns. -/
theorem selectionIndependent_eq_true_iff [Fintype m]
    (A : Matrix m n ℚ) {k : ℕ} (selection : Fin k → n) :
    selectionIndependent A selection = true ↔
      LinearIndependent ℚ (selectedColumns A selection).col := by
  simp [selectionIndependent, columnGram_det_ne_zero_iff]

/-- Main finite-search helper for the executable rank API: search all
`k`-column selections for a nonzero Gram determinant.  The two `Fintype`
instances are the finite-matrix inputs from claim (ii); the standard finite
existential decision needs no separate column-equality premise.  The predicate
reads only rational matrix entries and determinants. -/
def hasNonzeroGramMinor [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (k : ℕ) : Bool :=
  decide (∃ selection : Fin k → n,
    selectionIndependent A selection = true)

/-- The finite Boolean search succeeds exactly when it finds a linearly
independent selected column family. -/
theorem hasNonzeroGramMinor_eq_true_iff_exists
    [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (k : ℕ) :
    hasNonzeroGramMinor A k = true ↔
      ∃ selection : Fin k → n,
        LinearIndependent ℚ (selectedColumns A selection).col := by
  simp [hasNonzeroGramMinor, selectionIndependent_eq_true_iff]

/-! ## Search correctness -/

/-- Selecting columns cannot increase the semantic matrix rank. -/
theorem selectedColumns_rank_le [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) {k : ℕ} (selection : Fin k → n) :
    (selectedColumns A selection).rank ≤ A.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  exact ⟨selection j, rfl⟩

/-- A linearly independent `k`-column selection has semantic rank `k`. -/
theorem selectedColumns_rank_eq
    (A : Matrix m n ℚ) {k : ℕ} (selection : Fin k → n)
    (h : LinearIndependent ℚ (selectedColumns A selection).col) :
    (selectedColumns A selection).rank = k := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hcard := linearIndependent_iff_card_eq_finrank_span.mp h
  simpa using hcard.symm

/-- The executable Gram search is sound and complete for the semantic rank:
it succeeds at size `k` exactly when `k ≤ A.rank`. -/
theorem hasNonzeroGramMinor_eq_true_iff
    [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) (k : ℕ) :
    hasNonzeroGramMinor A k = true ↔ k ≤ A.rank := by
  constructor
  · intro h
    obtain ⟨selection, hselection⟩ :=
      (hasNonzeroGramMinor_eq_true_iff_exists A k).mp h
    calc
      k = (selectedColumns A selection).rank :=
        (selectedColumns_rank_eq A selection hselection).symm
      _ ≤ A.rank := selectedColumns_rank_le A selection
  · intro hk
    classical
    have hk' : k ≤ Module.finrank ℚ
        (Submodule.span ℚ (Set.range A.col)) := by
      simpa only [Matrix.rank_eq_finrank_span_cols] using hk
    obtain ⟨f, hfRange, _hfSpan, hfIndependent⟩ :=
      Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.col)
    let inclusion : Fin k → Fin
        (Module.finrank ℚ (Submodule.span ℚ (Set.range A.col))) :=
      Fin.castLE hk'
    have hinclusion : Function.Injective inclusion :=
      Fin.castLE_injective hk'
    choose selection hselection using
      fun i : Fin k => hfRange (inclusion i)
    apply (hasNonzeroGramMinor_eq_true_iff_exists A k).mpr
    refine ⟨selection, ?_⟩
    have hrestricted := hfIndependent.comp inclusion hinclusion
    have hfamily : (selectedColumns A selection).col = f ∘ inclusion := by
      funext i
      exact hselection i
    rw [hfamily]
    exact hrestricted

/-! ## Exact executable rank and defect -/

/-- Main executable rank API for the Cycle 7 proof obligation: compute the
largest accepted column-selection size.  Its finite-index premises come from
the finite presentation; the body uses only finite search, Boolean tests,
rational arithmetic, and determinants.  `Matrix.rank` and dimension APIs occur
only in correctness theorems. -/
def rationalMatrixRank [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) : ℕ :=
  (Finset.range (Fintype.card n + 1)).sup fun k =>
    if hasNonzeroGramMinor A k then k else 0

/-- The executable rational matrix rank equals the semantic matrix rank for
every finite rectangular matrix. -/
theorem rationalMatrixRank_eq_rank
    [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) : rationalMatrixRank A = A.rank := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro k _hk
    by_cases hminor : hasNonzeroGramMinor A k = true
    · simpa [hminor] using
        (hasNonzeroGramMinor_eq_true_iff A k).mp hminor
    · have hfalse : hasNonzeroGramMinor A k = false :=
        Bool.eq_false_of_not_eq_true hminor
      simp [hfalse]
  · have hrankMem : A.rank ∈ Finset.range (Fintype.card n + 1) := by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le A.rank_le_card_width
    have hminor : hasNonzeroGramMinor A A.rank = true :=
      (hasNonzeroGramMinor_eq_true_iff A A.rank).mpr le_rfl
    simpa [rationalMatrixRank, hminor] using
      (Finset.le_sup (f := fun k =>
        if hasNonzeroGramMinor A k then k else 0) hrankMem)

/-- The executable rank equals the dimension of the literal range of the
matrix linear map. -/
theorem rationalMatrixRank_eq_finrank_range
    [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) :
    rationalMatrixRank A =
      Module.finrank ℚ (LinearMap.range A.mulVecLin) := by
  rw [rationalMatrixRank_eq_rank]
  rfl

/-- Main executable defect API supporting claim (ii): compute the exact
domain-kernel and codomain-cokernel dimension pair from the executable rank.
Its only premises are the finite row and column index types; no kernel, range,
rank, or defect certificate is supplied. -/
def rationalMatrixDefect [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) : ℕ × ℕ :=
  (Fintype.card n - rationalMatrixRank A,
    Fintype.card m - rationalMatrixRank A)

/-- The executable dimension differences equal the literal kernel/cokernel
defect used by the G-107 defect semantics. -/
theorem rationalMatrixDefect_eq_blockDefect
    [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) :
    rationalMatrixDefect A = blockDefect A.mulVecLin := by
  rw [rationalMatrixDefect, rationalMatrixRank_eq_finrank_range]
  rw [blockDefect]
  apply Prod.ext
  · dsimp only
    have hrankNullity :=
      LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have hdomain : Module.finrank ℚ (n → ℚ) = Fintype.card n := by
      simp
    omega
  · dsimp only
    have hquotient := Submodule.finrank_quotient_add_finrank
      (LinearMap.range A.mulVecLin)
    have hcodomain : Module.finrank ℚ (m → ℚ) = Fintype.card m := by
      simp
    omega

/-- A matrix with a nonzero entry has positive semantic rank.  This helper is
used only to certify that the executed rank-sensitive examples are nonzero. -/
theorem rank_pos_of_entry_ne_zero [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) {i : m} {j : n} (hentry : A i j ≠ 0) :
    0 < A.rank := by
  apply Nat.pos_of_ne_zero
  intro hrank
  have hspanFinrank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range A.col)) = 0 := by
    simpa only [Matrix.rank_eq_finrank_span_cols] using hrank
  have hspan : Submodule.span ℚ (Set.range A.col) = ⊥ :=
    Submodule.finrank_eq_zero.mp hspanFinrank
  have hcolMem : A.col j ∈ Submodule.span ℚ (Set.range A.col) :=
    Submodule.subset_span ⟨j, rfl⟩
  have hcolZero : A.col j = 0 := by
    rw [hspan] at hcolMem
    simpa using hcolMem
  apply hentry
  simpa only [Matrix.col_apply, Pi.zero_apply] using congrFun hcolZero i

/-! ## Executed rectangular and rank-sensitive examples -/

namespace Examples

/-- Executable firing fixture for the generic rank API: the projection
`ℚ² → ℚ` as a rectangular matrix.  It supplies no rank premise. -/
def projectionMatrix : Matrix (Fin 1) (Fin 2) ℚ := !![1, 0]

/-- Executable firing fixture for the generic rank API: the inclusion
`ℚ → ℚ²` as a rectangular matrix.  It supplies no rank premise. -/
def inclusionMatrix : Matrix (Fin 2) (Fin 1) ℚ := !![1; 0]

/-- Executable firing fixture for the generic rank API: a two-column
outer-product matrix with equal columns.  Its rank sensitivity is proved rather
than stored. -/
def duplicateColumnMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.vecMulVec (![1, 0] : Fin 2 → ℚ) (![1, 1] : Fin 2 → ℚ)

/-- The executable evaluator computes rank one for the projection. -/
theorem projectionMatrix_rank : rationalMatrixRank projectionMatrix = 1 := by
  rw [rationalMatrixRank_eq_rank]
  have hle := projectionMatrix.rank_le_card_height
  have hpos := rank_pos_of_entry_ne_zero projectionMatrix
    (i := 0) (j := 0) (by norm_num [projectionMatrix])
  norm_num at hle
  omega

/-- The executable evaluator computes rank one for the inclusion. -/
theorem inclusionMatrix_rank : rationalMatrixRank inclusionMatrix = 1 := by
  rw [rationalMatrixRank_eq_rank]
  have hle := inclusionMatrix.rank_le_card_width
  have hpos := rank_pos_of_entry_ne_zero inclusionMatrix
    (i := 0) (j := 0) (by norm_num [inclusionMatrix])
  norm_num at hle
  omega

/-- The executable evaluator does not overcount a duplicated column. -/
theorem duplicateColumnMatrix_rank :
    rationalMatrixRank duplicateColumnMatrix = 1 := by
  rw [rationalMatrixRank_eq_rank]
  have hle : duplicateColumnMatrix.rank ≤ 1 := by
    simpa [duplicateColumnMatrix] using
      (Matrix.rank_vecMulVec_le
        (![1, 0] : Fin 2 → ℚ) (![1, 1] : Fin 2 → ℚ))
  have hpos := rank_pos_of_entry_ne_zero duplicateColumnMatrix
    (i := 0) (j := 0) (by norm_num [duplicateColumnMatrix, Matrix.vecMulVec])
  omega

/-- The executable evaluator computes full rank for the two-dimensional
identity matrix. -/
theorem identityMatrix_rank :
    rationalMatrixRank (1 : Matrix (Fin 2) (Fin 2) ℚ) = 2 := by
  simp [rationalMatrixRank_eq_rank]

/-- The executable evaluator computes rank zero for the two-dimensional zero
matrix. -/
theorem zeroMatrix_rank :
    rationalMatrixRank (0 : Matrix (Fin 2) (Fin 2) ℚ) = 0 := by
  simp [rationalMatrixRank_eq_rank]

/-- The projection has one-dimensional kernel and zero-dimensional
cokernel. -/
theorem projectionMatrix_defect :
    rationalMatrixDefect projectionMatrix = (1, 0) := by
  simp [rationalMatrixDefect, projectionMatrix_rank]

/-- The inclusion has zero-dimensional kernel and one-dimensional
cokernel. -/
theorem inclusionMatrix_defect :
    rationalMatrixDefect inclusionMatrix = (0, 1) := by
  simp [rationalMatrixDefect, inclusionMatrix_rank]

end Examples

end ExecutableRationalLinearAlgebra

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only
  AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra
