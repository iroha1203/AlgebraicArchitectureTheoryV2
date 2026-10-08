import ResearchLean.AG.AtlasCoefficientFiber.RationalGramProjection

/-!
# Executable coordinates for the original rational image

Position: G-135 E finite image construction. The average of all generated
maximal Gram projections is an executable matrix whose range is exactly the
original matrix image. Its kernel is the original transpose kernel.

## Implementation notes

Every maximal family spans the same image, so averaging preserves its identity
action on that image and its symmetry. The generated family is nonempty even
at rank zero, and its computed cardinal provides the denominator. Arbitrary
choice of a basis was rejected because it would prevent executing the same
producer on W tables. Full ambient dimensions are not claimed as homology
or coefficient dimensions; later native transports must identify the actual
projector images with original P/Q and the same maps.
-/

namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates

open Matrix
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra

universe u v
variable {m : Type u} {n : Type v} [Fintype m] [Fintype n]

/-- E executable image producer: average the rational Gram projections over
all maximal families generated from entries. No basis or rank is supplied. -/
def imageProjection (A : Matrix m n ℚ) : Matrix m m ℚ :=
  ((maximalGramSelections A).card : ℚ)⁻¹ •
    ∑ s ∈ maximalGramSelections A, gramProjection A s

/-- Owner denominator API: the generated finite set is nonempty, including
empty matrices, so the rational average denominator is nonzero. -/
theorem maximalGramSelections_card_ne_zero (A : Matrix m n ℚ) :
    ((maximalGramSelections A).card : ℚ) ≠ 0 := by
  exact_mod_cast (Finset.card_ne_zero.mpr (maximalGramSelections_nonempty A))

/-- Owner evaluation API displays all coordinate coefficients as the actual
finite rational average. Finite indices come solely from the input table. -/
theorem imageProjection_mulVec (A : Matrix m n ℚ) (x : m → ℚ) :
    imageProjection A *ᵥ x = ((maximalGramSelections A).card : ℚ)⁻¹ •
      ∑ s ∈ maximalGramSelections A, gramProjection A s *ᵥ x := by
  rw [imageProjection, Matrix.smul_mulVec, Matrix.sum_mulVec]

/-- E image-fixing theorem: every original image representative is fixed by
all generated family projections and hence by their executable average. -/
theorem imageProjection_fixes_range (A : Matrix m n ℚ) (x : m → ℚ)
    (hx : x ∈ LinearMap.range A.mulVecLin) : imageProjection A *ᵥ x = x := by
  rw [imageProjection_mulVec]
  have hs : (∑ s ∈ maximalGramSelections A, gramProjection A s *ᵥ x) =
      ∑ _s ∈ maximalGramSelections A, x := by
    apply Finset.sum_congr rfl
    intro s h
    exact gramProjection_fixes_range A s h x hx
  rw [hs, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (maximalGramSelections_card_ne_zero A), one_smul]

/-- Every averaged output lies in the same original image. The explicit
selected-column coefficients give this inclusion without a range certificate. -/
theorem imageProjection_mulVec_mem_range (A : Matrix m n ℚ) (x : m → ℚ) :
    imageProjection A *ᵥ x ∈ LinearMap.range A.mulVecLin := by
  rw [imageProjection_mulVec]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro s _hs
  rw [gramProjection_mulVec]
  exact selectedColumns_range_le A s ⟨_, rfl⟩

/-- E exact image coordinates: the generated projector image equals the
literal original matrix image in both directions. -/
theorem imageProjection_range (A : Matrix m n ℚ) :
    LinearMap.range (imageProjection A).mulVecLin = LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact imageProjection_mulVec_mem_range A y
  · intro x hx
    exact ⟨x, imageProjection_fixes_range A x hx⟩

/-- Owner symmetry API: averaging preserves the symmetry of each original
Gram projection. This proves the transpose-kernel characterization below. -/
theorem imageProjection_transpose (A : Matrix m n ℚ) :
    (imageProjection A)ᵀ = imageProjection A := by
  rw [imageProjection, Matrix.transpose_smul, Matrix.transpose_sum]
  simp only [gramProjection_transpose]

/-- Owner idempotence API follows from the actual range-fixing theorem; no
idempotence property is embedded in the executable data producer. -/
theorem imageProjection_mul_self (A : Matrix m n ℚ) :
    imageProjection A * imageProjection A = imageProjection A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  exact imageProjection_fixes_range A _ (imageProjection_mulVec_mem_range A x)

/-- The generated image projector fixes the original matrix on every input
column combination, as a full matrix equality. -/
theorem imageProjection_mul (A : Matrix m n ℚ) :
    imageProjection A * A = A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  exact imageProjection_fixes_range A _ ⟨x, rfl⟩

/-- Owner kernel API: zero projected output is equivalent to the same
original transpose equation. The reverse direction evaluates every selected
transpose component; no orthogonality certificate is supplied. -/
theorem imageProjection_mulVec_eq_zero_iff (A : Matrix m n ℚ) (x : m → ℚ) :
    imageProjection A *ᵥ x = 0 ↔ Aᵀ *ᵥ x = 0 := by
  constructor
  · intro hx
    have he : Aᵀ * imageProjection A = Aᵀ := by
      simpa only [Matrix.transpose_mul, imageProjection_transpose] using
        congrArg Matrix.transpose (imageProjection_mul A)
    have h := congrArg (fun C => C *ᵥ x) he
    change (Aᵀ * imageProjection A) *ᵥ x = Aᵀ *ᵥ x at h
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero] at h
    exact h.symm
  · intro hx
    rw [imageProjection_mulVec]
    have hs : ∀ s : Fin (rationalMatrixRank A) → n,
        gramProjection A s *ᵥ x = 0 := by
      intro s
      have hc : (selectedColumns A s)ᵀ *ᵥ x = 0 := by
        funext j
        rw [selectedColumns_transpose_mulVec, hx]
        rfl
      rw [gramProjection_mulVec, hc, Matrix.mulVec_zero, Matrix.mulVec_zero]
    simp only [hs, Finset.sum_const_zero, smul_zero]

/-- E exact transpose-kernel equality for the executable image coordinates.
Both kernels refer to the original full rational matrices. -/
theorem imageProjection_ker (A : Matrix m n ℚ) :
    LinearMap.ker (imageProjection A).mulVecLin = LinearMap.ker Aᵀ.mulVecLin := by
  ext x
  exact imageProjection_mulVec_eq_zero_iff A x

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.maximalGramSelections_card_ne_zero
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_fixes_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_mulVec_mem_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_transpose
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_mul
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_mulVec_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_ker

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
