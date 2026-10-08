import ResearchLean.AG.AtlasCoefficientFiber.RationalKernelCoordinates

/-!
# Generated coordinates for the original rational cokernel quotient

Position: G-135 E quotient construction. The original ambient module modulo
the original matrix range is identified in both directions with the generated
transpose-kernel projector image. The executable representative formula is
separate from mathlib's noncomputable quotient equivalence.

## Implementation notes

The first isomorphism theorem is applied to the generated complement map after
proving its kernel equals the original range. Defining the quotient as a
self-selected image would erase the construction obligation and was rejected.
The inverse is the original quotient class of the coordinate vector, not a
supplied representative. No coefficient/homology quotient is replaced here;
original native P/Q/R transports remain later obligations of E.
-/

namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates

open Matrix
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra

universe u v
variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq m]

/-- E generated quotient-coordinate equivalence, using the proved original
range as the removed space. The noncomputability is only quotient transport;
the coordinate representative is the executable kernelProjection A transpose. -/
noncomputable def quotientCoordinateEquiv (A : Matrix m n ℚ) :
    ((m → ℚ) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[ℚ]
      LinearMap.range (kernelProjection Aᵀ).mulVecLin :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [kernelProjection_ker, Matrix.transpose_transpose])).trans
      (kernelProjection Aᵀ).mulVecLin.quotKerEquivRange

/-- Owner representative API: every original quotient class maps to the
explicit executable coordinate correction of its original representative. -/
theorem quotientCoordinateEquiv_mk (A : Matrix m n ℚ) (x : m → ℚ) :
    (quotientCoordinateEquiv A (Submodule.Quotient.mk x) : m → ℚ) =
      kernelProjection Aᵀ *ᵥ x := by
  simp only [quotientCoordinateEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk,
    Matrix.mulVecLin_apply]

/-- Owner inverse API: the inverse of each generated coordinate is exactly
its original quotient class. The fixed-vector property is proved from the
same original transpose kernel, so no representative choice is supplied. -/
theorem quotientCoordinateEquiv_symm_apply (A : Matrix m n ℚ)
    (x : LinearMap.range (kernelProjection Aᵀ).mulVecLin) :
    (quotientCoordinateEquiv A).symm x = Submodule.Quotient.mk x.1 := by
  apply (quotientCoordinateEquiv A).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [quotientCoordinateEquiv_mk]
  exact (kernelProjection_fixes_ker Aᵀ x.1
    (by rw [← kernelProjection_range]; exact x.2)).symm

/-- E both-direction quotient-coordinate correspondence explicitly keeps
all original quotient classes, beyond representative-level equality. -/
theorem quotientCoordinateEquiv_left_inverse (A : Matrix m n ℚ)
    (x : (m → ℚ) ⧸ LinearMap.range A.mulVecLin) :
    (quotientCoordinateEquiv A).symm (quotientCoordinateEquiv A x) = x :=
  (quotientCoordinateEquiv A).symm_apply_apply x

/-- E every generated coordinate is recovered by the original quotient map
and the same executable correction, including rank-zero and empty cases. -/
theorem quotientCoordinateEquiv_right_inverse (A : Matrix m n ℚ)
    (x : LinearMap.range (kernelProjection Aᵀ).mulVecLin) :
    quotientCoordinateEquiv A ((quotientCoordinateEquiv A).symm x) = x :=
  (quotientCoordinateEquiv A).apply_symm_apply x

/-- E computed rank of the quotient-coordinate projector equals the
actual original cokernel dimension. No expected dimension is an input. -/
theorem quotientCoordinateEquiv_rank (A : Matrix m n ℚ) :
    rationalMatrixRank (kernelProjection Aᵀ) =
      Module.finrank ℚ ((m → ℚ) ⧸ LinearMap.range A.mulVecLin) := by
  rw [rationalMatrixRank_eq_finrank_range]
  exact (quotientCoordinateEquiv A).symm.finrank_eq

/-- E executable original kernel/cokernel dimensions are the ranks of the
two generated coordinate projectors. This is the literal G107 blockDefect,
not the unrestricted ambient defect of a redundant coordinate matrix. -/
theorem generatedCoordinateRanks_eq_blockDefect [DecidableEq n]
    (A : Matrix m n ℚ) :
    (rationalMatrixRank (kernelProjection A),
      rationalMatrixRank (kernelProjection Aᵀ)) =
        AAT.AG.ResolutionInvariance.blockDefect A.mulVecLin := by
  rw [kernelProjection_rank, quotientCoordinateEquiv_rank,
    AAT.AG.ResolutionInvariance.blockDefect_eq_finrank_sub_range]
  apply Prod.ext
  · have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    omega
  · have h := Submodule.finrank_quotient_add_finrank (LinearMap.range A.mulVecLin)
    omega

namespace Examples

/-- E firing input: rectangular projection with a genuine kernel. The
matrix supplies entries only, not expected dimension or basis certificates. -/
def projection : Matrix (Fin 1) (Fin 2) ℚ := !![1, 0]

/-- E firing input: rectangular inclusion with a genuine cokernel, using
the same rational coordinate producer as every other finite table. -/
def inclusion : Matrix (Fin 2) (Fin 1) ℚ := !![1; 0]

/-- E repeated-column input retains both original column names. Averaging
all generated maximal families must return the same one-dimensional image. -/
def repeatedColumns : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, 1]

/-- E kernel firing check executes the generic producer on the rectangular
projection; a nonzero solution coordinate is retained. -/
theorem projection_kernel : kernelProjection projection = !![0, 0; 0, 1] := by
  decide +kernel

/-- E quotient firing check executes the same producer for the surjective
projection, returning zero original cokernel coordinates. -/
theorem projection_quotient :
    kernelProjection projectionᵀ = (0 : Matrix (Fin 1) (Fin 1) ℚ) := by
  decide +kernel

/-- E image firing check executes the generic finite Gram average on the
rectangular inclusion, rather than taking its expected rank as input. -/
theorem inclusion_image : imageProjection inclusion = !![1, 0; 0, 0] := by
  decide +kernel

/-- E quotient firing check retains a nonzero original cokernel coordinate
of the rectangular inclusion. -/
theorem inclusion_quotient : kernelProjection inclusionᵀ = !![0, 0; 0, 1] := by
  decide +kernel

/-- E repeated-column firing check evaluates both maximal families and
averages their actual rational projections, preserving rank one. -/
theorem repeatedColumns_image :
    imageProjection repeatedColumns = !![1/2, 1/2; 1/2, 1/2] := by
  decide +kernel

/-- E repeated-column kernel check evaluates the orthogonal correction,
which is nonzero and differs from the image projection. -/
theorem repeatedColumns_kernel :
    kernelProjection repeatedColumns = !![1/2, -1/2; -1/2, 1/2] := by
  decide +kernel

/-- E empty-row check: all original column vectors solve the empty equation;
the same generic kernel producer returns their full identity coordinates. -/
theorem emptyRows_kernel :
    kernelProjection (0 : Matrix (Fin 0) (Fin 2) ℚ) = 1 := by
  decide +kernel

/-- E empty-column check: the original cokernel is the full row space;
the same generic quotient-coordinate producer returns its identity. -/
theorem emptyColumns_quotient :
    kernelProjection (0 : Matrix (Fin 2) (Fin 0) ℚ)ᵀ = 1 := by
  decide +kernel

/-- E empty-both check executes the maximal-family algorithm at rank zero,
without inserting a nonempty input or a default expected-rank certificate. -/
theorem empty_image :
    imageProjection (0 : Matrix (Fin 0) (Fin 0) ℚ) = 0 := by
  decide +kernel

/-- E diagnostic firing check reads only the generated projectors and their
computed ranks. The universal theorem connects this pair to blockDefect. -/
theorem projection_coordinate_ranks :
    (rationalMatrixRank (kernelProjection projection),
      rationalMatrixRank (kernelProjection projectionᵀ)) = (1, 0) := by
  decide +kernel

/-- E diagnostic firing check distinguishes nonzero original cokernel from
kernel using the same coordinate/rank evaluator. -/
theorem inclusion_coordinate_ranks :
    (rationalMatrixRank (kernelProjection inclusion),
      rationalMatrixRank (kernelProjection inclusionᵀ)) = (0, 1) := by
  decide +kernel

/-- E repeated-column diagnostic firing check gives both actual one-
dimensional defects without merging the two original input columns. -/
theorem repeatedColumns_coordinate_ranks :
    (rationalMatrixRank (kernelProjection repeatedColumns),
      rationalMatrixRank (kernelProjection repeatedColumnsᵀ)) = (1, 1) := by
  decide +kernel

end Examples

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.quotientCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.quotientCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.quotientCoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.quotientCoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.quotientCoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.quotientCoordinateEquiv_rank
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.generatedCoordinateRanks_eq_blockDefect
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.projection
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.inclusion
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.repeatedColumns
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.projection_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.projection_quotient
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.inclusion_image
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.inclusion_quotient
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.repeatedColumns_image
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.repeatedColumns_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.emptyRows_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.emptyColumns_quotient
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.empty_image
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.projection_coordinate_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.inclusion_coordinate_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.Examples.repeatedColumns_coordinate_ranks
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection.congr_simp

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
