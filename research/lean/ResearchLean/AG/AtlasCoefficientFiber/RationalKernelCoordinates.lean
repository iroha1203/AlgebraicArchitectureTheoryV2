import ResearchLean.AG.AtlasCoefficientFiber.RationalImageProjection

/-!
# Executable coordinates for the original rational kernel

Position: G-135 E kernel construction. The complement of the original
transpose image projection has range exactly the original matrix kernel.

## Implementation notes

Subtracting from the full identity is correct for this generic full matrix
kernel. A projected coefficient complex must later subtract its actual degree
projector instead, to remove unused ambient coordinates. Thus this generic
kernel is not silently substituted for H1(P) or H1(Q). The original equations,
both inclusions and fixed representatives are proved here; no kernel basis,
expected dimension or supplied projection law enters the data definition.
-/

namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates

open Matrix
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra

universe u v
variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n]

/-- E executable kernel producer from rational entries: complement the
image projector of the same original transpose matrix. -/
def kernelProjection (A : Matrix m n ℚ) : Matrix n n ℚ :=
  1 - imageProjection Aᵀ

/-- Owner evaluation API gives the explicit original-vector correction.
The identity needs decidable equality on the finite input column indices. -/
theorem kernelProjection_mulVec (A : Matrix m n ℚ) (x : n → ℚ) :
    kernelProjection A *ᵥ x = x - imageProjection Aᵀ *ᵥ x := by
  rw [kernelProjection, Matrix.sub_mulVec, Matrix.one_mulVec]

/-- Owner absorption API: the original matrix annihilates every generated
kernel representative. The transpose image-fixing equality proves this. -/
theorem mul_kernelProjection (A : Matrix m n ℚ) : A * kernelProjection A = 0 := by
  have h : A * imageProjection Aᵀ = A := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      imageProjection_transpose] using congrArg Matrix.transpose (imageProjection_mul Aᵀ)
  rw [kernelProjection, Matrix.mul_sub, Matrix.mul_one, h, sub_self]

/-- E generated representatives satisfy the same original equation Ax=0.
This is range inclusion, with no additional ambient restriction. -/
theorem kernelProjection_mulVec_mem_ker (A : Matrix m n ℚ) (x : n → ℚ) :
    kernelProjection A *ᵥ x ∈ LinearMap.ker A.mulVecLin := by
  change A *ᵥ (kernelProjection A *ᵥ x) = 0
  rw [Matrix.mulVec_mulVec, mul_kernelProjection, Matrix.zero_mulVec]

/-- E every original solution is fixed by the generated kernel coordinates.
The proof uses the original transpose-kernel equality in both directions. -/
theorem kernelProjection_fixes_ker (A : Matrix m n ℚ) (x : n → ℚ)
    (hx : x ∈ LinearMap.ker A.mulVecLin) : kernelProjection A *ᵥ x = x := by
  rw [kernelProjection_mulVec]
  have hp : imageProjection Aᵀ *ᵥ x = 0 :=
    (imageProjection_mulVec_eq_zero_iff Aᵀ x).2
      (by simpa only [Matrix.transpose_transpose] using hx)
  rw [hp, sub_zero]

/-- E exact original kernel as generated coordinate image, with both
inclusions and explicit fixed original solution representatives. -/
theorem kernelProjection_range (A : Matrix m n ℚ) :
    LinearMap.range (kernelProjection A).mulVecLin = LinearMap.ker A.mulVecLin := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact kernelProjection_mulVec_mem_ker A y
  · intro x hx
    exact ⟨x, kernelProjection_fixes_ker A x hx⟩

/-- Owner kernel API: a vector is removed precisely when it lies in the
same original transpose range. This supplies the quotient-coordinate map. -/
theorem kernelProjection_mulVec_eq_zero_iff (A : Matrix m n ℚ) (x : n → ℚ) :
    kernelProjection A *ᵥ x = 0 ↔ x ∈ LinearMap.range Aᵀ.mulVecLin := by
  rw [kernelProjection_mulVec, sub_eq_zero]
  constructor
  · intro h
    rw [h]
    exact imageProjection_mulVec_mem_range Aᵀ x
  · intro h
    exact (imageProjection_fixes_range Aᵀ x h).symm

/-- Owner exact removed-space equality, retaining the original transpose
range rather than quotienting by a self-defined replacement space. -/
theorem kernelProjection_ker (A : Matrix m n ℚ) :
    LinearMap.ker (kernelProjection A).mulVecLin = LinearMap.range Aᵀ.mulVecLin := by
  ext x
  exact kernelProjection_mulVec_eq_zero_iff A x

/-- Owner idempotence API follows from actual kernel representatives. -/
theorem kernelProjection_mul_self (A : Matrix m n ℚ) :
    kernelProjection A * kernelProjection A = kernelProjection A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  exact kernelProjection_fixes_ker A _ (kernelProjection_mulVec_mem_ker A x)

/-- Owner symmetry API for executable kernel coordinates, inherited from
the same original transpose image projection. -/
theorem kernelProjection_transpose (A : Matrix m n ℚ) :
    (kernelProjection A)ᵀ = kernelProjection A := by
  rw [kernelProjection, Matrix.transpose_sub, Matrix.transpose_one,
    imageProjection_transpose]

/-- E computed dimension of the original kernel. The evaluator receives
only the generated matrix, and its rank is the actual original kernel size. -/
theorem kernelProjection_rank (A : Matrix m n ℚ) :
    rationalMatrixRank (kernelProjection A) =
      Module.finrank ℚ (LinearMap.ker A.mulVecLin) := by
  rw [rationalMatrixRank_eq_finrank_range, kernelProjection_range]

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.mul_kernelProjection
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_mulVec_mem_ker
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_fixes_ker
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_mulVec_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_ker
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_transpose
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_rank

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
