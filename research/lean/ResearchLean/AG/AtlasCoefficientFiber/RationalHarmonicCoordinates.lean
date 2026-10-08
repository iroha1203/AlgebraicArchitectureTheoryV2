import ResearchLean.AG.AtlasCoefficientFiber.RationalQuotientCoordinates

/-!
# Executable harmonic coordinates in an original degree subspace

Position: G-135 E. The original degree projector is retained when removing
incoming boundaries and outgoing transpose images, so unused ambient
coordinates never become native homology classes.

## Implementation notes

Definitions use finite rational entries and the same C17 producer. General
correctness conditions are explicit direction hypotheses, to be discharged
from original native differentials in every M application. Supplying homology
bases or replacing the degree projector by identity was rejected because it
would lose the original quotient and its unused-coordinate correction.
-/
namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates
open Matrix
universe u v w
variable {I : Type u} {J : Type v} {K : Type w}
variable [Fintype I] [Fintype J] [Fintype K]

/-- A map fixing all original columns fixes their generated image projector. -/
theorem mul_imageProjection_of_mul_eq (p : Matrix J J ℚ) (A : Matrix J I ℚ)
    (hp : p * A = A) : p * imageProjection A = imageProjection A := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨y, hy⟩ := imageProjection_mulVec_mem_range A x
  change A *ᵥ y = imageProjection A *ᵥ x at hy
  rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec, hp]

omit [Fintype K] in
/-- A map annihilating original columns annihilates their full generated image. -/
theorem mul_imageProjection_of_mul_zero (D : Matrix K J ℚ) (A : Matrix J I ℚ)
    (h : D * A = 0) : D * imageProjection A = 0 := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨y, hy⟩ := imageProjection_mulVec_mem_range A x
  change A *ᵥ y = imageProjection A *ᵥ x at hy
  rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec, h,
    Matrix.zero_mulVec, Matrix.zero_mulVec]

/-- Executable harmonic producer retains the same original degree image. -/
def harmonicProjection (p : Matrix J J ℚ) (d0 : Matrix J I ℚ)
    (d1 : Matrix K J ℚ) : Matrix J J ℚ :=
  p - imageProjection d1ᵀ - imageProjection d0

/-- Owner evaluation exposes all three generated corrections. -/
theorem harmonicProjection_mulVec (p : Matrix J J ℚ) (d0 : Matrix J I ℚ)
    (d1 : Matrix K J ℚ) (x : J → ℚ) :
    harmonicProjection p d0 d1 *ᵥ x =
      p *ᵥ x - imageProjection d1ᵀ *ᵥ x - imageProjection d0 *ᵥ x := by
  rw [harmonicProjection, Matrix.sub_mulVec, Matrix.sub_mulVec]

/-- Owner zero-table API includes empty or zero outgoing maps. -/
theorem imageProjection_zero : imageProjection (0 : Matrix K J ℚ) = 0 := by
  apply Matrix.mulVec_injective
  funext x
  rw [Matrix.zero_mulVec]
  exact (imageProjection_mulVec_eq_zero_iff (0 : Matrix K J ℚ) x).2
    (by rw [Matrix.transpose_zero, Matrix.zero_mulVec])

section Correctness
variable (p : Matrix J J ℚ) (d0 : Matrix J I ℚ) (d1 : Matrix K J ℚ)

/-- The outgoing transpose image remains inside the original degree image. -/
theorem harmonic_outgoing_absorption (hps : pᵀ = p) (h1 : d1 * p = d1) : p * imageProjection d1ᵀ = imageProjection d1ᵀ := by
  apply mul_imageProjection_of_mul_eq
  simpa only [Matrix.transpose_mul, hps] using congrArg Matrix.transpose h1

/-- All generated outputs belong to the same original degree image. -/
theorem harmonicProjection_degree (hps : pᵀ = p) (hpi : p * p = p) (h0 : p * d0 = d0) (h1 : d1 * p = d1) : p * harmonicProjection p d0 d1 = harmonicProjection p d0 d1 := by
  rw [harmonicProjection, Matrix.mul_sub, Matrix.mul_sub, hpi,
    harmonic_outgoing_absorption p d1 hps h1, mul_imageProjection_of_mul_eq p d0 h0]

/-- Original square-zero makes the two generated image corrections orthogonal. -/
theorem harmonic_corrections_mul_zero (h10 : d1 * d0 = 0) : imageProjection d1ᵀ * imageProjection d0 = 0 := by
  apply mul_imageProjection_of_mul_zero
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  apply (imageProjection_mulVec_eq_zero_iff d1ᵀ _).2
  rw [Matrix.transpose_transpose, Matrix.mulVec_mulVec, h10, Matrix.zero_mulVec]

/-- The original outgoing differential annihilates all generated outputs. -/
theorem harmonicProjection_cycle (h1 : d1 * p = d1) (h10 : d1 * d0 = 0) : d1 * harmonicProjection p d0 d1 = 0 := by
  have hu : d1 * imageProjection d1ᵀ = d1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      imageProjection_transpose] using congrArg Matrix.transpose (imageProjection_mul d1ᵀ)
  rw [harmonicProjection, Matrix.mul_sub, Matrix.mul_sub, h1, hu,
    mul_imageProjection_of_mul_zero d1 d0 h10, sub_self, sub_self]

/-- Incoming transpose annihilates every generated representative. -/
theorem harmonicProjection_boundary_free (hps : pᵀ = p) (h0 : p * d0 = d0) (h10 : d1 * d0 = 0) : d0ᵀ * harmonicProjection p d0 d1 = 0 := by
  have hp : d0ᵀ * p = d0ᵀ := by
    simpa only [Matrix.transpose_mul, hps] using congrArg Matrix.transpose h0
  have hz : d0ᵀ * imageProjection d1ᵀ = 0 := by
    apply mul_imageProjection_of_mul_zero
    simpa only [Matrix.transpose_mul, Matrix.transpose_zero] using congrArg Matrix.transpose h10
  have hb : d0ᵀ * imageProjection d0 = d0ᵀ := by
    simpa only [Matrix.transpose_mul, imageProjection_transpose] using
      congrArg Matrix.transpose (imageProjection_mul d0)
  rw [harmonicProjection, Matrix.mul_sub, Matrix.mul_sub, hp, hz, hb,
    sub_zero, sub_self]

/-- A closed original degree representative receives only a boundary correction. -/
theorem harmonicProjection_closed (x : J → ℚ) (hp : p *ᵥ x = x)
    (hc : d1 *ᵥ x = 0) :
    harmonicProjection p d0 d1 *ᵥ x = x - imageProjection d0 *ᵥ x := by
  rw [harmonicProjection_mulVec, hp]
  have hu : imageProjection d1ᵀ *ᵥ x = 0 :=
    (imageProjection_mulVec_eq_zero_iff d1ᵀ x).2 (by rw [Matrix.transpose_transpose]; exact hc)
  rw [hu, sub_zero]

/-- On original closed representatives the removed space is exactly the
original boundary image, in both directions. -/
theorem harmonicProjection_closed_eq_zero_iff (x : J → ℚ)
    (hp : p *ᵥ x = x) (hc : d1 *ᵥ x = 0) :
    harmonicProjection p d0 d1 *ᵥ x = 0 ↔ x ∈ LinearMap.range d0.mulVecLin := by
  rw [harmonicProjection_closed p d0 d1 x hp hc, sub_eq_zero]
  constructor
  · intro h
    rw [h]
    exact imageProjection_mulVec_mem_range d0 x
  · intro h
    exact (imageProjection_fixes_range d0 x h).symm

/-- Every generated harmonic representative is fixed by the same producer. -/
theorem harmonicProjection_mul_self (hps : pᵀ = p) (hpi : p * p = p) (h0 : p * d0 = d0) (h1 : d1 * p = d1) (h10 : d1 * d0 = 0) :
    harmonicProjection p d0 d1 * harmonicProjection p d0 d1 = harmonicProjection p d0 d1 := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  have hp : p *ᵥ (harmonicProjection p d0 d1 *ᵥ x) = harmonicProjection p d0 d1 *ᵥ x := by
    rw [Matrix.mulVec_mulVec, harmonicProjection_degree p d0 d1 hps hpi h0 h1]
  have hc : d1 *ᵥ (harmonicProjection p d0 d1 *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, harmonicProjection_cycle p d0 d1 h1 h10, Matrix.zero_mulVec]
  rw [harmonicProjection_closed p d0 d1 _ hp hc]
  have hb : imageProjection d0 *ᵥ (harmonicProjection p d0 d1 *ᵥ x) = 0 :=
    (imageProjection_mulVec_eq_zero_iff d0 _).2 (by
      rw [Matrix.mulVec_mulVec, harmonicProjection_boundary_free p d0 d1 hps h0 h10,
        Matrix.zero_mulVec])
  rw [hb, sub_zero]

/-- The generated harmonic projector is symmetric. -/
theorem harmonicProjection_transpose (hps : pᵀ = p) : (harmonicProjection p d0 d1)ᵀ = harmonicProjection p d0 d1 := by
  rw [harmonicProjection, Matrix.transpose_sub, Matrix.transpose_sub,
    hps, imageProjection_transpose, imageProjection_transpose]

end Correctness
/-- Equal original column images generate the same orthogonal projector.
This supports verified primitive column reductions without semantic bases. -/
theorem imageProjection_eq_of_range_eq (A : Matrix J I ℚ) (B : Matrix J K ℚ)
    (h : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin) :
    imageProjection A = imageProjection B := by
  have hAB : imageProjection A * imageProjection B = imageProjection B := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec]
    apply imageProjection_fixes_range
    rw [h]
    exact imageProjection_mulVec_mem_range B x
  have hBA : imageProjection B * imageProjection A = imageProjection A := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec]
    apply imageProjection_fixes_range
    rw [← h]
    exact imageProjection_mulVec_mem_range A x
  have ht := congrArg Matrix.transpose hAB
  simp only [Matrix.transpose_mul, imageProjection_transpose] at ht
  exact hBA.symm.trans ht

/-- Owner-API consequence displays the same generated complement matrix
without downstream unfolding of the original kernel producer. -/
theorem kernelProjection_eq_complement [DecidableEq J] (A : Matrix I J ℚ) :
    kernelProjection A = 1 - imageProjection Aᵀ := by
  apply Matrix.mulVec_injective
  funext x
  rw [kernelProjection_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.mul_imageProjection_of_mul_eq
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.mul_imageProjection_of_mul_zero
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_zero
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonic_outgoing_absorption
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection_degree
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonic_corrections_mul_zero
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection_cycle
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection_boundary_free
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection_closed
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection_closed_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.harmonicProjection_transpose

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.imageProjection_eq_of_range_eq
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.kernelProjection_eq_complement

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
