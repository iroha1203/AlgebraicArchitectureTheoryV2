import ResearchLean.AG.AtlasCoefficientFiber.RationalHarmonicCoordinates
import ResearchLean.AG.TwoPhase.CohomologyComparison

/-!
# Original homology quotients in generated harmonic coordinates

Position: G-135 E native quotient transport. An original three-term complex
and its original degree embedding remain fixed throughout the construction.

## Implementation notes

The kernel and range of the harmonic map on original cycles are proved before
the first isomorphism theorem constructs the equivalence. All general image,
cycle and boundary representation conditions are direction hypotheses; native
applications must discharge them from original coordinate constructions.
Defining homology as a new projector image or supplying a semantic basis was
rejected because it would erase the original quotient obligation.
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates
open Matrix AAT.AG.TwoPhase
universe u v w
variable {I : Type u} {J : Type v} {K : Type w}
variable [Fintype I] [Fintype J] [Fintype K]

/-- Owner fixed-vector API for the full image of an idempotent degree map. -/
theorem degreeProjection_fixes_range (p : Matrix J J ℚ) (hpi : p * p = p)
    (x : J → ℚ) (hx : x ∈ LinearMap.range p.mulVecLin) : p *ᵥ x = x := by
  obtain ⟨y, hy⟩ := hx
  change p *ᵥ y = x at hy
  rw [← hy, Matrix.mulVec_mulVec, hpi]

variable (C : ThreeCochainComplex.{0,v} ℚ)
variable (e : C.C1 →ₗ[ℚ] (J → ℚ))
variable (p : Matrix J J ℚ) (d0 : Matrix J I ℚ) (d1 : Matrix K J ℚ)

/-- The generated harmonic map reads the original complex's literal cycles. -/
def cycleHarmonicMap : LinearMap.ker C.d1 →ₗ[ℚ] (J → ℚ) :=
  (harmonicProjection p d0 d1).mulVecLin.comp (e.comp (LinearMap.ker C.d1).subtype)

/-- Owner representative formula for every original cycle. -/
theorem cycleHarmonicMap_apply (x : LinearMap.ker C.d1) :
    cycleHarmonicMap C e p d0 d1 x = harmonicProjection p d0 d1 *ᵥ e x.1 := rfl

/-- Original degree-image equality makes every original cochain fixed by p. -/
theorem degreeEmbedding_fixed (hpi : p * p = p)
    (hr : LinearMap.range e = LinearMap.range p.mulVecLin) (x : C.C1) :
    p *ᵥ e x = e x :=
  degreeProjection_fixes_range p hpi (e x) (by rw [← hr]; exact ⟨x, rfl⟩)

/-- The restricted harmonic map removes exactly the original boundary
subspace of the original cycles, not a self-defined quotient relation. -/
theorem cycleHarmonicMap_ker (hi : Function.Injective e) (hpi : p * p = p)
    (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
    (h0 : LinearMap.range d0.mulVecLin = (LinearMap.range C.d0).map e)
    (h1 : ∀ x, d1 *ᵥ e x = 0 ↔ C.d1 x = 0) :
    LinearMap.ker (cycleHarmonicMap C e p d0 d1) = LinearMap.range C.boundaryToCycles := by
  ext z
  change cycleHarmonicMap C e p d0 d1 z = 0 ↔ z ∈ LinearMap.range C.boundaryToCycles
  rw [cycleHarmonicMap_apply,
    harmonicProjection_closed_eq_zero_iff p d0 d1 _
      (degreeEmbedding_fixed C e p hpi hr z.1) ((h1 z.1).2 z.2), h0]
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [ThreeCochainComplex.boundaryToCycles_apply]
    exact hi hx
  · rintro ⟨x, hx⟩
    refine ⟨C.d0 x, ⟨x, rfl⟩, ?_⟩
    have hv := congrArg Subtype.val hx
    rw [ThreeCochainComplex.boundaryToCycles_apply] at hv
    rw [hv]

/-- The original cycles map onto every generated harmonic vector. This uses
original degree-image surjectivity and original outgoing-cycle equivalence. -/
theorem cycleHarmonicMap_range (hps : pᵀ = p) (hpi : p * p = p)
    (hp0 : p * d0 = d0) (hp1 : d1 * p = d1) (h10 : d1 * d0 = 0)
    (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
    (h1 : ∀ x, d1 *ᵥ e x = 0 ↔ C.d1 x = 0) :
    LinearMap.range (cycleHarmonicMap C e p d0 d1) =
      LinearMap.range (harmonicProjection p d0 d1).mulVecLin := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    exact ⟨e z.1, cycleHarmonicMap_apply C e p d0 d1 z⟩
  · rintro x ⟨y, rfl⟩
    have hp : p *ᵥ (harmonicProjection p d0 d1 *ᵥ y) = harmonicProjection p d0 d1 *ᵥ y := by
      rw [Matrix.mulVec_mulVec, harmonicProjection_degree p d0 d1 hps hpi hp0 hp1]
    have he : harmonicProjection p d0 d1 *ᵥ y ∈ LinearMap.range e := by
      rw [hr]
      exact ⟨harmonicProjection p d0 d1 *ᵥ y, hp⟩
    obtain ⟨z, hz⟩ := he
    have hc : C.d1 z = 0 := (h1 z).1 (by
      rw [hz, Matrix.mulVec_mulVec, harmonicProjection_cycle p d0 d1 hp1 h10,
        Matrix.zero_mulVec])
    refine ⟨⟨z, hc⟩, ?_⟩
    rw [cycleHarmonicMap_apply, hz, Matrix.mulVec_mulVec,
      harmonicProjection_mul_self p d0 d1 hps hpi hp0 hp1 h10]
    rfl

/-- Both-direction equivalence from the original H1 quotient to generated
coordinates. Every compatibility premise must be generated in native uses. -/
def homologyCoordinateEquiv (hi : Function.Injective e)
    (hps : pᵀ = p) (hpi : p * p = p)
    (hp0 : p * d0 = d0) (hp1 : d1 * p = d1) (h10 : d1 * d0 = 0)
    (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
    (h0 : LinearMap.range d0.mulVecLin = (LinearMap.range C.d0).map e)
    (h1 : ∀ x, d1 *ᵥ e x = 0 ↔ C.d1 x = 0) :
    C.H1 ≃ₗ[ℚ] LinearMap.range (harmonicProjection p d0 d1).mulVecLin :=
  (Submodule.quotEquivOfEq _ _ (cycleHarmonicMap_ker C e p d0 d1 hi hpi hr h0 h1).symm).trans
    ((cycleHarmonicMap C e p d0 d1).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (cycleHarmonicMap_range C e p d0 d1 hps hpi hp0 hp1 h10 hr h1)))

/-- Owner all-representative formula preserves the original quotient class. -/
theorem homologyCoordinateEquiv_mk (hi : Function.Injective e)
    (hps : pᵀ = p) (hpi : p * p = p)
    (hp0 : p * d0 = d0) (hp1 : d1 * p = d1) (h10 : d1 * d0 = 0)
    (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
    (h0 : LinearMap.range d0.mulVecLin = (LinearMap.range C.d0).map e)
    (h1 : ∀ x, d1 *ᵥ e x = 0 ↔ C.d1 x = 0) (z : LinearMap.ker C.d1) :
    (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1
      (Submodule.Quotient.mk z) : J → ℚ) = harmonicProjection p d0 d1 *ᵥ e z.1 := by
  simp only [homologyCoordinateEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk,
    LinearEquiv.coe_ofEq_apply, cycleHarmonicMap_apply]

section EquivalenceAPI
variable (hi : Function.Injective e) (hps : pᵀ = p) (hpi : p * p = p)
variable (hp0 : p * d0 = d0) (hp1 : d1 * p = d1) (h10 : d1 * d0 = 0)
variable (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
variable (h0 : LinearMap.range d0.mulVecLin = (LinearMap.range C.d0).map e)
variable (h1 : ∀ x, d1 *ᵥ e x = 0 ↔ C.d1 x = 0)

/-- Every original quotient class is recovered in the inverse direction. -/
theorem homologyCoordinateEquiv_left_inverse (x : C.H1) :
    (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1).symm
      (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1 x) = x :=
  (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1).symm_apply_apply x

/-- Every generated harmonic coordinate is recovered, including rank-zero cases. -/
theorem homologyCoordinateEquiv_right_inverse
    (x : LinearMap.range (harmonicProjection p d0 d1).mulVecLin) :
    homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1
      ((homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1).symm x) = x :=
  (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1).apply_symm_apply x

/-- The inverse coordinate is the class of any original cycle with that
same harmonic embedding, not a supplied independent quotient. -/
theorem homologyCoordinateEquiv_symm_representative
    (x : LinearMap.range (harmonicProjection p d0 d1).mulVecLin)
    (z : LinearMap.ker C.d1) (hz : e z.1 = x.1) :
    (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1).symm x =
      Submodule.Quotient.mk z := by
  apply (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [homologyCoordinateEquiv_mk, hz]
  obtain ⟨y, hy⟩ := x.2
  change harmonicProjection p d0 d1 *ᵥ y = x.1 at hy
  rw [← hy, Matrix.mulVec_mulVec,
    harmonicProjection_mul_self p d0 d1 hps hpi hp0 hp1 h10]

include e hi hps hpi hp0 hp1 h10 hr h0 h1 in
/-- Computed harmonic rank equals the dimension of the original H1 quotient. -/
theorem homologyCoordinateEquiv_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank
      (harmonicProjection p d0 d1) = Module.finrank ℚ C.H1 := by
  rw [AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_finrank_range]
  exact (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1).symm.finrank_eq

/-- Every inverse coordinate has an original closed representative with
exactly that embedding; the representative is generated from original range
surjectivity rather than supplied as a basis or a separate quotient. -/
theorem homologyCoordinateEquiv_inverse_cycle
    (x : LinearMap.range (harmonicProjection p d0 d1).mulVecLin) :
    ∃ z : LinearMap.ker C.d1, e z.1 = x.1 ∧
      (homologyCoordinateEquiv C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1).symm x =
        Submodule.Quotient.mk z := by
  obtain ⟨y, hy⟩ := x.2
  change harmonicProjection p d0 d1 *ᵥ y = x.1 at hy
  have hp : p *ᵥ x.1 = x.1 := by
    rw [← hy, Matrix.mulVec_mulVec, harmonicProjection_degree p d0 d1 hps hpi hp0 hp1]
  have he : x.1 ∈ LinearMap.range e := by
    rw [hr]
    exact ⟨x.1, hp⟩
  obtain ⟨z, hz⟩ := he
  have hc : C.d1 z = 0 := (h1 z).1 (by
    rw [hz, ← hy, Matrix.mulVec_mulVec, harmonicProjection_cycle p d0 d1 hp1 h10,
      Matrix.zero_mulVec])
  refine ⟨⟨z, hc⟩, hz, ?_⟩
  exact homologyCoordinateEquiv_symm_representative C e p d0 d1 hi hps hpi hp0 hp1 h10 hr h0 h1 x ⟨z, hc⟩ hz

end EquivalenceAPI

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.degreeProjection_fixes_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.cycleHarmonicMap
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.cycleHarmonicMap_apply
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.degreeEmbedding_fixed
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.cycleHarmonicMap_ker
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.cycleHarmonicMap_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyCoordinateEquiv_mk

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyCoordinateEquiv_left_inverse

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyCoordinateEquiv_right_inverse

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyCoordinateEquiv_symm_representative

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyCoordinateEquiv_rank

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyCoordinateEquiv_inverse_cycle

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
