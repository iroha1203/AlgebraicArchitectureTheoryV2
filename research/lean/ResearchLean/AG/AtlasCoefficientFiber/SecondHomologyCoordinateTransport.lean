import ResearchLean.AG.AtlasCoefficientFiber.HomologyCoordinateTransport

/-!
# Original top-degree homology in generated coordinates

Position: G-135 E original H2 quotient. The output retains the original degree
projection and removes exactly the incoming original differential image.

## Implementation notes

The source is the literal original module modulo its original incoming range.
No shifted replacement complex or supplied basis is used. General embedding,
range and projector conditions are direction hypotheses to be discharged at
each native P/Q application. The data producer is finite rational arithmetic;
only the original quotient transport is noncomputable.
-/
namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates
open Matrix
universe u v w t
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- Executable top-degree coordinates retain the original degree projector. -/
def secondHomologyProjection (p : Matrix J J ℚ) (d : Matrix J I ℚ) : Matrix J J ℚ :=
  p - imageProjection d

/-- Owner direct producer formula separates the retained degree projection
from the computed original incoming image. -/
theorem secondHomologyProjection_sub (p : Matrix J J ℚ) (d : Matrix J I ℚ) :
    secondHomologyProjection p d = p - imageProjection d := rfl

/-- Owner connection to harmonic correction with genuinely zero outgoing map. -/
theorem secondHomologyProjection_eq (p : Matrix J J ℚ) (d : Matrix J I ℚ) :
    secondHomologyProjection p d = harmonicProjection p d (0 : Matrix (Fin 0) J ℚ) := by
  apply Matrix.mulVec_injective
  funext x
  simp only [secondHomologyProjection, Matrix.sub_mulVec, harmonicProjection_mulVec,
    Matrix.transpose_zero, imageProjection_zero, Matrix.zero_mulVec, sub_zero]

/-- Generated top representatives stay in the original degree image. -/
theorem secondHomologyProjection_degree (p : Matrix J J ℚ) (d : Matrix J I ℚ)
    (hps : pᵀ = p) (hpi : p * p = p) (hpd : p * d = d) :
    p * secondHomologyProjection p d = secondHomologyProjection p d := by
  rw [secondHomologyProjection_eq]
  exact harmonicProjection_degree p d (0 : Matrix (Fin 0) J ℚ) hps hpi hpd
    (by rw [Matrix.zero_mul])

/-- Every generated top representative is recovered by the same producer. -/
theorem secondHomologyProjection_mul_self (p : Matrix J J ℚ) (d : Matrix J I ℚ)
    (hps : pᵀ = p) (hpi : p * p = p) (hpd : p * d = d) :
    secondHomologyProjection p d * secondHomologyProjection p d = secondHomologyProjection p d := by
  rw [secondHomologyProjection_eq]
  exact harmonicProjection_mul_self p d (0 : Matrix (Fin 0) J ℚ) hps hpi hpd
    (by rw [Matrix.zero_mul]) (by rw [Matrix.zero_mul])

/-- Generated top projection is symmetric by the same original correction. -/
theorem secondHomologyProjection_transpose (p : Matrix J J ℚ) (d : Matrix J I ℚ)
    (hps : pᵀ = p) : (secondHomologyProjection p d)ᵀ = secondHomologyProjection p d := by
  rw [secondHomologyProjection_eq]
  exact harmonicProjection_transpose p d (0 : Matrix (Fin 0) J ℚ) hps

noncomputable section
variable {V : Type w} {W : Type t} [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]
variable (f : W →ₗ[ℚ] V) (e : V →ₗ[ℚ] (J → ℚ))
variable (p : Matrix J J ℚ) (d : Matrix J I ℚ)

/-- The original degree module maps through the same generated top correction. -/
def secondHarmonicMap : V →ₗ[ℚ] (J → ℚ) :=
  (secondHomologyProjection p d).mulVecLin.comp e

/-- Owner formula holds for every original top-degree representative. -/
theorem secondHarmonicMap_apply (x : V) :
    secondHarmonicMap e p d x = secondHomologyProjection p d *ᵥ e x := rfl

/-- Removed representatives are exactly the original incoming range. -/
theorem secondHarmonicMap_ker (hi : Function.Injective e) (hpi : p * p = p)
    (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
    (hd : LinearMap.range d.mulVecLin = (LinearMap.range f).map e) :
    LinearMap.ker (secondHarmonicMap e p d) = LinearMap.range f := by
  ext x
  change secondHarmonicMap e p d x = 0 ↔ x ∈ LinearMap.range f
  have hp : p *ᵥ e x = e x :=
    degreeProjection_fixes_range p hpi _ (by rw [← hr]; exact ⟨x, rfl⟩)
  rw [secondHarmonicMap_apply, secondHomologyProjection_eq,
    harmonicProjection_closed_eq_zero_iff p d (0 : Matrix (Fin 0) J ℚ) _ hp
      (by rw [Matrix.zero_mulVec]), hd]
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, hz⟩
    exact ⟨z, hi hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨f z, ⟨z, rfl⟩, rfl⟩

/-- The original top module covers the entire generated harmonic image. -/
theorem secondHarmonicMap_range (hps : pᵀ = p) (hpi : p * p = p)
    (hpd : p * d = d) (hr : LinearMap.range e = LinearMap.range p.mulVecLin) :
    LinearMap.range (secondHarmonicMap e p d) =
      LinearMap.range (secondHomologyProjection p d).mulVecLin := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    exact ⟨e z, rfl⟩
  · rintro x ⟨y, rfl⟩
    have hp : p *ᵥ (secondHomologyProjection p d *ᵥ y) = secondHomologyProjection p d *ᵥ y := by
      rw [secondHomologyProjection_eq, Matrix.mulVec_mulVec,
        harmonicProjection_degree p d (0 : Matrix (Fin 0) J ℚ) hps hpi hpd
          (by rw [Matrix.zero_mul])]
    have he : secondHomologyProjection p d *ᵥ y ∈ LinearMap.range e := by
      rw [hr]
      exact ⟨secondHomologyProjection p d *ᵥ y, hp⟩
    obtain ⟨z, hz⟩ := he
    refine ⟨z, ?_⟩
    rw [secondHarmonicMap_apply, hz, Matrix.mulVec_mulVec, secondHomologyProjection_eq,
      harmonicProjection_mul_self p d (0 : Matrix (Fin 0) J ℚ) hps hpi hpd
        (by rw [Matrix.zero_mul]) (by rw [Matrix.zero_mul])]
    rfl

/-- Both-direction coordinates for the original top-degree quotient. -/
def secondHomologyCoordinateEquiv (hi : Function.Injective e)
    (hps : pᵀ = p) (hpi : p * p = p) (hpd : p * d = d)
    (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
    (hd : LinearMap.range d.mulVecLin = (LinearMap.range f).map e) :
    (V ⧸ LinearMap.range f) ≃ₗ[ℚ] LinearMap.range (secondHomologyProjection p d).mulVecLin :=
  (Submodule.quotEquivOfEq _ _ (secondHarmonicMap_ker f e p d hi hpi hr hd).symm).trans
    ((secondHarmonicMap e p d).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (secondHarmonicMap_range e p d hps hpi hpd hr)))

/-- Owner coordinates of every original top-degree quotient representative. -/
theorem secondHomologyCoordinateEquiv_mk (hi : Function.Injective e)
    (hps : pᵀ = p) (hpi : p * p = p) (hpd : p * d = d)
    (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
    (hd : LinearMap.range d.mulVecLin = (LinearMap.range f).map e) (x : V) :
    (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd (Submodule.Quotient.mk x) : J → ℚ) =
      secondHomologyProjection p d *ᵥ e x := by
  simp only [secondHomologyCoordinateEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivRange_apply_mk,
    LinearEquiv.coe_ofEq_apply, secondHarmonicMap_apply]

section EquivalenceAPI
variable (hi : Function.Injective e) (hps : pᵀ = p) (hpi : p * p = p) (hpd : p * d = d)
variable (hr : LinearMap.range e = LinearMap.range p.mulVecLin)
variable (hd : LinearMap.range d.mulVecLin = (LinearMap.range f).map e)

/-- Every original top quotient class is recovered by the inverse. -/
theorem secondHomologyCoordinateEquiv_left_inverse (x : V ⧸ LinearMap.range f) :
    (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd).symm
      (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd x) = x :=
  (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd).symm_apply_apply x

/-- Every generated top coordinate is recovered by the forward map. -/
theorem secondHomologyCoordinateEquiv_right_inverse
    (x : LinearMap.range (secondHomologyProjection p d).mulVecLin) :
    secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd
      ((secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd).symm x) = x :=
  (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd).apply_symm_apply x

/-- The inverse is the literal original quotient class of a representative
with the same generated coordinate. -/
theorem secondHomologyCoordinateEquiv_symm_representative
    (x : LinearMap.range (secondHomologyProjection p d).mulVecLin) (z : V) (hz : e z = x.1) :
    (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd).symm x = Submodule.Quotient.mk z := by
  apply (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [secondHomologyCoordinateEquiv_mk, hz]
  obtain ⟨y, hy⟩ := x.2
  change secondHomologyProjection p d *ᵥ y = x.1 at hy
  rw [← hy, Matrix.mulVec_mulVec, secondHomologyProjection_mul_self p d hps hpi hpd]

include f e hi hps hpi hpd hr hd in
/-- Computed top projector rank equals the original incoming-range quotient dimension. -/
theorem secondHomologyCoordinateEquiv_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank
      (secondHomologyProjection p d) = Module.finrank ℚ (V ⧸ LinearMap.range f) := by
  rw [AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_finrank_range]
  exact (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd).symm.finrank_eq

/-- Every generated top coordinate has an original representative with that
same embedding, and its inverse is the literal original quotient class. -/
theorem secondHomologyCoordinateEquiv_inverse_representative
    (x : LinearMap.range (secondHomologyProjection p d).mulVecLin) :
    ∃ z : V, e z = x.1 ∧
      (secondHomologyCoordinateEquiv f e p d hi hps hpi hpd hr hd).symm x = Submodule.Quotient.mk z := by
  obtain ⟨y, hy⟩ := x.2
  change secondHomologyProjection p d *ᵥ y = x.1 at hy
  have hp : p *ᵥ x.1 = x.1 := by
    rw [← hy, Matrix.mulVec_mulVec, secondHomologyProjection_degree p d hps hpi hpd]
  have he : x.1 ∈ LinearMap.range e := by
    rw [hr]
    exact ⟨x.1, hp⟩
  obtain ⟨z, hz⟩ := he
  exact ⟨z, hz, secondHomologyCoordinateEquiv_symm_representative f e p d hi hps hpi hpd hr hd x z hz⟩

end EquivalenceAPI
end

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyProjection
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyProjection_sub
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyProjection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyProjection_degree
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyProjection_transpose
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHarmonicMap
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHarmonicMap_apply
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHarmonicMap_ker
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHarmonicMap_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyCoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyCoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyCoordinateEquiv_symm_representative
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyCoordinateEquiv_rank
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.secondHomologyCoordinateEquiv_inverse_representative

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
