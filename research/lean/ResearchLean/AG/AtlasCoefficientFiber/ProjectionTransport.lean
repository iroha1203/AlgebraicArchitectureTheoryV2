import ResearchLean.AG.AtlasCoefficientFiber.RationalQuotientCoordinates

/-!
# Original embedding and quotient coordinates from primitive projectors

Position: G-135 E native degree transport. These general APIs turn an original
injective embedding or surjective restriction into coordinates only after its
original image/kernel has been identified with the primitive table.

## Implementation notes

The original modules and maps are retained, and the first isomorphism theorem
constructs both inverses. Input image/kernel equalities are direction hypotheses
of these general lemmas; each original M application must discharge them from
C4 evaluation/restriction and the actual generated L columns. Supplying a basis
of P/Q or defining them as the projector image would erase that obligation and
was rejected. All coordinate representatives use the C17 executable matrices;
noncomputability is confined to the native linear equivalence transport.
-/

noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates
open Matrix
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra
universe u v w
variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq m]
variable {V : Type w} [AddCommGroup V] [Module ℚ V]

/-- E embedding transport: the original injective map identifies its source
with the generated annihilator image. The image premise is discharged from
actual evaluation in the native application, never a supplied P basis. -/
def embeddingCoordinateEquiv (L : Matrix m n ℚ) (e : V →ₗ[ℚ] (m → ℚ))
    (hi : Function.Injective e) (hr : LinearMap.range e = LinearMap.ker Lᵀ.mulVecLin) :
    V ≃ₗ[ℚ] LinearMap.range (kernelProjection Lᵀ).mulVecLin :=
  LinearEquiv.ofBijective
    (e.codRestrict _ (fun x => by
      rw [kernelProjection_range, ← hr]
      exact ⟨x, rfl⟩))
    ⟨fun _ _ h => hi (congrArg Subtype.val h), by
      intro y
      have hy : y.1 ∈ LinearMap.range e := by
        rw [hr, ← kernelProjection_range]
        exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

/-- Owner representative API: coordinates of every original P vector are
exactly its original embedding value, retaining all original components. -/
theorem embeddingCoordinateEquiv_apply (L : Matrix m n ℚ) (e : V →ₗ[ℚ] (m → ℚ))
    (hi : Function.Injective e) (hr : LinearMap.range e = LinearMap.ker Lᵀ.mulVecLin)
    (x : V) : (embeddingCoordinateEquiv L e hi hr x : m → ℚ) = e x := rfl

/-- Owner inverse API: every generated coordinate is recovered through the
same original embedding. This is the full underlying-vector equality. -/
theorem embeddingCoordinateEquiv_symm_apply (L : Matrix m n ℚ)
    (e : V →ₗ[ℚ] (m → ℚ)) (hi : Function.Injective e)
    (hr : LinearMap.range e = LinearMap.ker Lᵀ.mulVecLin)
    (x : LinearMap.range (kernelProjection Lᵀ).mulVecLin) :
    e ((embeddingCoordinateEquiv L e hi hr).symm x) = x.1 := by
  rw [← embeddingCoordinateEquiv_apply L e hi hr]
  exact congrArg Subtype.val ((embeddingCoordinateEquiv L e hi hr).apply_symm_apply x)

/-- E executable dimension: rank of the generated annihilator projection
is the dimension of the original embedding source. -/
theorem embeddingCoordinateEquiv_rank (L : Matrix m n ℚ)
    (e : V →ₗ[ℚ] (m → ℚ)) (hi : Function.Injective e)
    (hr : LinearMap.range e = LinearMap.ker Lᵀ.mulVecLin) :
    rationalMatrixRank (kernelProjection Lᵀ) = Module.finrank ℚ V := by
  rw [rationalMatrixRank_eq_finrank_range]
  exact (embeddingCoordinateEquiv L e hi hr).symm.finrank_eq

/-- E restriction transport: the original quotient target is identified
with the generated L image using the same original restriction kernel.
Surjectivity/kernel premises are discharged from C4 in native applications. -/
def restrictionCoordinateEquiv (L : Matrix m n ℚ) (r : (m → ℚ) →ₗ[ℚ] V)
    (hs : Function.Surjective r) (hk : LinearMap.ker r = LinearMap.ker Lᵀ.mulVecLin) :
    V ≃ₗ[ℚ] LinearMap.range (imageProjection L).mulVecLin :=
  (r.quotKerEquivOfSurjective hs).symm.trans
    ((Submodule.quotEquivOfEq _ _ (hk.trans (imageProjection_ker L).symm)).trans
      (imageProjection L).mulVecLin.quotKerEquivRange)

omit [DecidableEq m] in
/-- Owner full representative API: every original fine vector, after actual
restriction, has the executable L-image projection as its Q coordinate. -/
theorem restrictionCoordinateEquiv_apply (L : Matrix m n ℚ)
    (r : (m → ℚ) →ₗ[ℚ] V) (hs : Function.Surjective r)
    (hk : LinearMap.ker r = LinearMap.ker Lᵀ.mulVecLin) (x : m → ℚ) :
    (restrictionCoordinateEquiv L r hs hk (r x) : m → ℚ) = imageProjection L *ᵥ x := by
  simp only [restrictionCoordinateEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivRange_apply_mk, Matrix.mulVecLin_apply]

omit [DecidableEq m] in
/-- Owner inverse API: every generated Q coordinate returns its original
restriction value, not a chosen independent quotient class. -/
theorem restrictionCoordinateEquiv_symm_apply (L : Matrix m n ℚ)
    (r : (m → ℚ) →ₗ[ℚ] V) (hs : Function.Surjective r)
    (hk : LinearMap.ker r = LinearMap.ker Lᵀ.mulVecLin)
    (x : LinearMap.range (imageProjection L).mulVecLin) :
    (restrictionCoordinateEquiv L r hs hk).symm x = r x.1 := by
  apply (restrictionCoordinateEquiv L r hs hk).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [restrictionCoordinateEquiv_apply]
  exact (imageProjection_fixes_range L x.1 (by rw [← imageProjection_range]; exact x.2)).symm

omit [DecidableEq m] in
/-- Owner correction API: projecting any fine representative preserves its
same original restriction. This supplies native differential transport. -/
theorem restriction_imageProjection (L : Matrix m n ℚ)
    (r : (m → ℚ) →ₗ[ℚ] V) (hs : Function.Surjective r)
    (hk : LinearMap.ker r = LinearMap.ker Lᵀ.mulVecLin) (x : m → ℚ) :
    r (imageProjection L *ᵥ x) = r x := by
  have h := restrictionCoordinateEquiv_symm_apply L r hs hk
    (restrictionCoordinateEquiv L r hs hk (r x))
  rw [LinearEquiv.symm_apply_apply, restrictionCoordinateEquiv_apply] at h
  exact h.symm

omit [DecidableEq m] in
/-- E executable dimension: rank of the primitive image projection equals
the dimension of the original Q target, with no expected rank premise. -/
theorem restrictionCoordinateEquiv_rank (L : Matrix m n ℚ)
    (r : (m → ℚ) →ₗ[ℚ] V) (hs : Function.Surjective r)
    (hk : LinearMap.ker r = LinearMap.ker Lᵀ.mulVecLin) :
    rationalMatrixRank (imageProjection L) = Module.finrank ℚ V := by
  rw [rationalMatrixRank_eq_finrank_range]
  exact (restrictionCoordinateEquiv L r hs hk).symm.finrank_eq

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.embeddingCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.embeddingCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.embeddingCoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.embeddingCoordinateEquiv_rank
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.restrictionCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.restrictionCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.restrictionCoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.restriction_imageProjection
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.restrictionCoordinateEquiv_rank

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
