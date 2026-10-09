import ResearchLean.AG.AtlasCoefficientFiber.HomologyCoordinateTransport
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation

/-!
# Computed ranks on original homology coordinate images

Position: G-135 E diagnostic support. The raw ambient matrix is restricted to
the complete generated source image. Its rank is the original actual map rank;
source and target dimensions are projection ranks, not ambient cell counts.

## Implementation notes

The direction hypotheses are whole-value representation and source absorption.
Native applications discharge them from their original maps and generated
projections. Counting the ambient complement as a native kernel was rejected.
Submodule.equivMapOfInjective transports the original range and both directions
of the range equality are proved without a supplied rank certificate.
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.RationalCoordinates
open Matrix AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra
universe u v w x
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
variable {V : Type w} {W : Type x} [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]
variable (p : Matrix I I ℚ) (q : Matrix J J ℚ) (B : Matrix J I ℚ)
variable (f : V →ₗ[ℚ] W)
variable (eS : V ≃ₗ[ℚ] LinearMap.range p.mulVecLin)
variable (eT : W ≃ₗ[ℚ] LinearMap.range q.mulVecLin)
variable (hBP : B * p = B)
variable (hrep : ∀ x, (eT (f x) : J → ℚ) = B *ᵥ (eS x : I → ℚ))

include eS hBP hrep in
/-- All ambient columns land in exactly the embedded original map range,
because the generated source projection removes every unused component. -/
theorem coordinateMatrix_range : LinearMap.range B.mulVecLin =
    (LinearMap.range f).map
      ((LinearMap.range q.mulVecLin).subtype.comp eT.toLinearMap) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := eS.surjective ⟨p *ᵥ y, ⟨y, rfl⟩⟩
    have hzy : (eS z : I → ℚ) = p *ᵥ y := congrArg Subtype.val hz
    refine ⟨f z, ⟨z, rfl⟩, ?_⟩
    change (eT (f z) : J → ℚ) = B *ᵥ y
    rw [hrep, hzy, Matrix.mulVec_mulVec, hBP]
  · rintro _ ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨(eS z : I → ℚ), (hrep z).symm⟩

include eS hBP hrep in
/-- E computed entry rank equals the dimension of the original map range. -/
theorem coordinateMatrix_rank : rationalMatrixRank B = Module.finrank ℚ (LinearMap.range f) := by
  rw [rationalMatrixRank_eq_finrank_range, coordinateMatrix_range p q B f eS eT hBP hrep]
  let g := (LinearMap.range q.mulVecLin).subtype.comp eT.toLinearMap
  have hg : Function.Injective g := by
    intro x y hxy
    apply eT.injective
    exact Subtype.ext hxy
  exact (Submodule.equivMapOfInjective g hg (LinearMap.range f)).symm.finrank_eq

include eS eT in
/-- The generated source and target projection ranks are the exact original dimensions. -/
theorem coordinateProjection_dimensions :
    rationalMatrixRank p = Module.finrank ℚ V ∧ rationalMatrixRank q = Module.finrank ℚ W := by
  simp only [rationalMatrixRank_eq_finrank_range]
  exact ⟨eS.symm.finrank_eq, eT.symm.finrank_eq⟩

include eS eT hBP hrep in
/-- E the actual kernel/cokernel pair is computed by projection rank minus
map rank in both coordinates. Finite dimensionality is the original map's. -/
theorem coordinateMatrix_blockDefect [FiniteDimensional ℚ V] [FiniteDimensional ℚ W] :
    AAT.AG.ResolutionInvariance.blockDefect f =
      (rationalMatrixRank p - rationalMatrixRank B,
       rationalMatrixRank q - rationalMatrixRank B) := by
  rw [AAT.AG.ResolutionInvariance.blockDefect_eq_finrank_sub_range,
    coordinateMatrix_rank p q B f eS eT hBP hrep]
  rw [(coordinateProjection_dimensions p q eS eT).1,
    (coordinateProjection_dimensions p q eS eT).2]

/-- Original actual map transported by the two complete coordinate isomorphisms. -/
def homologyImageMap : LinearMap.range p.mulVecLin →ₗ[ℚ] LinearMap.range q.mulVecLin :=
  eT.toLinearMap.comp (f.comp eS.symm.toLinearMap)

/-- Owner coordinate map formula keeps the original actual map in the middle. -/
theorem homologyImageMap_apply (x : LinearMap.range p.mulVecLin) :
    homologyImageMap p q f eS eT x = eT (f (eS.symm x)) := rfl

include hrep in
/-- The coordinate map on every complete source-image vector is the generated matrix action. -/
theorem homologyImageMap_matrix (x : LinearMap.range p.mulVecLin) :
    (homologyImageMap p q f eS eT x : J → ℚ) = B *ᵥ x.1 := by
  rw [homologyImageMap_apply, hrep, LinearEquiv.apply_symm_apply]

/-- The actual-map diagram commutes on every original source class. -/
theorem homologyImageMap_natural (x : V) :
    eT (f x) = homologyImageMap p q f eS eT (eS x) := by
  rw [homologyImageMap_apply, LinearEquiv.symm_apply_apply]

/-- Both-direction original kernel identification, rather than an ambient matrix kernel. -/
def homologyImageMap_kernelEquiv : LinearMap.ker f ≃ₗ[ℚ]
    LinearMap.ker (homologyImageMap p q f eS eT) :=
  AAT.AG.AtlasDefectComposition.LinearConjugation.kernelEquiv f
    (homologyImageMap p q f eS eT) eS eT (homologyImageMap_natural p q f eS eT)

/-- Both-direction original cokernel identification in the complete target image. -/
def homologyImageMap_cokernelEquiv : (W ⧸ LinearMap.range f) ≃ₗ[ℚ]
    (LinearMap.range q.mulVecLin ⧸ LinearMap.range (homologyImageMap p q f eS eT)) :=
  AAT.AG.AtlasDefectComposition.LinearConjugation.cokernelEquiv f
    (homologyImageMap p q f eS eT) eS eT (homologyImageMap_natural p q f eS eT)

/-- E any further basis/display isomorphisms commute through the same original
map in both coordinates. Entries may change; the actual map is retained. -/
theorem homologyImageMap_change {V' W' : Type*}
    [AddCommGroup V'] [Module ℚ V'] [AddCommGroup W'] [Module ℚ W']
    (s : V ≃ₗ[ℚ] V') (t : W ≃ₗ[ℚ] W')
    (x : LinearMap.range p.mulVecLin) :
    t (eT.symm (homologyImageMap p q f eS eT x)) =
      t (f (s.symm ((eS.symm.trans s) x))) := by
  rw [homologyImageMap_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The same entry-based rank can be computed from transposed primitive
columns, with the equality proved against semantic rank rather than a fixture. -/
theorem rationalMatrixRank_transpose (B : Matrix J I ℚ) :
    rationalMatrixRank Bᵀ = rationalMatrixRank B := by
  rw [rationalMatrixRank_eq_rank, rationalMatrixRank_eq_rank, Matrix.rank_transpose]

end AAT.AG.AtlasCoefficientFiber.RationalCoordinates

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.coordinateMatrix_range
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.coordinateMatrix_rank
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.coordinateProjection_dimensions
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.coordinateMatrix_blockDefect
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyImageMap
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyImageMap_apply
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyImageMap_matrix
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyImageMap_natural
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyImageMap_kernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyImageMap_cokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.homologyImageMap_change

#print axioms AAT.AG.AtlasCoefficientFiber.RationalCoordinates.rationalMatrixRank_transpose

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.RationalCoordinates
