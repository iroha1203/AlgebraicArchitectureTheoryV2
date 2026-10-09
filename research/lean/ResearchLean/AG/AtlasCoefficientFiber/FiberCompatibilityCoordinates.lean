import ResearchLean.AG.AtlasCoefficientFiber.NativeDiagnosticMatrices
import ResearchLean.AG.AtlasCoefficientFiber.FiberCohomology

/-!
# Primitive coordinates of the original fiber compatibility

Position: G-135 E, original vertical homology and kappa. The kernel of the
original vertical endpoint map is quotiented by the original vertical face
boundary; mixed cycles remain the kernel of the original B.

## Implementation notes

The producer uses only original a/B/D/V entries, kernel/image projections,
and rational matrix multiplication. Coordinate inverses are noncomputable
transport of these original modules, not replacement complexes. Generic
whole-vector representation is a direction hypothesis, discharged below
from the original named-cell matrices. Expected homology rank, connectedness,
and a supplied kappa kernel are not inputs. All Phi components use the
accepted original vertical-to-Phi equivalence.
-/
set_option synthInstance.maxHeartbeats 200000

noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module Matrix
open RationalCoordinates
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra
universe u

/-- E the literal original free-chain kernel embeds by its original coefficients. -/
def chainKernelEmbedding {I J : Type u} [Finite J]
    (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) : LinearMap.ker f →ₗ[ℚ] (J → ℚ) :=
  (chainCoordinates J).toLinearMap.comp (LinearMap.ker f).subtype

/-- Owner full coefficient API for every original kernel element. -/
theorem chainKernelEmbedding_apply {I J : Type u} [Finite J]
    (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) (z : LinearMap.ker f) :
    chainKernelEmbedding f z = (z.1 : J → ℚ) := rfl

/-- E raw coefficients faithfully embed the original kernel. -/
theorem chainKernelEmbedding_injective {I J : Type u} [Finite J]
    (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) : Function.Injective (chainKernelEmbedding f) := by
  intro x y h
  apply Subtype.ext
  exact (chainCoordinates J).injective h

/-- E both inclusions identify the original kernel with the generated kernel
projection image. The full-vector premise is discharged in native uses. -/
theorem chainKernelEmbedding_range {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq J] (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) (B : Matrix I J ℚ)
    (h : ∀ x : J →₀ ℚ, B *ᵥ (x : J → ℚ) = (f x : I → ℚ)) :
    LinearMap.range (chainKernelEmbedding f) = LinearMap.range (kernelProjection B).mulVecLin := by
  rw [kernelProjection_range]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change B *ᵥ (z.1 : J → ℚ) = 0
    rw [h, show f z.1 = 0 from z.2]
    rfl
  · intro hx
    let z := (chainCoordinates J).symm x
    have hz : (z : J → ℚ) = x := chainCoordinates_symm_apply x
    have hf : f z = 0 := by
      apply Finsupp.ext
      intro i
      have hh := h z
      rw [hz] at hh
      have he : (f z : I → ℚ) = 0 := hh.symm.trans hx
      exact congrFun he i
    exact ⟨⟨z, hf⟩, hz⟩

/-- E both-direction transport of the literal original kernel; no new
complex or semantic basis enters the construction. -/
def chainKernelCoordinateEquiv {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq J] (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) (B : Matrix I J ℚ)
    (h : ∀ x : J →₀ ℚ, B *ᵥ (x : J → ℚ) = (f x : I → ℚ)) :
    LinearMap.ker f ≃ₗ[ℚ] LinearMap.range (kernelProjection B).mulVecLin :=
  LinearEquiv.ofBijective
    ((chainKernelEmbedding f).codRestrict _ (fun z => by
      rw [← chainKernelEmbedding_range f B h]
      exact ⟨z, rfl⟩))
    ⟨fun x y hh => chainKernelEmbedding_injective f (congrArg Subtype.val hh), by
      intro y
      have hy : y.1 ∈ LinearMap.range (chainKernelEmbedding f) := by
        simpa only [chainKernelEmbedding_range f B h] using y.2
      obtain ⟨z, hz⟩ := hy
      exact ⟨z, Subtype.ext hz⟩⟩

/-- Owner whole representative API for kernel coordinates. -/
theorem chainKernelCoordinateEquiv_apply {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq J] (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) (B : Matrix I J ℚ)
    (h : ∀ x : J →₀ ℚ, B *ᵥ (x : J → ℚ) = (f x : I → ℚ)) (z : LinearMap.ker f) :
    (chainKernelCoordinateEquiv f B h z : J → ℚ) = (z.1 : J → ℚ) := rfl

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (VerticalFace M A)]
variable [Fintype (MixedFace M A)] [Fintype (HorizontalEdge M A)]
variable [DecidableEq (VerticalEdge M A)] [DecidableEq (MixedFace M A)]

/-- E original vertical endpoint-incidence a, generated from its raw singles. -/
def primitiveVerticalEdgeMatrix :
    Matrix (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (VerticalEdge M A) ℚ :=
  freeChainMatrix (verticalEdgeBoundary M A)

omit [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)]
    [Fintype (HorizontalEdge M A)] [DecidableEq (VerticalEdge M A)]
    [DecidableEq (MixedFace M A)] in
/-- Owner every original a column, retaining both endpoint occurrences. -/
theorem primitiveVerticalEdgeMatrix_entry (i) (j) :
    primitiveVerticalEdgeMatrix M A i j = verticalEdgeBoundary M A (Finsupp.single j 1) i :=
  freeChainMatrix_entry _ i j

omit [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)]
    [Fintype (HorizontalEdge M A)] [DecidableEq (VerticalEdge M A)]
    [DecidableEq (MixedFace M A)] in
/-- Owner all-vector original a representation. -/
theorem primitiveVerticalEdgeMatrix_mulVec (x : VerticalEdge M A →₀ ℚ) :
    primitiveVerticalEdgeMatrix M A *ᵥ (x : VerticalEdge M A → ℚ) =
      (verticalEdgeBoundary M A x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :=
  freeChainMatrix_mulVec _ x

/-- E all original vertical cycles, in the generated original a-kernel coordinates. -/
def verticalCycleCoordinateEquiv : verticalCycles M A ≃ₗ[ℚ]
    LinearMap.range (kernelProjection (primitiveVerticalEdgeMatrix M A)).mulVecLin :=
  chainKernelCoordinateEquiv _ _ (primitiveVerticalEdgeMatrix_mulVec M A)

omit [Fintype (VerticalFace M A)] [Fintype (MixedFace M A)]
    [Fintype (HorizontalEdge M A)] [DecidableEq (MixedFace M A)] in
/-- Owner every original vertical cycle keeps all raw coefficients. -/
theorem verticalCycleCoordinateEquiv_apply (z : verticalCycles M A) :
    (verticalCycleCoordinateEquiv M A z : VerticalEdge M A → ℚ) = z.1 := rfl

/-- E all original mixed cycles, with the original B-kernel retained. -/
def mixedCycleCoordinateEquiv : mixedCycles M A ≃ₗ[ℚ]
    LinearMap.range (kernelProjection (primitiveBMatrix M A)).mulVecLin :=
  chainKernelCoordinateEquiv _ _ (primitiveBMatrix_mulVec M A)

omit [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)] [Fintype (VerticalFace M A)]
    [DecidableEq (VerticalEdge M A)] in
/-- Owner every original mixed cycle retains its named face coefficients. -/
theorem mixedCycleCoordinateEquiv_apply (z : mixedCycles M A) :
    (mixedCycleCoordinateEquiv M A z : MixedFace M A → ℚ) = z.1 := rfl

omit [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
    [Fintype (HorizontalEdge M A)] [DecidableEq (VerticalEdge M A)]
    [DecidableEq (MixedFace M A)] in
/-- E V-image is exactly the original boundary image inside the original
vertical-cycle embedding; both inclusions use actual original chains. -/
theorem primitiveVMatrix_cycle_range : LinearMap.range (primitiveVMatrix M A).mulVecLin =
    (LinearMap.range (verticalBoundaryToCycles M A)).map
      (chainKernelEmbedding (verticalEdgeBoundary M A)) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    let v := (chainCoordinates (VerticalFace M A)).symm z
    refine ⟨verticalBoundaryToCycles M A v, ⟨v, rfl⟩, ?_⟩
    rw [chainKernelEmbedding_apply, verticalBoundaryToCycles_val,
      ← primitiveVMatrix_mulVec, chainCoordinates_symm_apply]
    rfl
  · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
    exact ⟨(v : VerticalFace M A → ℚ), primitiveVMatrix_mulVec M A v⟩

omit [Fintype (MixedFace M A)] [Fintype (HorizontalEdge M A)]
    [DecidableEq (MixedFace M A)] in
/-- E actual vertical faces are a-closed; the generated a-kernel therefore
fixes V on all columns, without a supplied compatibility premise. -/
theorem primitiveVMatrix_kernel_absorption :
    kernelProjection (primitiveVerticalEdgeMatrix M A) * primitiveVMatrix M A =
      primitiveVMatrix M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  apply kernelProjection_fixes_ker
  rw [← kernelProjection_range,
    ← chainKernelEmbedding_range (verticalEdgeBoundary M A)
    (primitiveVerticalEdgeMatrix M A) (primitiveVerticalEdgeMatrix_mulVec M A)]
  have hv : primitiveVMatrix M A *ᵥ x ∈ LinearMap.range (primitiveVMatrix M A).mulVecLin :=
    ⟨x, rfl⟩
  rw [primitiveVMatrix_cycle_range] at hv
  obtain ⟨z, _, hz⟩ := hv
  exact ⟨z, hz⟩

/-- E executable original vertical homology projector: original a-kernel
minus the original V-image, keeping all original cycles and boundaries. -/
def verticalHomologyProjection : Matrix (VerticalEdge M A) (VerticalEdge M A) ℚ :=
  secondHomologyProjection (kernelProjection (primitiveVerticalEdgeMatrix M A)) (primitiveVMatrix M A)

omit [Fintype (MixedFace M A)] [Fintype (HorizontalEdge M A)]
    [DecidableEq (MixedFace M A)] in
/-- Owner direct formula for the same original quotient producer. -/
theorem verticalHomologyProjection_eq : verticalHomologyProjection M A =
    kernelProjection (primitiveVerticalEdgeMatrix M A) - imageProjection (primitiveVMatrix M A) := rfl

/-- E both-direction coordinates of the literal original VerticalHomology. -/
def verticalHomologyCoordinateEquiv : VerticalHomology M A ≃ₗ[ℚ]
    LinearMap.range (verticalHomologyProjection M A).mulVecLin :=
  secondHomologyCoordinateEquiv (verticalBoundaryToCycles M A)
    (chainKernelEmbedding (verticalEdgeBoundary M A))
    (kernelProjection (primitiveVerticalEdgeMatrix M A)) (primitiveVMatrix M A)
    (chainKernelEmbedding_injective _) (kernelProjection_transpose _)
    (kernelProjection_mul_self _) (primitiveVMatrix_kernel_absorption M A)
    (chainKernelEmbedding_range _ _ (primitiveVerticalEdgeMatrix_mulVec M A))
    (primitiveVMatrix_cycle_range M A)

omit [Fintype (MixedFace M A)] [Fintype (HorizontalEdge M A)]
    [DecidableEq (MixedFace M A)] in
/-- Owner coordinates of every original vertical homology representative. -/
theorem verticalHomologyCoordinateEquiv_mk (z : verticalCycles M A) :
    (verticalHomologyCoordinateEquiv M A (Submodule.Quotient.mk z) : VerticalEdge M A → ℚ) =
      verticalHomologyProjection M A *ᵥ (z.1 : VerticalEdge M A → ℚ) :=
  secondHomologyCoordinateEquiv_mk _ _ _ _ _ _ _ _ _ _ z

/-- E all original Phi homology components use the accepted original
vertical decomposition, rather than a replacement fiber space. -/
def phiHomologyCoordinateEquiv :
    ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) ≃ₗ[ℚ]
      LinearMap.range (verticalHomologyProjection M A).mulVecLin :=
  (verticalHomologyPhiEquiv M A).symm.trans (verticalHomologyCoordinateEquiv M A)

/-- E executable kappa table from the actual original B/D/a/V matrices. -/
def nativeKappaMatrix : Matrix (VerticalEdge M A) (MixedFace M A) ℚ :=
  verticalHomologyProjection M A * primitiveDMatrix M A * kernelProjection (primitiveBMatrix M A)

/-- Owner direct primitive formula for the kappa producer. -/
theorem nativeKappaMatrix_eq : nativeKappaMatrix M A =
    verticalHomologyProjection M A * primitiveDMatrix M A * kernelProjection (primitiveBMatrix M A) := rfl

/-- E every original mixed cycle represents the same raw Dy quotient. -/
theorem nativeKappaMatrix_rawKappa (z : mixedCycles M A) :
    (verticalHomologyCoordinateEquiv M A (rawKappa M A z) : VerticalEdge M A → ℚ) =
      nativeKappaMatrix M A *ᵥ (mixedCycleCoordinateEquiv M A z : MixedFace M A → ℚ) := by
  rw [rawKappa_apply, verticalHomologyCoordinateEquiv_mk, mixedCycleToVertical_val,
    nativeKappaMatrix_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mixedCycleCoordinateEquiv_apply]
  have hb : (z.1 : MixedFace M A → ℚ) ∈ LinearMap.ker (primitiveBMatrix M A).mulVecLin := by
    change primitiveBMatrix M A *ᵥ (z.1 : MixedFace M A → ℚ) = 0
    rw [primitiveBMatrix_mulVec, show mixedHorizontalBoundary M A z.1 = 0 from z.2]
    rfl
  rw [kernelProjection_fixes_ker _ _ hb, primitiveDMatrix_mulVec]

/-- E all Phi components of the original kappa have the same generated table. -/
theorem nativeKappaMatrix_kappa (z : mixedCycles M A) :
    (phiHomologyCoordinateEquiv M A (kappa M A z) : VerticalEdge M A → ℚ) =
      nativeKappaMatrix M A *ᵥ (mixedCycleCoordinateEquiv M A z : MixedFace M A → ℚ) := by
  rw [phiHomologyCoordinateEquiv, LinearEquiv.trans_apply, kappa_apply,
    LinearEquiv.symm_apply_apply, ← rawKappa_apply]
  exact nativeKappaMatrix_rawKappa M A z

/-- Owner kappa right absorption removes unused mixed ambient coordinates. -/
theorem nativeKappaMatrix_right_projection :
    nativeKappaMatrix M A * kernelProjection (primitiveBMatrix M A) = nativeKappaMatrix M A := by
  rw [nativeKappaMatrix_eq, Matrix.mul_assoc, kernelProjection_mul_self]

/-- E computed kappa rank is the actual original Dy quotient map rank. -/
theorem nativeKappaMatrix_raw_rank : rationalMatrixRank (nativeKappaMatrix M A) =
    finrank ℚ (LinearMap.range (rawKappa M A)) := by
  exact coordinateMatrix_rank (kernelProjection (primitiveBMatrix M A))
    (verticalHomologyProjection M A) (nativeKappaMatrix M A) (rawKappa M A)
    (mixedCycleCoordinateEquiv M A) (verticalHomologyCoordinateEquiv M A)
    (nativeKappaMatrix_right_projection M A) (nativeKappaMatrix_rawKappa M A)

/-- E all original Phi components have the same computed kappa rank. -/
theorem nativeKappaMatrix_rank : rationalMatrixRank (nativeKappaMatrix M A) =
    finrank ℚ (LinearMap.range (kappa M A)) := by
  rw [nativeKappaMatrix_raw_rank, ← kappa_range]
  exact (Submodule.equivMapOfInjective (verticalHomologyPhiEquiv M A).toLinearMap
    (verticalHomologyPhiEquiv M A).injective (LinearMap.range (rawKappa M A))).finrank_eq


section VerticalAPI
omit [Fintype (MixedFace M A)] [Fintype (HorizontalEdge M A)] [DecidableEq (MixedFace M A)]

/-- E every original vertical quotient class is recovered by the generated inverse. -/
theorem verticalHomologyCoordinateEquiv_left_inverse (z : VerticalHomology M A) :
    (verticalHomologyCoordinateEquiv M A).symm (verticalHomologyCoordinateEquiv M A z) = z :=
  (verticalHomologyCoordinateEquiv M A).symm_apply_apply z

/-- E every generated original vertical coordinate is recovered. -/
theorem verticalHomologyCoordinateEquiv_right_inverse
    (z : LinearMap.range (verticalHomologyProjection M A).mulVecLin) :
    verticalHomologyCoordinateEquiv M A ((verticalHomologyCoordinateEquiv M A).symm z) = z :=
  (verticalHomologyCoordinateEquiv M A).apply_symm_apply z

/-- E every generated coordinate has a literal original vertical cycle representative. -/
theorem verticalHomologyCoordinateEquiv_inverse_representative
    (x : LinearMap.range (verticalHomologyProjection M A).mulVecLin) :
    ∃ z : verticalCycles M A, (z.1 : VerticalEdge M A → ℚ) = x.1 ∧
      (verticalHomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  secondHomologyCoordinateEquiv_inverse_representative (verticalBoundaryToCycles M A)
    (chainKernelEmbedding (verticalEdgeBoundary M A))
    (kernelProjection (primitiveVerticalEdgeMatrix M A)) (primitiveVMatrix M A)
    (chainKernelEmbedding_injective _) (kernelProjection_transpose _)
    (kernelProjection_mul_self _) (primitiveVMatrix_kernel_absorption M A)
    (chainKernelEmbedding_range _ _ (primitiveVerticalEdgeMatrix_mulVec M A))
    (primitiveVMatrix_cycle_range M A) x

/-- E the generated vertical projector is recovered from itself. -/
theorem verticalHomologyProjection_mul_self :
    verticalHomologyProjection M A * verticalHomologyProjection M A = verticalHomologyProjection M A :=
  secondHomologyProjection_mul_self _ _ (kernelProjection_transpose _)
    (kernelProjection_mul_self _) (primitiveVMatrix_kernel_absorption M A)

/-- E computed projector dimension is the actual original vertical quotient dimension. -/
theorem verticalHomologyProjection_rank : rationalMatrixRank (verticalHomologyProjection M A) =
    finrank ℚ (VerticalHomology M A) := by
  rw [rationalMatrixRank_eq_finrank_range]
  exact (verticalHomologyCoordinateEquiv M A).symm.finrank_eq

/-- E all original Phi homology components have the same computed dimension. -/
theorem phiHomologyProjection_rank : rationalMatrixRank (verticalHomologyProjection M A) =
    finrank ℚ ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) := by
  rw [rationalMatrixRank_eq_finrank_range]
  exact (phiHomologyCoordinateEquiv M A).symm.finrank_eq

end VerticalAPI

/-- E computed kappa outputs remain in the original vertical homology image. -/
theorem nativeKappaMatrix_left_projection :
    verticalHomologyProjection M A * nativeKappaMatrix M A = nativeKappaMatrix M A := by
  rw [nativeKappaMatrix_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    verticalHomologyProjection_mul_self]

/-- E the same kappa acts on every generated original mixed coordinate. -/
theorem nativeKappaMatrix_imageMap
    (x : LinearMap.range (kernelProjection (primitiveBMatrix M A)).mulVecLin) :
    (phiHomologyCoordinateEquiv M A
      (kappa M A ((mixedCycleCoordinateEquiv M A).symm x)) : VerticalEdge M A → ℚ) =
        nativeKappaMatrix M A *ᵥ x.1 := by
  rw [nativeKappaMatrix_kappa, LinearEquiv.apply_symm_apply]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.chainKernelEmbedding
#print axioms AAT.AG.AtlasCoefficientFiber.chainKernelEmbedding_apply
#print axioms AAT.AG.AtlasCoefficientFiber.chainKernelEmbedding_injective
#print axioms AAT.AG.AtlasCoefficientFiber.chainKernelEmbedding_range
#print axioms AAT.AG.AtlasCoefficientFiber.chainKernelCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.chainKernelCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVerticalEdgeMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVerticalEdgeMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVerticalEdgeMatrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycleCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycleCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCycleCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCycleCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVMatrix_cycle_range
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVMatrix_kernel_absorption
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyProjection
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyProjection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.phiHomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix_rawKappa
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix_kappa
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix_right_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix_raw_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix_rank


#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyCoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyCoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyCoordinateEquiv_inverse_representative
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyProjection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.phiHomologyProjection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix_left_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeKappaMatrix_imageMap

#print axioms AAT.AG.AtlasCoefficientFiber.chainKernelEmbedding.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
