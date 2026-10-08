import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveMatrices
import ResearchLean.AG.AtlasCoefficientFiber.QuotientDual

/-!
# Primitive L columns in the original named cell coordinates

Position: G-135 E, all three degree presentations of the original L. Each
column is an original vertical endpoint difference, vertical edge or mixed
signed boundary, or original none face. No cohomology basis or rank is input.

## Implementation notes

Standard single bases and their product keep cell names and every incidence
occurrence. The native Set-selected presentation uses noncomputable standard
coordinate transport; finite rational table algorithms are separate C17 data.
Entry APIs identify their actual primitive columns before that algorithm is
applied. An arbitrary supplied L matrix, a pure-only finite presentation, and
selection of homology bases were rejected because they lose the original M
construction. The range theorem is about the original L, not a new chosen space.
-/

noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module Matrix
universe u

/-- E standard original chain coordinates: each named coefficient is retained.
The finite premise comes from the original selected cell type. -/
def chainCoordinates (I : Type u) [Finite I] : (I →₀ ℚ) ≃ₗ[ℚ] (I → ℚ) :=
  Finsupp.linearEquivFunOnFinite ℚ ℚ I

/-- Owner API exposes the same original coefficient function for every chain. -/
theorem chainCoordinates_apply {I : Type u} [Finite I] (x : I →₀ ℚ) :
    chainCoordinates I x = x := rfl

/-- Owner inverse API: native finite-chain coordinates recover every input
function, without choosing a basis from a desired homology dimension. -/
theorem chainCoordinates_symm_apply {I : Type u} [Finite I] (x : I → ℚ) :
    ((chainCoordinates I).symm x : I → ℚ) = x := by
  exact Finsupp.linearEquivFunOnFinite_symm_apply ℚ ℚ I x

/-- E product coordinates retain separate vertical and mixed cell columns. -/
def pairChainCoordinates (J K : Type u) [Finite J] [Finite K] :
    ((J →₀ ℚ) × (K →₀ ℚ)) ≃ₗ[ℚ] ((J ⊕ K) → ℚ) :=
  (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).repr.trans
    (chainCoordinates (J ⊕ K))

/-- Owner product API identifies all coordinates with the original two chains. -/
theorem pairChainCoordinates_apply {J K : Type u} [Finite J] [Finite K]
    (x : (J →₀ ℚ) × (K →₀ ℚ)) :
    pairChainCoordinates J K x = Sum.elim x.1 x.2 := by
  ext i
  cases i with
  | inl j => exact Basis.prod_repr_inl _ _ x j
  | inr k => exact Basis.prod_repr_inr _ _ x k

/-- E range transport for a table proved to represent an original map on all
vectors. Coordinate equivalences here are direction hypotheses; applications
below generate them from the original cell single bases. -/
theorem range_matrix_of_represents {I J X Y : Type u} [Fintype I] [Fintype J]
    [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    (eX : X ≃ₗ[ℚ] (J → ℚ)) (eY : Y ≃ₗ[ℚ] (I → ℚ))
    (f : X →ₗ[ℚ] Y) (B : Matrix I J ℚ)
    (h : ∀ x, B *ᵥ eX x = eY (f x)) :
    LinearMap.range B.mulVecLin = (LinearMap.range f).map eY.toLinearMap := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := eX.surjective y
    exact ⟨f z, ⟨z, rfl⟩, (h z).symm⟩
  · rintro x ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨eX z, h z⟩

/-- E single-basis table producer for original free-chain maps. Noncomputable
native transport is used only to present existing primitive columns. -/
def freeChainMatrix {I J : Type u} [Finite I] [Fintype J]
    (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) : Matrix I J ℚ := by
  classical
  exact LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne f

/-- Owner entry API: each table column is the same original single-chain image. -/
theorem freeChainMatrix_entry {I J : Type u} [Finite I] [Fintype J]
    (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) (i : I) (j : J) :
    freeChainMatrix f i j = f (Finsupp.single j 1) i := by
  classical
  rw [freeChainMatrix, LinearMap.toMatrix_apply]
  rfl

/-- Owner whole-vector API: every original chain is represented, not only
selected basis columns. Finite column enumeration is input-cell data. -/
theorem freeChainMatrix_mulVec {I J : Type u} [Fintype J] [Finite I]
    (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) (x : J →₀ ℚ) :
    freeChainMatrix f *ᵥ (x : J → ℚ) = (f x : I → ℚ) := by
  classical
  exact matrix_represents_map Finsupp.basisSingleOne Finsupp.basisSingleOne f x

/-- Owner original range equality: finite coefficient presentation keeps the
same image through the standard chain/function equivalence in both directions. -/
theorem freeChainMatrix_range {I J : Type u} [Fintype I] [Fintype J]
    (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) :
    LinearMap.range (freeChainMatrix f).mulVecLin =
      (LinearMap.range f).map (chainCoordinates I).toLinearMap :=
  range_matrix_of_represents (chainCoordinates J) (chainCoordinates I) f _
    (freeChainMatrix_mulVec f)

/-- E mixed/vertical product table, with no quotient of duplicate cell names. -/
def freePairChainMatrix {I J K : Type u} [Finite I] [Fintype J] [Fintype K]
    (f : ((J →₀ ℚ) × (K →₀ ℚ)) →ₗ[ℚ] (I →₀ ℚ)) : Matrix I (J ⊕ K) ℚ := by
  classical
  exact LinearMap.toMatrix (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)
    Finsupp.basisSingleOne f

/-- Owner product entry API: the two original summands keep separate columns.
The output finite premise is original cell data, not an image dimension. -/
theorem freePairChainMatrix_entry {I J K : Type u} [Finite I]
    [Fintype J] [Fintype K]
    (f : ((J →₀ ℚ) × (K →₀ ℚ)) →ₗ[ℚ] (I →₀ ℚ)) (i : I) (j : J ⊕ K) :
    freePairChainMatrix f i j =
      f ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) j) i := by
  classical
  rw [freePairChainMatrix, LinearMap.toMatrix_apply]
  rfl

/-- Owner full product-vector representation, supporting the original L1 sum. -/
theorem freePairChainMatrix_mulVec {I J K : Type u} [Finite I]
    [Fintype J] [Fintype K]
    (f : ((J →₀ ℚ) × (K →₀ ℚ)) →ₗ[ℚ] (I →₀ ℚ))
    (x : (J →₀ ℚ) × (K →₀ ℚ)) :
    freePairChainMatrix f *ᵥ pairChainCoordinates J K x = (f x : I → ℚ) := by
  classical
  exact matrix_represents_map (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne)
    Finsupp.basisSingleOne f x

/-- Owner product range equality with the original map; surjectivity of the
standard full coordinate equivalence supplies the reverse inclusion. -/
theorem freePairChainMatrix_range {I J K : Type u} [Fintype I]
    [Fintype J] [Fintype K]
    (f : ((J →₀ ℚ) × (K →₀ ℚ)) →ₗ[ℚ] (I →₀ ℚ)) :
    LinearMap.range (freePairChainMatrix f).mulVecLin =
      (LinearMap.range f).map (chainCoordinates I).toLinearMap :=
  range_matrix_of_represents (pairChainCoordinates J K) (chainCoordinates I) f _
    (freePairChainMatrix_mulVec f)

/-- E finite evaluation pairing from the original free dual API. This proves
transpose constraints using all original coefficients, without unfolding duals. -/
theorem freeDualEquiv_finite_sum {I : Type u} [Fintype I] (z : I → ℚ) (x : I →₀ ℚ) :
    freeDualEquiv I z x = ∑ i, x i * z i := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, hx, hy]
      simp only [Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  | single i a =>
      rw [freeDualEquiv_single]
      simp [Finsupp.single_apply]

/-- Owner transpose evaluation: primitive constraints are the same original
single-column dual pairing, with no inferred semantic equation supplied. -/
theorem freeChainMatrix_transpose_mulVec {I J : Type u} [Fintype I] [Fintype J]
    (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) (z : I → ℚ) (j : J) :
    ((freeChainMatrix f)ᵀ *ᵥ z) j = freeDualEquiv I z (f (Finsupp.single j 1)) := by
  rw [freeDualEquiv_finite_sum]
  rw [Matrix.mulVec_eq_sum]
  simp only [Finset.sum_apply, Matrix.transpose_transpose, Pi.smul_apply,
    op_smul_eq_smul, smul_eq_mul, freeChainMatrix_entry]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Owner transpose kernel API: the table equations are exactly annihilation
of the original generator range; no semantic vanishing field is accepted. -/
theorem freeChainMatrix_transpose_eq_zero_iff {I J : Type u}
    [Fintype I] [Fintype J] (f : (J →₀ ℚ) →ₗ[ℚ] (I →₀ ℚ)) (z : I → ℚ) :
    (freeChainMatrix f)ᵀ *ᵥ z = 0 ↔
      ∀ x ∈ LinearMap.range f, freeDualEquiv I z x = 0 := by
  rw [annihilates_freeRange_iff]
  constructor
  · intro h j
    simpa only [freeChainMatrix_transpose_mulVec, Pi.zero_apply] using congrFun h j
  · intro h
    ext j
    rw [freeChainMatrix_transpose_mulVec, h j, Pi.zero_apply]

/-- Owner product transpose evaluation uses each original product-basis
column. It is used to compare the full vertical-plus-mixed annihilator. -/
theorem freePairChainMatrix_transpose_mulVec {I J K : Type u}
    [Fintype I] [Fintype J] [Fintype K]
    (f : ((J →₀ ℚ) × (K →₀ ℚ)) →ₗ[ℚ] (I →₀ ℚ)) (z : I → ℚ) (j : J ⊕ K) :
    ((freePairChainMatrix f)ᵀ *ᵥ z) j =
      freeDualEquiv I z (f ((Finsupp.basisSingleOne.prod Finsupp.basisSingleOne) j)) := by
  rw [freeDualEquiv_finite_sum, Matrix.mulVec_eq_sum]
  simp only [Finset.sum_apply, Matrix.transpose_transpose, Pi.smul_apply,
    op_smul_eq_smul, smul_eq_mul, freePairChainMatrix_entry]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Owner product kernel API checks the entire original generator range,
including every mixed signed boundary and every vertical single. -/
theorem freePairChainMatrix_transpose_eq_zero_iff {I J K : Type u}
    [Fintype I] [Fintype J] [Fintype K]
    (f : ((J →₀ ℚ) × (K →₀ ℚ)) →ₗ[ℚ] (I →₀ ℚ)) (z : I → ℚ) :
    (freePairChainMatrix f)ᵀ *ᵥ z = 0 ↔
      ∀ x ∈ LinearMap.range f, freeDualEquiv I z x = 0 := by
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    have he : (freeDualEquiv I z).comp f = 0 := by
      apply (Finsupp.basisSingleOne.prod Finsupp.basisSingleOne).ext
      intro j
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply,
        freePairChainMatrix_transpose_mulVec, Pi.zero_apply] using congrFun h j
    exact LinearMap.congr_fun he y
  · intro h
    ext j
    rw [freePairChainMatrix_transpose_mulVec, h _ ⟨_, rfl⟩, Pi.zero_apply]

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- E original L0 generator: vertical endpoints with their signed difference. -/
def primitiveL0Generator : (VerticalEdge M A →₀ ℚ) →ₗ[ℚ] K0 Nf (comparisonFactor qc qf h ⁻¹' A) :=
  (chainD1 Nf _).comp (verticalEdgeInclusion M A)
/-- Owner L0 evaluation preserves the same original endpoint boundary. -/
theorem primitiveL0Generator_apply (x : VerticalEdge M A →₀ ℚ) :
    primitiveL0Generator M A x = chainD1 Nf _ (verticalEdgeInclusion M A x) := rfl
/-- Owner L0 range is the original specified subspace, in both directions. -/
theorem primitiveL0Generator_range : LinearMap.range (primitiveL0Generator M A) = degenerateL0 M A := by
  ext x
  rw [LinearMap.mem_range, mem_degenerateL0]
  simp only [primitiveL0Generator_apply]

/-- E original L1 generator retains the vertical chain and all mixed face
boundaries separately; it does not restrict mixed chains to ker B. -/
def primitiveL1Generator : ((VerticalEdge M A →₀ ℚ) × (MixedFace M A →₀ ℚ)) →ₗ[ℚ]
    K1 Nf (comparisonFactor qc qf h ⁻¹' A) :=
  (verticalEdgeInclusion M A).coprod ((chainD2 Nf _).comp (mixedFaceInclusion M A))
/-- Owner L1 evaluation reads both original summands with all signed incidence. -/
theorem primitiveL1Generator_apply (x : (VerticalEdge M A →₀ ℚ) × (MixedFace M A →₀ ℚ)) :
    primitiveL1Generator M A x = verticalEdgeInclusion M A x.1 +
      chainD2 Nf _ (mixedFaceInclusion M A x.2) := rfl
/-- Owner L1 range exactly equals the original vertical-plus-mixed subspace. -/
theorem primitiveL1Generator_range : LinearMap.range (primitiveL1Generator M A) = degenerateL1 M A := by
  ext x
  rw [LinearMap.mem_range, mem_degenerateL1]
  simp only [primitiveL1Generator_apply]
  constructor
  · rintro ⟨⟨v, f⟩, hx⟩; exact ⟨v, f, hx⟩
  · rintro ⟨v, f, hx⟩; exact ⟨(v, f), hx⟩

/-- E original L2 generator is inclusion of all none faces with original names. -/
def primitiveL2Generator : (DegenerateFace M A →₀ ℚ) →ₗ[ℚ]
    K2 Nf (comparisonFactor qc qf h ⁻¹' A) := degenerateFaceInclusion M A
/-- Owner L2 evaluation is the original none-face inclusion. -/
theorem primitiveL2Generator_apply (x : DegenerateFace M A →₀ ℚ) :
    primitiveL2Generator M A x = degenerateFaceInclusion M A x := rfl
/-- Owner L2 range exactly equals the original specified none-face subspace. -/
theorem primitiveL2Generator_range : LinearMap.range (primitiveL2Generator M A) = degenerateL2 M A := by
  ext x
  rw [LinearMap.mem_range, mem_degenerateL2]
  simp only [primitiveL2Generator_apply]

/-- E L0 entries are generated from the original vertical endpoint columns. -/
def primitiveL0Matrix [Finite (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] :
    Matrix (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (VerticalEdge M A) ℚ :=
  freeChainMatrix (primitiveL0Generator M A)
/-- E L1 entries retain vertical singles and all original mixed boundary columns. -/
def primitiveL1Matrix [Finite (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] :
    Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
      (VerticalEdge M A ⊕ MixedFace M A) ℚ := freePairChainMatrix (primitiveL1Generator M A)
/-- E L2 entries retain each original none-face single column. -/
def primitiveL2Matrix [Finite (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (DegenerateFace M A)] :
    Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (DegenerateFace M A) ℚ :=
  freeChainMatrix (primitiveL2Generator M A)

/-- Owner L0 entry gives the original signed vertical endpoint difference.
Repeated endpoints cancel by arithmetic, without discarding cell names. -/
theorem primitiveL0Matrix_entry [Finite (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)]
    (i : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (e : VerticalEdge M A) :
    primitiveL0Matrix M A i e =
      (Finsupp.single (Nf.targetSubsetEdgeRight _ e.1) (1 : ℚ) -
        Finsupp.single (Nf.targetSubsetEdgeLeft _ e.1) 1 :
        Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) →₀ ℚ) i := by
  rw [primitiveL0Matrix, freeChainMatrix_entry, primitiveL0Generator_apply,
    verticalEdgeInclusion_single, chainD1_single, one_smul]

/-- Owner L1 vertical column is the same original vertical edge single. -/
theorem primitiveL1Matrix_entry_inl [Finite (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
    (i : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (e : VerticalEdge M A) :
    primitiveL1Matrix M A i (Sum.inl e) = Finsupp.single e.1 (1 : ℚ) i := by
  classical
  rw [primitiveL1Matrix, freePairChainMatrix_entry, primitiveL1Generator_apply,
    Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd]
  simp only [Finsupp.coe_basisSingleOne, verticalEdgeInclusion_single, map_zero, add_zero]

/-- Owner L1 mixed column is the full original three-occurrence boundary.
It includes repeated and vertical occurrences, without any ker B restriction. -/
theorem primitiveL1Matrix_entry_inr [Finite (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
    (i : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (f : MixedFace M A) :
    primitiveL1Matrix M A i (Sum.inr f) =
      (Finsupp.single (Nf.targetSubsetFaceEdge0 _ f.1) (1 : ℚ) -
        Finsupp.single (Nf.targetSubsetFaceEdge1 _ f.1) 1 +
        Finsupp.single (Nf.targetSubsetFaceEdge2 _ f.1) 1 :
        Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) →₀ ℚ) i := by
  classical
  rw [primitiveL1Matrix, freePairChainMatrix_entry, primitiveL1Generator_apply,
    Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd]
  simp only [Finsupp.coe_basisSingleOne, map_zero, zero_add,
    mixedFaceInclusion_single, chainD2_single, one_smul]

/-- Owner L2 entry retains each original none-face single, even when empty. -/
theorem primitiveL2Matrix_entry [Finite (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (DegenerateFace M A)]
    (i : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (f : DegenerateFace M A) :
    primitiveL2Matrix M A i f = Finsupp.single f.1 (1 : ℚ) i := by
  rw [primitiveL2Matrix, freeChainMatrix_entry, primitiveL2Generator_apply,
    degenerateFaceInclusion_single]

/-- Owner L0 represents every original vertical chain, with the same boundary. -/
theorem primitiveL0Matrix_mulVec [Finite (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)] (x : VerticalEdge M A →₀ ℚ) :
    primitiveL0Matrix M A *ᵥ (x : VerticalEdge M A → ℚ) =
      (primitiveL0Generator M A x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :=
  freeChainMatrix_mulVec _ _

/-- Owner L1 represents every pair of original vertical and mixed chains. -/
theorem primitiveL1Matrix_mulVec [Finite (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
    (x : (VerticalEdge M A →₀ ℚ) × (MixedFace M A →₀ ℚ)) :
    primitiveL1Matrix M A *ᵥ pairChainCoordinates _ _ x =
      (primitiveL1Generator M A x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :=
  freePairChainMatrix_mulVec _ _

/-- Owner L2 represents every original none-face chain, including zero chains. -/
theorem primitiveL2Matrix_mulVec [Finite (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (DegenerateFace M A)] (x : DegenerateFace M A →₀ ℚ) :
    primitiveL2Matrix M A *ᵥ (x : DegenerateFace M A → ℚ) =
      (primitiveL2Generator M A x : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :=
  freeChainMatrix_mulVec _ _

/-- Owner L0 range is the original specified L0 in the full cell coordinates. -/
theorem primitiveL0Matrix_range [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)] :
    LinearMap.range (primitiveL0Matrix M A).mulVecLin =
      (degenerateL0 M A).map (chainCoordinates _).toLinearMap := by
  rw [primitiveL0Matrix, freeChainMatrix_range, primitiveL0Generator_range]

/-- Owner L1 range is the original full L1, not only closed mixed boundaries. -/
theorem primitiveL1Matrix_range [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] :
    LinearMap.range (primitiveL1Matrix M A).mulVecLin =
      (degenerateL1 M A).map (chainCoordinates _).toLinearMap := by
  rw [primitiveL1Matrix, freePairChainMatrix_range, primitiveL1Generator_range]

/-- Owner L2 range is the original all-none-face subspace in full coordinates. -/
theorem primitiveL2Matrix_range [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
    [Fintype (DegenerateFace M A)] :
    LinearMap.range (primitiveL2Matrix M A).mulVecLin =
      (degenerateL2 M A).map (chainCoordinates _).toLinearMap := by
  rw [primitiveL2Matrix, freeChainMatrix_range, primitiveL2Generator_range]

/-- Owner degree-0 primitive kernel test equals the actual restriction zero
condition on every original fine vector. The range is generated from M. -/
theorem restriction0_eq_zero_iff_primitive [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)]
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction0 M A z = 0 ↔ (primitiveL0Matrix M A)ᵀ *ᵥ z = 0 := by
  rw [primitiveL0Matrix, freeChainMatrix_transpose_eq_zero_iff, primitiveL0Generator_range]
  constructor
  · intro hz x hx
    have he := LinearMap.congr_fun hz ⟨x, hx⟩
    simpa only [restriction0_apply, LinearMap.zero_apply] using he
  · intro hz
    apply LinearMap.ext
    intro x
    rw [restriction0_apply, LinearMap.zero_apply]
    exact hz x.1 x.2

/-- Owner degree-0 full kernel equality discharges native coordinate
transport's same-kernel premise from the original primitive construction. -/
theorem restriction0_ker_eq_primitive [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] :
    LinearMap.ker (restriction0 M A) = LinearMap.ker (primitiveL0Matrix M A)ᵀ.mulVecLin := by
  ext z
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact restriction0_eq_zero_iff_primitive M A z

/-- Owner degree-1 primitive kernel test equals the actual restriction zero
condition on every original fine vector. The range is generated from M. -/
theorem restriction1_eq_zero_iff_primitive [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction1 M A z = 0 ↔ (primitiveL1Matrix M A)ᵀ *ᵥ z = 0 := by
  rw [primitiveL1Matrix, freePairChainMatrix_transpose_eq_zero_iff, primitiveL1Generator_range]
  constructor
  · intro hz x hx
    have he := LinearMap.congr_fun hz ⟨x, hx⟩
    simpa only [restriction1_apply, LinearMap.zero_apply] using he
  · intro hz
    apply LinearMap.ext
    intro x
    rw [restriction1_apply, LinearMap.zero_apply]
    exact hz x.1 x.2

/-- Owner degree-1 full kernel equality discharges native coordinate
transport's same-kernel premise from the original primitive construction. -/
theorem restriction1_ker_eq_primitive [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] :
    LinearMap.ker (restriction1 M A) = LinearMap.ker (primitiveL1Matrix M A)ᵀ.mulVecLin := by
  ext z
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact restriction1_eq_zero_iff_primitive M A z

/-- Owner degree-2 primitive kernel test equals the actual restriction zero
condition on every original fine vector. The range is generated from M. -/
theorem restriction2_eq_zero_iff_primitive [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (DegenerateFace M A)]
    (z : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction2 M A z = 0 ↔ (primitiveL2Matrix M A)ᵀ *ᵥ z = 0 := by
  rw [primitiveL2Matrix, freeChainMatrix_transpose_eq_zero_iff, primitiveL2Generator_range]
  constructor
  · intro hz x hx
    have he := LinearMap.congr_fun hz ⟨x, hx⟩
    simpa only [restriction2_apply, LinearMap.zero_apply] using he
  · intro hz
    apply LinearMap.ext
    intro x
    rw [restriction2_apply, LinearMap.zero_apply]
    exact hz x.1 x.2

/-- Owner degree-2 full kernel equality discharges native coordinate
transport's same-kernel premise from the original primitive construction. -/
theorem restriction2_ker_eq_primitive [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (DegenerateFace M A)] :
    LinearMap.ker (restriction2 M A) = LinearMap.ker (primitiveL2Matrix M A)ᵀ.mulVecLin := by
  ext z
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact restriction2_eq_zero_iff_primitive M A z

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.chainCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.chainCoordinates_apply
#print axioms AAT.AG.AtlasCoefficientFiber.chainCoordinates_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.pairChainCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.pairChainCoordinates_apply
#print axioms AAT.AG.AtlasCoefficientFiber.range_matrix_of_represents
#print axioms AAT.AG.AtlasCoefficientFiber.freeChainMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.freeChainMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.freeChainMatrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.freeChainMatrix_range
#print axioms AAT.AG.AtlasCoefficientFiber.freePairChainMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.freePairChainMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.freePairChainMatrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.freePairChainMatrix_range
#print axioms AAT.AG.AtlasCoefficientFiber.freeDualEquiv_finite_sum
#print axioms AAT.AG.AtlasCoefficientFiber.freeChainMatrix_transpose_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.freeChainMatrix_transpose_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.freePairChainMatrix_transpose_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.freePairChainMatrix_transpose_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL0Generator
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL0Generator_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL0Generator_range
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Generator
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Generator_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Generator_range
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL2Generator
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL2Generator_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL2Generator_range
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL0Matrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Matrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL2Matrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL0Matrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Matrix_entry_inl
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Matrix_entry_inr
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL2Matrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL0Matrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Matrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL2Matrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL0Matrix_range
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Matrix_range
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL2Matrix_range
#print axioms AAT.AG.AtlasCoefficientFiber.restriction0_eq_zero_iff_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.restriction0_ker_eq_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1_eq_zero_iff_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1_ker_eq_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.restriction2_eq_zero_iff_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.restriction2_ker_eq_primitive

#print axioms AAT.AG.AtlasCoefficientFiber.freeChainMatrix.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.freePairChainMatrix.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL0Matrix.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL1Matrix.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveL2Matrix.congr_simp

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
