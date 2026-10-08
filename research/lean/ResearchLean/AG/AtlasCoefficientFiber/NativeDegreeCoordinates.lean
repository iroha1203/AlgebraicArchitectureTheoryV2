import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveDegreeMatrices
import ResearchLean.AG.AtlasCoefficientFiber.ProjectionTransport
import ResearchLean.AG.AtlasCoefficientFiber.EvaluationAnnihilator

/-!
# Original Kan P and actual dual-L Q in generated degree coordinates

Position: G-135 E, native three-degree coordinate connection. The matrices
are generated from original vertical/mixed/none columns. Every P coordinate
uses the original injective evaluation, and every Q coordinate uses actual
restriction to the specified L; neither native complex is redefined.

## Implementation notes

C4 supplies evaluation image and restriction surjectivity; the original
primitive columns discharge the same-kernel condition. C17 then generates
orthogonal image/annihilator projections, without a requested rank or basis.
Raw finite cell enumerations and equality decisions are ambient input data.
Native Set-selected transport is noncomputable; rational table production is
computable and is checked separately on the same original witness tables.
An arbitrary intermediate complex or supplied semantic basis would lose this
connection, so neither is used. Both inverse equations and full underlying
representatives are provided, including empty types and repeated incidence.
-/

noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module Matrix
open RationalCoordinates
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

section Degree0
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]
variable [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]

/-- E degree-0 P projection is generated from the original L transpose.
Its image is the existing Kan evaluation image, proved below from C4. -/
def nativeP0Projection : Matrix (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  kernelProjection (primitiveL0Matrix M A)ᵀ

/-- Owner P projection equation exposes only the generated producer API. -/
theorem nativeP0Projection_eq : nativeP0Projection M A =
    kernelProjection (primitiveL0Matrix M A)ᵀ := rfl

/-- E degree-0 Q projection is generated from the original L columns.
The coordinate space represents actual dual L through original restriction. -/
def nativeQ0Projection : Matrix (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  imageProjection (primitiveL0Matrix M A)

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q projection equation exposes the same rational table producer. -/
theorem nativeQ0Projection_eq : nativeQ0Projection M A =
    imageProjection (primitiveL0Matrix M A) := rfl

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E degree-0 evaluation image is the primitive transpose kernel.
The reverse inclusion is C4's input-generated original Kan preimage. -/
theorem evaluation0_range_eq_primitive :
    LinearMap.range (evaluation0 M A) = LinearMap.ker (primitiveL0Matrix M A)ᵀ.mulVecLin := by
  rw [evaluation0_range_eq_ker, restriction0_ker_eq_primitive]

/-- E degree-0 generated P image equals the original evaluation image
in both directions; the original P remains its independent Kan construction. -/
theorem nativeP0Projection_range :
    LinearMap.range (nativeP0Projection M A).mulVecLin = LinearMap.range (evaluation0 M A) := by
  rw [nativeP0Projection_eq, kernelProjection_range, evaluation0_range_eq_primitive]

/-- E degree-0 actual P coordinate equivalence, using original evaluation
and its input-derived full image/injectivity, without an extra certificate. -/
def nativeP0CoordinateEquiv : (pushforwardComplex M A).C0 ≃ₗ[ℚ]
    LinearMap.range (nativeP0Projection M A).mulVecLin :=
  embeddingCoordinateEquiv (primitiveL0Matrix M A) (evaluation0 M A)
    (evaluation0_injective M A) (evaluation0_range_eq_primitive M A)

/-- Owner native P representative API holds for every original P vector. -/
theorem nativeP0CoordinateEquiv_apply (x : (pushforwardComplex M A).C0) :
    (nativeP0CoordinateEquiv M A x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) = evaluation0 M A x :=
  embeddingCoordinateEquiv_apply _ _ _ _ x

/-- Owner native P inverse representative API recovers every generated
coordinate through the same original evaluation, with all components. -/
theorem nativeP0CoordinateEquiv_symm_apply
    (x : LinearMap.range (nativeP0Projection M A).mulVecLin) :
    evaluation0 M A ((nativeP0CoordinateEquiv M A).symm x) = x.1 :=
  embeddingCoordinateEquiv_symm_apply _ _ _ _ x

/-- Owner native P left inverse recovers every original Kan vector. -/
theorem nativeP0CoordinateEquiv_left_inverse (x : (pushforwardComplex M A).C0) :
    (nativeP0CoordinateEquiv M A).symm (nativeP0CoordinateEquiv M A x) = x :=
  (nativeP0CoordinateEquiv M A).symm_apply_apply x

/-- Owner native P right inverse recovers every generated image coordinate. -/
theorem nativeP0CoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeP0Projection M A).mulVecLin) :
    nativeP0CoordinateEquiv M A ((nativeP0CoordinateEquiv M A).symm x) = x :=
  (nativeP0CoordinateEquiv M A).apply_symm_apply x

/-- E degree-0 computable projection rank equals the original P dimension.
No expected dimension, homology basis, or image certificate is an input. -/
theorem nativeP0Projection_rank :
    rationalMatrixRank (nativeP0Projection M A) = Module.finrank ℚ (pushforwardComplex M A).C0 := by
  rw [nativeP0Projection_eq]
  exact embeddingCoordinateEquiv_rank _ _ (evaluation0_injective M A)
    (evaluation0_range_eq_primitive M A)

/-- Owner P absorption fixes the original evaluation of every native vector. -/
theorem nativeP0Projection_evaluation (x : (pushforwardComplex M A).C0) :
    nativeP0Projection M A *ᵥ evaluation0 M A x = evaluation0 M A x := by
  rw [nativeP0Projection_eq]
  apply kernelProjection_fixes_ker
  rw [← evaluation0_range_eq_primitive]
  exact ⟨x, rfl⟩

/-- E degree-0 actual Q coordinate equivalence uses the original restriction
onto dual L and the same primitive kernel, both discharged from original M. -/
def nativeQ0CoordinateEquiv : (restrictionComplex M A).C0 ≃ₗ[ℚ]
    LinearMap.range (nativeQ0Projection M A).mulVecLin :=
  restrictionCoordinateEquiv (primitiveL0Matrix M A) (restriction0 M A)
    (restriction0_surjective M A) (restriction0_ker_eq_primitive M A)

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q representative API holds for every original fine vector. -/
theorem nativeQ0CoordinateEquiv_apply (x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    (nativeQ0CoordinateEquiv M A (restriction0 M A x) : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeQ0Projection M A *ᵥ x :=
  restrictionCoordinateEquiv_apply _ _ _ _ x

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q inverse representative recovers every image coordinate
through actual restriction to the original L, without a new quotient object. -/
theorem nativeQ0CoordinateEquiv_symm_apply
    (x : LinearMap.range (nativeQ0Projection M A).mulVecLin) :
    (nativeQ0CoordinateEquiv M A).symm x = restriction0 M A x.1 :=
  restrictionCoordinateEquiv_symm_apply _ _ _ _ x

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q left inverse recovers every original dual-L vector. -/
theorem nativeQ0CoordinateEquiv_left_inverse (x : (restrictionComplex M A).C0) :
    (nativeQ0CoordinateEquiv M A).symm (nativeQ0CoordinateEquiv M A x) = x :=
  (nativeQ0CoordinateEquiv M A).symm_apply_apply x

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q right inverse recovers every generated image coordinate. -/
theorem nativeQ0CoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeQ0Projection M A).mulVecLin) :
    nativeQ0CoordinateEquiv M A ((nativeQ0CoordinateEquiv M A).symm x) = x :=
  (nativeQ0CoordinateEquiv M A).apply_symm_apply x

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E degree-0 computable projection rank equals the original Q dimension.
The original restriction surjectivity and primitive kernel produce the result. -/
theorem nativeQ0Projection_rank :
    rationalMatrixRank (nativeQ0Projection M A) = Module.finrank ℚ (restrictionComplex M A).C0 := by
  rw [nativeQ0Projection_eq]
  exact restrictionCoordinateEquiv_rank _ _ (restriction0_surjective M A)
    (restriction0_ker_eq_primitive M A)

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q correction preserves actual restriction of every fine vector;
this is the full representative equation used for native Q differentials. -/
theorem restriction0_nativeQProjection (x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction0 M A (nativeQ0Projection M A *ᵥ x) = restriction0 M A x := by
  rw [nativeQ0Projection_eq]
  exact restriction_imageProjection _ _ (restriction0_surjective M A)
    (restriction0_ker_eq_primitive M A) x

/-- Owner P representative existence follows from the actual generated
projection range, and supplies native differential transport on all vectors. -/
theorem nativeP0Projection_preimage (x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    ∃ w : (pushforwardComplex M A).C0, evaluation0 M A w = nativeP0Projection M A *ᵥ x := by
  have hx : nativeP0Projection M A *ᵥ x ∈ LinearMap.range (evaluation0 M A) := by
    rw [← nativeP0Projection_range]
    exact ⟨x, rfl⟩
  exact hx

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q absorption fixes every coordinate of the original dual-L target.
The property follows from the generated image, rather than being supplied. -/
theorem nativeQ0Projection_coordinate (z : (restrictionComplex M A).C0) :
    nativeQ0Projection M A *ᵥ (nativeQ0CoordinateEquiv M A z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      (nativeQ0CoordinateEquiv M A z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  apply imageProjection_fixes_range
  rw [← imageProjection_range]
  exact (nativeQ0CoordinateEquiv M A z).2

end Degree0

section Degree1
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]

/-- E degree-1 P projection is generated from the original L transpose.
Its image is the existing Kan evaluation image, proved below from C4. -/
def nativeP1Projection : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  kernelProjection (primitiveL1Matrix M A)ᵀ

/-- Owner P projection equation exposes only the generated producer API. -/
theorem nativeP1Projection_eq : nativeP1Projection M A =
    kernelProjection (primitiveL1Matrix M A)ᵀ := rfl

/-- E degree-1 Q projection is generated from the original L columns.
The coordinate space represents actual dual L through original restriction. -/
def nativeQ1Projection : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  imageProjection (primitiveL1Matrix M A)

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q projection equation exposes the same rational table producer. -/
theorem nativeQ1Projection_eq : nativeQ1Projection M A =
    imageProjection (primitiveL1Matrix M A) := rfl

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E degree-1 evaluation image is the primitive transpose kernel.
The reverse inclusion is C4's input-generated original Kan preimage. -/
theorem evaluation1_range_eq_primitive :
    LinearMap.range (evaluation1 M A) = LinearMap.ker (primitiveL1Matrix M A)ᵀ.mulVecLin := by
  rw [evaluation1_range_eq_ker, restriction1_ker_eq_primitive]

/-- E degree-1 generated P image equals the original evaluation image
in both directions; the original P remains its independent Kan construction. -/
theorem nativeP1Projection_range :
    LinearMap.range (nativeP1Projection M A).mulVecLin = LinearMap.range (evaluation1 M A) := by
  rw [nativeP1Projection_eq, kernelProjection_range, evaluation1_range_eq_primitive]

/-- E degree-1 actual P coordinate equivalence, using original evaluation
and its input-derived full image/injectivity, without an extra certificate. -/
def nativeP1CoordinateEquiv : (pushforwardComplex M A).C1 ≃ₗ[ℚ]
    LinearMap.range (nativeP1Projection M A).mulVecLin :=
  embeddingCoordinateEquiv (primitiveL1Matrix M A) (evaluation1 M A)
    (evaluation1_injective M A) (evaluation1_range_eq_primitive M A)

/-- Owner native P representative API holds for every original P vector. -/
theorem nativeP1CoordinateEquiv_apply (x : (pushforwardComplex M A).C1) :
    (nativeP1CoordinateEquiv M A x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) = evaluation1 M A x :=
  embeddingCoordinateEquiv_apply _ _ _ _ x

/-- Owner native P inverse representative API recovers every generated
coordinate through the same original evaluation, with all components. -/
theorem nativeP1CoordinateEquiv_symm_apply
    (x : LinearMap.range (nativeP1Projection M A).mulVecLin) :
    evaluation1 M A ((nativeP1CoordinateEquiv M A).symm x) = x.1 :=
  embeddingCoordinateEquiv_symm_apply _ _ _ _ x

/-- Owner native P left inverse recovers every original Kan vector. -/
theorem nativeP1CoordinateEquiv_left_inverse (x : (pushforwardComplex M A).C1) :
    (nativeP1CoordinateEquiv M A).symm (nativeP1CoordinateEquiv M A x) = x :=
  (nativeP1CoordinateEquiv M A).symm_apply_apply x

/-- Owner native P right inverse recovers every generated image coordinate. -/
theorem nativeP1CoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeP1Projection M A).mulVecLin) :
    nativeP1CoordinateEquiv M A ((nativeP1CoordinateEquiv M A).symm x) = x :=
  (nativeP1CoordinateEquiv M A).apply_symm_apply x

/-- E degree-1 computable projection rank equals the original P dimension.
No expected dimension, homology basis, or image certificate is an input. -/
theorem nativeP1Projection_rank :
    rationalMatrixRank (nativeP1Projection M A) = Module.finrank ℚ (pushforwardComplex M A).C1 := by
  rw [nativeP1Projection_eq]
  exact embeddingCoordinateEquiv_rank _ _ (evaluation1_injective M A)
    (evaluation1_range_eq_primitive M A)

/-- Owner P absorption fixes the original evaluation of every native vector. -/
theorem nativeP1Projection_evaluation (x : (pushforwardComplex M A).C1) :
    nativeP1Projection M A *ᵥ evaluation1 M A x = evaluation1 M A x := by
  rw [nativeP1Projection_eq]
  apply kernelProjection_fixes_ker
  rw [← evaluation1_range_eq_primitive]
  exact ⟨x, rfl⟩

/-- E degree-1 actual Q coordinate equivalence uses the original restriction
onto dual L and the same primitive kernel, both discharged from original M. -/
def nativeQ1CoordinateEquiv : (restrictionComplex M A).C1 ≃ₗ[ℚ]
    LinearMap.range (nativeQ1Projection M A).mulVecLin :=
  restrictionCoordinateEquiv (primitiveL1Matrix M A) (restriction1 M A)
    (restriction1_surjective M A) (restriction1_ker_eq_primitive M A)

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q representative API holds for every original fine vector. -/
theorem nativeQ1CoordinateEquiv_apply (x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    (nativeQ1CoordinateEquiv M A (restriction1 M A x) : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeQ1Projection M A *ᵥ x :=
  restrictionCoordinateEquiv_apply _ _ _ _ x

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q inverse representative recovers every image coordinate
through actual restriction to the original L, without a new quotient object. -/
theorem nativeQ1CoordinateEquiv_symm_apply
    (x : LinearMap.range (nativeQ1Projection M A).mulVecLin) :
    (nativeQ1CoordinateEquiv M A).symm x = restriction1 M A x.1 :=
  restrictionCoordinateEquiv_symm_apply _ _ _ _ x

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q left inverse recovers every original dual-L vector. -/
theorem nativeQ1CoordinateEquiv_left_inverse (x : (restrictionComplex M A).C1) :
    (nativeQ1CoordinateEquiv M A).symm (nativeQ1CoordinateEquiv M A x) = x :=
  (nativeQ1CoordinateEquiv M A).symm_apply_apply x

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q right inverse recovers every generated image coordinate. -/
theorem nativeQ1CoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeQ1Projection M A).mulVecLin) :
    nativeQ1CoordinateEquiv M A ((nativeQ1CoordinateEquiv M A).symm x) = x :=
  (nativeQ1CoordinateEquiv M A).apply_symm_apply x

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E degree-1 computable projection rank equals the original Q dimension.
The original restriction surjectivity and primitive kernel produce the result. -/
theorem nativeQ1Projection_rank :
    rationalMatrixRank (nativeQ1Projection M A) = Module.finrank ℚ (restrictionComplex M A).C1 := by
  rw [nativeQ1Projection_eq]
  exact restrictionCoordinateEquiv_rank _ _ (restriction1_surjective M A)
    (restriction1_ker_eq_primitive M A)

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q correction preserves actual restriction of every fine vector;
this is the full representative equation used for native Q differentials. -/
theorem restriction1_nativeQProjection (x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction1 M A (nativeQ1Projection M A *ᵥ x) = restriction1 M A x := by
  rw [nativeQ1Projection_eq]
  exact restriction_imageProjection _ _ (restriction1_surjective M A)
    (restriction1_ker_eq_primitive M A) x

/-- Owner P representative existence follows from the actual generated
projection range, and supplies native differential transport on all vectors. -/
theorem nativeP1Projection_preimage (x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    ∃ w : (pushforwardComplex M A).C1, evaluation1 M A w = nativeP1Projection M A *ᵥ x := by
  have hx : nativeP1Projection M A *ᵥ x ∈ LinearMap.range (evaluation1 M A) := by
    rw [← nativeP1Projection_range]
    exact ⟨x, rfl⟩
  exact hx

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q absorption fixes every coordinate of the original dual-L target.
The property follows from the generated image, rather than being supplied. -/
theorem nativeQ1Projection_coordinate (z : (restrictionComplex M A).C1) :
    nativeQ1Projection M A *ᵥ (nativeQ1CoordinateEquiv M A z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      (nativeQ1CoordinateEquiv M A z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  apply imageProjection_fixes_range
  rw [← imageProjection_range]
  exact (nativeQ1CoordinateEquiv M A z).2

end Degree1

section Degree2
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (DegenerateFace M A)]
variable [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]

/-- E degree-2 P projection is generated from the original L transpose.
Its image is the existing Kan evaluation image, proved below from C4. -/
def nativeP2Projection : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  kernelProjection (primitiveL2Matrix M A)ᵀ

/-- Owner P projection equation exposes only the generated producer API. -/
theorem nativeP2Projection_eq : nativeP2Projection M A =
    kernelProjection (primitiveL2Matrix M A)ᵀ := rfl

/-- E degree-2 Q projection is generated from the original L columns.
The coordinate space represents actual dual L through original restriction. -/
def nativeQ2Projection : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  imageProjection (primitiveL2Matrix M A)

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q projection equation exposes the same rational table producer. -/
theorem nativeQ2Projection_eq : nativeQ2Projection M A =
    imageProjection (primitiveL2Matrix M A) := rfl

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E degree-2 evaluation image is the primitive transpose kernel.
The reverse inclusion is C4's input-generated original Kan preimage. -/
theorem evaluation2_range_eq_primitive :
    LinearMap.range (evaluation2 M A) = LinearMap.ker (primitiveL2Matrix M A)ᵀ.mulVecLin := by
  rw [evaluation2_range_eq_ker, restriction2_ker_eq_primitive]

/-- E degree-2 generated P image equals the original evaluation image
in both directions; the original P remains its independent Kan construction. -/
theorem nativeP2Projection_range :
    LinearMap.range (nativeP2Projection M A).mulVecLin = LinearMap.range (evaluation2 M A) := by
  rw [nativeP2Projection_eq, kernelProjection_range, evaluation2_range_eq_primitive]

/-- E degree-2 actual P coordinate equivalence, using original evaluation
and its input-derived full image/injectivity, without an extra certificate. -/
def nativeP2CoordinateEquiv : (pushforwardComplex M A).C2 ≃ₗ[ℚ]
    LinearMap.range (nativeP2Projection M A).mulVecLin :=
  embeddingCoordinateEquiv (primitiveL2Matrix M A) (evaluation2 M A)
    (evaluation2_injective M A) (evaluation2_range_eq_primitive M A)

/-- Owner native P representative API holds for every original P vector. -/
theorem nativeP2CoordinateEquiv_apply (x : (pushforwardComplex M A).C2) :
    (nativeP2CoordinateEquiv M A x : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) = evaluation2 M A x :=
  embeddingCoordinateEquiv_apply _ _ _ _ x

/-- Owner native P inverse representative API recovers every generated
coordinate through the same original evaluation, with all components. -/
theorem nativeP2CoordinateEquiv_symm_apply
    (x : LinearMap.range (nativeP2Projection M A).mulVecLin) :
    evaluation2 M A ((nativeP2CoordinateEquiv M A).symm x) = x.1 :=
  embeddingCoordinateEquiv_symm_apply _ _ _ _ x

/-- Owner native P left inverse recovers every original Kan vector. -/
theorem nativeP2CoordinateEquiv_left_inverse (x : (pushforwardComplex M A).C2) :
    (nativeP2CoordinateEquiv M A).symm (nativeP2CoordinateEquiv M A x) = x :=
  (nativeP2CoordinateEquiv M A).symm_apply_apply x

/-- Owner native P right inverse recovers every generated image coordinate. -/
theorem nativeP2CoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeP2Projection M A).mulVecLin) :
    nativeP2CoordinateEquiv M A ((nativeP2CoordinateEquiv M A).symm x) = x :=
  (nativeP2CoordinateEquiv M A).apply_symm_apply x

/-- E degree-2 computable projection rank equals the original P dimension.
No expected dimension, homology basis, or image certificate is an input. -/
theorem nativeP2Projection_rank :
    rationalMatrixRank (nativeP2Projection M A) = Module.finrank ℚ (pushforwardComplex M A).C2 := by
  rw [nativeP2Projection_eq]
  exact embeddingCoordinateEquiv_rank _ _ (evaluation2_injective M A)
    (evaluation2_range_eq_primitive M A)

/-- Owner P absorption fixes the original evaluation of every native vector. -/
theorem nativeP2Projection_evaluation (x : (pushforwardComplex M A).C2) :
    nativeP2Projection M A *ᵥ evaluation2 M A x = evaluation2 M A x := by
  rw [nativeP2Projection_eq]
  apply kernelProjection_fixes_ker
  rw [← evaluation2_range_eq_primitive]
  exact ⟨x, rfl⟩

/-- E degree-2 actual Q coordinate equivalence uses the original restriction
onto dual L and the same primitive kernel, both discharged from original M. -/
def nativeQ2CoordinateEquiv : (restrictionComplex M A).C2 ≃ₗ[ℚ]
    LinearMap.range (nativeQ2Projection M A).mulVecLin :=
  restrictionCoordinateEquiv (primitiveL2Matrix M A) (restriction2 M A)
    (restriction2_surjective M A) (restriction2_ker_eq_primitive M A)

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q representative API holds for every original fine vector. -/
theorem nativeQ2CoordinateEquiv_apply (x : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    (nativeQ2CoordinateEquiv M A (restriction2 M A x) : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeQ2Projection M A *ᵥ x :=
  restrictionCoordinateEquiv_apply _ _ _ _ x

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q inverse representative recovers every image coordinate
through actual restriction to the original L, without a new quotient object. -/
theorem nativeQ2CoordinateEquiv_symm_apply
    (x : LinearMap.range (nativeQ2Projection M A).mulVecLin) :
    (nativeQ2CoordinateEquiv M A).symm x = restriction2 M A x.1 :=
  restrictionCoordinateEquiv_symm_apply _ _ _ _ x

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q left inverse recovers every original dual-L vector. -/
theorem nativeQ2CoordinateEquiv_left_inverse (x : (restrictionComplex M A).C2) :
    (nativeQ2CoordinateEquiv M A).symm (nativeQ2CoordinateEquiv M A x) = x :=
  (nativeQ2CoordinateEquiv M A).symm_apply_apply x

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner native Q right inverse recovers every generated image coordinate. -/
theorem nativeQ2CoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeQ2Projection M A).mulVecLin) :
    nativeQ2CoordinateEquiv M A ((nativeQ2CoordinateEquiv M A).symm x) = x :=
  (nativeQ2CoordinateEquiv M A).apply_symm_apply x

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E degree-2 computable projection rank equals the original Q dimension.
The original restriction surjectivity and primitive kernel produce the result. -/
theorem nativeQ2Projection_rank :
    rationalMatrixRank (nativeQ2Projection M A) = Module.finrank ℚ (restrictionComplex M A).C2 := by
  rw [nativeQ2Projection_eq]
  exact restrictionCoordinateEquiv_rank _ _ (restriction2_surjective M A)
    (restriction2_ker_eq_primitive M A)

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q correction preserves actual restriction of every fine vector;
this is the full representative equation used for native Q differentials. -/
theorem restriction2_nativeQProjection (x : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction2 M A (nativeQ2Projection M A *ᵥ x) = restriction2 M A x := by
  rw [nativeQ2Projection_eq]
  exact restriction_imageProjection _ _ (restriction2_surjective M A)
    (restriction2_ker_eq_primitive M A) x

/-- Owner P representative existence follows from the actual generated
projection range, and supplies native differential transport on all vectors. -/
theorem nativeP2Projection_preimage (x : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    ∃ w : (pushforwardComplex M A).C2, evaluation2 M A w = nativeP2Projection M A *ᵥ x := by
  have hx : nativeP2Projection M A *ᵥ x ∈ LinearMap.range (evaluation2 M A) := by
    rw [← nativeP2Projection_range]
    exact ⟨x, rfl⟩
  exact hx

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner Q absorption fixes every coordinate of the original dual-L target.
The property follows from the generated image, rather than being supplied. -/
theorem nativeQ2Projection_coordinate (z : (restrictionComplex M A).C2) :
    nativeQ2Projection M A *ᵥ (nativeQ2CoordinateEquiv M A z : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      (nativeQ2CoordinateEquiv M A z : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  apply imageProjection_fixes_range
  rw [← imageProjection_range]
  exact (nativeQ2CoordinateEquiv M A z).2

end Degree2

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Projection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation0_range_eq_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0CoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0CoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0CoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0CoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0CoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection_evaluation
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0CoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0CoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0CoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0CoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0CoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Projection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.restriction0_nativeQProjection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection_preimage
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Projection_coordinate
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Projection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1_range_eq_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1CoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1CoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1CoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1CoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1CoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection_evaluation
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1CoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1CoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1CoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1CoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1CoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Projection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1_nativeQProjection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection_preimage
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Projection_coordinate
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Projection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2_range_eq_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2CoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2CoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2CoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2CoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2CoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection_evaluation
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2CoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2CoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2CoordinateEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2CoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2CoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Projection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.restriction2_nativeQProjection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection_preimage
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Projection_coordinate

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
