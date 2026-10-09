import ResearchLean.AG.AtlasCoefficientFiber.SecondHomologyCoordinateTransport
import ResearchLean.AG.AtlasDefectComposition.EndpointHomology
import ResearchLean.AG.AtlasCoefficientFiber.NativeDegreeDifferentials

/-!
# Generated harmonic coordinates for the original P/Q homology

Position: G-135 E native homology transport. All matrix conditions are derived
from the same primitive L projectors and original differential representations.

## Implementation notes

Original Kan P and dual-L Q are retained. Degree projector absorption is
proved on all vectors through the public differential evaluation formulas.
An arbitrary new matrix complex or supplied homology basis was rejected
because it would erase the original objects and their quotient classes.
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module Matrix
open RationalCoordinates TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
/-- The full range of an original equivalence followed by subtype is the
same entire coordinate submodule, not a selected set of representatives. -/
theorem range_subtype_coordinateEquiv {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (S : Submodule ℚ W) (e : V ≃ₗ[ℚ] S) :
    LinearMap.range (S.subtype.comp e.toLinearMap) = S := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    exact (e v).2
  · intro x hx
    obtain ⟨v, hv⟩ := e.surjective ⟨x, hx⟩
    exact ⟨v, congrArg Subtype.val hv⟩

variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

section Degree0
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]
variable [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- Original P degree 0 projection is symmetric by its generated producer. -/
theorem nativeP0Projection_symmetric : (nativeP0Projection M A)ᵀ = nativeP0Projection M A := by
  rw [nativeP0Projection_eq, kernelProjection_transpose]

/-- Original P degree 0 projection is idempotent, with no input certificate. -/
theorem nativeP0Projection_idempotent : nativeP0Projection M A * nativeP0Projection M A = nativeP0Projection M A := by
  rw [nativeP0Projection_eq, kernelProjection_mul_self]

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q degree 0 projection is symmetric by its generated producer. -/
theorem nativeQ0Projection_symmetric : (nativeQ0Projection M A)ᵀ = nativeQ0Projection M A := by
  rw [nativeQ0Projection_eq, imageProjection_transpose]

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q degree 0 projection is idempotent, with no input certificate. -/
theorem nativeQ0Projection_idempotent : nativeQ0Projection M A * nativeQ0Projection M A = nativeQ0Projection M A := by
  rw [nativeQ0Projection_eq, imageProjection_mul_self]

end Degree0

section Degree1
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]
variable [Fintype (MixedFace M A)]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- Original P degree 1 projection is symmetric by its generated producer. -/
theorem nativeP1Projection_symmetric : (nativeP1Projection M A)ᵀ = nativeP1Projection M A := by
  rw [nativeP1Projection_eq, kernelProjection_transpose]

/-- Original P degree 1 projection is idempotent, with no input certificate. -/
theorem nativeP1Projection_idempotent : nativeP1Projection M A * nativeP1Projection M A = nativeP1Projection M A := by
  rw [nativeP1Projection_eq, kernelProjection_mul_self]

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q degree 1 projection is symmetric by its generated producer. -/
theorem nativeQ1Projection_symmetric : (nativeQ1Projection M A)ᵀ = nativeQ1Projection M A := by
  rw [nativeQ1Projection_eq, imageProjection_transpose]

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q degree 1 projection is idempotent, with no input certificate. -/
theorem nativeQ1Projection_idempotent : nativeQ1Projection M A * nativeQ1Projection M A = nativeQ1Projection M A := by
  rw [nativeQ1Projection_eq, imageProjection_mul_self]

/-- Actual Q1 embedded in its generated coordinates, using the original
restriction equivalence and all original dual-L elements. -/
def nativeQ1Embedding : (restrictionComplex M A).C1 →ₗ[ℚ]
    (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :=
  (LinearMap.range (nativeQ1Projection M A).mulVecLin).subtype.comp
    (nativeQ1CoordinateEquiv M A).toLinearMap

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner embedding formula keeps every original Q cochain. -/
theorem nativeQ1Embedding_apply (z : (restrictionComplex M A).C1) :
    nativeQ1Embedding M A z = (nativeQ1CoordinateEquiv M A z :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := rfl

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q embedding is injective by its generated full equivalence. -/
theorem nativeQ1Embedding_injective : Function.Injective (nativeQ1Embedding M A) := by
  intro x y hxy
  apply (nativeQ1CoordinateEquiv M A).injective
  exact Subtype.ext hxy

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q embedding has the entire same generated degree image. -/
theorem nativeQ1Embedding_range : LinearMap.range (nativeQ1Embedding M A) =
    LinearMap.range (nativeQ1Projection M A).mulVecLin :=
  range_subtype_coordinateEquiv _ (nativeQ1CoordinateEquiv M A)

end Degree1

section Degree2
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (DegenerateFace M A)]
variable [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- Original P degree 2 projection is symmetric by its generated producer. -/
theorem nativeP2Projection_symmetric : (nativeP2Projection M A)ᵀ = nativeP2Projection M A := by
  rw [nativeP2Projection_eq, kernelProjection_transpose]

/-- Original P degree 2 projection is idempotent, with no input certificate. -/
theorem nativeP2Projection_idempotent : nativeP2Projection M A * nativeP2Projection M A = nativeP2Projection M A := by
  rw [nativeP2Projection_eq, kernelProjection_mul_self]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q degree 2 projection is symmetric by its generated producer. -/
theorem nativeQ2Projection_symmetric : (nativeQ2Projection M A)ᵀ = nativeQ2Projection M A := by
  rw [nativeQ2Projection_eq, imageProjection_transpose]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q degree 2 projection is idempotent, with no input certificate. -/
theorem nativeQ2Projection_idempotent : nativeQ2Projection M A * nativeQ2Projection M A = nativeQ2Projection M A := by
  rw [nativeQ2Projection_eq, imageProjection_mul_self]

/-- Actual Q2 embeds into the original primitive degree coordinate image. -/
def nativeQ2Embedding : (restrictionComplex M A).C2 →ₗ[ℚ]
    (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :=
  (LinearMap.range (nativeQ2Projection M A).mulVecLin).subtype.comp
    (nativeQ2CoordinateEquiv M A).toLinearMap

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner embedding formula retains every original dual-L degree-two cochain. -/
theorem nativeQ2Embedding_apply (z : (restrictionComplex M A).C2) :
    nativeQ2Embedding M A z = (nativeQ2CoordinateEquiv M A z :
      Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := rfl

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q2 embedding is injective by its generated full equivalence. -/
theorem nativeQ2Embedding_injective : Function.Injective (nativeQ2Embedding M A) := by
  intro x y hxy
  apply (nativeQ2CoordinateEquiv M A).injective
  exact Subtype.ext hxy

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q2 embedding covers the entire same primitive coordinate image. -/
theorem nativeQ2Embedding_range : LinearMap.range (nativeQ2Embedding M A) =
    LinearMap.range (nativeQ2Projection M A).mulVecLin :=
  range_subtype_coordinateEquiv _ (nativeQ2CoordinateEquiv M A)

end Degree2

section Differential0
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (MixedFace M A)]
variable [Fintype (VerticalEdge M A)]
variable [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- Original P differential 0 has left degree absorption on all vectors. -/
theorem nativeP0Differential_left_projection :
    nativeP1Projection M A * nativeP0Differential M A = nativeP0Differential M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  simp only [nativeP0Differential_mulVec]
  rw [Matrix.mulVec_mulVec, nativeP1Projection_idempotent]

/-- Original P differential 0 has right degree absorption on all vectors. -/
theorem nativeP0Differential_right_projection :
    nativeP0Differential M A * nativeP0Projection M A = nativeP0Differential M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  simp only [nativeP0Differential_mulVec]
  rw [Matrix.mulVec_mulVec, nativeP0Projection_idempotent]

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q differential 0 has left degree absorption on all vectors. -/
theorem nativeQ0Differential_left_projection :
    nativeQ1Projection M A * nativeQ0Differential M A = nativeQ0Differential M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  simp only [nativeQ0Differential_mulVec]
  rw [Matrix.mulVec_mulVec, nativeQ1Projection_idempotent]

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q differential 0 has right degree absorption on all vectors. -/
theorem nativeQ0Differential_right_projection :
    nativeQ0Differential M A * nativeQ0Projection M A = nativeQ0Differential M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  simp only [nativeQ0Differential_mulVec]
  rw [Matrix.mulVec_mulVec, nativeQ0Projection_idempotent]

/-- Original P incoming boundaries have exactly the image of the same
generated differential, transported by original evaluation on all vectors. -/
theorem nativeP0Differential_range : LinearMap.range (nativeP0Differential M A).mulVecLin =
    (LinearMap.range (pushforwardComplex M A).d0).map (evaluation1 M A) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨w, _hw, hd⟩ := nativeP0Differential_all_representatives M A y
    exact ⟨(pushforwardComplex M A).d0 w, ⟨w, rfl⟩, hd.symm⟩
  · rintro x ⟨y, ⟨w, rfl⟩, rfl⟩
    refine ⟨(nativeP0CoordinateEquiv M A w :
      Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ), ?_⟩
    have hd := nativeP0Differential_represents M A w
    rw [nativeP1CoordinateEquiv_apply] at hd
    exact hd

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q incoming boundaries are represented on the whole original
range, using restriction representatives and the same degree equivalences. -/
theorem nativeQ0Differential_range : LinearMap.range (nativeQ0Differential M A).mulVecLin =
    (LinearMap.range (restrictionComplex M A).d0).map (nativeQ1Embedding M A) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine ⟨(restrictionComplex M A).d0 (restriction0 M A y), ⟨restriction0 M A y, rfl⟩, ?_⟩
    rw [nativeQ1Embedding_apply]
    exact (nativeQ0Differential_all_representatives M A y).symm
  · rintro x ⟨y, ⟨w, rfl⟩, rfl⟩
    refine ⟨(nativeQ0CoordinateEquiv M A w :
      Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ), ?_⟩
    rw [nativeQ1Embedding_apply]
    exact nativeQ0Differential_represents M A w

end Differential0

section Differential1
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (DegenerateFace M A)]
variable [Fintype (MixedFace M A)]
variable [Fintype (VerticalEdge M A)]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- Original P differential 1 has left degree absorption on all vectors. -/
theorem nativeP1Differential_left_projection :
    nativeP2Projection M A * nativeP1Differential M A = nativeP1Differential M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  simp only [nativeP1Differential_mulVec]
  rw [Matrix.mulVec_mulVec, nativeP2Projection_idempotent]

/-- Original P differential 1 has right degree absorption on all vectors. -/
theorem nativeP1Differential_right_projection :
    nativeP1Differential M A * nativeP1Projection M A = nativeP1Differential M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  simp only [nativeP1Differential_mulVec]
  rw [Matrix.mulVec_mulVec, nativeP1Projection_idempotent]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q differential 1 has left degree absorption on all vectors. -/
theorem nativeQ1Differential_left_projection :
    nativeQ2Projection M A * nativeQ1Differential M A = nativeQ1Differential M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  simp only [nativeQ1Differential_mulVec]
  rw [Matrix.mulVec_mulVec, nativeQ2Projection_idempotent]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q differential 1 has right degree absorption on all vectors. -/
theorem nativeQ1Differential_right_projection :
    nativeQ1Differential M A * nativeQ1Projection M A = nativeQ1Differential M A := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec]
  simp only [nativeQ1Differential_mulVec]
  rw [Matrix.mulVec_mulVec, nativeQ1Projection_idempotent]

/-- Original P cycles are exactly the same generated outgoing equations,
by actual evaluation compatibility and its original degree-two injectivity. -/
theorem nativeP1Differential_cycle_iff (x : (pushforwardComplex M A).C1) :
    nativeP1Differential M A *ᵥ evaluation1 M A x = 0 ↔ (pushforwardComplex M A).d1 x = 0 := by
  have hd := nativeP1Differential_represents M A x
  rw [nativeP1CoordinateEquiv_apply, nativeP2CoordinateEquiv_apply] at hd
  rw [hd]
  constructor
  · intro hx
    apply evaluation2_injective M A
    rw [map_zero]
    exact hx
  · intro hx
    rw [hx, map_zero]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q cycles are exactly the generated outgoing equations, with
no supplied compatibility or homology-basis premise. -/
theorem nativeQ1Differential_cycle_iff (x : (restrictionComplex M A).C1) :
    nativeQ1Differential M A *ᵥ nativeQ1Embedding M A x = 0 ↔ (restrictionComplex M A).d1 x = 0 := by
  rw [nativeQ1Embedding_apply, nativeQ1Differential_represents]
  constructor
  · intro hx
    apply (nativeQ2CoordinateEquiv M A).injective
    apply Subtype.ext
    rw [map_zero]
    exact hx
  · intro hx
    rw [hx, map_zero]
    rfl

/-- Original P degree-one differential has exactly the same top boundary
image, with every original cochain and fine representative retained. -/
theorem nativeP1Differential_range : LinearMap.range (nativeP1Differential M A).mulVecLin =
    (LinearMap.range (pushforwardComplex M A).d1).map (evaluation2 M A) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨w, _hw, hd⟩ := nativeP1Differential_all_representatives M A y
    exact ⟨(pushforwardComplex M A).d1 w, ⟨w, rfl⟩, hd.symm⟩
  · rintro x ⟨y, ⟨w, rfl⟩, rfl⟩
    refine ⟨(nativeP1CoordinateEquiv M A w :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ), ?_⟩
    have hd := nativeP1Differential_represents M A w
    rw [nativeP2CoordinateEquiv_apply] at hd
    exact hd

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Original Q top boundaries have the same full generated matrix image. -/
theorem nativeQ1Differential_range : LinearMap.range (nativeQ1Differential M A).mulVecLin =
    (LinearMap.range (restrictionComplex M A).d1).map (nativeQ2Embedding M A) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine ⟨(restrictionComplex M A).d1 (restriction1 M A y), ⟨restriction1 M A y, rfl⟩, ?_⟩
    rw [nativeQ2Embedding_apply]
    exact (nativeQ1Differential_all_representatives M A y).symm
  · rintro x ⟨y, ⟨w, rfl⟩, rfl⟩
    refine ⟨(nativeQ1CoordinateEquiv M A w :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ), ?_⟩
    rw [nativeQ2Embedding_apply]
    exact nativeQ1Differential_represents M A w

end Differential1

section HomologyP1
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]
variable [Fintype (MixedFace M A)]
variable [Fintype (DegenerateFace M A)]
variable [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- The executable same original P H1 projector retains its degree image
and removes incoming boundaries and outgoing transpose images. -/
def nativeP1HomologyProjection : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  harmonicProjection (nativeP1Projection M A) (nativeP0Differential M A) (nativeP1Differential M A)

/-- Owner producer formula contains only original degree/differential tables. -/
theorem nativeP1HomologyProjection_eq : nativeP1HomologyProjection M A =
    harmonicProjection (nativeP1Projection M A) (nativeP0Differential M A) (nativeP1Differential M A) := rfl

/-- Full coordinates for the original P H1 quotient; every general transport
condition is discharged from the same original generated maps. -/
def nativeP1HomologyCoordinateEquiv : (pushforwardComplex M A).H1 ≃ₗ[ℚ]
    LinearMap.range (nativeP1HomologyProjection M A).mulVecLin :=
  homologyCoordinateEquiv (pushforwardComplex M A) (evaluation1 M A) (nativeP1Projection M A)
    (nativeP0Differential M A) (nativeP1Differential M A)
    (evaluation1_injective M A) (nativeP1Projection_symmetric M A) (nativeP1Projection_idempotent M A)
    (nativeP0Differential_left_projection M A) (nativeP1Differential_right_projection M A)
    (nativeP1Differential_mul_P0 M A) ((nativeP1Projection_range M A).symm)
    (nativeP0Differential_range M A) (nativeP1Differential_cycle_iff M A)

/-- Owner formula represents every original P cocycle quotient class. -/
theorem nativeP1HomologyCoordinateEquiv_mk (z : LinearMap.ker (pushforwardComplex M A).d1) :
    (nativeP1HomologyCoordinateEquiv M A (Submodule.Quotient.mk z) : (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) → ℚ) =
      nativeP1HomologyProjection M A *ᵥ evaluation1 M A z.1 :=
  homologyCoordinateEquiv_mk (pushforwardComplex M A) (evaluation1 M A) (nativeP1Projection M A)
    (nativeP0Differential M A) (nativeP1Differential M A)
    (evaluation1_injective M A) (nativeP1Projection_symmetric M A) (nativeP1Projection_idempotent M A)
    (nativeP0Differential_left_projection M A) (nativeP1Differential_right_projection M A)
    (nativeP1Differential_mul_P0 M A) ((nativeP1Projection_range M A).symm)
    (nativeP0Differential_range M A) (nativeP1Differential_cycle_iff M A) z

/-- Every original P H1 class is recovered by the full inverse. -/
theorem nativeP1HomologyCoordinateEquiv_left_inverse (x : (pushforwardComplex M A).H1) :
    (nativeP1HomologyCoordinateEquiv M A).symm (nativeP1HomologyCoordinateEquiv M A x) = x :=
  (nativeP1HomologyCoordinateEquiv M A).symm_apply_apply x

/-- Every generated P harmonic coordinate is recovered by the forward map. -/
theorem nativeP1HomologyCoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeP1HomologyProjection M A).mulVecLin) :
    nativeP1HomologyCoordinateEquiv M A ((nativeP1HomologyCoordinateEquiv M A).symm x) = x :=
  (nativeP1HomologyCoordinateEquiv M A).apply_symm_apply x

/-- Inverse coordinates preserve the same original P cycle class. -/
theorem nativeP1HomologyCoordinateEquiv_symm_representative
    (x : LinearMap.range (nativeP1HomologyProjection M A).mulVecLin)
    (z : LinearMap.ker (pushforwardComplex M A).d1) (hz : evaluation1 M A z.1 = x.1) :
    (nativeP1HomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  homologyCoordinateEquiv_symm_representative (pushforwardComplex M A) (evaluation1 M A) (nativeP1Projection M A)
    (nativeP0Differential M A) (nativeP1Differential M A)
    (evaluation1_injective M A) (nativeP1Projection_symmetric M A) (nativeP1Projection_idempotent M A)
    (nativeP0Differential_left_projection M A) (nativeP1Differential_right_projection M A)
    (nativeP1Differential_mul_P0 M A) ((nativeP1Projection_range M A).symm)
    (nativeP0Differential_range M A) (nativeP1Differential_cycle_iff M A) x z hz

set_option synthInstance.maxHeartbeats 200000 in
/-- Computed P harmonic rank equals the original native H1 dimension. -/
theorem nativeP1HomologyProjection_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank
      (nativeP1HomologyProjection M A) = Module.finrank ℚ (pushforwardComplex M A).H1 :=
  homologyCoordinateEquiv_rank (pushforwardComplex M A) (evaluation1 M A) (nativeP1Projection M A)
    (nativeP0Differential M A) (nativeP1Differential M A)
    (evaluation1_injective M A) (nativeP1Projection_symmetric M A) (nativeP1Projection_idempotent M A)
    (nativeP0Differential_left_projection M A) (nativeP1Differential_right_projection M A)
    (nativeP1Differential_mul_P0 M A) ((nativeP1Projection_range M A).symm)
    (nativeP0Differential_range M A) (nativeP1Differential_cycle_iff M A)

/-- The original P harmonic projector fixes every generated coordinate. -/
theorem nativeP1HomologyProjection_mul_self :
    nativeP1HomologyProjection M A * nativeP1HomologyProjection M A = nativeP1HomologyProjection M A := by
  rw [nativeP1HomologyProjection_eq]
  exact harmonicProjection_mul_self (nativeP1Projection M A)
    (nativeP0Differential M A) (nativeP1Differential M A)
    (nativeP1Projection_symmetric M A) (nativeP1Projection_idempotent M A)
    (nativeP0Differential_left_projection M A) (nativeP1Differential_right_projection M A)
    (nativeP1Differential_mul_P0 M A)

/-- Every P inverse harmonic coordinate has an original closed representative
with exactly that embedding and the same original quotient class. -/
theorem nativeP1HomologyCoordinateEquiv_inverse_cycle
    (x : LinearMap.range (nativeP1HomologyProjection M A).mulVecLin) :
    ∃ z : LinearMap.ker (pushforwardComplex M A).d1, evaluation1 M A z.1 = x.1 ∧
      (nativeP1HomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  homologyCoordinateEquiv_inverse_cycle (pushforwardComplex M A) (evaluation1 M A) (nativeP1Projection M A)
    (nativeP0Differential M A) (nativeP1Differential M A)
    (evaluation1_injective M A) (nativeP1Projection_symmetric M A) (nativeP1Projection_idempotent M A)
    (nativeP0Differential_left_projection M A) (nativeP1Differential_right_projection M A)
    (nativeP1Differential_mul_P0 M A) ((nativeP1Projection_range M A).symm)
    (nativeP0Differential_range M A) (nativeP1Differential_cycle_iff M A) x

set_option synthInstance.maxHeartbeats 200000 in
/-- Original standard P H1 has the same native generated harmonic coordinates. -/
def nativeP1StandardHomologyCoordinateEquiv :
    (zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ≃ₗ[ℚ]
      LinearMap.range (nativeP1HomologyProjection M A).mulVecLin :=
  (oldH1Equiv (pushforwardComplex M A)).symm.trans (nativeP1HomologyCoordinateEquiv M A)

/-- Owner standard coordinate formula retains the original-to-standard transport. -/
theorem nativeP1StandardHomologyCoordinateEquiv_apply
    (x : (zeroExtension (pushforwardComplex M A)).homology (1 : ℤ)) :
    nativeP1StandardHomologyCoordinateEquiv M A x =
      nativeP1HomologyCoordinateEquiv M A ((oldH1Equiv (pushforwardComplex M A)).symm x) := rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- Owner standard H1 formula preserves every original P cocycle class. -/
theorem nativeP1StandardHomologyCoordinateEquiv_mk (z : LinearMap.ker (pushforwardComplex M A).d1) :
    (nativeP1StandardHomologyCoordinateEquiv M A
      (oldH1Equiv (pushforwardComplex M A) (Submodule.Quotient.mk z)) :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeP1HomologyProjection M A *ᵥ evaluation1 M A z.1 := by
  rw [nativeP1StandardHomologyCoordinateEquiv_apply, LinearEquiv.symm_apply_apply]
  exact nativeP1HomologyCoordinateEquiv_mk M A z

end HomologyP1

section HomologyQ1
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]
variable [Fintype (MixedFace M A)]
variable [Fintype (DegenerateFace M A)]
variable [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- The executable same original Q H1 projector retains its degree image
and removes incoming boundaries and outgoing transpose images. -/
def nativeQ1HomologyProjection : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  harmonicProjection (nativeQ1Projection M A) (nativeQ0Differential M A) (nativeQ1Differential M A)

/-- Owner producer formula contains only original degree/differential tables. -/
theorem nativeQ1HomologyProjection_eq : nativeQ1HomologyProjection M A =
    harmonicProjection (nativeQ1Projection M A) (nativeQ0Differential M A) (nativeQ1Differential M A) := rfl

/-- Full coordinates for the original Q H1 quotient; every general transport
condition is discharged from the same original generated maps. -/
def nativeQ1HomologyCoordinateEquiv : (restrictionComplex M A).H1 ≃ₗ[ℚ]
    LinearMap.range (nativeQ1HomologyProjection M A).mulVecLin :=
  homologyCoordinateEquiv (restrictionComplex M A) (nativeQ1Embedding M A) (nativeQ1Projection M A)
    (nativeQ0Differential M A) (nativeQ1Differential M A)
    (nativeQ1Embedding_injective M A) (nativeQ1Projection_symmetric M A) (nativeQ1Projection_idempotent M A)
    (nativeQ0Differential_left_projection M A) (nativeQ1Differential_right_projection M A)
    (nativeQ1Differential_mul_Q0 M A) (nativeQ1Embedding_range M A)
    (nativeQ0Differential_range M A) (nativeQ1Differential_cycle_iff M A)

/-- Owner formula represents every original Q cocycle quotient class. -/
theorem nativeQ1HomologyCoordinateEquiv_mk (z : LinearMap.ker (restrictionComplex M A).d1) :
    (nativeQ1HomologyCoordinateEquiv M A (Submodule.Quotient.mk z) : (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) → ℚ) =
      nativeQ1HomologyProjection M A *ᵥ nativeQ1Embedding M A z.1 :=
  homologyCoordinateEquiv_mk (restrictionComplex M A) (nativeQ1Embedding M A) (nativeQ1Projection M A)
    (nativeQ0Differential M A) (nativeQ1Differential M A)
    (nativeQ1Embedding_injective M A) (nativeQ1Projection_symmetric M A) (nativeQ1Projection_idempotent M A)
    (nativeQ0Differential_left_projection M A) (nativeQ1Differential_right_projection M A)
    (nativeQ1Differential_mul_Q0 M A) (nativeQ1Embedding_range M A)
    (nativeQ0Differential_range M A) (nativeQ1Differential_cycle_iff M A) z

/-- Every original Q H1 class is recovered by the full inverse. -/
theorem nativeQ1HomologyCoordinateEquiv_left_inverse (x : (restrictionComplex M A).H1) :
    (nativeQ1HomologyCoordinateEquiv M A).symm (nativeQ1HomologyCoordinateEquiv M A x) = x :=
  (nativeQ1HomologyCoordinateEquiv M A).symm_apply_apply x

/-- Every generated Q harmonic coordinate is recovered by the forward map. -/
theorem nativeQ1HomologyCoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeQ1HomologyProjection M A).mulVecLin) :
    nativeQ1HomologyCoordinateEquiv M A ((nativeQ1HomologyCoordinateEquiv M A).symm x) = x :=
  (nativeQ1HomologyCoordinateEquiv M A).apply_symm_apply x

/-- Inverse coordinates preserve the same original Q cycle class. -/
theorem nativeQ1HomologyCoordinateEquiv_symm_representative
    (x : LinearMap.range (nativeQ1HomologyProjection M A).mulVecLin)
    (z : LinearMap.ker (restrictionComplex M A).d1) (hz : nativeQ1Embedding M A z.1 = x.1) :
    (nativeQ1HomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  homologyCoordinateEquiv_symm_representative (restrictionComplex M A) (nativeQ1Embedding M A) (nativeQ1Projection M A)
    (nativeQ0Differential M A) (nativeQ1Differential M A)
    (nativeQ1Embedding_injective M A) (nativeQ1Projection_symmetric M A) (nativeQ1Projection_idempotent M A)
    (nativeQ0Differential_left_projection M A) (nativeQ1Differential_right_projection M A)
    (nativeQ1Differential_mul_Q0 M A) (nativeQ1Embedding_range M A)
    (nativeQ0Differential_range M A) (nativeQ1Differential_cycle_iff M A) x z hz

/-- Computed Q harmonic rank equals the original native H1 dimension. -/
theorem nativeQ1HomologyProjection_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank
      (nativeQ1HomologyProjection M A) = Module.finrank ℚ (restrictionComplex M A).H1 :=
  homologyCoordinateEquiv_rank (restrictionComplex M A) (nativeQ1Embedding M A) (nativeQ1Projection M A)
    (nativeQ0Differential M A) (nativeQ1Differential M A)
    (nativeQ1Embedding_injective M A) (nativeQ1Projection_symmetric M A) (nativeQ1Projection_idempotent M A)
    (nativeQ0Differential_left_projection M A) (nativeQ1Differential_right_projection M A)
    (nativeQ1Differential_mul_Q0 M A) (nativeQ1Embedding_range M A)
    (nativeQ0Differential_range M A) (nativeQ1Differential_cycle_iff M A)

/-- The original Q harmonic projector fixes every generated coordinate. -/
theorem nativeQ1HomologyProjection_mul_self :
    nativeQ1HomologyProjection M A * nativeQ1HomologyProjection M A = nativeQ1HomologyProjection M A := by
  rw [nativeQ1HomologyProjection_eq]
  exact harmonicProjection_mul_self (nativeQ1Projection M A)
    (nativeQ0Differential M A) (nativeQ1Differential M A)
    (nativeQ1Projection_symmetric M A) (nativeQ1Projection_idempotent M A)
    (nativeQ0Differential_left_projection M A) (nativeQ1Differential_right_projection M A)
    (nativeQ1Differential_mul_Q0 M A)

/-- Every Q inverse harmonic coordinate has an original closed representative
with exactly that embedding and the same original quotient class. -/
theorem nativeQ1HomologyCoordinateEquiv_inverse_cycle
    (x : LinearMap.range (nativeQ1HomologyProjection M A).mulVecLin) :
    ∃ z : LinearMap.ker (restrictionComplex M A).d1, nativeQ1Embedding M A z.1 = x.1 ∧
      (nativeQ1HomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  homologyCoordinateEquiv_inverse_cycle (restrictionComplex M A) (nativeQ1Embedding M A) (nativeQ1Projection M A)
    (nativeQ0Differential M A) (nativeQ1Differential M A)
    (nativeQ1Embedding_injective M A) (nativeQ1Projection_symmetric M A) (nativeQ1Projection_idempotent M A)
    (nativeQ0Differential_left_projection M A) (nativeQ1Differential_right_projection M A)
    (nativeQ1Differential_mul_Q0 M A) (nativeQ1Embedding_range M A)
    (nativeQ0Differential_range M A) (nativeQ1Differential_cycle_iff M A) x

/-- Original standard Q H1 has the same native generated harmonic coordinates. -/
def nativeQ1StandardHomologyCoordinateEquiv :
    (zeroExtension (restrictionComplex M A)).homology (1 : ℤ) ≃ₗ[ℚ]
      LinearMap.range (nativeQ1HomologyProjection M A).mulVecLin :=
  (oldH1Equiv (restrictionComplex M A)).symm.trans (nativeQ1HomologyCoordinateEquiv M A)

/-- Owner standard coordinate formula retains the original-to-standard transport. -/
theorem nativeQ1StandardHomologyCoordinateEquiv_apply
    (x : (zeroExtension (restrictionComplex M A)).homology (1 : ℤ)) :
    nativeQ1StandardHomologyCoordinateEquiv M A x =
      nativeQ1HomologyCoordinateEquiv M A ((oldH1Equiv (restrictionComplex M A)).symm x) := rfl

/-- Owner standard H1 formula preserves every original Q cocycle class. -/
theorem nativeQ1StandardHomologyCoordinateEquiv_mk (z : LinearMap.ker (restrictionComplex M A).d1) :
    (nativeQ1StandardHomologyCoordinateEquiv M A
      (oldH1Equiv (restrictionComplex M A) (Submodule.Quotient.mk z)) :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeQ1HomologyProjection M A *ᵥ nativeQ1Embedding M A z.1 := by
  rw [nativeQ1StandardHomologyCoordinateEquiv_apply, LinearEquiv.symm_apply_apply]
  exact nativeQ1HomologyCoordinateEquiv_mk M A z

end HomologyQ1

section HomologyP2
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]
variable [Fintype (MixedFace M A)]
variable [Fintype (DegenerateFace M A)]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- Executable original P top projector removes its incoming image only. -/
def nativeP2HomologyProjection : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  secondHomologyProjection (nativeP2Projection M A) (nativeP1Differential M A)

/-- Owner producer formula uses the same original degree and differential. -/
theorem nativeP2HomologyProjection_eq : nativeP2HomologyProjection M A =
    secondHomologyProjection (nativeP2Projection M A) (nativeP1Differential M A) := rfl

/-- Full coordinates for the original P top quotient with all general
conditions discharged from original evaluation or restriction. -/
def nativeP2HomologyCoordinateEquiv :
    ((pushforwardComplex M A).C2 ⧸ LinearMap.range (pushforwardComplex M A).d1) ≃ₗ[ℚ]
      LinearMap.range (nativeP2HomologyProjection M A).mulVecLin :=
  secondHomologyCoordinateEquiv ((pushforwardComplex M A).d1) (evaluation2 M A) (nativeP2Projection M A)
    (nativeP1Differential M A) (evaluation2_injective M A)
    (nativeP2Projection_symmetric M A) (nativeP2Projection_idempotent M A)
    (nativeP1Differential_left_projection M A) ((nativeP2Projection_range M A).symm) (nativeP1Differential_range M A)

/-- Owner formula preserves every original P top quotient representative. -/
theorem nativeP2HomologyCoordinateEquiv_mk (z : (pushforwardComplex M A).C2) :
    (nativeP2HomologyCoordinateEquiv M A (Submodule.Quotient.mk z) : (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) → ℚ) =
      nativeP2HomologyProjection M A *ᵥ evaluation2 M A z :=
  secondHomologyCoordinateEquiv_mk ((pushforwardComplex M A).d1) (evaluation2 M A) (nativeP2Projection M A)
    (nativeP1Differential M A) (evaluation2_injective M A)
    (nativeP2Projection_symmetric M A) (nativeP2Projection_idempotent M A)
    (nativeP1Differential_left_projection M A) ((nativeP2Projection_range M A).symm) (nativeP1Differential_range M A) z

/-- Every original P top quotient class is recovered by the inverse. -/
theorem nativeP2HomologyCoordinateEquiv_left_inverse
    (x : (pushforwardComplex M A).C2 ⧸ LinearMap.range (pushforwardComplex M A).d1) :
    (nativeP2HomologyCoordinateEquiv M A).symm (nativeP2HomologyCoordinateEquiv M A x) = x :=
  (nativeP2HomologyCoordinateEquiv M A).symm_apply_apply x

/-- Every generated P top coordinate is recovered by the forward map. -/
theorem nativeP2HomologyCoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeP2HomologyProjection M A).mulVecLin) :
    nativeP2HomologyCoordinateEquiv M A ((nativeP2HomologyCoordinateEquiv M A).symm x) = x :=
  (nativeP2HomologyCoordinateEquiv M A).apply_symm_apply x

/-- Original P representative with the same top coordinate gives the inverse class. -/
theorem nativeP2HomologyCoordinateEquiv_symm_representative
    (x : LinearMap.range (nativeP2HomologyProjection M A).mulVecLin) (z : (pushforwardComplex M A).C2)
    (hz : evaluation2 M A z = x.1) :
    (nativeP2HomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  secondHomologyCoordinateEquiv_symm_representative ((pushforwardComplex M A).d1) (evaluation2 M A) (nativeP2Projection M A)
    (nativeP1Differential M A) (evaluation2_injective M A)
    (nativeP2Projection_symmetric M A) (nativeP2Projection_idempotent M A)
    (nativeP1Differential_left_projection M A) ((nativeP2Projection_range M A).symm) (nativeP1Differential_range M A) x z hz

/-- Computed P top rank equals the original incoming-range quotient dimension. -/
theorem nativeP2HomologyProjection_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeP2HomologyProjection M A) =
      Module.finrank ℚ ((pushforwardComplex M A).C2 ⧸ LinearMap.range (pushforwardComplex M A).d1) :=
  secondHomologyCoordinateEquiv_rank ((pushforwardComplex M A).d1) (evaluation2 M A) (nativeP2Projection M A)
    (nativeP1Differential M A) (evaluation2_injective M A)
    (nativeP2Projection_symmetric M A) (nativeP2Projection_idempotent M A)
    (nativeP1Differential_left_projection M A) ((nativeP2Projection_range M A).symm) (nativeP1Differential_range M A)

/-- Original standard P H2 has the same generated coordinates through the
accepted standard-to-original quotient equivalence, retaining the original object. -/
def nativeP2StandardHomologyCoordinateEquiv :
    (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ) ≃ₗ[ℚ]
      LinearMap.range (nativeP2HomologyProjection M A).mulVecLin :=
  (oldH2Equiv (pushforwardComplex M A)).symm.trans (nativeP2HomologyCoordinateEquiv M A)

/-- Owner standard representative formula agrees with every original top class. -/
theorem nativeP2StandardHomologyCoordinateEquiv_mk (z : (pushforwardComplex M A).C2) :
    (nativeP2StandardHomologyCoordinateEquiv M A
      (oldH2Equiv (pushforwardComplex M A) (Submodule.Quotient.mk z)) : (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) → ℚ) =
      nativeP2HomologyProjection M A *ᵥ evaluation2 M A z := by
  simp only [nativeP2StandardHomologyCoordinateEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, nativeP2HomologyCoordinateEquiv_mk]

/-- Original P top projection fixes every generated top coordinate. -/
theorem nativeP2HomologyProjection_mul_self :
    nativeP2HomologyProjection M A * nativeP2HomologyProjection M A = nativeP2HomologyProjection M A := by
  rw [nativeP2HomologyProjection_eq]
  exact secondHomologyProjection_mul_self (nativeP2Projection M A) (nativeP1Differential M A)
    (nativeP2Projection_symmetric M A) (nativeP2Projection_idempotent M A)
    (nativeP1Differential_left_projection M A)

/-- Owner standard top coordinates retain the original quotient transport. -/
theorem nativeP2StandardHomologyCoordinateEquiv_apply
    (x : (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ)) :
    nativeP2StandardHomologyCoordinateEquiv M A x =
      nativeP2HomologyCoordinateEquiv M A ((oldH2Equiv (pushforwardComplex M A)).symm x) := rfl

/-- Every inverse P H2 coordinate has an original representative, generated
from the original evaluation range rather than supplied as a certificate. -/
theorem nativeP2HomologyCoordinateEquiv_inverse_representative
    (x : LinearMap.range (nativeP2HomologyProjection M A).mulVecLin) :
    ∃ z : (pushforwardComplex M A).C2, evaluation2 M A z = x.1 ∧
      (nativeP2HomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  secondHomologyCoordinateEquiv_inverse_representative (pushforwardComplex M A).d1
    (evaluation2 M A) (nativeP2Projection M A) (nativeP1Differential M A)
    (evaluation2_injective M A) (nativeP2Projection_symmetric M A)
    (nativeP2Projection_idempotent M A) (nativeP1Differential_left_projection M A)
    ((nativeP2Projection_range M A).symm) (nativeP1Differential_range M A) x

end HomologyP2

section HomologyQ2
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]
variable [Fintype (MixedFace M A)]
variable [Fintype (DegenerateFace M A)]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
/-- Executable original Q top projector removes its incoming image only. -/
def nativeQ2HomologyProjection : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  secondHomologyProjection (nativeQ2Projection M A) (nativeQ1Differential M A)

/-- Owner producer formula uses the same original degree and differential. -/
theorem nativeQ2HomologyProjection_eq : nativeQ2HomologyProjection M A =
    secondHomologyProjection (nativeQ2Projection M A) (nativeQ1Differential M A) := rfl

/-- Full coordinates for the original Q top quotient with all general
conditions discharged from original evaluation or restriction. -/
def nativeQ2HomologyCoordinateEquiv :
    ((restrictionComplex M A).C2 ⧸ LinearMap.range (restrictionComplex M A).d1) ≃ₗ[ℚ]
      LinearMap.range (nativeQ2HomologyProjection M A).mulVecLin :=
  secondHomologyCoordinateEquiv ((restrictionComplex M A).d1) (nativeQ2Embedding M A) (nativeQ2Projection M A)
    (nativeQ1Differential M A) (nativeQ2Embedding_injective M A)
    (nativeQ2Projection_symmetric M A) (nativeQ2Projection_idempotent M A)
    (nativeQ1Differential_left_projection M A) (nativeQ2Embedding_range M A) (nativeQ1Differential_range M A)

/-- Owner formula preserves every original Q top quotient representative. -/
theorem nativeQ2HomologyCoordinateEquiv_mk (z : (restrictionComplex M A).C2) :
    (nativeQ2HomologyCoordinateEquiv M A (Submodule.Quotient.mk z) : (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) → ℚ) =
      nativeQ2HomologyProjection M A *ᵥ nativeQ2Embedding M A z :=
  secondHomologyCoordinateEquiv_mk ((restrictionComplex M A).d1) (nativeQ2Embedding M A) (nativeQ2Projection M A)
    (nativeQ1Differential M A) (nativeQ2Embedding_injective M A)
    (nativeQ2Projection_symmetric M A) (nativeQ2Projection_idempotent M A)
    (nativeQ1Differential_left_projection M A) (nativeQ2Embedding_range M A) (nativeQ1Differential_range M A) z

/-- Every original Q top quotient class is recovered by the inverse. -/
theorem nativeQ2HomologyCoordinateEquiv_left_inverse
    (x : (restrictionComplex M A).C2 ⧸ LinearMap.range (restrictionComplex M A).d1) :
    (nativeQ2HomologyCoordinateEquiv M A).symm (nativeQ2HomologyCoordinateEquiv M A x) = x :=
  (nativeQ2HomologyCoordinateEquiv M A).symm_apply_apply x

/-- Every generated Q top coordinate is recovered by the forward map. -/
theorem nativeQ2HomologyCoordinateEquiv_right_inverse
    (x : LinearMap.range (nativeQ2HomologyProjection M A).mulVecLin) :
    nativeQ2HomologyCoordinateEquiv M A ((nativeQ2HomologyCoordinateEquiv M A).symm x) = x :=
  (nativeQ2HomologyCoordinateEquiv M A).apply_symm_apply x

/-- Original Q representative with the same top coordinate gives the inverse class. -/
theorem nativeQ2HomologyCoordinateEquiv_symm_representative
    (x : LinearMap.range (nativeQ2HomologyProjection M A).mulVecLin) (z : (restrictionComplex M A).C2)
    (hz : nativeQ2Embedding M A z = x.1) :
    (nativeQ2HomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  secondHomologyCoordinateEquiv_symm_representative ((restrictionComplex M A).d1) (nativeQ2Embedding M A) (nativeQ2Projection M A)
    (nativeQ1Differential M A) (nativeQ2Embedding_injective M A)
    (nativeQ2Projection_symmetric M A) (nativeQ2Projection_idempotent M A)
    (nativeQ1Differential_left_projection M A) (nativeQ2Embedding_range M A) (nativeQ1Differential_range M A) x z hz

/-- Computed Q top rank equals the original incoming-range quotient dimension. -/
theorem nativeQ2HomologyProjection_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeQ2HomologyProjection M A) =
      Module.finrank ℚ ((restrictionComplex M A).C2 ⧸ LinearMap.range (restrictionComplex M A).d1) :=
  secondHomologyCoordinateEquiv_rank ((restrictionComplex M A).d1) (nativeQ2Embedding M A) (nativeQ2Projection M A)
    (nativeQ1Differential M A) (nativeQ2Embedding_injective M A)
    (nativeQ2Projection_symmetric M A) (nativeQ2Projection_idempotent M A)
    (nativeQ1Differential_left_projection M A) (nativeQ2Embedding_range M A) (nativeQ1Differential_range M A)

/-- Original standard Q H2 has the same generated coordinates through the
accepted standard-to-original quotient equivalence, retaining the original object. -/
def nativeQ2StandardHomologyCoordinateEquiv :
    (zeroExtension (restrictionComplex M A)).homology (2 : ℤ) ≃ₗ[ℚ]
      LinearMap.range (nativeQ2HomologyProjection M A).mulVecLin :=
  (oldH2Equiv (restrictionComplex M A)).symm.trans (nativeQ2HomologyCoordinateEquiv M A)

/-- Owner standard representative formula agrees with every original top class. -/
theorem nativeQ2StandardHomologyCoordinateEquiv_mk (z : (restrictionComplex M A).C2) :
    (nativeQ2StandardHomologyCoordinateEquiv M A
      (oldH2Equiv (restrictionComplex M A) (Submodule.Quotient.mk z)) : (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) → ℚ) =
      nativeQ2HomologyProjection M A *ᵥ nativeQ2Embedding M A z := by
  simp only [nativeQ2StandardHomologyCoordinateEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  exact nativeQ2HomologyCoordinateEquiv_mk M A z

/-- Original Q top projection fixes every generated top coordinate. -/
theorem nativeQ2HomologyProjection_mul_self :
    nativeQ2HomologyProjection M A * nativeQ2HomologyProjection M A = nativeQ2HomologyProjection M A := by
  rw [nativeQ2HomologyProjection_eq]
  exact secondHomologyProjection_mul_self (nativeQ2Projection M A) (nativeQ1Differential M A)
    (nativeQ2Projection_symmetric M A) (nativeQ2Projection_idempotent M A)
    (nativeQ1Differential_left_projection M A)

/-- Owner standard top coordinates retain the original quotient transport. -/
theorem nativeQ2StandardHomologyCoordinateEquiv_apply
    (x : (zeroExtension (restrictionComplex M A)).homology (2 : ℤ)) :
    nativeQ2StandardHomologyCoordinateEquiv M A x =
      nativeQ2HomologyCoordinateEquiv M A ((oldH2Equiv (restrictionComplex M A)).symm x) := rfl

/-- Every inverse Q H2 coordinate has an original dual-L representative,
generated from the original full restriction coordinate isomorphism. -/
theorem nativeQ2HomologyCoordinateEquiv_inverse_representative
    (x : LinearMap.range (nativeQ2HomologyProjection M A).mulVecLin) :
    ∃ z : (restrictionComplex M A).C2, nativeQ2Embedding M A z = x.1 ∧
      (nativeQ2HomologyCoordinateEquiv M A).symm x = Submodule.Quotient.mk z :=
  secondHomologyCoordinateEquiv_inverse_representative (restrictionComplex M A).d1
    (nativeQ2Embedding M A) (nativeQ2Projection M A) (nativeQ1Differential M A)
    (nativeQ2Embedding_injective M A) (nativeQ2Projection_symmetric M A)
    (nativeQ2Projection_idempotent M A) (nativeQ1Differential_left_projection M A)
    (nativeQ2Embedding_range M A) (nativeQ1Differential_range M A) x

end HomologyQ2

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.range_subtype_coordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection_symmetric
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection_idempotent
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Projection_symmetric
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Projection_idempotent
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection_symmetric
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection_idempotent
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Projection_symmetric
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Projection_idempotent
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Embedding
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Embedding_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Embedding_injective
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Embedding_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection_symmetric
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection_idempotent
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Projection_symmetric
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Projection_idempotent
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Embedding
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Embedding_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Embedding_injective
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2Embedding_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential_left_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential_right_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Differential_left_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Differential_right_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Differential_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_left_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_right_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential_left_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential_right_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_cycle_iff
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential_cycle_iff
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential_range
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyProjection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyProjection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyCoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyCoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyCoordinateEquiv_symm_representative
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyProjection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1HomologyCoordinateEquiv_inverse_cycle
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1StandardHomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1StandardHomologyCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1StandardHomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyProjection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyProjection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyCoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyCoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyCoordinateEquiv_symm_representative
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyProjection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1HomologyCoordinateEquiv_inverse_cycle
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1StandardHomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1StandardHomologyCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1StandardHomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyProjection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyProjection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyCoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyCoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyCoordinateEquiv_symm_representative
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyProjection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2StandardHomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2StandardHomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2StandardHomologyCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyCoordinateEquiv_inverse_representative
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyProjection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyProjection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyCoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyCoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyCoordinateEquiv_symm_representative
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyProjection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2StandardHomologyCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2StandardHomologyCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyProjection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2StandardHomologyCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyCoordinateEquiv_inverse_representative
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Differential.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Projection.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Projection.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2Projection.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ2HomologyProjection.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP2HomologyProjection.congr_simp

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
