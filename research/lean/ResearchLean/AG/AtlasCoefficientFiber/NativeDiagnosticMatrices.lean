import ResearchLean.AG.AtlasCoefficientFiber.NativeHomologyCoordinates
import ResearchLean.AG.AtlasCoefficientFiber.CellularHomologyCoordinates
import ResearchLean.AG.AtlasCoefficientFiber.HomologyCoordinateRank
import ResearchLean.AG.AtlasCoefficientFiber.DefectMaps
import ResearchLean.AG.AtlasCoefficientFiber.TransgressionRepresentatives

/-!
# Original diagnostic maps in generated homology coordinates

Position: G-135 E. Source and target are the original homology groups of
T0, embedded in the images of their generated harmonic projections.

## Implementation notes

The original primitive comparison table is sandwiched between the computed
source and target homology projections. The actual unit and independent direct
comparison remain their original maps. The tau table uses the same fine
microdifferential and original Q/P projections, with its sign supplied by the
proved original standard connecting-map representative formula. An ambient
matrix kernel is not counted as the native kernel: dimensions use the source
and target projection ranks.
-/
set_option synthInstance.maxHeartbeats 200000

noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module Matrix
open RationalCoordinates TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)
variable [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)]
variable [Fintype (Nc.FaceInTargetSubset A)]
variable [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)]
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)]

/-- E actual unit H1 table uses only the original generated matrices. -/
def nativeAMatrix : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (Nc.EdgeInTargetSubset A) ℚ :=
  nativeP1HomologyProjection M A * primitiveComparison1Matrix M A * cellularH1Projection Nc A

/-- Owner producer expression for the actual a table. -/
theorem nativeAMatrix_eq : nativeAMatrix M A =
    nativeP1HomologyProjection M A * primitiveComparison1Matrix M A * cellularH1Projection Nc A := rfl

/-- E actual direct H1 table uses the independent original comparison. -/
def nativeTMatrix : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (Nc.EdgeInTargetSubset A) ℚ :=
  cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A) *
    primitiveComparison1Matrix M A * cellularH1Projection Nc A

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)] in
/-- Owner producer expression for the actual T table. -/
theorem nativeTMatrix_eq : nativeTMatrix M A =
    cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A) *
      primitiveComparison1Matrix M A * cellularH1Projection Nc A := rfl

/-- E literal R coordinates use the accepted original QH1 to ker kappa-star
isomorphism. They do not replace R by all vertical-fiber cohomology. -/
def nativeRCoordinateEquiv : R M A ≃ₗ[ℚ]
    LinearMap.range (nativeQ1HomologyProjection M A).mulVecLin :=
  (restrictionStandardHomologyREquiv M A).symm.trans (nativeQ1StandardHomologyCoordinateEquiv M A)

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner all-class formula retains the literal R inverse transport. -/
theorem nativeRCoordinateEquiv_apply (x : R M A) :
    nativeRCoordinateEquiv M A x = nativeQ1StandardHomologyCoordinateEquiv M A
      ((restrictionStandardHomologyREquiv M A).symm x) := rfl

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- Owner formula for the original Q standard representative of literal R. -/
theorem nativeRCoordinateEquiv_restriction
    (x : (zeroExtension (restrictionComplex M A)).homology (1 : ℤ)) :
    nativeRCoordinateEquiv M A (restrictionStandardHomologyREquiv M A x) =
      nativeQ1StandardHomologyCoordinateEquiv M A x := by
  rw [nativeRCoordinateEquiv_apply, LinearEquiv.symm_apply_apply]

/-- E tau table uses the same original fine differential, without a chosen
lifting or transgression certificate as input. -/
def nativeTauMatrix : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))
    (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  nativeP2HomologyProjection M A *
    primitiveD1Matrix Nf (comparisonFactor qc qf h ⁻¹' A) * nativeQ1HomologyProjection M A

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] in
/-- Owner producer expression for the connecting-map table. -/
theorem nativeTauMatrix_eq : nativeTauMatrix M A =
    nativeP2HomologyProjection M A *
      primitiveD1Matrix Nf (comparisonFactor qc qf h ⁻¹' A) * nativeQ1HomologyProjection M A := rfl

/-- The a matrix fixes the proved source image before acting. -/
theorem nativeAMatrix_right_projection : nativeAMatrix M A * cellularH1Projection Nc A = nativeAMatrix M A := by
  rw [nativeAMatrix_eq, Matrix.mul_assoc, cellularH1Projection_mul_self]

/-- The a matrix takes values in the proved original P H1 image. -/
theorem nativeAMatrix_left_projection : nativeP1HomologyProjection M A * nativeAMatrix M A = nativeAMatrix M A := by
  rw [nativeAMatrix_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nativeP1HomologyProjection_mul_self]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)] in
/-- The T matrix fixes the same original source image. -/
theorem nativeTMatrix_right_projection : nativeTMatrix M A * cellularH1Projection Nc A = nativeTMatrix M A := by
  rw [nativeTMatrix_eq, Matrix.mul_assoc, cellularH1Projection_mul_self]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)] in
/-- The T matrix takes values in the proved original fine H1 image. -/
theorem nativeTMatrix_left_projection :
    cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A) * nativeTMatrix M A = nativeTMatrix M A := by
  rw [nativeTMatrix_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, cellularH1Projection_mul_self]

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] in
/-- The tau matrix fixes its original literal R coordinate image. -/
theorem nativeTauMatrix_right_projection :
    nativeTauMatrix M A * nativeQ1HomologyProjection M A = nativeTauMatrix M A := by
  rw [nativeTauMatrix_eq, Matrix.mul_assoc, nativeQ1HomologyProjection_mul_self]

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] in
/-- The tau matrix takes values in the original P H2 coordinate image. -/
theorem nativeTauMatrix_left_projection :
    nativeP2HomologyProjection M A * nativeTauMatrix M A = nativeTauMatrix M A := by
  rw [nativeTauMatrix_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nativeP2HomologyProjection_mul_self]

/-- E every original native unit-H1 value is represented by the generated
matrix. The source inverse is an actual original closed cochain. -/
theorem nativeAMatrix_represents (x : (Nc.targetSubsetComplex A).H1) :
    (nativeP1HomologyCoordinateEquiv M A ((unitHom M A).h1Map x) :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeAMatrix M A *ᵥ (cellularH1CoordinateEquiv Nc A x : Nc.EdgeInTargetSubset A → ℚ) := by
  let c := cellularH1CoordinateEquiv Nc A x
  obtain ⟨z, hz, hclass⟩ := cellularH1CoordinateEquiv_inverse_cycle Nc A c
  have hx : x = Submodule.Quotient.mk z := by
    rw [← hclass]
    exact ((cellularH1CoordinateEquiv Nc A).symm_apply_apply x).symm
  have hc : cellularH1Projection Nc A *ᵥ c.1 = c.1 :=
    degreeProjection_fixes_range _ (cellularH1Projection_mul_self Nc A) c.1 c.2
  have hu := primitiveComparison1Matrix_unit M A z.1
  rw [nativeP1CoordinateEquiv_apply] at hu
  calc
    _ = nativeP1HomologyProjection M A *ᵥ evaluation1 M A ((unitHom M A).f1 z.1) := by
      have hm : (unitHom M A).h1Map (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk ((unitHom M A).cyclesMap z) := (unitHom M A).h1Map_mk z
      rw [hx, hm, nativeP1HomologyCoordinateEquiv_mk, ThreeCochainComplex.Hom.cyclesMap_apply]
    _ = nativeP1HomologyProjection M A *ᵥ (primitiveComparison1Matrix M A *ᵥ c.1) := by
      rw [← hu, hz]
    _ = nativeAMatrix M A *ᵥ c.1 := by
      rw [nativeAMatrix_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)] in
/-- E every original native direct-H1 value is represented by the independently
generated comparison matrix on the original cellular quotient. -/
theorem nativeTMatrix_represents (x : (Nc.targetSubsetComplex A).H1) :
    (cellularH1CoordinateEquiv Nf (comparisonFactor qc qf h ⁻¹' A)
      ((M.aSubnerveComparisonHom A).h1Map x) :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeTMatrix M A *ᵥ (cellularH1CoordinateEquiv Nc A x : Nc.EdgeInTargetSubset A → ℚ) := by
  let c := cellularH1CoordinateEquiv Nc A x
  obtain ⟨z, hz, hclass⟩ := cellularH1CoordinateEquiv_inverse_cycle Nc A c
  have hx : x = Submodule.Quotient.mk z := by
    rw [← hclass]
    exact ((cellularH1CoordinateEquiv Nc A).symm_apply_apply x).symm
  have hc : cellularH1Projection Nc A *ᵥ c.1 = c.1 :=
    degreeProjection_fixes_range _ (cellularH1Projection_mul_self Nc A) c.1 c.2
  calc
    _ = cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A) *ᵥ
        (M.aSubnerveComparisonHom A).f1 z.1 := by
      have hm : (M.aSubnerveComparisonHom A).h1Map (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk ((M.aSubnerveComparisonHom A).cyclesMap z) :=
        (M.aSubnerveComparisonHom A).h1Map_mk z
      rw [hx, hm, cellularH1CoordinateEquiv_mk, ThreeCochainComplex.Hom.cyclesMap_apply]
    _ = cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A) *ᵥ
        (primitiveComparison1Matrix M A *ᵥ c.1) := by
      rw [← primitiveComparison1Matrix_mulVec, hz]
    _ = nativeTMatrix M A *ᵥ c.1 := by
      rw [nativeTMatrix_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc]

/-- E the same a table represents the accepted standard unitH1 on every class. -/
theorem nativeAMatrix_unitH1 (x : (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ)) :
    (nativeP1StandardHomologyCoordinateEquiv M A (unitH1 M A x) :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeAMatrix M A *ᵥ (cellularH1StandardCoordinateEquiv Nc A x : Nc.EdgeInTargetSubset A → ℚ) := by
  let y := (oldH1Equiv (Nc.targetSubsetComplex A)).symm x
  have hx : oldH1Equiv (Nc.targetSubsetComplex A) y = x :=
    (oldH1Equiv (Nc.targetSubsetComplex A)).apply_symm_apply x
  rw [unitH1_apply, ← hx, ← oldH1Equiv_natural,
    nativeP1StandardHomologyCoordinateEquiv_apply, LinearEquiv.symm_apply_apply,
    cellularH1StandardCoordinateEquiv_apply, LinearEquiv.symm_apply_apply]
  exact nativeAMatrix_represents M A y

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)] in
/-- E the same T table represents the accepted standard directH1 on every class. -/
theorem nativeTMatrix_directH1 (x : (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ)) :
    (cellularH1StandardCoordinateEquiv Nf (comparisonFactor qc qf h ⁻¹' A) (directH1 M A x) :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeTMatrix M A *ᵥ (cellularH1StandardCoordinateEquiv Nc A x : Nc.EdgeInTargetSubset A → ℚ) := by
  let y := (oldH1Equiv (Nc.targetSubsetComplex A)).symm x
  have hx : oldH1Equiv (Nc.targetSubsetComplex A) y = x :=
    (oldH1Equiv (Nc.targetSubsetComplex A)).apply_symm_apply x
  rw [directH1_apply, ← hx, ← oldH1Equiv_natural,
    cellularH1StandardCoordinateEquiv_apply, LinearEquiv.symm_apply_apply,
    cellularH1StandardCoordinateEquiv_apply, LinearEquiv.symm_apply_apply]
  exact nativeTMatrix_represents M A y

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (DegenerateFace M A)] in
/-- Original Q embedding is a section of the actual restriction map. -/
theorem restriction1_nativeQ1Embedding (z : (restrictionComplex M A).C1) :
    restriction1 M A (nativeQ1Embedding M A z) = z := by
  rw [nativeQ1Embedding_apply, ← nativeQ1CoordinateEquiv_symm_apply]
  exact (nativeQ1CoordinateEquiv M A).symm_apply_apply z

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] in
/-- E all literal R values of the actual connecting map have the generated
tau coordinates, with the sign of the original standard delta. -/
theorem nativeTauMatrix_connectingTau (x : R M A) :
    (nativeP2StandardHomologyCoordinateEquiv M A (connectingTau M A x) :
      Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeTauMatrix M A *ᵥ (nativeRCoordinateEquiv M A x :
        Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  let r := (oldH1Equiv (restrictionComplex M A)).symm
    ((restrictionStandardHomologyREquiv M A).symm x)
  let c := nativeQ1HomologyCoordinateEquiv M A r
  obtain ⟨z, hz, hclass⟩ := nativeQ1HomologyCoordinateEquiv_inverse_cycle M A c
  have hr : r = Submodule.Quotient.mk z := by
    rw [← hclass]
    exact ((nativeQ1HomologyCoordinateEquiv M A).symm_apply_apply r).symm
  have hx : x = restrictionStandardHomologyREquiv M A
      (oldH1Equiv (restrictionComplex M A) (Submodule.Quotient.mk z)) := by
    apply (restrictionStandardHomologyREquiv M A).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    apply (oldH1Equiv (restrictionComplex M A)).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact hr
  have hcR : (nativeRCoordinateEquiv M A x :
      Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) = c.1 := by
    rw [nativeRCoordinateEquiv_apply, nativeQ1StandardHomologyCoordinateEquiv_apply]
  have hc : nativeQ1HomologyProjection M A *ᵥ c.1 = c.1 :=
    degreeProjection_fixes_range _ (nativeQ1HomologyProjection_mul_self M A) c.1 c.2
  have hq : restriction1 M A c.1 = z.1 := by
    rw [← hz, restriction1_nativeQ1Embedding]
  have hd : restriction2 M A
      ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1 c.1) = 0 := by
    rw [restriction_comm1, hq]
    exact z.2
  obtain ⟨p, hp⟩ := evaluation2_preimage_of_restriction_zero M A _ hd
  calc
    _ = (nativeP2StandardHomologyCoordinateEquiv M A
        (oldH2Equiv (pushforwardComplex M A) (Submodule.Quotient.mk p)) :
          Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
      rw [hx, connectingTau_restrictionStandardHomologyREquiv,
        evaluationRestriction_connecting_representative M A z c.1 p hq hp]
    _ = nativeP2HomologyProjection M A *ᵥ evaluation2 M A p :=
      nativeP2StandardHomologyCoordinateEquiv_mk M A p
    _ = nativeP2HomologyProjection M A *ᵥ
        (primitiveD1Matrix Nf (comparisonFactor qc qf h ⁻¹' A) *ᵥ c.1) := by
      rw [hp, primitiveD1Matrix_mulVec]
    _ = nativeTauMatrix M A *ᵥ (nativeRCoordinateEquiv M A x :
        Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
      rw [nativeTauMatrix_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcR, hc]

/-- E the actual unit-H1 range dimension is computed from the same a table. -/
theorem nativeAMatrix_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeAMatrix M A) =
      Module.finrank ℚ (LinearMap.range (unitH1 M A)) :=
  coordinateMatrix_rank (cellularH1Projection Nc A) (nativeP1HomologyProjection M A)
    (nativeAMatrix M A) (unitH1 M A) (cellularH1StandardCoordinateEquiv Nc A)
    (nativeP1StandardHomologyCoordinateEquiv M A) (nativeAMatrix_right_projection M A)
    (nativeAMatrix_unitH1 M A)

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)] in
/-- E the actual direct-H1 range dimension is computed from the same T table. -/
theorem nativeTMatrix_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeTMatrix M A) =
      Module.finrank ℚ (LinearMap.range (directH1 M A)) :=
  coordinateMatrix_rank (cellularH1Projection Nc A)
    (cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A)) (nativeTMatrix M A)
    (directH1 M A) (cellularH1StandardCoordinateEquiv Nc A)
    (cellularH1StandardCoordinateEquiv Nf (comparisonFactor qc qf h ⁻¹' A))
    (nativeTMatrix_right_projection M A) (nativeTMatrix_directH1 M A)

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] in
/-- E the actual literal-R transgression rank is computed from the same tau table. -/
theorem nativeTauMatrix_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeTauMatrix M A) =
      Module.finrank ℚ (LinearMap.range (connectingTau M A)) :=
  coordinateMatrix_rank (nativeQ1HomologyProjection M A) (nativeP2HomologyProjection M A)
    (nativeTauMatrix M A) (connectingTau M A) (nativeRCoordinateEquiv M A)
    (nativeP2StandardHomologyCoordinateEquiv M A) (nativeTauMatrix_right_projection M A)
    (nativeTauMatrix_connectingTau M A)

/-- E computed ranks give the actual accepted unit kernel/cokernel pair. -/
theorem nativeAMatrix_blockDefect :
    blockDefect (unitH1 M A) =
      (AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (cellularH1Projection Nc A) -
        AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeAMatrix M A),
       AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeP1HomologyProjection M A) -
        AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeAMatrix M A)) :=
  coordinateMatrix_blockDefect (cellularH1Projection Nc A) (nativeP1HomologyProjection M A)
    (nativeAMatrix M A) (unitH1 M A) (cellularH1StandardCoordinateEquiv Nc A)
    (nativeP1StandardHomologyCoordinateEquiv M A) (nativeAMatrix_right_projection M A)
    (nativeAMatrix_unitH1 M A)

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)] in
/-- E computed ranks give the actual accepted direct kernel/cokernel pair J. -/
theorem nativeTMatrix_blockDefect :
    blockDefect (directH1 M A) =
      (AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (cellularH1Projection Nc A) -
        AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeTMatrix M A),
       AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank
        (cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A)) -
        AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank (nativeTMatrix M A)) :=
  coordinateMatrix_blockDefect (cellularH1Projection Nc A)
    (cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A)) (nativeTMatrix M A)
    (directH1 M A) (cellularH1StandardCoordinateEquiv Nc A)
    (cellularH1StandardCoordinateEquiv Nf (comparisonFactor qc qf h ⁻¹' A))
    (nativeTMatrix_right_projection M A) (nativeTMatrix_directH1 M A)

/-- E the complete native a coordinate map acts by its generated table on every source image. -/
theorem nativeAMatrix_imageMap
    (x : LinearMap.range (cellularH1Projection Nc A).mulVecLin) :
    (homologyImageMap (cellularH1Projection Nc A) (nativeP1HomologyProjection M A)
      (unitH1 M A) (cellularH1StandardCoordinateEquiv Nc A)
      (nativeP1StandardHomologyCoordinateEquiv M A) x :
        Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeAMatrix M A *ᵥ x.1 :=
  homologyImageMap_matrix _ _ _ _ _ _ (nativeAMatrix_unitH1 M A) x

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)] in
/-- E the complete native T coordinate map acts by its generated table on every source image. -/
theorem nativeTMatrix_imageMap
    (x : LinearMap.range (cellularH1Projection Nc A).mulVecLin) :
    (homologyImageMap (cellularH1Projection Nc A)
      (cellularH1Projection Nf (comparisonFactor qc qf h ⁻¹' A))
      (directH1 M A) (cellularH1StandardCoordinateEquiv Nc A)
      (cellularH1StandardCoordinateEquiv Nf (comparisonFactor qc qf h ⁻¹' A)) x :
        Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeTMatrix M A *ᵥ x.1 :=
  homologyImageMap_matrix _ _ _ _ _ _ (nativeTMatrix_directH1 M A) x

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)] [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)] in
/-- E the complete literal R coordinate map acts by its generated tau table. -/
theorem nativeTauMatrix_imageMap
    (x : LinearMap.range (nativeQ1HomologyProjection M A).mulVecLin) :
    (homologyImageMap (nativeQ1HomologyProjection M A) (nativeP2HomologyProjection M A)
      (connectingTau M A) (nativeRCoordinateEquiv M A)
      (nativeP2StandardHomologyCoordinateEquiv M A) x :
        Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      nativeTauMatrix M A *ᵥ x.1 :=
  homologyImageMap_matrix _ _ _ _ _ _ (nativeTauMatrix_connectingTau M A) x

omit [Fintype (Nc.ChartInTargetSubset A)] [Fintype (Nc.EdgeInTargetSubset A)]
    [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)]
    [DecidableEq (Nc.EdgeInTargetSubset A)]
    [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E computed literal R dimension is the same original Q harmonic rank,
through the accepted original ker-kappa-star correspondence. -/
theorem nativeRProjection_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank
      (nativeQ1HomologyProjection M A) = Module.finrank ℚ (R M A) := by
  rw [AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_finrank_range]
  exact (nativeRCoordinateEquiv M A).symm.finrank_eq

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeRCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.nativeRCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.nativeRCoordinateEquiv_restriction
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTauMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTauMatrix_eq
#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix_right_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix_left_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix_right_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix_left_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTauMatrix_right_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTauMatrix_left_projection
#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix_unitH1
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix_directH1
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1_nativeQ1Embedding
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTauMatrix_connectingTau
#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTauMatrix_rank
#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix_blockDefect
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix_blockDefect
#print axioms AAT.AG.AtlasCoefficientFiber.nativeAMatrix_imageMap
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTMatrix_imageMap
#print axioms AAT.AG.AtlasCoefficientFiber.nativeTauMatrix_imageMap

#print axioms AAT.AG.AtlasCoefficientFiber.nativeRProjection_rank

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
