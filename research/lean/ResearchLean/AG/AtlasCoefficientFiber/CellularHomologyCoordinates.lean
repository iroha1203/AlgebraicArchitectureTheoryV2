import ResearchLean.AG.AtlasCoefficientFiber.SecondHomologyCoordinateTransport
import ResearchLean.AG.AtlasCoefficientFiber.NativeDegreeDifferentials
import ResearchLean.AG.AtlasDefectComposition.EndpointHomology

/-!
# Generated coordinates for original cellular homology

Position: G-135 E coarse/fine H1/H2. The original targetSubsetComplex is
retained and represented on its original named selected cells.

## Implementation notes

Full cellular degree spaces use identity projections. Their original
microdifferentials provide the two harmonic corrections; the correctness
conditions come from the original nerve complex and whole-vector matrix API.
Using semantic homology bases or a separately supplied matrix complex was
rejected because it would lose the original targetSubsetComplex maps.
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module Matrix
open RationalCoordinates TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
variable (N : TargetSupportedNerve.{u,u} q) (S : Set q.Target)

section H1
variable [Fintype (N.ChartInTargetSubset S)] [Fintype (N.EdgeInTargetSubset S)]
variable [Fintype (N.FaceInTargetSubset S)]
variable [DecidableEq (N.ChartInTargetSubset S)] [DecidableEq (N.EdgeInTargetSubset S)]

omit [Fintype (N.FaceInTargetSubset S)] [DecidableEq (N.EdgeInTargetSubset S)] in
/-- Original cellular incoming boundaries are represented by the original table. -/
theorem primitiveD0Matrix_range : LinearMap.range (primitiveD0Matrix N S).mulVecLin =
    (LinearMap.range (N.targetSubsetComplex S).d0).map
      (LinearMap.id : (N.EdgeInTargetSubset S → ℚ) →ₗ[ℚ] (N.EdgeInTargetSubset S → ℚ)) := by
  simpa using range_matrix_of_represents (LinearEquiv.refl ℚ (N.ChartInTargetSubset S → ℚ))
    (LinearEquiv.refl ℚ (N.EdgeInTargetSubset S → ℚ)) (N.targetSubsetComplex S).d0
    (primitiveD0Matrix N S) (primitiveD0Matrix_mulVec N S)

/-- Executable original cellular H1 projector uses all original selected cells. -/
def cellularH1Projection : Matrix (N.EdgeInTargetSubset S) (N.EdgeInTargetSubset S) ℚ :=
  harmonicProjection 1 (primitiveD0Matrix N S) (primitiveD1Matrix N S)

/-- Owner expression exposes the original identity-degree correction only. -/
theorem cellularH1Projection_eq : cellularH1Projection N S =
    harmonicProjection 1 (primitiveD0Matrix N S) (primitiveD1Matrix N S) := rfl

/-- Full original cellular H1 quotient coordinates with every condition derived. -/
def cellularH1CoordinateEquiv : (N.targetSubsetComplex S).H1 ≃ₗ[ℚ]
    LinearMap.range (cellularH1Projection N S).mulVecLin :=
  homologyCoordinateEquiv (N.targetSubsetComplex S) LinearMap.id
    1 (primitiveD0Matrix N S) (primitiveD1Matrix N S)
    Function.injective_id Matrix.transpose_one (Matrix.one_mul _)
    (Matrix.one_mul _) (Matrix.mul_one _) (primitiveD1Matrix_mul_D0 N S)
    (by rw [Matrix.mulVecLin_one]) (primitiveD0Matrix_range N S)
    (fun x => by change primitiveD1Matrix N S *ᵥ x = 0 ↔ _; rw [primitiveD1Matrix_mulVec])

/-- Owner formula represents every original cellular cocycle quotient class. -/
theorem cellularH1CoordinateEquiv_mk (z : LinearMap.ker (N.targetSubsetComplex S).d1) :
    (cellularH1CoordinateEquiv N S (Submodule.Quotient.mk z) : N.EdgeInTargetSubset S → ℚ) =
      cellularH1Projection N S *ᵥ z.1 := by
  exact homologyCoordinateEquiv_mk (N.targetSubsetComplex S) LinearMap.id
    1 (primitiveD0Matrix N S) (primitiveD1Matrix N S)
    Function.injective_id Matrix.transpose_one (Matrix.one_mul _)
    (Matrix.one_mul _) (Matrix.mul_one _) (primitiveD1Matrix_mul_D0 N S)
    (by rw [Matrix.mulVecLin_one]) (primitiveD0Matrix_range N S)
    (fun x => by change primitiveD1Matrix N S *ᵥ x = 0 ↔ _; rw [primitiveD1Matrix_mulVec]) z

/-- Every original cellular H1 class is recovered by the inverse. -/
theorem cellularH1CoordinateEquiv_left_inverse (x : (N.targetSubsetComplex S).H1) :
    (cellularH1CoordinateEquiv N S).symm (cellularH1CoordinateEquiv N S x) = x :=
  (cellularH1CoordinateEquiv N S).symm_apply_apply x

/-- Every generated cellular harmonic coordinate is recovered by the forward map. -/
theorem cellularH1CoordinateEquiv_right_inverse
    (x : LinearMap.range (cellularH1Projection N S).mulVecLin) :
    cellularH1CoordinateEquiv N S ((cellularH1CoordinateEquiv N S).symm x) = x :=
  (cellularH1CoordinateEquiv N S).apply_symm_apply x

/-- Computed original cellular harmonic rank equals the literal original H1 dimension. -/
theorem cellularH1Projection_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank
      (cellularH1Projection N S) = Module.finrank ℚ (N.targetSubsetComplex S).H1 := by
  rw [AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_finrank_range]
  exact (cellularH1CoordinateEquiv N S).symm.finrank_eq

/-- Original standard cellular H1 has these same generated coordinates. -/
def cellularH1StandardCoordinateEquiv :
    (zeroExtension (N.targetSubsetComplex S)).homology (1 : ℤ) ≃ₗ[ℚ]
      LinearMap.range (cellularH1Projection N S).mulVecLin :=
  (oldH1Equiv (N.targetSubsetComplex S)).symm.trans (cellularH1CoordinateEquiv N S)

/-- Owner standard H1 formula preserves every original cocycle class. -/
theorem cellularH1StandardCoordinateEquiv_mk (z : LinearMap.ker (N.targetSubsetComplex S).d1) :
    (cellularH1StandardCoordinateEquiv N S
      (oldH1Equiv (N.targetSubsetComplex S) (Submodule.Quotient.mk z)) : N.EdgeInTargetSubset S → ℚ) =
      cellularH1Projection N S *ᵥ z.1 := by
  simp only [cellularH1StandardCoordinateEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, cellularH1CoordinateEquiv_mk]

/-- The original cellular H1 projection fixes its complete image. -/
theorem cellularH1Projection_mul_self :
    cellularH1Projection N S * cellularH1Projection N S = cellularH1Projection N S := by
  rw [cellularH1Projection_eq]
  exact harmonicProjection_mul_self 1 (primitiveD0Matrix N S) (primitiveD1Matrix N S)
    Matrix.transpose_one (Matrix.one_mul _) (Matrix.one_mul _) (Matrix.mul_one _)
    (primitiveD1Matrix_mul_D0 N S)

/-- Every inverse cellular H1 coordinate has an original closed representative. -/
theorem cellularH1CoordinateEquiv_inverse_cycle
    (x : LinearMap.range (cellularH1Projection N S).mulVecLin) :
    ∃ z : LinearMap.ker (N.targetSubsetComplex S).d1, z.1 = x.1 ∧
      (cellularH1CoordinateEquiv N S).symm x = Submodule.Quotient.mk z :=
  homologyCoordinateEquiv_inverse_cycle (N.targetSubsetComplex S) LinearMap.id
    1 (primitiveD0Matrix N S) (primitiveD1Matrix N S)
    Function.injective_id Matrix.transpose_one (Matrix.one_mul _)
    (Matrix.one_mul _) (Matrix.mul_one _) (primitiveD1Matrix_mul_D0 N S)
    (by rw [Matrix.mulVecLin_one]) (primitiveD0Matrix_range N S)
    (fun x => by change primitiveD1Matrix N S *ᵥ x = 0 ↔ _; rw [primitiveD1Matrix_mulVec]) x

/-- Owner formula for standard cellular H1 coordinates on every class. -/
theorem cellularH1StandardCoordinateEquiv_apply
    (x : (zeroExtension (N.targetSubsetComplex S)).homology (1 : ℤ)) :
    cellularH1StandardCoordinateEquiv N S x =
      cellularH1CoordinateEquiv N S ((oldH1Equiv (N.targetSubsetComplex S)).symm x) := rfl

end H1

section H2
variable [Fintype (N.EdgeInTargetSubset S)] [Fintype (N.FaceInTargetSubset S)]
variable [DecidableEq (N.EdgeInTargetSubset S)] [DecidableEq (N.FaceInTargetSubset S)]

omit [DecidableEq (N.FaceInTargetSubset S)] in
/-- Original cellular top boundaries are represented by the original signed table. -/
theorem primitiveD1Matrix_range : LinearMap.range (primitiveD1Matrix N S).mulVecLin =
    (LinearMap.range (N.targetSubsetComplex S).d1).map
      (LinearMap.id : (N.FaceInTargetSubset S → ℚ) →ₗ[ℚ] (N.FaceInTargetSubset S → ℚ)) := by
  simpa using range_matrix_of_represents (LinearEquiv.refl ℚ (N.EdgeInTargetSubset S → ℚ))
    (LinearEquiv.refl ℚ (N.FaceInTargetSubset S → ℚ)) (N.targetSubsetComplex S).d1
    (primitiveD1Matrix N S) (primitiveD1Matrix_mulVec N S)

/-- Executable original cellular H2 projector uses the same incoming differential. -/
def cellularH2Projection : Matrix (N.FaceInTargetSubset S) (N.FaceInTargetSubset S) ℚ :=
  secondHomologyProjection 1 (primitiveD1Matrix N S)

/-- Owner expression exposes the original identity-degree top correction. -/
theorem cellularH2Projection_eq : cellularH2Projection N S =
    secondHomologyProjection 1 (primitiveD1Matrix N S) := rfl

/-- Full coordinates for the original cellular top-degree quotient. -/
def cellularH2CoordinateEquiv :
    ((N.targetSubsetComplex S).C2 ⧸ LinearMap.range (N.targetSubsetComplex S).d1) ≃ₗ[ℚ]
      LinearMap.range (cellularH2Projection N S).mulVecLin :=
  secondHomologyCoordinateEquiv (N.targetSubsetComplex S).d1 LinearMap.id
    1 (primitiveD1Matrix N S) Function.injective_id Matrix.transpose_one
    (Matrix.one_mul _) (Matrix.one_mul _) (by rw [Matrix.mulVecLin_one])
    (primitiveD1Matrix_range N S)

/-- Every original cellular top representative has the same quotient coordinates. -/
theorem cellularH2CoordinateEquiv_mk (z : (N.targetSubsetComplex S).C2) :
    (cellularH2CoordinateEquiv N S (Submodule.Quotient.mk z) : N.FaceInTargetSubset S → ℚ) =
      cellularH2Projection N S *ᵥ z := by
  exact secondHomologyCoordinateEquiv_mk (N.targetSubsetComplex S).d1 LinearMap.id
    1 (primitiveD1Matrix N S) Function.injective_id Matrix.transpose_one
    (Matrix.one_mul _) (Matrix.one_mul _) (by rw [Matrix.mulVecLin_one])
    (primitiveD1Matrix_range N S) z

/-- Every original cellular top quotient class is recovered by the inverse. -/
theorem cellularH2CoordinateEquiv_left_inverse
    (x : (N.targetSubsetComplex S).C2 ⧸ LinearMap.range (N.targetSubsetComplex S).d1) :
    (cellularH2CoordinateEquiv N S).symm (cellularH2CoordinateEquiv N S x) = x :=
  (cellularH2CoordinateEquiv N S).symm_apply_apply x

/-- Every generated cellular top coordinate is recovered by the forward map. -/
theorem cellularH2CoordinateEquiv_right_inverse
    (x : LinearMap.range (cellularH2Projection N S).mulVecLin) :
    cellularH2CoordinateEquiv N S ((cellularH2CoordinateEquiv N S).symm x) = x :=
  (cellularH2CoordinateEquiv N S).apply_symm_apply x

/-- Computed cellular top rank equals the original incoming-range quotient dimension. -/
theorem cellularH2Projection_rank :
    AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank
      (cellularH2Projection N S) =
        Module.finrank ℚ ((N.targetSubsetComplex S).C2 ⧸ LinearMap.range (N.targetSubsetComplex S).d1) := by
  rw [AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra.rationalMatrixRank_eq_finrank_range]
  exact (cellularH2CoordinateEquiv N S).symm.finrank_eq

/-- Original standard cellular H2 has the same generated coordinates. -/
def cellularH2StandardCoordinateEquiv :
    (zeroExtension (N.targetSubsetComplex S)).homology (2 : ℤ) ≃ₗ[ℚ]
      LinearMap.range (cellularH2Projection N S).mulVecLin :=
  (oldH2Equiv (N.targetSubsetComplex S)).symm.trans (cellularH2CoordinateEquiv N S)

/-- Owner standard H2 formula preserves every original top quotient class. -/
theorem cellularH2StandardCoordinateEquiv_mk (z : (N.targetSubsetComplex S).C2) :
    (cellularH2StandardCoordinateEquiv N S
      (oldH2Equiv (N.targetSubsetComplex S) (Submodule.Quotient.mk z)) : N.FaceInTargetSubset S → ℚ) =
      cellularH2Projection N S *ᵥ z := by
  simp only [cellularH2StandardCoordinateEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, cellularH2CoordinateEquiv_mk]

/-- The original cellular H2 projection fixes its complete image. -/
theorem cellularH2Projection_mul_self :
    cellularH2Projection N S * cellularH2Projection N S = cellularH2Projection N S := by
  rw [cellularH2Projection_eq]
  exact secondHomologyProjection_mul_self 1 (primitiveD1Matrix N S)
    Matrix.transpose_one (Matrix.one_mul _) (Matrix.one_mul _)

/-- Every inverse cellular H2 coordinate has an original top representative. -/
theorem cellularH2CoordinateEquiv_inverse_representative
    (x : LinearMap.range (cellularH2Projection N S).mulVecLin) :
    ∃ z : (N.targetSubsetComplex S).C2, z = x.1 ∧
      (cellularH2CoordinateEquiv N S).symm x = Submodule.Quotient.mk z :=
  secondHomologyCoordinateEquiv_inverse_representative (N.targetSubsetComplex S).d1 LinearMap.id
    1 (primitiveD1Matrix N S) Function.injective_id Matrix.transpose_one
    (Matrix.one_mul _) (Matrix.one_mul _) (by rw [Matrix.mulVecLin_one])
    (primitiveD1Matrix_range N S) x

/-- Owner formula for standard cellular H2 coordinates on every class. -/
theorem cellularH2StandardCoordinateEquiv_apply
    (x : (zeroExtension (N.targetSubsetComplex S)).homology (2 : ℤ)) :
    cellularH2StandardCoordinateEquiv N S x =
      cellularH2CoordinateEquiv N S ((oldH2Equiv (N.targetSubsetComplex S)).symm x) := rfl

end H2
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD0Matrix_range
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1Projection
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1Projection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1CoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1CoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1CoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1CoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1Projection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1StandardCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1StandardCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1Projection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1CoordinateEquiv_inverse_cycle
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1StandardCoordinateEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD1Matrix_range
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2Projection
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2Projection_eq
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2CoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2CoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2CoordinateEquiv_left_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2CoordinateEquiv_right_inverse
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2Projection_rank
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2StandardCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2StandardCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2Projection_mul_self
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2CoordinateEquiv_inverse_representative
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2StandardCoordinateEquiv_apply

#print axioms AAT.AG.AtlasCoefficientFiber.cellularH2Projection.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD1Matrix.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD0Matrix.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.cellularH1Projection.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
