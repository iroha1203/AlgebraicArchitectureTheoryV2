import ResearchLean.AG.RelativeRepairComposition.W1DualMinimalRanges
import ResearchLean.AG.RelativeRepairComposition.W1ActualCorrections
import ResearchLean.AG.RelativeRepairComposition.W1PermissionClassification

/-!
# Original actual W1 repairs at the specified symbolic value update

The same geometry, all original affine operations, private h and candidate
names are retained. The right-hand values change from (0,0) to (0,1).
Restoration constructs complete actual repairs with the prescribed h=0,
and the same original quotient dual witnesses the empty-range failure.
-/
namespace AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1AuthoredOperations W1Regions W1ActualRepairs
open W1PermissionClassification W1DualMinimalRanges W1ActualCorrections
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

/-- The value update changes the actual signed face defect but not either original authored word. -/
theorem symbolic_signed_rhs (x y : ZMod 3) :
    W1RelativeCoefficients.faceCoordinates true x y
      (-W1RelativeCoefficients.actualDefect true x y) false = x ∧
    W1RelativeCoefficients.faceCoordinates true x y
      (-W1RelativeCoefficients.actualDefect true x y) true = y := by
  simpa using And.intro
    (W1RelativeCoefficients.signedDefect_coordinates true x y false)
    (W1RelativeCoefficients.signedDefect_coordinates true x y true)

/-- The specified b-only correction is admitted by the same original laws and original mask. -/
theorem b_parameters :
    Equations true 0 1 ⟨2, 0, 1, 0⟩ ∧ Allowed {name edgeB} ⟨2, 0, 1, 0⟩ := by
  constructor
  · exact ⟨by decide, by decide⟩
  · simp [Allowed, geometry, name, edgeB, edgeC]

/-- The specified c-only correction is admitted without any b permission. -/
theorem c_parameters :
    Equations true 0 1 ⟨0, 0, 0, 1⟩ ∧ Allowed {name edgeC} ⟨0, 0, 0, 1⟩ := by
  constructor
  · exact ⟨by decide, by decide⟩
  · simp [Allowed, geometry, name, edgeB, edgeC]

/-- The b-only updated object is a full independent original affine repair. -/
noncomputable def bUpdated : RealRepairs true 0 1 {name edgeB} :=
  actualRepair true 0 1 {name edgeB} ⟨2, 0, 1, 0⟩ b_parameters.1 b_parameters.2

/-- The c-only updated object retains the same whole original affine input. -/
noncomputable def cUpdated : RealRepairs true 0 1 {name edgeC} :=
  actualRepair true 0 1 {name edgeC} ⟨0, 0, 0, 1⟩ c_parameters.1 c_parameters.2

/-- The complete original operations of the b-only repair are exactly the prescribed restored operations at every original edge. -/
theorem b_operations : @bUpdated.operation = @operation true 0 1 2 0 1 0 := rfl

/-- The complete c-only repair restores all six original operations, including both fixed input loops. -/
theorem c_operations : @cUpdated.operation = @operation true 0 1 0 0 0 1 := rfl

/-- Every restored b-only correction reads the complete prescribed full-kernel value at the same original name. -/
theorem b_corrections (e : geometry.Edge () ()) :
    NativeAffine.realCorrection geometry (reference true 0 1)
      comparison (fixedEdges {name edgeB}) bUpdated (name e) =
      correctionValue 2 0 1 0 e :=
  actualRepair_real_correction true 0 1 {name edgeB} ⟨2, 0, 1, 0⟩ b_parameters.1 b_parameters.2 (name e)

/-- Every restored c-only correction reads the complete prescribed full-kernel value at the same original name. -/
theorem c_corrections (e : geometry.Edge () ()) :
    NativeAffine.realCorrection geometry (reference true 0 1)
      comparison (fixedEdges {name edgeC}) cUpdated (name e) =
      correctionValue 0 0 0 1 e :=
  actualRepair_real_correction true 0 1 {name edgeC} ⟨0, 0, 0, 1⟩ c_parameters.1 c_parameters.2 (name e)

/-- The same original actual quotient dual is nonzero after the specified update and has both named candidates in its support. -/
theorem updated_failure_dual :
    dualCoordinate 0 1 (W1OriginalObstruction.obstruction 0 1) ≠ 0 ∧
      NamedDual.support
        (OriginalRanges.column (k := ZMod 3) (originalTower true 0 1).toTower.localCoefficients
          fixedRegion candidates candidates_outside (W1FiniteCoefficients.original_linear true 0 1))
        (dualCoordinate 0 1) = Set.univ :=
  empty_failure_dual 0 1 (by decide)

/-- The original zero-value input admits empty permissions, whereas the updated input does not. -/
theorem zero_to_nonzero_empty :
    Nonempty (RealRepairs true 0 0 ∅) ∧ ¬ Nonempty (RealRepairs true 0 1 ∅) := by
  exact ⟨(negative_empty_exists_iff 0 0).mpr (by decide),
    fun h => (by decide : (1 : ZMod 3) - 0 ≠ 0) ((negative_empty_exists_iff 0 1).mp h)⟩

end AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SymbolicActualUpdates
