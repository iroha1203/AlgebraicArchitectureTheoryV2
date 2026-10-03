import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionCoordinates
import ResearchLean.AG.RelativeRepairComposition.SubdivisionObstruction
import ResearchLean.AG.RelativeRepairComposition.SubdivisionZeroCohomology

/-!
# The full original W1 complex, obstruction and holonomy survive subdivision

The same full original tower, same a factors and same physical/candidate sets
instantiate the complete general comparison. The supplemental whole kernel is
contractible by its identity differential. Every original complete closed word
retains its actual repaired holonomy, and the actual defect keeps both input values.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation
open CategoryTheory Limits TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients
open W1SubdivisionInput W1SubdivisionRepairs
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3)
local notation "T" => W1AffineInput.originalTower true x y
local notation "F" => factors x y

/-- The original authored three-cell compatibility is discharged from this specified empty original three-cell carrier. -/
theorem original_syzygy (s : geometry.ThreeCell) : AuthoredSyzygy (T).toTower.toTransportData 1
    (geometry.threeLeft s) (geometry.threeRight s) := s.elim

/-- Both actual full original defect coordinates are retained after both authored a substitutions. -/
theorem defect_value (f : geometry.TwoCell) :
    middleCoefficient x y ((splitTower x y).toTower.defect f) = -(if (f : Bool) = true then y else x) := by
  rw [Subdivision.defect_substitute]
  exact W1FiniteCoefficients.defect_coordinate true x y f

/-- The complete relative complex in every original permission range splits as the original complex plus the whole fresh identity complex. -/
noncomputable def complexIso (S : Set (EdgeName (K := geometry))) :=
  Subdivision.relativeBiprodIso (T) chosen (F) fixedRegion candidates S chosen_not_P chosen_not_candidate

/-- The entire native cohomology comparison holds in every degree and every original permission range. -/
noncomputable def allHomologyIso (S : Set (EdgeName (K := geometry))) (n : Nat) :=
  Subdivision.relativeHomologyIso (T) chosen (F) fixedRegion candidates S chosen_not_P chosen_not_candidate n

/-- Full degree-zero stabilizer labels are retained by the original relative comparison. -/
noncomputable def h0Equiv (S : Set (EdgeName (K := geometry))) :=
  Subdivision.relativeH0Equiv (T) chosen (F) fixedRegion candidates S chosen_not_P chosen_not_candidate

/-- The same original actual obstruction class is preserved at every permission range. -/
theorem obstruction_class (S : Set (EdgeName (K := geometry))) :
    (Subdivision.relativeH2Iso (T) chosen (F) fixedRegion candidates S chosen_not_P chosen_not_candidate).hom
      (ActualRelative.obstructionClass (splitTower x y)
        (Subdivision.oldRegion geometry chosen fixedRegion chosen_not_P)
        (Subdivision.oldEdgeSet geometry chosen candidates) (Subdivision.oldEdgeSet geometry chosen S)
        (Subdivision.fixed_face_laws (T) chosen (F) fixedRegion chosen_not_P (fixed_faces true x y))
        (Subdivision.three_laws (T) chosen (F) (original_syzygy x y))) =
      ActualRelative.obstructionClass (T) fixedRegion candidates S (fixed_faces true x y) (original_syzygy x y) :=
  Subdivision.obstruction_class_collapse (T) chosen (F) fixedRegion chosen_not_P
    (fixed_faces true x y) (original_syzygy x y) candidates S chosen_not_candidate

/-- Every complete original closed word retains its literal actual repaired holonomy under the full collapse. -/
theorem old_holonomy (R : Solution (splitTower x y)) (i : geometry.Vertex) (w : geometry.Path i i) :
    (selectedUpper (Subdivision.presentation geometry chosen)
      (GroupExtension.projection (projection (k := ZMod 3) (A := ZMod 3)))
      (GroupExtension.terminal (ZMod 3 ≃ₗ[ZMod 3] ZMod 3)) (splitTower x y).original R.choice).pathLift
        (Subdivision.substitutePath geometry chosen w) =
    (selectedUpper geometry (GroupExtension.projection (projection (k := ZMod 3) (A := ZMod 3)))
      (GroupExtension.terminal (ZMod 3 ≃ₗ[ZMod 3] ZMod 3)) (T).original
      (Subdivision.collapseSolution (T) chosen (F) R).choice).pathLift w :=
  Subdivision.old_closed_holonomy (T) chosen (F) R i w

/-- Every entire fresh kernel value is retained by the supplemental identity differential. -/
theorem fresh_identity (a : (splitTower x y).toTower.localCoefficients.A (.inr ())) :
    (Subdivision.freshComplex (T) chosen (F)).d 0 1 (ULift.up a) = ULift.up a := by
  change (NativeIdentityComplex.complex _).d 0 1 (ULift.up a) = ULift.up a
  rw [NativeIdentityComplex.d_zero_one]
  rfl

/-- The native contraction retains every full fresh kernel value, rather than a selected zero representative. -/
theorem fresh_contraction (a : (splitTower x y).toTower.localCoefficients.A (.inr ())) :
    (Subdivision.freshContraction (T) chosen (F)).hom 1 0 (ULift.up a) = ULift.up a := rfl

end AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionPreservation
