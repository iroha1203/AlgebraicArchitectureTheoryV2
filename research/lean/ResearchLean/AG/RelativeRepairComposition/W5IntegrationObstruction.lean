import ResearchLean.AG.RelativeRepairComposition.W5NativeDescent
import ResearchLean.AG.RelativeRepairComposition.W5RelativeObstruction
import ResearchLean.AG.RelativeRepairComposition.W5OverlapCohomology
import ResearchLean.AG.RelativeRepairComposition.NativeCoverObstruction
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCorrection

/-! # W5's integration class for every independent actual local plan

Both local solutions come from the full actual native repair correspondence.
Their same original shared-edge difference evaluates to b2-b1. The original
sum-of-images quotient, choice independence and positive connecting class are
those of the same generic B, retaining every original label and coefficient.
-/
namespace AAT.AG.RelativeRepairComposition.W5IntegrationObstruction
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W5AffineInput W5Regions W5AuthoredOperations W5OriginalDifferentials
open W5RelativeCoefficients W5RelativeObstruction W5LocalCohomology W5OverlapCohomology W5NativeDescent
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (b₁ b₂ : ZMod 2)
local notation "T" => originalTower b₁ b₂
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower b₁ b₂))
local notation "δ" => actualDefect b₁ b₂
/-- Every independent actual native plan has its full original relative shared correction. -/
noncomputable def planValue (side : Bool) (R : NativeDescent.LocalGroupoid T fixedRegion (region side)) : ZMod 2 :=
  edgeCoordinates b₁ b₂ (region side) (region_shared side)
    (NativeCoverObstruction.localCoordinate T fixedRegion (fixed_faces b₁ b₂) (region side) R).1
/-- The original local affine equation derived from actual repair forces the same physical input value. -/
theorem planValue_input (side : Bool) (R : NativeDescent.LocalGroupoid T fixedRegion (region side)) :
    planValue b₁ b₂ side R = inputValue b₁ b₂ side := by
  let h := NativeCoverObstruction.localCoordinate T fixedRegion (fixed_faces b₁ b₂) (region side) R
  have hv := W5RelativeCoefficients.d1_value b₁ b₂ (region side) (region_shared side) h.1
    ⟨side,face_in_region side⟩
  change faceCoordinates b₁ b₂ (region side) (RelativeCover.d1 M (region side) fixedRegion h.1) _ =
    planValue b₁ b₂ side R at hv
  rw [h.2,map_neg] at hv
  change -faceCoordinates b₁ b₂ (region side)
    (CoverEquation.defect M fixedRegion δ (region side)) ⟨side,face_in_region side⟩ =
      planValue b₁ b₂ side R at hv
  have hd : faceCoordinates b₁ b₂ (region side)
      (CoverEquation.defect M fixedRegion δ (region side)) ⟨side,face_in_region side⟩ =
        -inputValue b₁ b₂ side := actualDefect_value b₁ b₂ side
  rw [hd,neg_neg] at hv
  exact hv.symm
/-- The complete actual local correspondence reads the same original shared affine operation value. -/
theorem planValue_actual (side : Bool) (R : NativeDescent.LocalGroupoid T fixedRegion (region side)) :
    planValue b₁ b₂ side R = W5LocalRepairs.localValue (region side) (W5LocalRepairs.patch_shared side)
      (localObjectEquiv b₁ b₂ (region side) R.back) := by
  rw [planValue_input,W5LocalRepairs.localValue_input]

/-- The actual original plan difference uses the full original shared e with second-minus-first sign. -/
theorem difference_cycle_value (R : NativeDescent.LocalGroupoid T fixedRegion leftRegion)
    (Q : NativeDescent.LocalGroupoid T fixedRegion rightRegion) :
    edgeCoordinates b₁ b₂ overlap overlap_shared
      (NativeCoverObstruction.differenceCycle T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R Q).1 =
        planValue b₁ b₂ true Q - planValue b₁ b₂ false R := by
  change kernelCoordinate b₁ b₂ vertexT
    ((CoverObstruction.differenceCycle M fixedRegion δ leftRegion rightRegion
      (NativeCoverObstruction.localCoordinate T fixedRegion (fixed_faces b₁ b₂) leftRegion R)
      (NativeCoverObstruction.localCoordinate T fixedRegion (fixed_faces b₁ b₂) rightRegion Q)).1.1
      ⟨name edgeE,overlap_shared⟩) = _
  rw [CoverObstruction.difference_cycle_value]
  rw [map_sub]
  rfl
/-- Every pair of independent actual local plans has the same complete H1 difference value. -/
theorem difference_class_value (R : NativeDescent.LocalGroupoid T fixedRegion leftRegion)
    (Q : NativeDescent.LocalGroupoid T fixedRegion rightRegion) :
    h1Coordinate b₁ b₂
      (NativeCoverObstruction.differenceClass T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R Q) = b₂ - b₁ := by
  rw [NativeCoverObstruction.differenceClass,h1Coordinate_class,difference_cycle_value,
    planValue_input,planValue_input]
  rfl
/-- Every independent actual pair evaluates to b2-b1 in the whole prescribed Omega quotient. -/
theorem omega_value (R : NativeDescent.LocalGroupoid T fixedRegion leftRegion)
    (Q : NativeDescent.LocalGroupoid T fixedRegion rightRegion) :
    omegaCoordinate b₁ b₂
      (NativeCoverObstruction.omega T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R Q) = b₂ - b₁ := by
  rw [NativeCoverObstruction.omega,omegaCoordinate_class,difference_class_value]
/-- Choice independence retains all independent actual plans in the original generic B quotient. -/
theorem omega_independent (R R' : NativeDescent.LocalGroupoid T fixedRegion leftRegion)
    (Q Q' : NativeDescent.LocalGroupoid T fixedRegion rightRegion) :
    NativeCoverObstruction.omega T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R Q =
      NativeCoverObstruction.omega T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R' Q' :=
  NativeCoverObstruction.omega_independent T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R R' Q Q'
/-- The same original connecting map has the required positive actual-defect class on every actual pair. -/
theorem connecting_actual_difference (R : NativeDescent.LocalGroupoid T fixedRegion leftRegion)
    (Q : NativeDescent.LocalGroupoid T fixedRegion rightRegion) :
    CoverObstructionKernel.connecting M fixedRegion leftRegion rightRegion regions_cover
      (NativeCoverObstruction.differenceClass T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R Q) =
        ActualRelative.obstructionClass T fixedRegion ∅ ∅ (fixed_faces b₁ b₂) (original_syzygy b₁ b₂) :=
  NativeCoverObstruction.connecting_actual_difference T fixedRegion (fixed_faces b₁ b₂)
    (original_syzygy b₁ b₂) leftRegion rightRegion regions_cover R Q
/-- The same entire Omega-to-original-H2 equivalence sends the actual class to its actual defect class. -/
theorem omega_original_class (R : NativeDescent.LocalGroupoid T fixedRegion leftRegion)
    (Q : NativeDescent.LocalGroupoid T fixedRegion rightRegion) :
    omegaOriginalH2Equiv b₁ b₂
      (NativeCoverObstruction.omega T fixedRegion (fixed_faces b₁ b₂) leftRegion rightRegion R Q) =
        ActualRelative.obstructionClass T fixedRegion ∅ ∅ (fixed_faces b₁ b₂) (original_syzygy b₁ b₂) :=
  NativeCoverObstruction.omega_kernel_actual_class T fixedRegion (fixed_faces b₁ b₂)
    (original_syzygy b₁ b₂) leftRegion rightRegion regions_cover R Q

end AAT.AG.RelativeRepairComposition.W5IntegrationObstruction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5IntegrationObstruction
