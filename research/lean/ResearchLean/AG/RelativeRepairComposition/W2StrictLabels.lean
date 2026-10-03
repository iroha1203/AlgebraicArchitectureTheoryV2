import ResearchLean.AG.RelativeRepairComposition.W2StrictGeneratedCover

/-!
# Full actual W2 labels, strict original-vertex agreement and zero empty arrows

The strict construction compares the full values at the same original w. Its
complete label group is equivalent to the actual global gauge group for every
permission set. Under empty permission the full label is zero, while ordinary
descent retains all three independent overlap seams.
-/
namespace AAT.AG.RelativeRepairComposition.W2StrictLabels
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs W2FiniteCoefficients W2GaugeLabels
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower originalTower)

/-- The strict label family retains full values at every original vertex. -/
noncomputable abbrev Labels (S : Set (EdgeName (K := geometry))) :=
  StrictSupportedCover.Labels M fixedRegion regions candidates S

/-- Every full actual global label and every full compatible original local label correspond, for all S. -/
noncomputable def actualLabelEquiv (S : Set (EdgeName (K := geometry))) : GlobalLabels S ≃+ Labels S :=
  (NativeAffine.gaugeLabelEquivalence geometry reference reference comparison linear_faces
    fixedRegion.vertices (fixedEdges S)).symm.trans
    ((SupportedNativeEquation.gaugeEquiv originalTower fixedRegion candidates S).trans
      (StrictCoverRestoration.labelEquiv M fixedRegion regions candidates S enumRegions indexed_cover))

/-- Restoring a strict reading retains every full actual original vertex value. -/
theorem restore_original_vertex (S : Set (EdgeName (K := geometry))) (b : GlobalLabels S)
    (v : geometry.Vertex) :
    ((actualLabelEquiv S).symm (actualLabelEquiv S b)).1 v = b.1 v :=
  congrArg (fun c : GlobalLabels S => c.1 v) ((actualLabelEquiv S).symm_apply_apply b)

/-- Extraction after restoration retains the entire strict label family. -/
theorem extract_restored_label (S : Set (EdgeName (K := geometry))) (b : Labels S) :
    actualLabelEquiv S ((actualLabelEquiv S).symm b) = b :=
  (actualLabelEquiv S).apply_symm_apply b

/-- Strict agreement compares the same whole original kernel value at w in U and V. -/
theorem shared_w_value (S : Set (EdgeName (K := geometry))) (b : Labels S) :
    (b.1 false).1.1 W2GaugeLabels.leftW = (b.1 true).1.1 W2GaugeLabels.rightW :=
  b.2 false true vertexW (Or.inr rfl) (Or.inl rfl)

/-- The same whole original w kernel has equal full F3 readings on the two strict patches. -/
theorem shared_w_coordinate (S : Set (EdgeName (K := geometry))) (b : Labels S) :
    kernelCoordinate vertexW ((b.1 false).1.1 W2GaugeLabels.leftW) =
      kernelCoordinate vertexW ((b.1 true).1.1 W2GaugeLabels.rightW) :=
  congrArg (kernelCoordinate vertexW) (shared_w_value S b)

/-- Every complete strict empty-permission label is zero, including the original w value. -/
theorem empty_label_zero (b : Labels ∅) : b = 0 := by
  apply (actualLabelEquiv ∅).symm.injective
  exact (global_empty_zero ((actualLabelEquiv ∅).symm b)).trans
    ((actualLabelEquiv ∅).symm.map_zero).symm

/-- Every strictly generated empty-permission arrow has its entire original label equal to zero. -/
theorem empty_arrow_label {g h : W2StrictGeneratedCover.Groupoid ∅} (f : g ⟶ h) :
    f.1.toAdd = 0 := empty_label_zero f.1.toAdd

end AAT.AG.RelativeRepairComposition.W2StrictLabels
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2StrictLabels
