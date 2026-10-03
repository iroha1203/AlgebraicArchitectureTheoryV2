import ResearchLean.AG.RelativeRepairComposition.W3StrictGeneratedCover
import ResearchLean.AG.RelativeRepairComposition.W3LocalLabels
import ResearchLean.AG.RelativeRepairComposition.NativeAffineFiniteCover

/-! # W3's entire strict labels at both same original vertices

Strict agreement retains the whole original s and t kernel values. Every
actual global label has both inverse strict coordinates. Empty permission
keeps precisely the full fixed-vector group, including all stabilizers.
-/
namespace AAT.AG.RelativeRepairComposition.W3StrictLabels
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs W3FiniteCoefficients
open W3GaugeLabels W3LocalLabels W3StrictGeneratedCover
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (sheared : Bool)
local notation "T" => originalTower sheared
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)

/-- The full strict family compares original vertex values under every permission. -/
noncomputable abbrev Labels (S : Set (EdgeName (K := geometry))) :=
  StrictSupportedCover.Labels M fixedRegion regions candidates S

/-- Every full original actual label and every full strict compatible label have both additive inverses. -/
noncomputable def actualLabelEquiv (S : Set (EdgeName (K := geometry))) :
    GlobalLabels sheared S ≃+ Labels sheared S :=
  (NativeAffine.gaugeLabelEquivalence geometry (reference sheared) (reference sheared)
    comparison (linear_faces sheared) fixedRegion.vertices (fixedEdges S)).symm.trans
    ((SupportedNativeEquation.gaugeEquiv T fixedRegion candidates S).trans
      (StrictCoverRestoration.labelEquiv M fixedRegion regions candidates S enumRegions indexed_cover))

/-- Restoration keeps the entire actual vector at every original vertex. -/
theorem restore_original_vertex (S : Set (EdgeName (K := geometry))) (b : GlobalLabels sheared S)
    (v : geometry.Vertex) :
    ((actualLabelEquiv sheared S).symm (actualLabelEquiv sheared S b)).1 v = b.1 v :=
  congrArg (fun c : GlobalLabels sheared S => c.1 v) ((actualLabelEquiv sheared S).symm_apply_apply b)

/-- Extraction after restoration keeps the entire original strict label family. -/
theorem extract_restored_label (S : Set (EdgeName (K := geometry))) (b : Labels sheared S) :
    actualLabelEquiv sheared S ((actualLabelEquiv sheared S).symm b) = b :=
  (actualLabelEquiv sheared S).apply_symm_apply b

/-- Strict s matching compares the same entire original kernel vector in U and V. -/
theorem shared_s_value (S : Set (EdgeName (K := geometry))) (b : Labels sheared S) :
    (b.1 false).1.1 leftS = (b.1 true).1.1 rightS :=
  b.2 false true vertexS (Set.mem_univ _) (Set.mem_univ _)

/-- Strict t matching compares the same entire original kernel vector in U and V. -/
theorem shared_t_value (S : Set (EdgeName (K := geometry))) (b : Labels sheared S) :
    (b.1 false).1.1 leftT = (b.1 true).1.1 rightT :=
  b.2 false true vertexT (Set.mem_univ _) (Set.mem_univ _)

/-- Both whole actual s coordinates agree across the original strict patches. -/
theorem shared_s_coordinate (S : Set (EdgeName (K := geometry))) (b : Labels sheared S) :
    kernelCoordinate sheared vertexS ((b.1 false).1.1 leftS) =
      kernelCoordinate sheared vertexS ((b.1 true).1.1 rightS) :=
  congrArg (kernelCoordinate sheared vertexS) (shared_s_value sheared S b)

/-- Both whole actual t coordinates agree across the original strict patches. -/
theorem shared_t_coordinate (S : Set (EdgeName (K := geometry))) (b : Labels sheared S) :
    kernelCoordinate sheared vertexT ((b.1 false).1.1 leftT) =
      kernelCoordinate sheared vertexT ((b.1 true).1.1 rightT) :=
  congrArg (kernelCoordinate sheared vertexT) (shared_t_value sheared S b)

/-- Forward strict extraction reads the same full actual original vector on each patch. -/
theorem forward_patch_value (S : Set (EdgeName (K := geometry))) (b : GlobalLabels sheared S)
    (j : Bool) (v : (regions j).vertices) :
    kernelCoordinate sheared v.1 (((actualLabelEquiv sheared S b).1 j).1.1 v) = b.1 v.1 :=
  NativeAffine.finite_forward_label_value 2 geometry (reference sheared) (reference sheared)
    comparison (linear_faces sheared) fixedRegion regions candidates enumRegions indexed_cover S b j v

/-- The whole strict functor's arrow map is this same full-label extraction, for every S. -/
theorem actual_forward_label (S : Set (EdgeName (K := geometry)))
    {R Q : ActualCategory sheared S} (f : R ⟶ Q) :
    ((actualEquivalence sheared S).functor.map f).1.toAdd =
      actualLabelEquiv sheared S f.1.toAdd := rfl

/-- All strict empty-permission labels have both inverse coordinates in the whole original fixed-vector group. -/
noncomputable def emptyLabelsEquiv : Labels sheared ∅ ≃+ FixedVectors sheared :=
  (actualLabelEquiv sheared ∅).symm.trans (emptyLabelEquiv sheared)

/-- Empty strict labels retain their entire original fixed vector at each original vertex. -/
theorem empty_label_vector (b : Labels sheared ∅) (v : geometry.Vertex) :
    (emptyLabelsEquiv sheared b).1 = ((actualLabelEquiv sheared ∅).symm b).1 v := by
  have h := congrArg (fun c : GlobalLabels sheared ∅ => c.1 v)
    ((emptyLabelEquiv sheared).symm_apply_apply ((actualLabelEquiv sheared ∅).symm b))
  exact h

/-- Every full strict shear label is the original complete F3 fixed-vector coordinate. -/
noncomputable def shearLabelsEquiv : Labels true ∅ ≃+ ZMod 3 :=
  (emptyLabelsEquiv true).trans shearFixedEquiv

/-- Every full strict identity label is the same entire original A vector. -/
noncomputable def identityLabelsEquiv : Labels false ∅ ≃+ A :=
  (emptyLabelsEquiv false).trans identityFixedEquiv

end AAT.AG.RelativeRepairComposition.W3StrictLabels
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3StrictLabels
