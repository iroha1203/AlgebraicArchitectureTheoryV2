import ResearchLean.AG.RelativeRepairComposition.W2GaugeLabels
import ResearchLean.AG.RelativeRepairComposition.W2SingletonCoordinates

/-!
# W2's original restricted global, local and overlap groupoids

The actual global and one-edge patch groupoids have their full zero label
group. Their original overlap has the entire F3 label group. The equivalences
use the independent actual object and full-label correspondences, retaining
all original affine operations and every actual arrow.
-/
namespace AAT.AG.RelativeRepairComposition.W2EmptyGroupoids
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs W2GaugeLabels

/-- The point category has its complete trivial arrow group. -/
abbrev Point := SingleObj (Multiplicative PUnit.{1})
/-- BA has the full original additive F3 as its multiplicative arrow labels. -/
abbrev BA := SingleObj (Multiplicative (ZMod 3))

/-- Every full left label has mutually inverse zero-group coordinates. -/
noncomputable def leftLabelEquiv : LocalLabels leftRegion ∅ ≃+ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => 0
  left_inv b := (left_empty_zero b).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Every full right label has mutually inverse zero-group coordinates. -/
noncomputable def rightLabelEquiv : LocalLabels rightRegion ∅ ≃+ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => 0
  left_inv b := (right_empty_zero b).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The full actual global restricted repair groupoid is a point. -/
noncomputable def globalPointEquivalence : ActualCategory ∅ ≌ Point := by
  letI := gaugeAddAction geometry reference reference comparison linear_faces
    fixedRegion.vertices (fixedEdges ∅)
  exact W2SingletonCoordinates.equivalence emptyObjectEquiv globalEmptyLabelEquiv.toMultiplicative

/-- The full actual left restricted repair groupoid is a point. -/
noncomputable def leftPointEquivalence : LocalCategory leftRegion ∅ ≌ Point := by
  letI := gaugeAddAction (ClosedRegion.presentation leftRegion) (restrictOperations leftRegion reference)
    (restrictOperations leftRegion reference) (fun f => comparison f.1)
    (restricted_faces leftRegion reference linear_faces)
    (ClosedRegion.restrictedVertices leftRegion fixedRegion.vertices)
    (ClosedRegion.restrictedEdges leftRegion (fixedEdges ∅))
  exact W2SingletonCoordinates.equivalence (localEmptyObjectEquiv leftRegion) leftLabelEquiv.toMultiplicative

/-- The full actual right restricted repair groupoid is a point. -/
noncomputable def rightPointEquivalence : LocalCategory rightRegion ∅ ≌ Point := by
  letI := gaugeAddAction (ClosedRegion.presentation rightRegion) (restrictOperations rightRegion reference)
    (restrictOperations rightRegion reference) (fun f => comparison f.1)
    (restricted_faces rightRegion reference linear_faces)
    (ClosedRegion.restrictedVertices rightRegion fixedRegion.vertices)
    (ClosedRegion.restrictedEdges rightRegion (fixedEdges ∅))
  exact W2SingletonCoordinates.equivalence (localEmptyObjectEquiv rightRegion) rightLabelEquiv.toMultiplicative

/-- The entire original overlap groupoid is BA, retaining every full F3 arrow. -/
noncomputable def overlapBAEquivalence : LocalCategory overlap ∅ ≌ BA := by
  letI := gaugeAddAction (ClosedRegion.presentation overlap) (restrictOperations overlap reference)
    (restrictOperations overlap reference) (fun f => comparison f.1)
    (restricted_faces overlap reference linear_faces)
    (ClosedRegion.restrictedVertices overlap fixedRegion.vertices)
    (ClosedRegion.restrictedEdges overlap (fixedEdges ∅))
  exact W2SingletonCoordinates.equivalence (localEmptyObjectEquiv overlap) overlapLabelEquiv.toMultiplicative

/-- Forward overlap coordinates read the entire actual original w label on every arrow. -/
theorem overlap_forward_label {R Q : LocalCategory overlap ∅} (f : R ⟶ Q) :
    letI := gaugeAddAction (ClosedRegion.presentation overlap) (restrictOperations overlap reference)
      (restrictOperations overlap reference) (fun f => comparison f.1)
      (restricted_faces overlap reference linear_faces)
      (ClosedRegion.restrictedVertices overlap fixedRegion.vertices)
      (ClosedRegion.restrictedEdges overlap (fixedEdges ∅))
    Multiplicative.toAdd (overlapBAEquivalence.functor.map f) = f.1.toAdd.1 overlapW := rfl

end AAT.AG.RelativeRepairComposition.W2EmptyGroupoids
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2EmptyGroupoids
