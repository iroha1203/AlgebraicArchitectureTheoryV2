import ResearchLean.AG.RelativeRepairComposition.W2EmptyGroupoids
import ResearchLean.AG.RelativeRepairComposition.CommaCoordinates

/-!
# The actual restricted W2 ordinary descent diagram

The original overlap has no edge operation to select and its sole original
vertex is w. Each boundary map therefore restricts the full actual label to
that same w. The diagram is constructed from those actual restrictions before
computing its comma objects or comparing its number of classes.
-/
namespace AAT.AG.RelativeRepairComposition.W2RestrictionDiagram
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions W2ActualRepairs W2GaugeLabels W2EmptyGroupoids

/-- The original full affine label action on the actual left patch. -/
noncomputable local instance leftAction :
    AddAction (LocalLabels leftRegion ∅) (LocalRepairs leftRegion ∅) :=
  gaugeAddAction (ClosedRegion.presentation leftRegion) (restrictOperations leftRegion reference)
    (restrictOperations leftRegion reference) (fun f => comparison f.1)
    (restricted_faces leftRegion reference linear_faces)
    (ClosedRegion.restrictedVertices leftRegion fixedRegion.vertices)
    (ClosedRegion.restrictedEdges leftRegion (fixedEdges ∅))

/-- The original full affine label action on the actual right patch. -/
noncomputable local instance rightAction :
    AddAction (LocalLabels rightRegion ∅) (LocalRepairs rightRegion ∅) :=
  gaugeAddAction (ClosedRegion.presentation rightRegion) (restrictOperations rightRegion reference)
    (restrictOperations rightRegion reference) (fun f => comparison f.1)
    (restricted_faces rightRegion reference linear_faces)
    (ClosedRegion.restrictedVertices rightRegion fixedRegion.vertices)
    (ClosedRegion.restrictedEdges rightRegion (fixedEdges ∅))

/-- The original full affine label action on the original overlap. -/
noncomputable local instance overlapAction :
    AddAction (LocalLabels overlap ∅) (LocalRepairs overlap ∅) :=
  gaugeAddAction (ClosedRegion.presentation overlap) (restrictOperations overlap reference)
    (restrictOperations overlap reference) (fun f => comparison f.1)
    (restricted_faces overlap reference linear_faces)
    (ClosedRegion.restrictedVertices overlap fixedRegion.vertices)
    (ClosedRegion.restrictedEdges overlap (fixedEdges ∅))

/-- The actual left restriction keeps the original w value on every overlap vertex. -/
noncomputable def leftLabelRestriction : LocalLabels leftRegion ∅ →+ LocalLabels overlap ∅ where
  toFun b := overlapLabel (b.1 leftW)
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The actual right restriction keeps the same original w value on every overlap vertex. -/
noncomputable def rightLabelRestriction : LocalLabels rightRegion ∅ →+ LocalLabels overlap ∅ where
  toFun b := overlapLabel (b.1 rightW)
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Every restricted left actual label has its original w coordinate. -/
theorem left_label_value (b : LocalLabels leftRegion ∅) :
    (leftLabelRestriction b).1 overlapW = b.1 leftW := rfl

/-- Every restricted right actual label has its original w coordinate. -/
theorem right_label_value (b : LocalLabels rightRegion ∅) :
    (rightLabelRestriction b).1 overlapW = b.1 rightW := rfl

/-- No original overlap edge value can be changed or discarded by left restriction. -/
theorem left_operation_restriction (R : LocalRepairs leftRegion ∅)
    {i j : (ClosedRegion.presentation overlap).Vertex} (e : (ClosedRegion.presentation overlap).Edge i j) :
    (localReferenceRepair overlap ∅).operation e =
      R.operation (show ClosedRegion.Edge leftRegion
        ⟨i.1,(ClosedRegion.inter_left leftRegion rightRegion).vertices i.2⟩
        ⟨j.1,(ClosedRegion.inter_left leftRegion rightRegion).vertices j.2⟩ from
        ⟨e.1,(ClosedRegion.inter_left leftRegion rightRegion).edges e.2⟩) := by
  exact (overlap_no_edge ⟨i,j,e⟩).elim

/-- No original overlap edge value can be changed or discarded by right restriction. -/
theorem right_operation_restriction (R : LocalRepairs rightRegion ∅)
    {i j : (ClosedRegion.presentation overlap).Vertex} (e : (ClosedRegion.presentation overlap).Edge i j) :
    (localReferenceRepair overlap ∅).operation e =
      R.operation (show ClosedRegion.Edge rightRegion
        ⟨i.1,(ClosedRegion.inter_right leftRegion rightRegion).vertices i.2⟩
        ⟨j.1,(ClosedRegion.inter_right leftRegion rightRegion).vertices j.2⟩ from
        ⟨e.1,(ClosedRegion.inter_right leftRegion rightRegion).edges e.2⟩) := by
  exact (overlap_no_edge ⟨i,j,e⟩).elim

/-- The original actual left repair restriction keeps all actual arrows through their original labels. -/
noncomputable def leftRestriction : LocalCategory leftRegion ∅ ⥤ LocalCategory overlap ∅ :=
  actionLabelFunctor leftLabelRestriction.toMultiplicative
    (fun _ => localReferenceRepair overlap ∅)
    (fun _ _ => (local_empty_unique overlap _).symm)

/-- The original actual right repair restriction keeps all actual arrows through their original labels. -/
noncomputable def rightRestriction : LocalCategory rightRegion ∅ ⥤ LocalCategory overlap ∅ :=
  actionLabelFunctor rightLabelRestriction.toMultiplicative
    (fun _ => localReferenceRepair overlap ∅)
    (fun _ _ => (local_empty_unique overlap _).symm)

/-- Mapping a full left actual arrow preserves its original w label exactly. -/
theorem left_map_value {R Q : LocalCategory leftRegion ∅} (f : R ⟶ Q) :
    ((leftRestriction.map f).1.toAdd).1 overlapW = f.1.toAdd.1 leftW := rfl

/-- Mapping a full right actual arrow preserves its original w label exactly. -/
theorem right_map_value {R Q : LocalCategory rightRegion ∅} (f : R ⟶ Q) :
    ((rightRestriction.map f).1.toAdd).1 overlapW = f.1.toAdd.1 rightW := rfl

/-- The ordinary homotopy pullback is the actual full comma of the original restrictions. -/
abbrev Ordinary := Comma leftRestriction rightRestriction

/-- Every ordinary overlap morphism is an isomorphism, since both actual patches are groupoids. -/
theorem ordinary_is_groupoid : IsGroupoid Ordinary :=
  CommaCoordinates.comma_is_groupoid leftRestriction rightRestriction

end AAT.AG.RelativeRepairComposition.W2RestrictionDiagram
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2RestrictionDiagram
