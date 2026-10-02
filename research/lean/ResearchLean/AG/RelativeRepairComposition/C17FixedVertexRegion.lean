import ResearchLean.AG.RelativeRepairComposition.C17IsomorphismClasses

/-! # W4's independently specified closed part fixing the new vertex
## Implementation notes

This closed part is specified independently, fixes both actual vertices, and keeps the same retained fixed cells. It is a second input, not a modification of the free-vertex equivalence. Encoding the fixed vertex in a chosen equivalence would conceal the change from three to nine classes.
-/
namespace AAT.AG.RelativeRepairComposition.C17SubdivisionInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction

/-- The separate original closed part contains both vertices and exactly the same retained fixed cells. -/
noncomputable def fixedBothRegion : ClosedRegion (Subdivision.presentation geometry chosen) where
  vertices := Set.univ
  edges := Subdivision.oldEdgeSet geometry chosen ∅
  faces := ∅
  triples := ∅
  edge_closed := by
    intro e he
    rw [Subdivision.old_set_empty] at he
    exact he.elim
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim

/-- The separate fixed-new-vertex groupoid is the actual groupoid of this independently specified closed part. -/
theorem fixed_new_input :
    RepairGroupoid splitTower fixedBothRegion.vertices fixedBothRegion.edges = FixedNewCategory := rfl
/-- The new intermediate vertex is fixed in the separate input. -/
theorem new_vertex_fixed :
    (Sum.inr () : (Subdivision.presentation geometry chosen).Vertex) ∈ fixedBothRegion.vertices :=
  Set.mem_univ _
/-- The same separate closed-part input has all nine actual isomorphism classes. -/
theorem closed_fixed_new_class_card :
    Nat.card (Quotient (isIsomorphicSetoid
      (RepairGroupoid splitTower fixedBothRegion.vertices fixedBothRegion.edges))) = 9 :=
  fixed_new_class_card

end AAT.AG.RelativeRepairComposition.C17SubdivisionInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C17SubdivisionInput
