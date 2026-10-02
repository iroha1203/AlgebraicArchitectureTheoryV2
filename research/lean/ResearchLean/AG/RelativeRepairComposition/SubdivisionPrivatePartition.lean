import ResearchLean.AG.RelativeRepairComposition.SubdivisionClosedCovers
import ResearchLean.AG.RelativeRepairComposition.FiniteCoordinatePartition

/-!
# Independently generated shared and private sets after subdivision

## Implementation notes

The new shared and private sets use the existing cover definitions on the
generated new regions. Their equations are proved by reading complete original
names, rather than defining the new private set to be the desired image. Both
factors are private precisely when the chosen edge is private. Full public
name comparison is therefore possible without deleting either factor freedom.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open TransportCoherence
universe uG uI
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))
variable {I : Type uI} (U : I → ClosedRegion K) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K)))

/-- Sharedness in the generated cover reads exactly original sharedness. -/
theorem expanded_shared_edges (i : I) :
    ClosedRegion.sharedEdges (fun j => expandedRegion K chosen (U j)) i =
      expandedEdgeSet K chosen (ClosedRegion.sharedEdges U i) := rfl

/-- The independently defined private set reads exactly the original four private conditions. -/
theorem expanded_private_edges (hc : chosen ∉ candidates) (i : I) :
    ClosedRegion.privateAlwaysEdges (fun j => expandedRegion K chosen (U j))
      (expandedRegion K chosen P) (oldEdgeSet K chosen candidates) i =
      expandedEdgeSet K chosen (ClosedRegion.privateAlwaysEdges U P candidates i) := by
  rw [← expanded_set_avoiding K chosen candidates hc]
  rfl

/-- Each retained original complete name has exactly its original sharedness. -/
theorem retained_shared_iff (i : I) (e : EdgeName (K := K)) (he : e ≠ chosen) :
    oldEdgeName K chosen e he ∈ ClosedRegion.sharedEdges
      (fun j => expandedRegion K chosen (U j)) i ↔ e ∈ ClosedRegion.sharedEdges U i := Iff.rfl

/-- Every retained full name has exactly the original private membership. -/
theorem retained_private_iff (hc : chosen ∉ candidates) (i : I)
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    oldEdgeName K chosen e he ∈ ClosedRegion.privateAlwaysEdges
      (fun j => expandedRegion K chosen (U j)) (expandedRegion K chosen P)
      (oldEdgeSet K chosen candidates) i ↔ e ∈ ClosedRegion.privateAlwaysEdges U P candidates i := by
  rw [expanded_private_edges K chosen U P candidates hc]
  exact Iff.rfl

/-- The first factor is private exactly when the original chosen edge is private. -/
theorem first_private_iff (hc : chosen ∉ candidates) (i : I) :
    firstEdgeName K chosen ∈ ClosedRegion.privateAlwaysEdges
      (fun j => expandedRegion K chosen (U j)) (expandedRegion K chosen P)
      (oldEdgeSet K chosen candidates) i ↔ chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i := by
  rw [expanded_private_edges K chosen U P candidates hc]
  exact Iff.rfl

/-- The second factor has the same full private condition, without removing its correction coordinate. -/
theorem second_private_iff (hc : chosen ∉ candidates) (i : I) :
    secondEdgeName K chosen ∈ ClosedRegion.privateAlwaysEdges
      (fun j => expandedRegion K chosen (U j)) (expandedRegion K chosen P)
      (oldEdgeSet K chosen candidates) i ↔ chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i := by
  rw [expanded_private_edges K chosen U P candidates hc]
  exact Iff.rfl

/-- A private chosen edge belongs to no other member of the original cover. -/
theorem chosen_outside_other (i j : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (hj : j ≠ i) :
    chosen ∉ (U j).edges := by
  intro he
  exact hi.2.2.2 ⟨j,hj,he⟩

/-- Original private membership supplies the uniqueness used for retained overlaps. -/
theorem private_chosen_unique (i : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) :
    ∀ j l, chosen ∈ (U j).edges → chosen ∈ (U l).edges → j = l := by
  intro j l hj hl
  have hji : j = i := by
    by_contra h
    exact chosen_outside_other K chosen U P candidates i j hi h hj
  have hli : l = i := by
    by_contra h
    exact chosen_outside_other K chosen U P candidates i l hi h hl
  exact hji.trans hli.symm

/-- A chosen private edge creates no fresh vertex in any other cover member. -/
theorem fresh_outside_other (i j : I)
    (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (hj : j ≠ i) :
    (Sum.inr () : (presentation K chosen).Vertex) ∉ (expandedRegion K chosen (U j)).vertices :=
  chosen_outside_other K chosen U P candidates i j hi hj

/-- All candidates remain nonprivate in every generated member. -/
theorem retained_candidate_not_private (hc : chosen ∉ candidates) (i : I)
    (e : EdgeName (K := K)) (he : e ∈ candidates) :
    oldEdgeName K chosen e (fun h => hc (h ▸ he)) ∉ ClosedRegion.privateAlwaysEdges
      (fun j => expandedRegion K chosen (U j)) (expandedRegion K chosen P)
      (oldEdgeSet K chosen candidates) i := by
  rw [retained_private_iff K chosen U P candidates hc]
  exact ClosedRegion.candidate_not_private U P candidates i e he

/-- Every original shared value stays outside the generated private variables. -/
theorem retained_shared_not_private (hc : chosen ∉ candidates) (i : I)
    (e : EdgeName (K := K)) (he : e ≠ chosen) (hs : e ∈ ClosedRegion.sharedEdges U i) :
    oldEdgeName K chosen e he ∉ ClosedRegion.privateAlwaysEdges
      (fun j => expandedRegion K chosen (U j)) (expandedRegion K chosen P)
      (oldEdgeSet K chosen candidates) i := by
  rw [retained_private_iff K chosen U P candidates hc]
  exact ClosedRegion.shared_not_private U P candidates i e hs

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
