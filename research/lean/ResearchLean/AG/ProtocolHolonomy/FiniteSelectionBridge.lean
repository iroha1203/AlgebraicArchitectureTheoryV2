import ResearchLean.AG.ProtocolHolonomy.FiniteIrredundantSelection
import ResearchLean.AG.ProtocolHolonomy.UndirectedNamedTrees
import Formal.Util.AssertStandardAxioms

/-!
# Retained original names satisfy the literal bridge condition

An alternate selected route between a retained edge's endpoints would let
every selected walk reroute around that edge. The erasure would still span all
original components, contradicting the finite pruning result. The conversion
from signed paths keeps the actual original edge names and their orientations.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- An alternate endpoint connection lets every selected connection avoid
the erased original name. -/
theorem selectedNamedReachable_erase_of_endpoints
    (Q : FixedFDirectedMultigraph.{u, v}) [DecidableEq Q.Edge]
    (selected : Finset Q.Edge) (e : Q.Edge)
    (halt : SelectedNamedReachable Q (selected.erase e)
      (Q.source e) (Q.target e))
    {a b : Q.Vertex} (h : SelectedNamedReachable Q selected a b) :
    SelectedNamedReachable Q (selected.erase e) a b := by
  induction h with
  | rel a b hab =>
      obtain ⟨f, hf, hs, ht⟩ := hab
      by_cases hfe : f = e
      · subst f
        simpa [hs, ht] using halt
      · exact Relation.EqvGen.rel _ _
          ⟨f, Finset.mem_erase.mpr ⟨hfe, hf⟩, hs, ht⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- A signed path using only permitted original names induces selected-name
reachability, including its backward traversals. -/
theorem usesNamedEdges_selectedReachable
    (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Q.Edge → Prop) (names : Finset Q.Edge)
    (hsub : ∀ e, selected e → e ∈ names)
    {a b : Q.Vertex} (p : SignedPath Q a b)
    (hp : UsesNamedEdges selected p) :
    SelectedNamedReachable Q names a b := by
  induction hp with
  | nil => exact Relation.EqvGen.refl _
  | cons p edge hp he ih =>
      cases edge with
      | inl f =>
          exact Relation.EqvGen.trans _ _ _ ih
            (Relation.EqvGen.rel _ _
              ⟨f.1, hsub f.1 he, f.2.1, f.2.2⟩)
      | inr f =>
          exact Relation.EqvGen.trans _ _ _ ih
            (Relation.EqvGen.symm _ _
              (Relation.EqvGen.rel _ _
                ⟨f.1, hsub f.1 he, f.2.1, f.2.2⟩))

/-- Each retained name is a bridge in the exact original signed-path sense. -/
theorem finiteSpanningEdgeSelection_bridge
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (e : Q.Edge)
    (he : e ∈ finiteSpanningEdgeSelection Q vertices edges) :
    ¬ ∃ p : SignedPath Q (Q.source e) (Q.target e),
      UsesNamedEdges
        (fun f => f ∈ finiteSpanningEdgeSelection Q vertices edges ∧ f ≠ e) p := by
  rintro ⟨p, hp⟩
  let selected := finiteSpanningEdgeSelection Q vertices edges
  have hreach : SelectedNamedReachable Q (selected.erase e)
      (Q.source e) (Q.target e) :=
    usesNamedEdges_selectedReachable Q _ (selected.erase e)
      (by
        intro f hf
        exact Finset.mem_erase.mpr ⟨hf.2, hf.1⟩)
      p hp
  have hspan : SpansOriginalComponents Q edges (selected.erase e) := by
    intro a b hab
    exact selectedNamedReachable_erase_of_endpoints Q selected e hreach
      (finiteSpanningEdgeSelection_spans Q vertices edges a b hab)
  exact finiteSpanningEdgeSelection_irredundant Q vertices edges e he hspan

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.selectedNamedReachable_erase_of_endpoints
#print axioms AAT.AG.ProtocolHolonomy.usesNamedEdges_selectedReachable
#print axioms AAT.AG.ProtocolHolonomy.finiteSpanningEdgeSelection_bridge
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
