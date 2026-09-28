import ResearchLean.AG.ProtocolHolonomy.SelectedNamedPaths
import Formal.Util.AssertStandardAxioms

/-!
# Construct the original named spanning forest from finite tables

Restrict the input-generated edge selection to each original component. The
selected-path equivalence supplies connectivity, while the finite bridge
theorem excludes every alternate route after removing a retained original
name. This yields the actual forest structure, with no supplied tree.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- Weakening the permitted original edge-name predicate preserves a signed
path's name certificate. -/
theorem usesNamedEdges_mono
    (Q : FixedFDirectedMultigraph.{u, v})
    (selected larger : Q.Edge → Prop)
    (hsub : ∀ e, selected e → larger e)
    {a b : Q.Vertex} (p : SignedPath Q a b)
    (hp : UsesNamedEdges selected p) : UsesNamedEdges larger p := by
  induction hp with
  | nil => exact UsesNamedEdges.nil _
  | cons p edge hp he ih =>
      exact UsesNamedEdges.cons _ _ ih (hsub _ he)

/-- Every original name on a selected path starting in a component belongs
to that same original component. -/
theorem usesNamedEdges_restrictComponent
    (Q : FixedFDirectedMultigraph.{u, v})
    (selected : Finset Q.Edge) (j : FixedFComponent Q)
    {a b : Q.Vertex} (p : SignedPath Q a b)
    (ha : fixedFComponentMk Q a = j)
    (hp : UsesNamedEdges (fun e => e ∈ selected) p) :
    UsesNamedEdges
      (fun e => e ∈ selected ∧ fixedFComponentMk Q (Q.source e) = j) p := by
  induction hp with
  | nil => exact UsesNamedEdges.nil _
  | cons p edge hp he ih =>
      rename_i t z
      have ht : fixedFComponentMk Q t = j :=
        ((component_eq_iff_signedReachable Q a t).mpr ⟨p⟩).symm.trans ha
      cases edge with
      | inl f =>
          have hsource : fixedFComponentMk Q (Q.source f.1) = j := by
            simpa [f.2.1] using ht
          exact UsesNamedEdges.cons _ _ ih ⟨he, hsource⟩
      | inr f =>
          have hst : fixedFComponentMk Q (Q.source f.1) =
              fixedFComponentMk Q (Q.target f.1) :=
            (component_eq_iff_signedReachable Q _ _).mpr
              ⟨signedToPath Q (Sum.inl ⟨f.1, rfl, rfl⟩)⟩
          have hsource : fixedFComponentMk Q (Q.source f.1) = j :=
            hst.trans (by simpa [f.2.2] using ht)
          exact UsesNamedEdges.cons _ _ ih ⟨he, hsource⟩

/-- The edge set computed solely from the explicit original tables is a
genuine undirected named spanning forest on every original component. -/
def finiteNamedSpanningForest
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge) :
    UndirectedNamedSpanningForest Q where
  tree j :=
    { selected := fun e =>
        e ∈ finiteSpanningEdgeSelection Q vertices edges ∧
          fixedFComponentMk Q (Q.source e) = j
      within := by
        intro e he
        exact he.2
      connected := by
        intro a b
        have hsame : fixedFComponentMk Q a.1 = fixedFComponentMk Q b.1 :=
          a.2.trans b.2.symm
        have horig : FixedFUndirectedReachable Q a.1 b.1 :=
          (fixedFComponentMk_eq_iff Q a.1 b.1).mp hsame
        have hselected := finiteSpanningEdgeSelection_originalReachable
          Q vertices edges a.1 b.1 horig
        obtain ⟨p, hp⟩ :=
          (selectedNamedReachable_iff_usesNamedEdges Q
            (finiteSpanningEdgeSelection Q vertices edges) a.1 b.1).mp hselected
        exact ⟨p, usesNamedEdges_restrictComponent Q _ j p a.2 hp⟩
      bridge := by
        intro e he hpath
        obtain ⟨p, hp⟩ := hpath
        apply finiteSpanningEdgeSelection_bridge Q vertices edges e he.1
        refine ⟨p, ?_⟩
        exact usesNamedEdges_mono Q _ _
          (by intro f hf; exact ⟨hf.1.1, hf.2⟩) p hp }

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.usesNamedEdges_mono
#print axioms AAT.AG.ProtocolHolonomy.usesNamedEdges_restrictComponent
#print axioms AAT.AG.ProtocolHolonomy.finiteNamedSpanningForest
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
