import ResearchLean.AG.ProtocolHolonomy.SpanningTrees
import Formal.Util.AssertStandardAxioms

/-!
# Undirected spanning trees of original named edges

An undirected tree selects original edge names, independent of their stored
orientation. Connectivity is witnessed by signed passages through selected
edges. Every selected edge is a bridge; this excludes loops and parallel-edge
cycles without identifying their names. Any root in each such tree supplies
the root paths used by B1, B2, and C1. The finite-table construction of such
trees belongs to E.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- A signed path passes only through the selected original named edges. -/
inductive UsesNamedEdges {Q : FixedFDirectedMultigraph.{u, v}}
    (selected : Q.Edge → Prop) :
    {s t : Q.Vertex} → SignedPath Q s t → Prop where
  | nil (s : Q.Vertex) : UsesNamedEdges selected (signedNil Q s)
  | cons {s t z : Q.Vertex} (p : SignedPath Q s t)
      (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom t z)
      (hp : UsesNamedEdges selected p)
      (he : selected (match e with
        | Sum.inl f => f.1
        | Sum.inr f => f.1)) :
      UsesNamedEdges selected (signedCons Q p e)

/-- An intrinsic undirected spanning tree on one original graph component.
The bridge condition excludes a selected edge whenever its endpoints remain
connected after removing that exact edge name. -/
structure UndirectedNamedSpanningTree
    (Q : FixedFDirectedMultigraph.{u, v}) (j : FixedFComponent Q) where
  selected : Q.Edge → Prop
  within : ∀ e : Q.Edge, selected e → fixedFComponentMk Q (Q.source e) = j
  connected : ∀ a b : ComponentVertex Q j,
    ∃ p : SignedPath Q a.1 b.1, UsesNamedEdges selected p
  bridge : ∀ e : Q.Edge, selected e →
    ¬ ∃ p : SignedPath Q (Q.source e) (Q.target e),
      UsesNamedEdges (fun f => selected f ∧ f ≠ e) p

namespace UndirectedNamedSpanningTree

variable {Q : FixedFDirectedMultigraph.{u, v}} {j : FixedFComponent Q}
    (T : UndirectedNamedSpanningTree Q j)

/-- Select a root-to-vertex path in the actual named tree. The root path is
normalized to the empty path. -/
noncomputable def pathFromRootWithProof (r x : ComponentVertex Q j) :
    {p : SignedPath Q r.1 x.1 // UsesNamedEdges T.selected p} := by
  classical
  by_cases h : x = r
  · subst x
    exact ⟨signedNil Q r.1, UsesNamedEdges.nil r.1⟩
  · exact ⟨Classical.choose (T.connected r x),
      Classical.choose_spec (T.connected r x)⟩

noncomputable def pathFromRoot (r x : ComponentVertex Q j) :
    SignedPath Q r.1 x.1 := (T.pathFromRootWithProof r x).1

/-- Every chosen root path uses only the original selected edge names. -/
theorem pathFromRoot_usesEdges (r x : ComponentVertex Q j) :
    UsesNamedEdges T.selected (T.pathFromRoot r x) :=
  (T.pathFromRootWithProof r x).2

/-- The normalized root-to-root path is empty. -/
theorem pathFromRoot_self (r : ComponentVertex Q j) :
    T.pathFromRoot r r = signedNil Q r.1 := by
  classical
  unfold pathFromRoot pathFromRootWithProof
  simp

end UndirectedNamedSpanningTree

/-- A tree on every component, with edge names kept in the original edge
carrier. -/
structure UndirectedNamedSpanningForest
    (Q : FixedFDirectedMultigraph.{u, v}) where
  tree : ∀ j : FixedFComponent Q, UndirectedNamedSpanningTree Q j

namespace UndirectedNamedSpanningForest

variable {Q : FixedFDirectedMultigraph.{u, v}}
    (S : UndirectedNamedSpanningForest Q)

/-- Any roots in the respective components and any genuine undirected named
spanning forest give the exact root-path input of B and C. -/
noncomputable def toRootedPaths
    (roots : ∀ j : FixedFComponent Q, ComponentVertex Q j) : RootedPaths Q where
  root j := (roots j).1
  root_component j := (roots j).2
  path j x hx := (S.tree j).pathFromRoot (roots j) ⟨x, hx⟩
  path_root := by
    intro j
    exact (S.tree j).pathFromRoot_self (roots j)

/-- Its B/C root paths stay entirely in the selected original named tree. -/
theorem toRootedPaths_path_usesEdges
    (roots : ∀ j : FixedFComponent Q, ComponentVertex Q j)
    (j : FixedFComponent Q) (x : Q.Vertex)
    (hx : fixedFComponentMk Q x = j) :
    UsesNamedEdges (S.tree j).selected ((S.toRootedPaths roots).path j x hx) :=
  (S.tree j).pathFromRoot_usesEdges (roots j) ⟨x, hx⟩

end UndirectedNamedSpanningForest

#print axioms AAT.AG.ProtocolHolonomy.UndirectedNamedSpanningTree.pathFromRoot_usesEdges
#print axioms AAT.AG.ProtocolHolonomy.UndirectedNamedSpanningTree.pathFromRoot_self
#print axioms AAT.AG.ProtocolHolonomy.UndirectedNamedSpanningForest.toRootedPaths
#print axioms AAT.AG.ProtocolHolonomy.UndirectedNamedSpanningForest.toRootedPaths_path_usesEdges
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
end AAT.AG.ProtocolHolonomy
