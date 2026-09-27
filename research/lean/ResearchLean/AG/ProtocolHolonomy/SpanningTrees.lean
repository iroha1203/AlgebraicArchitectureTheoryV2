import ResearchLean.AG.ProtocolHolonomy.VerticalCentralizer
import Mathlib.Combinatorics.Quiver.Arborescence
import Formal.Util.AssertStandardAxioms

/-!
# Spanning trees retaining original signed named edges

Each original undirected component is represented as a quiver whose arrows
are the actual positive or negative named edge passages. A spanning tree is
an outward arborescence of a wide subquiver, preserving parallel edge names.
Its unique root paths supply the `RootedPaths` data used in B1 and B2.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

abbrev ComponentVertex (Q : FixedFDirectedMultigraph.{u, v})
    (j : FixedFComponent Q) :=
  {x : Q.Vertex // fixedFComponentMk Q x = j}

/-- The signed original named edges within one existing component. -/
instance componentSignedQuiver (Q : FixedFDirectedMultigraph.{u, v})
    (j : FixedFComponent Q) : Quiver (ComponentVertex Q j) where
  Hom a b := (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom a.1 b.1

/-- Read a signed original named path inside its existing component. -/
def signedToComponentPath {Q : FixedFDirectedMultigraph.{u, v}}
    {s t : Q.Vertex} (p : SignedPath Q s t)
    (j : FixedFComponent Q) (hs : fixedFComponentMk Q s = j) :
    @Quiver.Path (ComponentVertex Q j) (componentSignedQuiver Q j)
      ⟨s, hs⟩ ⟨t, ReversibleData.path_target_component p j hs⟩ := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil => exact Quiver.Path.nil
  | cons p e ih => exact ih.cons e

/-- Every vertex in an original component is reachable from any chosen root. -/
theorem component_rootedConnected (Q : FixedFDirectedMultigraph.{u, v})
    (j : FixedFComponent Q) (r : ComponentVertex Q j) :
    Quiver.RootedConnected r := by
  refine ⟨?_⟩
  intro b
  have hsame : fixedFComponentMk Q r.1 = fixedFComponentMk Q b.1 :=
    r.2.trans b.2.symm
  obtain ⟨p⟩ := (component_eq_iff_signedReachable Q r.1 b.1).mp hsame
  exact ⟨signedToComponentPath p j r.2⟩

/-- A chosen oriented spanning tree inside one component, carrying edge names. -/
structure NamedSpanningTree (Q : FixedFDirectedMultigraph.{u, v})
    (j : FixedFComponent Q) where
  edges : WideSubquiver (ComponentVertex Q j)
  arborescence : Quiver.Arborescence edges

namespace NamedSpanningTree

variable {Q : FixedFDirectedMultigraph.{u, v}} {j : FixedFComponent Q}
  (T : NamedSpanningTree Q j)

/-- The actual root vertex of the selected tree. -/
def root : ComponentVertex Q j := by
  letI := T.arborescence
  exact Quiver.root T.edges

/-- Its unique directed path, with tree edge names retained. -/
def rootPath (x : ComponentVertex Q j) :
    @Quiver.Path T.edges (WideSubquiver.quiver T.edges) T.root x := by
  letI := T.arborescence
  change Quiver.Path (Quiver.root T.edges) x
  exact (T.arborescence.uniquePath x).default

/-- Any tree path from the chosen root is the selected path. -/
theorem rootPath_unique (x : ComponentVertex Q j)
    (p : @Quiver.Path T.edges (WideSubquiver.quiver T.edges) T.root x) :
    p = T.rootPath x := by
  letI : Unique (@Quiver.Path T.edges (WideSubquiver.quiver T.edges)
      T.root x) := T.arborescence.uniquePath x
  exact Subsingleton.elim _ _

/-- Forget the tree-edge selection while retaining each signed named edge. -/
def pathToSigned {a b : ComponentVertex Q j}
    (p : @Quiver.Path T.edges (WideSubquiver.quiver T.edges) a b) :
    SignedPath Q a.1 b.1 := by
  induction p with
  | nil => exact signedNil Q a.1
  | cons p e ih => exact signedCons Q ih e.1

/-- The tree path to its root is empty, by uniqueness. -/
theorem rootPath_self :
    T.rootPath T.root =
      (@Quiver.Path.nil T.edges (WideSubquiver.quiver T.edges) T.root) := by
  letI := T.arborescence
  letI : Unique (@Quiver.Path T.edges (WideSubquiver.quiver T.edges)
      T.root T.root) := T.arborescence.uniquePath T.root
  exact Subsingleton.elim _ _

end NamedSpanningTree

/-- A named spanning tree exists from any selected root, using shortest signed
paths in the original component. This structural choice is noncomputable;
GOAL E separately requires a terminating finite-table construction. -/
noncomputable def geodesicNamedSpanningTree
    (Q : FixedFDirectedMultigraph.{u, v})
    (j : FixedFComponent Q) (r : ComponentVertex Q j) :
    NamedSpanningTree Q j := by
  letI : Quiver.RootedConnected r := component_rootedConnected Q j r
  exact { edges := Quiver.geodesicSubtree r, arborescence := inferInstance }

theorem geodesicNamedSpanningTree_root
    (Q : FixedFDirectedMultigraph.{u, v})
    (j : FixedFComponent Q) (r : ComponentVertex Q j) :
    (geodesicNamedSpanningTree Q j r).root = r := by
  rfl

/-- One chosen named spanning tree for every existing undirected component. -/
structure NamedSpanningForest (Q : FixedFDirectedMultigraph.{u, v}) where
  tree : ∀ j : FixedFComponent Q, NamedSpanningTree Q j

/-- Construct one outward named tree per component from arbitrary chosen roots. -/
noncomputable def geodesicNamedSpanningForest
    (Q : FixedFDirectedMultigraph.{u, v})
    (roots : ∀ j : FixedFComponent Q, ComponentVertex Q j) :
    NamedSpanningForest Q where
  tree j := geodesicNamedSpanningTree Q j (roots j)

/-- A structural spanning forest exists for every original named graph. -/
noncomputable def chooseNamedSpanningForest
    (Q : FixedFDirectedMultigraph.{u, v}) : NamedSpanningForest Q :=
  geodesicNamedSpanningForest Q
    (fun j => ⟨Quotient.out j, Quotient.out_eq j⟩)

namespace NamedSpanningForest

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (S : NamedSpanningForest Q)

/-- The unique paths of any chosen spanning forest provide B's root data. -/
def toRootedPaths : RootedPaths Q where
  root j := (S.tree j).root.1
  root_component j := (S.tree j).root.2
  path j x hx :=
    (S.tree j).pathToSigned
      ((S.tree j).rootPath (⟨x, hx⟩ : ComponentVertex Q j))
  path_root := by
    intro j
    change (S.tree j).pathToSigned ((S.tree j).rootPath (S.tree j).root) =
      signedNil Q (S.tree j).root.1
    rw [(S.tree j).rootPath_self]
    rfl

end NamedSpanningForest
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.component_rootedConnected
#print axioms AAT.AG.ProtocolHolonomy.NamedSpanningTree.rootPath_unique
#print axioms AAT.AG.ProtocolHolonomy.geodesicNamedSpanningTree
#print axioms AAT.AG.ProtocolHolonomy.geodesicNamedSpanningTree_root
#print axioms AAT.AG.ProtocolHolonomy.NamedSpanningForest.toRootedPaths
#print axioms AAT.AG.ProtocolHolonomy.chooseNamedSpanningForest
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
