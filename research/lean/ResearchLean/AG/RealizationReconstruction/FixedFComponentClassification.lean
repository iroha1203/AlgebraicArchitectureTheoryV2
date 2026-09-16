import ResearchLean.AG.RealizationReconstruction.FixedFSourceClassification
import Mathlib.Logic.Relation
import Formal.Util.AssertStandardAxioms

/-!
# Component classification for a fixed directed multigraph

The undirected components of a directed multigraph are constructed directly
as the equivalence closure of its directed endpoint relation.  Direction is
forgotten only by `Relation.EqvGen`; named and parallel edges remain part of
the original source graph.

An edge-constant hidden permutation family is constant along this generated
reachability relation and therefore descends uniquely to the component
quotient.  Conversely, every component-indexed permutation family pulls back
to an edge-constant vertex family.  Combining this equivalence with the
Cycle 111 source classification identifies operation-preserving following
changes with component-indexed permutations.

No component representatives, finiteness, decidable equality, connectedness
certificate, or semantic result is accepted as input.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

/-- One directed edge step between its source and target vertices. -/
def fixedFDirectedEdgeStep (F : FixedFDirectedMultigraph)
    (first second : F.Vertex) : Prop :=
  ∃ namedEdge : F.Edge,
    F.source namedEdge = first ∧ F.target namedEdge = second

/-- Undirected reachability is the equivalence closure of directed edge
steps.  Symmetry is generated rather than stored as extra graph data. -/
abbrev FixedFUndirectedReachable (F : FixedFDirectedMultigraph) :
    F.Vertex → F.Vertex → Prop :=
  Relation.EqvGen (fixedFDirectedEdgeStep F)

/-- The setoid generated solely by the fixed graph's endpoint relation. -/
def fixedFComponentSetoid (F : FixedFDirectedMultigraph) : Setoid F.Vertex :=
  Relation.EqvGen.setoid (fixedFDirectedEdgeStep F)

/-- Undirected connected components of the fixed directed multigraph. -/
abbrev FixedFComponent (F : FixedFDirectedMultigraph) :=
  Quotient (fixedFComponentSetoid F)

/-- Send a source vertex to its generated undirected component. -/
def fixedFComponentMk (F : FixedFDirectedMultigraph) (vertex : F.Vertex) :
    FixedFComponent F :=
  Quotient.mk (fixedFComponentSetoid F) vertex

/-- Equality of generated component classes is exactly undirected
reachability. -/
theorem fixedFComponentMk_eq_iff
    (F : FixedFDirectedMultigraph) (first second : F.Vertex) :
    fixedFComponentMk F first = fixedFComponentMk F second ↔
      FixedFUndirectedReachable F first second := by
  change
    Quotient.mk (fixedFComponentSetoid F) first =
        Quotient.mk (fixedFComponentSetoid F) second ↔
      FixedFUndirectedReachable F first second
  exact Quotient.eq_iff_equiv

/-- Every named edge has source and target in the same generated component. -/
theorem fixedFComponent_source_eq_target
    (F : FixedFDirectedMultigraph) (namedEdge : F.Edge) :
    fixedFComponentMk F (F.source namedEdge) =
      fixedFComponentMk F (F.target namedEdge) := by
  change
    Quotient.mk (fixedFComponentSetoid F) (F.source namedEdge) =
      Quotient.mk (fixedFComponentSetoid F) (F.target namedEdge)
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ ⟨namedEdge, rfl, rfl⟩

/-- Component-indexed hidden permutation families. -/
abbrev FixedFComponentPermutationFamily
    (F : FixedFDirectedMultigraph) (K : Type w) :=
  FixedFComponent F → Equiv.Perm K

namespace FixedFEdgeConstantPermutationFamily

variable {F : FixedFDirectedMultigraph} {K : Type w}

/-- Edge constancy extends along the entire generated undirected reachability
relation. -/
theorem perm_eq_of_reachable
    (family : FixedFEdgeConstantPermutationFamily F K)
    {first second : F.Vertex}
    (reachable : FixedFUndirectedReachable F first second) :
    family.perm first = family.perm second := by
  induction reachable with
  | rel first second step =>
      obtain ⟨namedEdge, sourceEquality, targetEquality⟩ := step
      subst first
      subst second
      exact family.edge_constant namedEdge
  | refl vertex =>
      rfl
  | symm first second relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans first second third firstRelation secondRelation
      firstInduction secondInduction =>
      exact firstInduction.trans secondInduction

/-- Descend an edge-constant vertex family to the component quotient. -/
def descendToComponents
    (family : FixedFEdgeConstantPermutationFamily F K) :
    FixedFComponentPermutationFamily F K :=
  Quotient.lift family.perm
    (fun _ _ reachable => family.perm_eq_of_reachable reachable)

/-- Edge-constant vertex families are exactly component-indexed permutation
families.  The inverse is pullback along the quotient map. -/
def equivComponentPermutationFamilies :
    FixedFEdgeConstantPermutationFamily F K ≃
      FixedFComponentPermutationFamily F K where
  toFun := descendToComponents
  invFun componentFamily :=
    { perm := fun vertex => componentFamily (fixedFComponentMk F vertex)
      edge_constant := fun namedEdge =>
        congrArg componentFamily
          (fixedFComponent_source_eq_target F namedEdge) }
  left_inv family := by
    apply FixedFEdgeConstantPermutationFamily.ext
    funext vertex
    change family.descendToComponents (fixedFComponentMk F vertex) =
      family.perm vertex
    rfl
  right_inv componentFamily := by
    funext component
    refine Quotient.inductionOn component ?_
    intro vertex
    rfl

end FixedFEdgeConstantPermutationFamily

namespace FixedFFollowingStateChange

variable {F : FixedFDirectedMultigraph} {K : Type w}
  {u : FixedFGraphAutomorphism F}

/-- Operation-preserving following changes are classified by one hidden
permutation for each generated undirected component. -/
def preservingEquivComponentPermutationFamilies :
    { change : FixedFFollowingStateChange F K u //
      change.PreservesNamedOperations } ≃
      FixedFComponentPermutationFamily F K :=
  preservingEquivEdgeConstantFamilies.trans
    FixedFEdgeConstantPermutationFamily.equivComponentPermutationFamilies

end FixedFFollowingStateChange

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
