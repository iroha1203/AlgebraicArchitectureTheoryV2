import Mathlib.Logic.Equiv.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Source classification for a fixed directed multigraph

This module gives an independent source-side model for a fixed directed
multigraph `F`.  A graph automorphism renames vertices and named edges while
preserving their endpoints.  A following state change stores only an
equivalence of states `Vertex × K` and the observation law saying that its
visible vertex is the renamed source vertex.

The hidden fiber permutation at each vertex is constructed from the state
equivalence and its inverse; it is not accepted as a certificate field.
Preservation of named operations is an actual execution equation after edge
renaming.  It is proved equivalent to constancy of the constructed fiber
permutations along every directed edge.  Consequently preserving changes are
equivalent to source-owned edge-constant permutation families.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

/-- An explicit directed multigraph with named edges. -/
structure FixedFDirectedMultigraph where
  Vertex : Type u
  Edge : Type v
  source : Edge → Vertex
  target : Edge → Vertex

/-- An automorphism renames both vertices and named edges and preserves the
two endpoint maps. -/
structure FixedFGraphAutomorphism (F : FixedFDirectedMultigraph) where
  vertex : F.Vertex ≃ F.Vertex
  edge : F.Edge ≃ F.Edge
  source_rename : ∀ namedEdge,
    F.source (edge namedEdge) = vertex (F.source namedEdge)
  target_rename : ∀ namedEdge,
    F.target (edge namedEdge) = vertex (F.target namedEdge)

/-- State immediately before execution of a named edge. -/
def fixedFNamedSourceState (F : FixedFDirectedMultigraph)
    (K : Type w) (namedEdge : F.Edge) (hidden : K) : F.Vertex × K :=
  (F.source namedEdge, hidden)

/-- State immediately after execution of a named edge.  The named operation
changes the visible endpoint and retains the hidden state. -/
def fixedFNamedExecution (F : FixedFDirectedMultigraph)
    (K : Type w) (namedEdge : F.Edge) (hidden : K) : F.Vertex × K :=
  (F.target namedEdge, hidden)

/-- A named operation together with the hidden input on which it executes. -/
abbrev FixedFOperationPoint (F : FixedFDirectedMultigraph) (K : Type w) :=
  F.Edge × K

/-- A state change following the fixed graph automorphism.  Only the complete
state equivalence and its observation law are stored. -/
structure FixedFFollowingStateChange
    (F : FixedFDirectedMultigraph) (K : Type w)
    (u : FixedFGraphAutomorphism F) where
  h : (F.Vertex × K) ≃ (F.Vertex × K)
  observation : ∀ vertex hidden,
    (h (vertex, hidden)).1 = u.vertex vertex

namespace FixedFFollowingStateChange

variable {F : FixedFDirectedMultigraph} {K : Type w}
  {u : FixedFGraphAutomorphism F}

@[ext] theorem ext
    {first second : FixedFFollowingStateChange F K u}
    (equality : first.h = second.h) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- The inverse state equivalence over a renamed vertex returns to the
original visible vertex. -/
theorem symm_observation
    (change : FixedFFollowingStateChange F K u)
    (vertex : F.Vertex) (hidden : K) :
    (change.h.symm (u.vertex vertex, hidden)).1 = vertex := by
  apply u.vertex.injective
  calc
    u.vertex (change.h.symm (u.vertex vertex, hidden)).1 =
        (change.h
          (change.h.symm (u.vertex vertex, hidden))).1 :=
      (change.observation
        (change.h.symm (u.vertex vertex, hidden)).1
        (change.h.symm (u.vertex vertex, hidden)).2).symm
    _ = u.vertex vertex := by
      rw [change.h.apply_symm_apply]

/-- The hidden permutation at one source vertex, constructed from `h` and
`h.symm`. -/
def fiberPerm (change : FixedFFollowingStateChange F K u)
    (vertex : F.Vertex) : Equiv.Perm K where
  toFun hidden := (change.h (vertex, hidden)).2
  invFun hidden := (change.h.symm (u.vertex vertex, hidden)).2
  left_inv hidden := by
    have imageEquality :
        (u.vertex vertex, (change.h (vertex, hidden)).2) =
          change.h (vertex, hidden) := by
      apply Prod.ext
      · exact (change.observation vertex hidden).symm
      · rfl
    change
      (change.h.symm
        (u.vertex vertex, (change.h (vertex, hidden)).2)).2 = hidden
    rw [imageEquality, change.h.symm_apply_apply]
  right_inv hidden := by
    have preimageEquality :
        (vertex, (change.h.symm (u.vertex vertex, hidden)).2) =
          change.h.symm (u.vertex vertex, hidden) := by
      apply Prod.ext
      · exact (change.symm_observation vertex hidden).symm
      · rfl
    change
      (change.h
        (vertex, (change.h.symm (u.vertex vertex, hidden)).2)).2 = hidden
    rw [preimageEquality, change.h.apply_symm_apply]

/-- Every following state change factors into the visible graph renaming and
its constructed hidden fiber permutation. -/
theorem factorization
    (change : FixedFFollowingStateChange F K u)
    (vertex : F.Vertex) (hidden : K) :
    change.h (vertex, hidden) =
      (u.vertex vertex, change.fiberPerm vertex hidden) := by
  apply Prod.ext
  · exact change.observation vertex hidden
  · rfl

/-- The constructed fiber family is the unique family giving the state
factorization. -/
theorem fiberPerm_unique
    (change : FixedFFollowingStateChange F K u)
    (family : F.Vertex → Equiv.Perm K)
    (factor : ∀ vertex hidden,
      change.h (vertex, hidden) = (u.vertex vertex, family vertex hidden)) :
    family = change.fiberPerm := by
  funext vertex
  apply Equiv.ext
  intro hidden
  exact (congrArg Prod.snd (factor vertex hidden)).symm

/-- Preservation of named operations is the actual execution square after
renaming the edge.  It is not defined as equality of fiber families. -/
def PreservesNamedOperations
    (change : FixedFFollowingStateChange F K u) : Prop :=
  ∀ namedEdge hidden,
    change.h (fixedFNamedExecution F K namedEdge hidden) =
      fixedFNamedExecution F K (u.edge namedEdge)
        (change.h (fixedFNamedSourceState F K namedEdge hidden)).2

/-- The operation adapter induced by the graph renaming and the constructed
source-fiber permutation.  In particular the adapter is not stored as an
additional input. -/
def operationMap (change : FixedFFollowingStateChange F K u) :
    FixedFOperationPoint F K → FixedFOperationPoint F K :=
  fun operation =>
    (u.edge operation.1,
      change.fiberPerm (F.source operation.1) operation.2)

/-- The operation adapter always commutes with the source-state map. -/
theorem sourceState_operationMap
    (change : FixedFFollowingStateChange F K u)
    (operation : FixedFOperationPoint F K) :
    fixedFNamedSourceState F K (change.operationMap operation).1
        (change.operationMap operation).2 =
      change.h
        (fixedFNamedSourceState F K operation.1 operation.2) := by
  rcases operation with ⟨namedEdge, hidden⟩
  apply Prod.ext
  · change F.source (u.edge namedEdge) =
      (change.h (F.source namedEdge, hidden)).1
    rw [u.source_rename, change.observation]
  · rfl

/-- The operation map is explicitly the renamed named edge with the source
fiber permutation acting on hidden state. -/
theorem operationMap_formula
    (change : FixedFFollowingStateChange F K u)
    (preserves : change.PreservesNamedOperations)
    (namedEdge : F.Edge) (hidden : K) :
    change.h (fixedFNamedExecution F K namedEdge hidden) =
      fixedFNamedExecution F K
        (change.operationMap (namedEdge, hidden)).1
        (change.operationMap (namedEdge, hidden)).2 := by
  exact preserves namedEdge hidden

/-- The semantic execution square is equivalent to constancy of the
constructed fiber permutations along every named edge. -/
theorem preservesNamedOperations_iff
    (change : FixedFFollowingStateChange F K u) :
    change.PreservesNamedOperations ↔
      ∀ namedEdge,
        change.fiberPerm (F.source namedEdge) =
          change.fiberPerm (F.target namedEdge) := by
  constructor
  · intro preserves namedEdge
    apply Equiv.ext
    intro hidden
    have executionEquality := congrArg Prod.snd
      (preserves namedEdge hidden)
    exact executionEquality.symm
  · intro edgeConstant namedEdge hidden
    apply Prod.ext
    · change (change.h (F.target namedEdge, hidden)).1 =
        F.target (u.edge namedEdge)
      rw [change.observation]
      exact (u.target_rename namedEdge).symm
    · change change.fiberPerm (F.target namedEdge) hidden =
        change.fiberPerm (F.source namedEdge) hidden
      exact congrArg (fun permutation : Equiv.Perm K => permutation hidden)
        (edgeConstant namedEdge).symm

end FixedFFollowingStateChange

/-- Source-owned hidden permutation families constant along every directed
edge. -/
structure FixedFEdgeConstantPermutationFamily
    (F : FixedFDirectedMultigraph) (K : Type w) where
  perm : F.Vertex → Equiv.Perm K
  edge_constant : ∀ namedEdge,
    perm (F.source namedEdge) = perm (F.target namedEdge)

namespace FixedFEdgeConstantPermutationFamily

variable {F : FixedFDirectedMultigraph} {K : Type w}

@[ext] theorem ext
    {first second : FixedFEdgeConstantPermutationFamily F K}
    (equality : first.perm = second.perm) : first = second := by
  cases first
  cases second
  cases equality
  rfl

end FixedFEdgeConstantPermutationFamily

namespace FixedFFollowingStateChange

variable {F : FixedFDirectedMultigraph} {K : Type w}
  {u : FixedFGraphAutomorphism F}

/-- Construct a following state change from a source-owned fiber family. -/
def ofFamily (family : F.Vertex → Equiv.Perm K) :
    FixedFFollowingStateChange F K u where
  h :=
    { toFun := fun state =>
        (u.vertex state.1, family state.1 state.2)
      invFun := fun state =>
        (u.vertex.symm state.1,
          (family (u.vertex.symm state.1)).symm state.2)
      left_inv := by
        rintro ⟨vertex, hidden⟩
        simp
      right_inv := by
        rintro ⟨vertex, hidden⟩
        simp }
  observation vertex hidden := rfl

/-- Fiber extraction from a constructed change recovers the authored family. -/
theorem fiberPerm_ofFamily (family : F.Vertex → Equiv.Perm K) :
    (ofFamily (u := u) family).fiberPerm = family := by
  funext vertex
  apply Equiv.ext
  intro hidden
  rfl

/-- Central classification: operation-preserving following state changes are
exactly edge-constant source-owned permutation families. -/
def preservingEquivEdgeConstantFamilies :
    { change : FixedFFollowingStateChange F K u //
      change.PreservesNamedOperations } ≃
      FixedFEdgeConstantPermutationFamily F K where
  toFun change :=
    { perm := change.1.fiberPerm
      edge_constant :=
        (change.1.preservesNamedOperations_iff).1 change.2 }
  invFun family :=
    ⟨ofFamily (u := u) family.perm,
      (preservesNamedOperations_iff
        (ofFamily (u := u) family.perm)).2 (by
          intro namedEdge
          rw [fiberPerm_ofFamily]
          exact family.edge_constant namedEdge)⟩
  left_inv change := by
    apply Subtype.ext
    apply FixedFFollowingStateChange.ext
    apply Equiv.ext
    rintro ⟨vertex, hidden⟩
    exact (change.1.factorization vertex hidden).symm
  right_inv family := by
    apply FixedFEdgeConstantPermutationFamily.ext
    exact fiberPerm_ofFamily family.perm

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFFollowingStateChange

end AAT.AG.RealizationReconstruction
