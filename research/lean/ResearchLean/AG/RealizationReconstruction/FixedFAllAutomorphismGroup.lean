import ResearchLean.AG.RealizationReconstruction.FixedFComponentClassification
import Mathlib.GroupTheory.Perm.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Group classification over all fixed-graph automorphisms

Graph automorphisms of a fixed directed multigraph form a group by simultaneous
composition of their vertex and named-edge equivalences.  Operation-preserving
following changes over all graph automorphisms likewise form a group: the
state equivalences compose, and the visible graph automorphisms compose with
them.

The hidden fiber formula for a product contains the essential reindexing:
for a first change over `u` and second change over `v`, the product fiber at
`x` is `first.fiberPerm (v.vertex x) * second.fiberPerm x`.  It is not the
pointwise product at `x`.

Projection to the visible graph automorphism is a group homomorphism.  The
canonical visible-renaming change, with identity hidden action, gives a group
homomorphic section.  No exact-sequence, kernel-torsor, or subgroup
classification claim is made here.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

namespace FixedFGraphAutomorphism

variable {F : FixedFDirectedMultigraph}

@[ext] theorem ext
    {first second : FixedFGraphAutomorphism F}
    (vertexEquality : first.vertex = second.vertex)
    (edgeEquality : first.edge = second.edge) : first = second := by
  cases first
  cases second
  cases vertexEquality
  cases edgeEquality
  rfl

instance : One (FixedFGraphAutomorphism F) where
  one :=
    { vertex := 1
      edge := 1
      source_rename := fun _ => rfl
      target_rename := fun _ => rfl }

instance : Mul (FixedFGraphAutomorphism F) where
  mul first second :=
    { vertex := first.vertex * second.vertex
      edge := first.edge * second.edge
      source_rename := fun namedEdge => by
        calc
          F.source ((first.edge * second.edge) namedEdge) =
              F.source (first.edge (second.edge namedEdge)) := rfl
          _ = first.vertex (F.source (second.edge namedEdge)) :=
            first.source_rename (second.edge namedEdge)
          _ = first.vertex (second.vertex (F.source namedEdge)) :=
            congrArg first.vertex (second.source_rename namedEdge)
          _ = (first.vertex * second.vertex) (F.source namedEdge) := rfl
      target_rename := fun namedEdge => by
        calc
          F.target ((first.edge * second.edge) namedEdge) =
              F.target (first.edge (second.edge namedEdge)) := rfl
          _ = first.vertex (F.target (second.edge namedEdge)) :=
            first.target_rename (second.edge namedEdge)
          _ = first.vertex (second.vertex (F.target namedEdge)) :=
            congrArg first.vertex (second.target_rename namedEdge)
          _ = (first.vertex * second.vertex) (F.target namedEdge) := rfl }

instance : Inv (FixedFGraphAutomorphism F) where
  inv automorphism :=
    { vertex := automorphism.vertex⁻¹
      edge := automorphism.edge⁻¹
      source_rename := fun namedEdge => by
        apply automorphism.vertex.injective
        simpa using
          (automorphism.source_rename
            (automorphism.edge.symm namedEdge)).symm
      target_rename := fun namedEdge => by
        apply automorphism.vertex.injective
        simpa using
          (automorphism.target_rename
            (automorphism.edge.symm namedEdge)).symm }

@[simp] theorem one_vertex :
    (1 : FixedFGraphAutomorphism F).vertex = 1 := rfl

@[simp] theorem one_edge :
    (1 : FixedFGraphAutomorphism F).edge = 1 := rfl

@[simp] theorem mul_vertex
    (first second : FixedFGraphAutomorphism F) :
    (first * second).vertex = first.vertex * second.vertex := rfl

@[simp] theorem mul_edge
    (first second : FixedFGraphAutomorphism F) :
    (first * second).edge = first.edge * second.edge := rfl

@[simp] theorem inv_vertex (automorphism : FixedFGraphAutomorphism F) :
    (automorphism⁻¹).vertex = automorphism.vertex⁻¹ := rfl

@[simp] theorem inv_edge (automorphism : FixedFGraphAutomorphism F) :
    (automorphism⁻¹).edge = automorphism.edge⁻¹ := rfl

instance : Group (FixedFGraphAutomorphism F) where
  mul_assoc first second third := by
    apply ext <;> simp [mul_assoc]
  one_mul automorphism := by
    apply ext <;> simp
  mul_one automorphism := by
    apply ext <;> simp
  inv_mul_cancel automorphism := by
    apply ext <;> simp

/-- Source endpoint under an inverse graph automorphism. -/
theorem source_inv (automorphism : FixedFGraphAutomorphism F)
    (namedEdge : F.Edge) :
    F.source (automorphism.edge.symm namedEdge) =
      automorphism.vertex.symm (F.source namedEdge) := by
  exact (automorphism⁻¹).source_rename namedEdge

/-- Target endpoint under an inverse graph automorphism. -/
theorem target_inv (automorphism : FixedFGraphAutomorphism F)
    (namedEdge : F.Edge) :
    F.target (automorphism.edge.symm namedEdge) =
      automorphism.vertex.symm (F.target namedEdge) := by
  exact (automorphism⁻¹).target_rename namedEdge

end FixedFGraphAutomorphism

namespace FixedFFollowingStateChange

variable {F : FixedFDirectedMultigraph} {K : Type w}

/-- Composition of following changes over composable visible graph
automorphisms. -/
def comp {firstAutomorphism secondAutomorphism : FixedFGraphAutomorphism F}
    (first : FixedFFollowingStateChange F K firstAutomorphism)
    (second : FixedFFollowingStateChange F K secondAutomorphism) :
    FixedFFollowingStateChange F K
      (firstAutomorphism * secondAutomorphism) where
  h := first.h * second.h
  observation vertex hidden := by
    change (first.h (second.h (vertex, hidden))).1 =
      firstAutomorphism.vertex (secondAutomorphism.vertex vertex)
    calc
      (first.h (second.h (vertex, hidden))).1 =
          firstAutomorphism.vertex (second.h (vertex, hidden)).1 :=
        first.observation _ _
      _ = firstAutomorphism.vertex
          (secondAutomorphism.vertex vertex) :=
        congrArg firstAutomorphism.vertex (second.observation vertex hidden)

/-- Product fibers compose with reindexing by the second visible vertex
action. -/
theorem comp_fiberPerm
    {firstAutomorphism secondAutomorphism : FixedFGraphAutomorphism F}
    (first : FixedFFollowingStateChange F K firstAutomorphism)
    (second : FixedFFollowingStateChange F K secondAutomorphism)
    (vertex : F.Vertex) :
    (comp first second).fiberPerm vertex =
      first.fiberPerm (secondAutomorphism.vertex vertex) *
        second.fiberPerm vertex := by
  apply Equiv.ext
  intro hidden
  change (first.h (second.h (vertex, hidden))).2 =
    first.fiberPerm (secondAutomorphism.vertex vertex)
      (second.fiberPerm vertex hidden)
  rw [second.factorization, first.factorization]

/-- Inverse following change over the inverse visible automorphism. -/
def inverse {automorphism : FixedFGraphAutomorphism F}
    (change : FixedFFollowingStateChange F K automorphism) :
    FixedFFollowingStateChange F K automorphism⁻¹ where
  h := change.h⁻¹
  observation vertex hidden := by
    have recovered := change.symm_observation
      (automorphism.vertex.symm vertex) hidden
    simpa using recovered

/-- Fibers of the inverse change are inverse fibers reindexed along the
inverse visible vertex action. -/
theorem inverse_fiberPerm
    {automorphism : FixedFGraphAutomorphism F}
    (change : FixedFFollowingStateChange F K automorphism)
    (vertex : F.Vertex) :
    change.inverse.fiberPerm vertex =
      (change.fiberPerm (automorphism.vertex.symm vertex))⁻¹ := by
  apply Equiv.ext
  intro hidden
  change (change.h.symm (vertex, hidden)).2 =
    (change.h.symm
      (automorphism.vertex (automorphism.vertex.symm vertex), hidden)).2
  rw [automorphism.vertex.apply_symm_apply]

/-- Composition preserves named operations. -/
theorem comp_preservesNamedOperations
    {firstAutomorphism secondAutomorphism : FixedFGraphAutomorphism F}
    (first : FixedFFollowingStateChange F K firstAutomorphism)
    (second : FixedFFollowingStateChange F K secondAutomorphism)
    (firstPreserves : first.PreservesNamedOperations)
    (secondPreserves : second.PreservesNamedOperations) :
    (comp first second).PreservesNamedOperations := by
  rw [(comp first second).preservesNamedOperations_iff]
  intro namedEdge
  rw [comp_fiberPerm, comp_fiberPerm]
  have firstConstant :=
    (first.preservesNamedOperations_iff).1 firstPreserves
      (secondAutomorphism.edge namedEdge)
  have secondConstant :=
    (second.preservesNamedOperations_iff).1 secondPreserves namedEdge
  rw [secondAutomorphism.source_rename,
    secondAutomorphism.target_rename] at firstConstant
  rw [firstConstant, secondConstant]

/-- Inversion preserves named operations. -/
theorem inverse_preservesNamedOperations
    {automorphism : FixedFGraphAutomorphism F}
    (change : FixedFFollowingStateChange F K automorphism)
    (preserves : change.PreservesNamedOperations) :
    change.inverse.PreservesNamedOperations := by
  rw [change.inverse.preservesNamedOperations_iff]
  intro namedEdge
  rw [inverse_fiberPerm, inverse_fiberPerm,
    ← automorphism.source_inv, ← automorphism.target_inv]
  have constant :=
    (change.preservesNamedOperations_iff).1 preserves
      (automorphism.edge.symm namedEdge)
  exact congrArg Inv.inv constant

end FixedFFollowingStateChange

/-- An operation-preserving following change together with its visible graph
automorphism. -/
structure FixedFPreservingFollowingPair
    (F : FixedFDirectedMultigraph) (K : Type w) where
  automorphism : FixedFGraphAutomorphism F
  h : (F.Vertex × K) ≃ (F.Vertex × K)
  observation : ∀ vertex hidden,
    (h (vertex, hidden)).1 = automorphism.vertex vertex
  preserves : ∀ namedEdge hidden,
    h (fixedFNamedExecution F K namedEdge hidden) =
      fixedFNamedExecution F K (automorphism.edge namedEdge)
        (h (fixedFNamedSourceState F K namedEdge hidden)).2

namespace FixedFPreservingFollowingPair

variable {F : FixedFDirectedMultigraph} {K : Type w}

/-- Forget only the all-automorphism packaging. -/
def change (pair : FixedFPreservingFollowingPair F K) :
    FixedFFollowingStateChange F K pair.automorphism :=
  ⟨pair.h, pair.observation⟩

theorem change_preserves (pair : FixedFPreservingFollowingPair F K) :
    pair.change.PreservesNamedOperations :=
  pair.preserves

@[ext] theorem ext
    {first second : FixedFPreservingFollowingPair F K}
    (automorphismEquality : first.automorphism = second.automorphism)
    (stateEquality : first.h = second.h) : first = second := by
  cases first
  cases second
  cases automorphismEquality
  cases stateEquality
  rfl

instance : One (FixedFPreservingFollowingPair F K) where
  one :=
    { automorphism := 1
      h := 1
      observation := fun _ _ => rfl
      preserves := fun namedEdge hidden => by
        change fixedFNamedExecution F K namedEdge hidden =
          fixedFNamedExecution F K namedEdge hidden
        rfl }

instance : Mul (FixedFPreservingFollowingPair F K) where
  mul first second :=
    { automorphism := first.automorphism * second.automorphism
      h := first.h * second.h
      observation := (first.change.comp second.change).observation
      preserves := first.change.comp_preservesNamedOperations second.change
        first.change_preserves second.change_preserves }

instance : Inv (FixedFPreservingFollowingPair F K) where
  inv pair :=
    { automorphism := pair.automorphism⁻¹
      h := pair.h⁻¹
      observation := pair.change.inverse.observation
      preserves := pair.change.inverse_preservesNamedOperations
        pair.change_preserves }

@[simp] theorem one_automorphism :
    (1 : FixedFPreservingFollowingPair F K).automorphism = 1 := rfl

@[simp] theorem one_h :
    (1 : FixedFPreservingFollowingPair F K).h = 1 := rfl

@[simp] theorem mul_automorphism
    (first second : FixedFPreservingFollowingPair F K) :
    (first * second).automorphism =
      first.automorphism * second.automorphism := rfl

@[simp] theorem mul_h
    (first second : FixedFPreservingFollowingPair F K) :
    (first * second).h = first.h * second.h := rfl

@[simp] theorem inv_automorphism
    (pair : FixedFPreservingFollowingPair F K) :
    (pair⁻¹).automorphism = pair.automorphism⁻¹ := rfl

@[simp] theorem inv_h (pair : FixedFPreservingFollowingPair F K) :
    (pair⁻¹).h = pair.h⁻¹ := rfl

instance : Group (FixedFPreservingFollowingPair F K) where
  mul_assoc first second third := by
    apply ext <;> simp [mul_assoc]
  one_mul pair := by
    apply ext <;> simp
  mul_one pair := by
    apply ext <;> simp
  inv_mul_cancel pair := by
    apply ext <;> simp

/-- Fiber family of an all-automorphism preserving pair. -/
def fiberPerm (pair : FixedFPreservingFollowingPair F K) :=
  pair.change.fiberPerm

/-- Product fibers have the semidirect reindexing formula, not pointwise
multiplication at the original vertex. -/
theorem mul_fiberPerm
    (first second : FixedFPreservingFollowingPair F K)
    (vertex : F.Vertex) :
    (first * second).fiberPerm vertex =
      first.fiberPerm (second.automorphism.vertex vertex) *
        second.fiberPerm vertex :=
  first.change.comp_fiberPerm second.change vertex

/-- Projection to the visible graph automorphism. -/
def automorphismProjection :
    FixedFPreservingFollowingPair F K →*
      FixedFGraphAutomorphism F where
  toFun := automorphism
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Canonical following pair with visible renaming and identity hidden
action. -/
def visibleRename (automorphism : FixedFGraphAutomorphism F) :
    FixedFPreservingFollowingPair F K where
  automorphism := automorphism
  h :=
    { toFun := fun state => (automorphism.vertex state.1, state.2)
      invFun := fun state => (automorphism.vertex.symm state.1, state.2)
      left_inv := by rintro ⟨vertex, hidden⟩; simp
      right_inv := by rintro ⟨vertex, hidden⟩; simp }
  observation _ _ := rfl
  preserves namedEdge hidden := by
    apply Prod.ext
    · exact (automorphism.target_rename namedEdge).symm
    · rfl

/-- Visible renaming is a group-homomorphic canonical section. -/
def visibleRenameSection :
    FixedFGraphAutomorphism F →*
      FixedFPreservingFollowingPair F K where
  toFun := visibleRename
  map_one' := by
    apply ext <;> rfl
  map_mul' first second := by
    apply ext
    · rfl
    · apply Equiv.ext
      rintro ⟨vertex, hidden⟩
      rfl

/-- Projection of the canonical section is the identity. -/
theorem automorphismProjection_visibleRenameSection
    (automorphism : FixedFGraphAutomorphism F) :
    automorphismProjection (K := K)
        (visibleRenameSection (K := K) automorphism) =
      automorphism :=
  rfl

/-- The canonical section has identity hidden fiber at every vertex. -/
theorem visibleRename_fiberPerm
    (automorphism : FixedFGraphAutomorphism F) (vertex : F.Vertex) :
    (visibleRename (K := K) automorphism).fiberPerm vertex = 1 := by
  apply Equiv.ext
  intro hidden
  rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFPreservingFollowingPair

end AAT.AG.RealizationReconstruction
