import ResearchLean.AG.RealizationReconstruction.FixedFFiniteExamples
import ResearchLean.AG.RealizationReconstruction.ProtocolReconstruction
import Mathlib.Combinatorics.Quiver.Prefunctor
import Formal.Util.AssertStandardAxioms

/-!
# Fixed-graph changes in the independent protocol semantics

This file connects the fixed-`F` classification to the independently defined
protocol semantics of G-123(E).  A directed multigraph is converted to a
typed protocol schema without forgetting an operation name: an edge from
`v` to `w` is an original edge of `F` together with its endpoint equations.
The protocol realization has one copy of the hidden state at every control
point and executes a named edge by retaining that hidden state.

For a fixed graph automorphism `u`, a protocol change is defined directly by
state equivalences over all control points and the actual squares for all
typed operation names.  It is then identified in both directions with the
operation-preserving fixed-`F` changes.  The all-path theorem is derived from
the generator squares.  Finally, the ordinary protocol category is used to
state the adapter square for completely arbitrary, possibly noninvertible,
morphisms; no invertibility field is introduced there.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace FixedFProtocolConnection

/-! ## The typed protocol schema carried by a fixed graph -/

/-- An original fixed-graph edge with both endpoints retained in its type. -/
abbrev TypedEdge (F : FixedFDirectedMultigraph.{u, u})
    (source target : F.Vertex) :=
  { namedEdge : F.Edge //
    F.source namedEdge = source ∧ F.target namedEdge = target }

/-- The protocol schema carried by `F`.  There are no additional path
relations: every finite path remains an execution, and original edge names
remain distinguishable even if a realization assigns them equal functions. -/
abbrev schema (F : FixedFDirectedMultigraph.{u, u})
    [Finite F.Vertex] [Finite F.Edge] : ProtocolSchema.{u} where
  Vertex := F.Vertex
  vertex_finite := inferInstance
  Edge := TypedEdge F
  edge_finite := fun _ _ => inferInstance
  RelationIndex := ULift.{u} Empty
  relation_finite := inferInstance
  relationSource := fun r => Empty.elim r.down
  relationTarget := fun r => Empty.elim r.down
  relationLeft := fun r => Empty.elim r.down
  relationRight := fun r => Empty.elim r.down

/-- Every original edge occurs in the protocol schema at its original typed
endpoints. -/
def typedEdge (F : FixedFDirectedMultigraph.{u, u})
    [Finite F.Vertex] [Finite F.Edge]
    (namedEdge : F.Edge) :
    (schema F).Edge (F.source namedEdge) (F.target namedEdge) :=
  ⟨namedEdge, rfl, rfl⟩

/-- The fixed graph quiver is the endpoint-typed operation family of its
protocol schema. -/
local instance fixedFProtocolQuiver
    (F : FixedFDirectedMultigraph.{u, u}) : Quiver F.Vertex where
  Hom := TypedEdge F

/-- A graph automorphism renames a typed protocol operation while preserving
its actual source and target. -/
def renameTypedEdge {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (automorphism : FixedFGraphAutomorphism F)
    {source target : F.Vertex} (edge : (schema F).Edge source target) :
    (schema F).Edge (automorphism.vertex source)
      (automorphism.vertex target) :=
  ⟨automorphism.edge edge.1,
    by rw [automorphism.source_rename, edge.2.1],
    by rw [automorphism.target_rename, edge.2.2]⟩

/-- The quiver map induced by the actual vertex and operation-name rename. -/
def renamePrefunctor {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (automorphism : FixedFGraphAutomorphism F) :
    (schema F).Vertex ⥤q (schema F).Vertex where
  obj := automorphism.vertex
  map := renameTypedEdge automorphism

/-- Rename every operation name in a finite protocol execution. -/
def renamePath {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (automorphism : FixedFGraphAutomorphism F)
    {source target : F.Vertex} (path : Quiver.Path source target) :
    Quiver.Path (automorphism.vertex source) (automorphism.vertex target) :=
  (renamePrefunctor automorphism).mapPath path

@[simp]
theorem renamePath_nil {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (automorphism : FixedFGraphAutomorphism F) (vertex : F.Vertex) :
    renamePath automorphism (Quiver.Path.nil : Quiver.Path vertex vertex) =
      Quiver.Path.nil :=
  rfl

@[simp]
theorem renamePath_cons {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (automorphism : FixedFGraphAutomorphism F)
    {first second third : F.Vertex}
    (path : Quiver.Path first second) (edge : (schema F).Edge second third) :
    renamePath automorphism (path.cons edge) =
      (renamePath automorphism path).cons
      (renameTypedEdge automorphism edge) :=
  rfl

/-- Rename paths functorially before passing to the quotient execution
category. -/
def renamePathFunctor {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (automorphism : FixedFGraphAutomorphism F) :
    Paths (schema F).Vertex ⥤ Paths (schema F).Vertex where
  obj := automorphism.vertex
  map := renamePath automorphism
  map_id := fun _ => rfl
  map_comp := fun first second =>
    Prefunctor.mapPath_comp (renamePrefunctor automorphism) first second

/-- Operation-name renaming on every quotient execution.  Descent is
constructed from the authored relation family; for the fixed-F schema that
family is empty, rather than supplied as an execution-preservation
certificate. -/
def renameExecutionFunctor {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (automorphism : FixedFGraphAutomorphism F) :
    (schema F).ExecutionCategory ⥤ (schema F).ExecutionCategory :=
  CategoryTheory.Quotient.lift (schema F).pathRelation
    (renamePathFunctor automorphism ⋙
      CategoryTheory.Quotient.functor (schema F).pathRelation) (by
        intro source target left right relation
        obtain ⟨index, _⟩ := relation
        exact Empty.elim index.down)

/-- On a represented execution, quotient-level renaming is exactly the
pathwise renaming of every original operation name. -/
@[simp]
theorem renameExecutionFunctor_map_path
    {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (automorphism : FixedFGraphAutomorphism F)
    {source target : F.Vertex} (path : Quiver.Path source target) :
    (renameExecutionFunctor automorphism).map
        ((schema F).pathMorphism path) =
      (schema F).pathMorphism (renamePath automorphism path) :=
  rfl

/-! ## The independent protocol realization -/

/-- The fixed observation functor used by the graph protocol: observations
remember the control-point sort externally, while their value contains no
hidden-state information. -/
abbrev observationFunctor (F : FixedFDirectedMultigraph.{u, u})
    [Finite F.Vertex] [Finite F.Edge] :
    (schema F).ExecutionCategory ⥤ Type u where
  obj := fun _ => PUnit
  map := fun _ => id
  map_id := by intro; rfl
  map_comp := by intros; rfl

/-- The free-path semantics which retains the hidden state on every named
edge. -/
def hiddenPathFunctor (F : FixedFDirectedMultigraph.{u, u})
    [Finite F.Vertex] [Finite F.Edge] (K : Type u) :
    Paths (schema F).Vertex ⥤ Type u :=
  (schema F).pathFunctorOfEdgeAction (fun _ => K) (fun _ => id)

/-- Since the graph schema has no authored path equations, the hidden-state
path functor descends to the quotient execution category without adding an
equation certificate to the realization. -/
def hiddenExecutionFunctor (F : FixedFDirectedMultigraph.{u, u})
    [Finite F.Vertex] [Finite F.Edge] (K : Type u) :
    (schema F).ExecutionCategory ⥤ Type u :=
  CategoryTheory.Quotient.lift (schema F).pathRelation
    (hiddenPathFunctor F K) (by
      intro source target left right relation
      obtain ⟨index, _⟩ := relation
      exact Empty.elim index.down)

/-- The independent protocol realization associated with `(F,K)`.  Its
functor interprets every quotient execution, not only the generating edges. -/
def realization (F : FixedFDirectedMultigraph.{u, u})
    [Finite F.Vertex] [Finite F.Edge]
    (K : Type u) [Finite K] :
    ProtocolRealization (schema F) (observationFunctor F) where
  toFunctor := hiddenExecutionFunctor F K
  state_finite := fun _ => by
    change Finite K
    infer_instance
  observation :=
    { app := fun _ _ => PUnit.unit
      naturality := by intros; funext x; exact Subsingleton.elim _ _ }

/-- A named protocol operation executes by retaining the hidden state. -/
@[simp]
theorem realization_edgeAction {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    (K : Type u) [Finite K] {source target : F.Vertex}
    (edge : (schema F).Edge source target) :
    (realization F K).edgeAction edge = id := by
  rfl

/-! ## Independent fixed-automorphism protocol changes -/

/-- A protocol-side invertible change following one fixed graph
automorphism.  The state maps and the squares for the original typed operation
names are the independent CS-side conditions; no fixed-`F` change or hidden
permutation family is a field. -/
@[ext]
structure ProtocolInvertibleChange
    (F : FixedFDirectedMultigraph.{u, u})
    [Finite F.Vertex] [Finite F.Edge]
    (K : Type u) [Finite K]
    (automorphism : FixedFGraphAutomorphism F) where
  stateEquiv : ∀ vertex : F.Vertex,
    (realization F K).State vertex ≃
      (realization F K).State (automorphism.vertex vertex)
  edge_naturality : ∀ {source target : F.Vertex}
      (edge : (schema F).Edge source target) (state : (realization F K).State source),
    stateEquiv target ((realization F K).edgeAction edge state) =
      (realization F K).edgeAction (renameTypedEdge automorphism edge)
        (stateEquiv source state)
  observation_naturality : ∀ vertex state,
    (realization F K).observe (automorphism.vertex vertex)
        (stateEquiv vertex state) =
      (realization F K).observe vertex state

namespace ProtocolInvertibleChange

variable {F : FixedFDirectedMultigraph.{u, u}}
  [Finite F.Vertex] [Finite F.Edge]
  {K : Type u} [Finite K]
  {automorphism : FixedFGraphAutomorphism F}

/-- The state type at each vertex is definitionally the authored hidden type,
so a protocol change yields a source-owned hidden permutation. -/
def hiddenPermutation
    (change : ProtocolInvertibleChange F K automorphism)
    (vertex : F.Vertex) : Equiv.Perm K :=
  change.stateEquiv vertex

/-- Forget protocol vocabulary by assembling the vertex-indexed state maps
into one complete fixed-`F` state equivalence. -/
def toFollowingStateChange
    (change : ProtocolInvertibleChange F K automorphism) :
    FixedFFollowingStateChange F K automorphism :=
  FixedFFollowingStateChange.ofFamily change.hiddenPermutation

/-- The protocol squares for every original typed edge prove the actual
fixed-`F` named-execution squares. -/
theorem toFollowingStateChange_preserves
    (change : ProtocolInvertibleChange F K automorphism) :
    change.toFollowingStateChange.PreservesNamedOperations := by
  rw [FixedFFollowingStateChange.preservesNamedOperations_iff]
  intro namedEdge
  apply Equiv.ext
  intro hidden
  exact (change.edge_naturality (typedEdge F namedEdge) hidden).symm

/-- Construct the independent protocol change from an actual preserving
fixed-`F` change.  The state equivalences are the fiber permutations
constructed from its complete state equivalence, not additional inputs. -/
def ofFollowingStateChange
    (change : { actual : FixedFFollowingStateChange F K automorphism //
      actual.PreservesNamedOperations }) :
    ProtocolInvertibleChange F K automorphism where
  stateEquiv := change.1.fiberPerm
  edge_naturality := by
    intro source target edge hidden
    change change.1.fiberPerm target hidden =
      change.1.fiberPerm source hidden
    have edgeConstancy :=
      (change.1.preservesNamedOperations_iff).1 change.2 edge.1
    rw [edge.2.1, edge.2.2] at edgeConstancy
    exact congrArg (fun permutation : Equiv.Perm K => permutation hidden)
      edgeConstancy.symm
  observation_naturality := by
    intro vertex state
    exact Subsingleton.elim _ _

/-- Independent fixed-automorphism protocol changes are exactly the actual
operation-preserving fixed-`F` changes. -/
def equivPreservingFollowingChanges :
    ProtocolInvertibleChange F K automorphism ≃
      { actual : FixedFFollowingStateChange F K automorphism //
        actual.PreservesNamedOperations } where
  toFun change := ⟨change.toFollowingStateChange,
    change.toFollowingStateChange_preserves⟩
  invFun := ofFollowingStateChange
  left_inv change := by
    apply ProtocolInvertibleChange.ext
    funext vertex
    change change.toFollowingStateChange.fiberPerm vertex =
      change.stateEquiv vertex
    exact congrFun
      (FixedFFollowingStateChange.fiberPerm_ofFamily
        change.hiddenPermutation) vertex
  right_inv change := by
    apply Subtype.ext
    apply FixedFFollowingStateChange.ext
    apply Equiv.ext
    rintro ⟨vertex, hidden⟩
    exact (change.1.factorization vertex hidden).symm

/-- The protocol state map is exactly the hidden component of the complete
fixed-`F` state map. -/
theorem stateEquiv_eq_following_hidden
    (change : ProtocolInvertibleChange F K automorphism)
    (vertex : F.Vertex) (hidden : K) :
    change.stateEquiv vertex hidden =
      (change.toFollowingStateChange.h (vertex, hidden)).2 := by
  rfl

/-- Protocol operation-name adaptation agrees literally with the first
component of the fixed-`F` operation map. -/
theorem operationName_compatibility
    (change : ProtocolInvertibleChange F K automorphism)
    {source target : F.Vertex} (edge : (schema F).Edge source target)
    (hidden : K) :
    (renameTypedEdge automorphism edge).1 =
      (change.toFollowingStateChange.operationMap (edge.1, hidden)).1 := by
  rfl

/-- The state supplied to the renamed protocol operation agrees with the
hidden component of the fixed-`F` operation adapter. -/
theorem operationState_compatibility
    (change : ProtocolInvertibleChange F K automorphism)
    {source target : F.Vertex} (edge : (schema F).Edge source target)
    (hidden : K) :
    change.stateEquiv source hidden =
      (change.toFollowingStateChange.operationMap (edge.1, hidden)).2 := by
  rw [FixedFFollowingStateChange.operationMap]
  change change.stateEquiv source hidden =
    change.toFollowingStateChange.fiberPerm (F.source edge.1) hidden
  rw [edge.2.1]
  rfl

/-- Generator naturality extends to every finite execution path.  Both the
original path and the path with every operation name renamed are retained. -/
theorem path_naturality
    (change : ProtocolInvertibleChange F K automorphism)
    {source target : F.Vertex} (path : Quiver.Path source target)
    (state : (realization F K).State source) :
    change.stateEquiv target ((realization F K).pathAction path state) =
      (realization F K).pathAction (renamePath automorphism path)
        (change.stateEquiv source state) := by
  induction path with
  | nil => rfl
  | cons path edge inductionHypothesis =>
      change
        change.stateEquiv _
            ((realization F K).edgeAction edge
              ((realization F K).pathAction path state)) =
          (realization F K).edgeAction (renameTypedEdge automorphism edge)
            ((realization F K).pathAction (renamePath automorphism path)
              (change.stateEquiv source state))
      rw [change.edge_naturality edge]
      exact congrArg
        ((realization F K).edgeAction (renameTypedEdge automorphism edge))
        inductionHypothesis

/-- The generator proof extends to every morphism of the quotient execution
category, not only to named edges or a chosen path representative. -/
theorem execution_naturality
    (change : ProtocolInvertibleChange F K automorphism)
    {source target : (schema F).ExecutionCategory}
    (execution : source ⟶ target)
    (state : (realization F K).toFunctor.obj source) :
    change.stateEquiv target.as
        ((realization F K).toFunctor.map execution state) =
      (realization F K).toFunctor.map
          ((renameExecutionFunctor automorphism).map execution)
        (change.stateEquiv source.as state) := by
  revert state
  apply CategoryTheory.Quotient.induction (r := (schema F).pathRelation)
    (P := fun {first second} execution =>
      ∀ state : (realization F K).toFunctor.obj first,
        change.stateEquiv second.as
            ((realization F K).toFunctor.map execution state) =
          (realization F K).toFunctor.map
              ((renameExecutionFunctor automorphism).map execution)
            (change.stateEquiv first.as state))
  intro pathSource pathTarget path state
  exact change.path_naturality path state

/-- Forget the visible operation-name rename while retaining its induced
state adapter as a complete morphism of the independent protocol semantic
category.  Naturality on all quotient executions is constructed by the
existing `ext` theorem from the named-edge squares. -/
def asHom (change : ProtocolInvertibleChange F K automorphism) :
    realization F K ⟶ realization F K :=
  ProtocolRealization.ext
    { component := fun vertex state => change.stateEquiv vertex state
      edge_naturality := fun edge => by
        funext state
        exact change.edge_naturality edge state
      observation_naturality := fun vertex => by
        funext state
        exact change.observation_naturality vertex state }

end ProtocolInvertibleChange

/-! ## Arbitrary, possibly noninvertible protocol adapters -/

/-- The literal P1 adapter square `b q = q' a` in the independent protocol
category.  All four sides are ordinary `ProtocolRealization.Hom`s; in
particular neither adapter is assumed invertible. -/
def AdapterSquare {S : ProtocolSchema.{u}}
    {O : S.ExecutionCategory ⥤ Type u}
    {X Y X' Y' : ProtocolRealization S O}
    (q : X ⟶ Y) (q' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') : Prop :=
  q ≫ b = a ≫ q'

/-- The categorical adapter square is equivalent to equality of its total
maps at every execution-category object and every state.  This includes all
noninvertible `q,q',a,b`. -/
theorem adapterSquare_iff_totalMaps {S : ProtocolSchema.{u}}
    {O : S.ExecutionCategory ⥤ Type u}
    {X Y X' Y' : ProtocolRealization S O}
    (q : X ⟶ Y) (q' : X' ⟶ Y')
    (a : X ⟶ X') (b : Y ⟶ Y') :
    AdapterSquare q q' a b ↔
      ∀ object state,
        b.toNatTrans.app object (q.toNatTrans.app object state) =
          q'.toNatTrans.app object (a.toNatTrans.app object state) := by
  constructor
  · intro square object state
    have component := congrArg
      (fun morphism : X ⟶ Y' => morphism.toNatTrans.app object state) square
    change
      b.toNatTrans.app object (q.toNatTrans.app object state) =
        q'.toNatTrans.app object (a.toNatTrans.app object state)
      at component
    exact component
  · intro component
    apply ProtocolRealization.Hom.ext
    ext object state
    exact component object state

/-- The exact n1015 P1 scope: `q,q'` are arbitrary (possibly
noninvertible) protocol morphisms, while the endpoint changes `a,b` are
actual isomorphisms in the independently defined semantic category. -/
def InvertibleAdapterSquare {S : ProtocolSchema.{u}}
    {O : S.ExecutionCategory ⥤ Type u}
    {X Y X' Y' : ProtocolRealization S O}
    (q : X ⟶ Y) (q' : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') : Prop :=
  AdapterSquare q q' a.hom b.hom

/-- The n1015 statewise equation is equivalent to the categorical P1 square
for every quotient execution object, without imposing invertibility on either
pre-existing adapter. -/
theorem invertibleAdapterSquare_iff_totalMaps
    {S : ProtocolSchema.{u}}
    {O : S.ExecutionCategory ⥤ Type u}
    {X Y X' Y' : ProtocolRealization S O}
    (q : X ⟶ Y) (q' : X' ⟶ Y')
    (a : X ≅ X') (b : Y ≅ Y') :
    InvertibleAdapterSquare q q' a b ↔
      ∀ object state,
        b.hom.toNatTrans.app object (q.toNatTrans.app object state) =
          q'.toNatTrans.app object
            (a.hom.toNatTrans.app object state) :=
  adapterSquare_iff_totalMaps q q' a.hom b.hom

/-- P1 for the fixed-graph protocol: the pre-existing adapters `q,q'` remain
arbitrary semantic morphisms (and may be noninvertible), while `a,b` are the
independently constructed invertible endpoint changes following the same
visible operation-name rename. -/
def ProtocolChangeAdapterSquare
    {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    {KX KY : Type u} [Finite KX] [Finite KY]
    {automorphism : FixedFGraphAutomorphism F}
    (q q' : realization F KX ⟶ realization F KY)
    (a : ProtocolInvertibleChange F KX automorphism)
    (b : ProtocolInvertibleChange F KY automorphism) : Prop :=
  AdapterSquare q q' a.asHom b.asHom

/-- The fixed-graph P1 square is exactly the statewise adapter equation at
every quotient execution object.  No inverse for `q` or `q'` is assumed. -/
theorem protocolChangeAdapterSquare_iff_allExecutions
    {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    {KX KY : Type u} [Finite KX] [Finite KY]
    {automorphism : FixedFGraphAutomorphism F}
    (q q' : realization F KX ⟶ realization F KY)
    (a : ProtocolInvertibleChange F KX automorphism)
    (b : ProtocolInvertibleChange F KY automorphism) :
    ProtocolChangeAdapterSquare q q' a b ↔
      ∀ object state,
        b.asHom.toNatTrans.app object
            (q.toNatTrans.app object state) =
          q'.toNatTrans.app object
            (a.asHom.toNatTrans.app object state) :=
  adapterSquare_iff_totalMaps q q' a.asHom b.asHom

/-- Equivalently, P1 can be checked state-by-state at every named control
point; the completed equality then holds on all quotient executions because
all four sides are actual `ProtocolRealization.Hom`s. -/
theorem protocolChangeAdapterSquare_iff_vertices
    {F : FixedFDirectedMultigraph.{u, u}}
    [Finite F.Vertex] [Finite F.Edge]
    {KX KY : Type u} [Finite KX] [Finite KY]
    {automorphism : FixedFGraphAutomorphism F}
    (q q' : realization F KX ⟶ realization F KY)
    (a : ProtocolInvertibleChange F KX automorphism)
    (b : ProtocolInvertibleChange F KY automorphism) :
    ProtocolChangeAdapterSquare q q' a b ↔
      ∀ vertex state,
        b.stateEquiv vertex
            (ProtocolRealization.app q ((schema F).vertexObject vertex) state) =
          ProtocolRealization.app q' ((schema F).vertexObject vertex)
            (a.stateEquiv vertex state) := by
  constructor
  · intro square vertex state
    simpa [ProtocolRealization.app, ProtocolInvertibleChange.asHom] using
      (protocolChangeAdapterSquare_iff_allExecutions q q' a b).1 square
        ((schema F).vertexObject vertex) state
  · intro component
    apply (protocolChangeAdapterSquare_iff_allExecutions q q' a b).2
    intro object state
    simpa [ProtocolRealization.app, ProtocolInvertibleChange.asHom] using
      component object.as state

/-! ## The fixed two-session `Fin 4` protocol -/

open FixedFFiniteExamples

local instance : Finite protocolGraph.Edge := by
  change Finite Bool
  infer_instance

/-- The independent protocol-side representative of the exact visible
session exchange used in the fixed `Fin 4` example. -/
def protocolSessionSwapChange :
    ProtocolInvertibleChange protocolGraph Bool
      protocolSessionSwapAutomorphism :=
  ProtocolInvertibleChange.ofFollowingStateChange
    ⟨protocolSessionSwapLift.1.change,
      protocolSessionSwapLift.1.preserves⟩

/-- On every control point the session-swap protocol change keeps the hidden
state, while the visible control point and operation name are exchanged. -/
theorem protocolSessionSwapChange_state
    (vertex : Fin 4) (hidden : Bool) :
    protocolSessionSwapChange.stateEquiv vertex hidden = hidden := by
  change protocolSessionSwapLift.1.fiberPerm vertex hidden = hidden
  rw [protocolSessionSwapLift_fiberPerm]
  rfl

/-- The original `false` operation name is adapted to the original `true`
name, with the exact hidden execution value retained. -/
theorem protocolSessionSwapChange_false (hidden : Bool) :
    (renameTypedEdge protocolSessionSwapAutomorphism
        (typedEdge protocolGraph false)).1 = true ∧
      protocolSessionSwapChange.stateEquiv
        (protocolGraph.source false) hidden = hidden := by
  constructor
  · change protocolEdgeSwap false = true
    decide
  · exact protocolSessionSwapChange_state _ hidden

/-- The original `true` operation name is adapted to the original `false`
name, with the exact hidden execution value retained. -/
theorem protocolSessionSwapChange_true (hidden : Bool) :
    (renameTypedEdge protocolSessionSwapAutomorphism
        (typedEdge protocolGraph true)).1 = false ∧
      protocolSessionSwapChange.stateEquiv
        (protocolGraph.source true) hidden = hidden := by
  constructor
  · change protocolEdgeSwap true = false
    decide
  · exact protocolSessionSwapChange_state _ hidden

/-- The protocol-side operation adapter is the same concrete map as the
fixed-`F` session-swap adapter. -/
theorem protocolSessionSwap_operationMap_connection
    (namedEdge : Bool) (hidden : Bool) :
    ((renameTypedEdge protocolSessionSwapAutomorphism
        (typedEdge protocolGraph namedEdge)).1,
      protocolSessionSwapChange.stateEquiv
        (protocolGraph.source namedEdge) hidden) =
      protocolSessionSwapLift.1.change.operationMap (namedEdge, hidden) := by
  apply Prod.ext
  · rfl
  · change protocolSessionSwapLift.1.change.fiberPerm
        (protocolGraph.source namedEdge) hidden =
      (protocolSessionSwapLift.1.change.operationMap
        (namedEdge, hidden)).2
    rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFProtocolConnection

end AAT.AG.RealizationReconstruction
