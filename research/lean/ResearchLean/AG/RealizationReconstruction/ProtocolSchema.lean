import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Finite.Defs
import Formal.Util.AssertStandardAxioms

/-!
# Finite protocol schemas and their quotient path categories

This module fixes the independent protocol input of G-123(E), n1015 §3: a
finite typed directed multigraph together with a finite family of parallel path
equations.  The execution category is Mathlib's free path category quotiented
by the generated relation.  Operation names remain the original edge terms;
they are not identified merely because a later realization gives them equal
functions.

## Implementation notes

The relation family is finite through `RelationIndex`.  Its contextual,
equivalence, and compositional closure is supplied by Mathlib's category
quotient, rather than by an AAT-specific replacement.  No realization or
decoder data occurs in `ProtocolSchema`.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u v

/-- The fixed finite schema `Q,L` of G-123(E), n1015 §3.1.

This is an independent input structure: vertices, named typed edges, and a
finite family of parallel path equations.  It contains no state carrier,
transition table, observation, or reconstruction certificate. -/
structure ProtocolSchema where
  /-- The finite family of protocol control points from n1015 §3.1. -/
  Vertex : Type u
  /-- Finiteness of the fixed control-point family. -/
  vertex_finite : Finite Vertex
  /-- The finite family of named operations at each typed pair of endpoints. -/
  Edge : Vertex → Vertex → Type u
  /-- Finiteness of each fixed typed operation family. -/
  edge_finite : ∀ v w, Finite (Edge v w)
  /-- Indices for the fixed finite family `L` of parallel path equations. -/
  RelationIndex : Type u
  /-- Finiteness of the equation family, not of all derived executions. -/
  relation_finite : Finite RelationIndex
  /-- Source control point of a generating path equation. -/
  relationSource : RelationIndex → Vertex
  /-- Target control point of a generating path equation. -/
  relationTarget : RelationIndex → Vertex
  /-- Left execution path of a generating equation in `L`. -/
  relationLeft : (r : RelationIndex) →
    @Quiver.Path Vertex ⟨Edge⟩ (relationSource r) (relationTarget r)
  /-- Right execution path of the same generating equation in `L`. -/
  relationRight : (r : RelationIndex) →
    @Quiver.Path Vertex ⟨Edge⟩ (relationSource r) (relationTarget r)

namespace ProtocolSchema

/-- The Mathlib quiver carried by the named operations of a protocol schema.

This API instance connects the G-123(E) input directly to `Quiver.Path`. -/
instance (S : ProtocolSchema.{u}) : Quiver S.Vertex where
  Hom := S.Edge

/-- Transport a typed path along equalities of its endpoints.

This API helper keeps endpoint transport explicit when the finite equation
family is viewed as a hom relation on the path category. -/
def castPath (S : ProtocolSchema.{u}) {v w v' w' : S.Vertex}
    (p : Quiver.Path v w) (hv : v = v') (hw : w = w') : Quiver.Path v' w' :=
  @Quiver.homOfEq (Paths S.Vertex) _ v w v' w' p hv hw

/-- The generating hom relation induced by the finite equation family `L`.

This is an API definition for n1015 §3.1.  Contextual and equivalence closure
are deliberately left to Mathlib's `CategoryTheory.Quotient`. -/
def pathRelation (S : ProtocolSchema.{u}) : HomRel (Paths S.Vertex) :=
  fun v w p q => ∃ r : S.RelationIndex,
    ∃ hs : S.relationSource r = v, ∃ ht : S.relationTarget r = w,
      p = S.castPath (S.relationLeft r) hs ht ∧
        q = S.castPath (S.relationRight r) hs ht

/-- The quotient path category `C_Q` from n1015 §3.1.

It is Mathlib's category quotient of the free path category by the fixed finite
equations, so operation names and arbitrary finite executions remain explicit. -/
abbrev ExecutionCategory (S : ProtocolSchema.{u}) :=
  CategoryTheory.Quotient (S.pathRelation)

/-- Embed a control point into the quotient execution category.

This is object-level API for the n1015 §3.1 category `C_Q`. -/
def vertexObject (S : ProtocolSchema.{u}) (v : S.Vertex) : S.ExecutionCategory :=
  (CategoryTheory.Quotient.functor S.pathRelation).obj v

/-- Embed a named schema edge as a one-step execution in `C_Q`.

This is the operation-name API used by protocol tables and their naturality
conditions; no realized transition function is used to identify an edge. -/
def edgeMorphism (S : ProtocolSchema.{u}) {v w : S.Vertex} (e : S.Edge v w) :
    S.vertexObject v ⟶ S.vertexObject w :=
  (CategoryTheory.Quotient.functor S.pathRelation).map ((Paths.of S.Vertex).map e)

/-- Embed an arbitrary finite path as an execution in `C_Q`.

This API supports the path-inductive extension theorem required by G-123(B0). -/
def pathMorphism (S : ProtocolSchema.{u}) {v w : S.Vertex} (p : Quiver.Path v w) :
    S.vertexObject v ⟶ S.vertexObject w :=
  (CategoryTheory.Quotient.functor S.pathRelation).map p

/-- Every fixed generating equation holds in the quotient execution category.

This API theorem connects the source equation family `L` to Mathlib's quotient
soundness and is the premise used when decoding edge tables. -/
theorem relation_sound (S : ProtocolSchema.{u}) (r : S.RelationIndex) :
    S.pathMorphism (S.relationLeft r) = S.pathMorphism (S.relationRight r) := by
  apply CategoryTheory.Quotient.sound
  exact ⟨r, rfl, rfl, rfl, rfl⟩

/-- The free-path functor generated by a family of typed operation actions.

This is the Mathlib connection used by the G-123(E) decoder: only vertex types
and named-edge functions are inputs, while all finite executions are constructed
by `Paths.lift`. -/
def pathFunctorOfEdgeAction (S : ProtocolSchema.{u}) (A : S.Vertex → Type v)
    (edgeAction : ∀ {v w : S.Vertex}, S.Edge v w → A v → A w) :
    Paths S.Vertex ⥤ Type v :=
  Paths.lift
    { obj := A
      map := edgeAction }

/-- Evaluate an arbitrary finite path by composing the supplied named-edge actions.

This no-unfold API is the generated execution semantics of n1015 §3.1; the
input contains no precomputed action for a composite path. -/
def evaluatePath (S : ProtocolSchema.{u}) {A : S.Vertex → Type v}
    (edgeAction : ∀ {v w : S.Vertex}, S.Edge v w → A v → A w)
    {v w : S.Vertex} (p : Quiver.Path v w) : A v → A w :=
  (S.pathFunctorOfEdgeAction A edgeAction).map p

/-- A singleton execution evaluates to the supplied named-edge action.

This constructor API for `evaluatePath` connects G-123's generator tables to
one-step protocol execution. -/
@[simp]
theorem evaluatePath_toPath (S : ProtocolSchema.{u}) {A : S.Vertex → Type v}
    (edgeAction : ∀ {v w : S.Vertex}, S.Edge v w → A v → A w)
    {v w : S.Vertex} (e : S.Edge v w) :
    S.evaluatePath edgeAction (Quiver.Hom.toPath e) = edgeAction e := by
  exact Paths.lift_toPath _ _

/-- Concatenated executions evaluate by function composition.

This path API supplies the induction step needed for n1015 §3.1 naturality and
relation proofs from generator equations. -/
@[simp]
theorem evaluatePath_comp (S : ProtocolSchema.{u}) {A : S.Vertex → Type v}
    (edgeAction : ∀ {v w : S.Vertex}, S.Edge v w → A v → A w)
    {v w z : S.Vertex} (p : Quiver.Path v w) (q : Quiver.Path w z) :
    S.evaluatePath edgeAction (p.comp q) =
      S.evaluatePath edgeAction q ∘ S.evaluatePath edgeAction p :=
  (S.pathFunctorOfEdgeAction A edgeAction).map_comp p q

/-- Lifting every vertex carrier and edge action commutes with path evaluation.

This API theorem connects finite `Fin` tables to the universe-polymorphic
decoder without changing any state value or execution. -/
@[simp]
theorem evaluatePath_ulift (S : ProtocolSchema.{u}) {A : S.Vertex → Type v}
    (edgeAction : ∀ {v w : S.Vertex}, S.Edge v w → A v → A w)
    {v w : S.Vertex} (p : Quiver.Path v w) (x : ULift.{u} (A v)) :
    (S.evaluatePath (A := fun z => ULift.{u} (A z))
      (fun e y => ULift.up (edgeAction e y.down)) p x).down =
      S.evaluatePath edgeAction p x.down := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change edgeAction e
          ((S.evaluatePath (A := fun z => ULift.{u} (A z))
            (fun e y => ULift.up (edgeAction e y.down)) p x).down) =
        edgeAction e (S.evaluatePath edgeAction p x.down)
      rw [ih]

end ProtocolSchema

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
