import Mathlib.CategoryTheory.Types.Basic
import ResearchLean.AG.RealizationReconstruction.ProtocolSchema

/-!
# Independent finite-state protocol semantics

For a fixed protocol schema `S=(Q,L)` and observation functor `O`, this module
defines the category `R_proto(Q,L,O)` from G-123(E), n1015 §3 independently of
any finite presentation or decoder.  Objects are finite-carrier functors from
the quotient execution category to types, equipped with a natural observation
map.  Morphisms are all natural transformations over `O`, including
noninvertible adapters.

## Implementation notes

The use of actual Mathlib functors and natural transformations makes execution
of every quotient path, not only of generating edges, part of the semantic
object.  Finiteness is required only at the fixed schema vertices.  Neither
finite enumeration nor representability is an object or morphism field.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- An object of the independent category `R_proto(Q,L,O)` in G-123(E).

The functor and observation map are precisely the n1015 §3.1 semantic inputs;
`state_finite` is the specified finite-carrier condition.  No presentation,
decoder membership, or extension certificate is stored. -/
structure ProtocolRealization (S : ProtocolSchema.{u})
    (O : S.ExecutionCategory ⥤ Type u) where
  /-- The functor interpreting every control point and quotient execution. -/
  toFunctor : S.ExecutionCategory ⥤ Type u
  /-- Finiteness of the carrier at every fixed schema vertex. -/
  state_finite : ∀ v : S.Vertex, Finite (toFunctor.obj (S.vertexObject v))
  /-- The natural observation map `o : X ⟶ O` from n1015 §3.1. -/
  observation : toFunctor ⟶ O

namespace ProtocolRealization

variable {S : ProtocolSchema.{u}} {O : S.ExecutionCategory ⥤ Type u}

/-- State type at a named control point; an object API for n1015 §3.1. -/
abbrev State (X : ProtocolRealization S O) (v : S.Vertex) :=
  X.toFunctor.obj (S.vertexObject v)

/-- Every named state carrier is finite by the n1015 §3.1 object premise. -/
instance (X : ProtocolRealization S O) (v : S.Vertex) : Finite (X.State v) :=
  X.state_finite v

/-- Action of a named operation, kept separate from its operation name.

This is the one-step execution API for G-123(E); it is obtained from the
semantic functor on `S.edgeMorphism e`. -/
def edgeAction (X : ProtocolRealization S O) {v w : S.Vertex} (e : S.Edge v w) :
    X.State v → X.State w :=
  X.toFunctor.map (S.edgeMorphism e)

/-- Action of an arbitrary finite execution path.

This API retains the complete path semantics required by n1015 §3.1, rather
than replacing execution by a generator-only table. -/
def pathAction (X : ProtocolRealization S O) {v w : S.Vertex} (p : Quiver.Path v w) :
    X.State v → X.State w :=
  X.toFunctor.map (S.pathMorphism p)

/-- Observation at a named control point; this is the component of the fixed
n1015 §3.1 map `o : X ⟶ O`. -/
def observe (X : ProtocolRealization S O) (v : S.Vertex) :
    X.State v → O.obj (S.vertexObject v) :=
  X.observation.app (S.vertexObject v)

/-- A protocol morphism is an arbitrary natural transformation over `O`.

This is the complete morphism class of G-123(E), n1015 §3.1; it includes
noninvertible adapters and imposes no finite-presentation membership. -/
@[ext]
structure Hom (X Y : ProtocolRealization S O) where
  /-- The natural transformation on all objects and quotient executions. -/
  toNatTrans : X.toFunctor ⟶ Y.toFunctor
  /-- The n1015 observation-preservation equation `a ≫ o_Y = o_X`. -/
  observation_naturality : toNatTrans ≫ Y.observation = X.observation

/-- The independent protocol realizations and all observation-preserving
natural transformations form the semantic category required by G-123(A,E). -/
instance : Category (ProtocolRealization S O) where
  Hom := Hom
  id X :=
    { toNatTrans := 𝟙 X.toFunctor
      observation_naturality := Category.id_comp _ }
  comp f g :=
    { toNatTrans := f.toNatTrans ≫ g.toNatTrans
      observation_naturality := by
        rw [Category.assoc, g.observation_naturality, f.observation_naturality] }
  id_comp := by
    intro X Y f
    ext q x
    rfl
  comp_id := by
    intro X Y f
    ext q x
    rfl
  assoc := by
    intro W X Y Z f g h
    ext q x
    rfl

/-- A semantic protocol morphism acts at every quotient-category object; this
is the component API used by G-123(B0) restriction. -/
def app {X Y : ProtocolRealization S O} (a : X ⟶ Y) (q : S.ExecutionCategory) :
    X.toFunctor.obj q → Y.toFunctor.obj q :=
  a.toNatTrans.app q

/-- Naturality of a complete semantic morphism along a named operation.

This is an API specialization of naturality used to define and audit generator
tables in G-123(B0). -/
theorem edge_naturality {X Y : ProtocolRealization S O} (a : X ⟶ Y)
    {v w : S.Vertex} (e : S.Edge v w) :
    X.edgeAction e ≫ a.toNatTrans.app (S.vertexObject w) =
      a.toNatTrans.app (S.vertexObject v) ≫ Y.edgeAction e :=
  a.toNatTrans.naturality (S.edgeMorphism e)

/-- Naturality of a complete semantic morphism along every finite execution.

This records the all-path conclusion required by n1015 §3.1 and is inherited
from the actual natural transformation, not postulated for generator data. -/
theorem path_naturality {X Y : ProtocolRealization S O} (a : X ⟶ Y)
    {v w : S.Vertex} (p : Quiver.Path v w) :
    X.pathAction p ≫ a.toNatTrans.app (S.vertexObject w) =
      a.toNatTrans.app (S.vertexObject v) ≫ Y.pathAction p :=
  a.toNatTrans.naturality (S.pathMorphism p)

/-- Observation preservation at every named control point.

This component API follows from the n1015 §3.1 equation stored for a complete
semantic morphism and is used by G-123(B0) restriction. -/
theorem observation_app {X Y : ProtocolRealization S O} (a : X ⟶ Y)
    (v : S.Vertex) :
    a.toNatTrans.app (S.vertexObject v) ≫ Y.observe v = X.observe v := by
  have h := NatTrans.congr_app a.observation_naturality (S.vertexObject v)
  exact h

end ProtocolRealization

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
