import Mathlib.CategoryTheory.PathCategory.MorphismProperty
import ResearchLean.AG.RealizationReconstruction.ProtocolSemantics

/-!
# Protocol generator restriction and path-inductive extension

This module proves G-123(B0) for the independent protocol category.  Generator
data consists only of a state map at each schema vertex, satisfying the named
edge squares and observation equations.  Extension constructs naturality for
every free path by `Paths.liftNatTrans` and then for every quotient execution by
Mathlib quotient induction.

## Implementation notes

`ProtocolGeneratorMap` does not contain a completed natural transformation or
an extension certificate.  Its equations are exactly the generator-level
conditions fixed in n1015 §3.1.  Both inverse equations are stated separately.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace ProtocolRealization

variable {S : ProtocolSchema.{u}} {O : S.ExecutionCategory ⥤ Type u}

/-- Generator-level map between two independent protocol realizations.

This is the finite-family data of G-123(B0), n1015 §3.1: one component per
fixed vertex, named-edge commutation, and observation preservation.  It stores
neither all-path naturality nor a completed semantic morphism. -/
@[ext]
structure GeneratorMap (X Y : ProtocolRealization S O) where
  /-- State map at each fixed schema vertex. -/
  component : ∀ v : S.Vertex, X.State v → Y.State v
  /-- Naturality only for each named operation generator. -/
  edge_naturality : ∀ {v w : S.Vertex} (e : S.Edge v w),
    component w ∘ X.edgeAction e = Y.edgeAction e ∘ component v
  /-- Observation preservation at each fixed vertex. -/
  observation_naturality : ∀ v : S.Vertex,
    Y.observe v ∘ component v = X.observe v

/-- Generator squares extend to a natural transformation on every free path.

This is the path-induction step demanded by G-123(B0), n1015 §3.1; the all-path
equations are constructed from named-edge equations via Mathlib's path API. -/
def generatorPathNatTrans {X Y : ProtocolRealization S O}
    (t : GeneratorMap X Y) :
    CategoryTheory.Quotient.functor S.pathRelation ⋙ X.toFunctor ⟶
      CategoryTheory.Quotient.functor S.pathRelation ⋙ Y.toFunctor :=
  Paths.liftNatTrans t.component t.edge_naturality

/-- A generator map commutes with every finite execution path.

This no-unfold API exposes the all-path conclusion constructed by
`generatorPathNatTrans`; no path-wise map family is an input. -/
theorem generator_path_naturality {X Y : ProtocolRealization S O}
    (t : GeneratorMap X Y) {v w : S.Vertex} (p : Quiver.Path v w) :
    t.component w ∘ X.pathAction p = Y.pathAction p ∘ t.component v := by
  exact (generatorPathNatTrans t).naturality p

/-- Restrict a complete semantic morphism to its vertex generator maps.

This is `res` in the protocol instance of G-123(B0); edge and observation
equations are consequences of the complete morphism's naturality. -/
def res {X Y : ProtocolRealization S O} (a : X ⟶ Y) : GeneratorMap X Y where
  component v := a.toNatTrans.app (S.vertexObject v)
  edge_naturality := ProtocolRealization.edge_naturality a
  observation_naturality := ProtocolRealization.observation_app a

/-- Extend generator data to a complete semantic protocol morphism.

This is `ext` in G-123(B0), n1015 §3.1.  Naturality for arbitrary quotient
executions is derived by path induction and quotient induction. -/
def ext {X Y : ProtocolRealization S O} (t : GeneratorMap X Y) : X ⟶ Y where
  toNatTrans :=
    { app := fun q => t.component q.as
      naturality := by
        intro q q' f
        apply CategoryTheory.Quotient.induction (r := S.pathRelation)
          (P := fun {a b} f =>
            X.toFunctor.map f ≫ t.component b.as =
              t.component a.as ≫ Y.toFunctor.map f)
        intro a b p
        exact (generatorPathNatTrans t).naturality p }
  observation_naturality := by
    ext q x
    exact congrFun (t.observation_naturality q.as) x

/-- Restriction after the constructed extension recovers the generator data.

This is one direction of the protocol G-123(B0) bijection and uses only
function extensionality and proof irrelevance. -/
@[simp]
theorem res_ext {X Y : ProtocolRealization S O} (t : GeneratorMap X Y) :
    res (ext t) = t := by
  ext v x
  rfl

/-- Extension after restriction recovers the complete semantic morphism.

This is the all-object/all-execution direction of G-123(B0), not merely an
equality on named generators. -/
@[simp]
theorem ext_res {X Y : ProtocolRealization S O} (a : X ⟶ Y) :
    ext (res a) = a := by
  apply Hom.ext
  ext q x
  rfl

/-- Complete protocol morphisms are equivalent to generator-level maps.

This is the protocol endpointwise reconstruction theorem of G-123(B0),
assembled from the separately proved `res_ext` and `ext_res`. -/
def homEquivGeneratorMap (X Y : ProtocolRealization S O) :
    (X ⟶ Y) ≃ GeneratorMap X Y where
  toFun := res
  invFun := ext
  left_inv := ext_res
  right_inv := res_ext

/-- Restriction sends semantic identity to identity vertex maps.

This functoriality API supports the four separate G-123(B) reconstruction
properties without unfolding `res`. -/
@[simp]
theorem res_id (X : ProtocolRealization S O) :
    ∀ (v : S.Vertex) (x : X.State v), (res (𝟙 X)).component v x = x :=
  fun _ _ => rfl

/-- Restriction sends semantic composition to pointwise table composition.

This functoriality API is derived from the category structure on complete
natural transformations. -/
@[simp]
theorem res_comp {X Y Z : ProtocolRealization S O} (a : X ⟶ Y) (b : Y ⟶ Z)
    (v : S.Vertex) (x : X.State v) :
    (res (a ≫ b)).component v x = (res b).component v ((res a).component v x) := rfl

end ProtocolRealization

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
