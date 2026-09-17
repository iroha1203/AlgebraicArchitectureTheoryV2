import Mathlib.CategoryTheory.FintypeCat
import ResearchLean.AG.LocalSemanticReconstruction.LocalModelCategory
import Formal.Util.AssertStandardAxioms

/-!
# Actual finite local readings for the two CS branches

This module constructs the first actual finite-value slices of the G-124(A--B)
reading.  A lens is read on its finite reference fiber.  A protocol is read at
each named vertex on its finite state carrier.  Every admitted closed-family
morphism is read by the corresponding accepted semantic component.

The restriction index in each slice is the one-point discrete category.  The
family of protocol slices is indexed externally by the parameter-owned vertex
type.  Consequently this module does not claim the final four-branch
`Lambda_Theta`, the operation/observation restriction equations, or the main
reading functor.  In particular it does not manufacture empty tagged or G-122
components to make a vacuous common reading.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

universe u v

/-- Bundle a type whose accepted object premise proves finiteness as an object
of `FintypeCat`.  The chosen enumeration is not an effectiveness claim. -/
noncomputable abbrev finiteLocalValue (A : Type u) [Finite A] : FintypeCat.{u} := by
  letI := Fintype.ofFinite A
  exact FintypeCat.of A

/-- Reading of every closed-family lens realization on its finite reference
fiber.  Its map is the exact restriction of the admitted package morphism. -/
noncomputable def lensFiberValueReading (input : LensFamilyInput.{u}) :
    FamilyRealization.{u, v} (.lens input) ⥤ FintypeCat.{u} where
  obj X := by
    cases X with
    | lens realization => exact finiteLocalValue realization.Fiber
  map {X Y} f := by
    cases X with
    | lens source =>
      cases Y with
      | lens target =>
        exact FintypeCat.homMk
          (LensRealization.res f.down.toSemanticHom)
  map_id X := by
    cases X with
    | lens realization =>
      apply FintypeCat.hom_ext
      intro state
      rfl
  map_comp {X Y Z} f g := by
    cases X with
    | lens source =>
      cases Y with
      | lens middle =>
        cases Z with
        | lens target =>
          apply FintypeCat.hom_ext
          intro state
          rfl

/-- The lens-fiber value reading, viewed as a genuine local-model reading on
the one-point restriction category. -/
noncomputable def lensFiberLocalReading (input : LensFamilyInput.{u}) :
    ClosedFamilyLocalReading (.lens input)
      (Discrete PUnit) FintypeCat.{u} :=
  lensFiberValueReading input ⋙ Functor.const ((Discrete PUnit)ᵒᵖ)

/-- No-unfold object API: the unique local value is exactly the accepted
finite reference fiber. -/
@[simp] theorem lensFiberLocalReading_obj
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    ((lensFiberLocalReading input).obj (.lens X)).obj
        (Opposite.op (Discrete.mk PUnit.unit)) =
      finiteLocalValue X.Fiber :=
  rfl

/-- No-unfold map API: the unique local component is exactly `res` on the
accepted semantic morphism. -/
@[simp] theorem lensFiberLocalReading_map_app
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : FamilyRealization.lens X ⟶ FamilyRealization.lens Y)
    (state : X.Fiber) :
    (((lensFiberLocalReading input).map f).app
        (Opposite.op (Discrete.mk PUnit.unit))) state =
      LensRealization.res f.down.toSemanticHom state :=
  rfl

/-- At a fixed parameter-owned vertex, read every protocol realization on its
finite state carrier and every admitted morphism by its exact component. -/
noncomputable def protocolVertexValueReading
    (input : ProtocolFamilyInput.{u}) (vertex : input.schema.Vertex) :
    FamilyRealization.{u, v} (.protocol input) ⥤ FintypeCat.{u} where
  obj X := by
    cases X with
    | protocol realization => exact finiteLocalValue (realization.State vertex)
  map {X Y} f := by
    cases X with
    | protocol source =>
      cases Y with
      | protocol target =>
        exact FintypeCat.homMk
          (ProtocolRealization.app f.down.toSemanticHom
            (input.schema.vertexObject vertex))
  map_id X := by
    cases X with
    | protocol realization =>
      apply FintypeCat.hom_ext
      intro state
      rfl
  map_comp {X Y Z} f g := by
    cases X with
    | protocol source =>
      cases Y with
      | protocol middle =>
        cases Z with
        | protocol target =>
          apply FintypeCat.hom_ext
          intro state
          rfl

/-- A named protocol-state reading as a local-model reading on the one-point
restriction category.  Quantifying over `vertex` gives the actual family of
finite named-state readings. -/
noncomputable def protocolVertexLocalReading
    (input : ProtocolFamilyInput.{u}) (vertex : input.schema.Vertex) :
    ClosedFamilyLocalReading (.protocol input)
      (Discrete PUnit) FintypeCat.{u} :=
  protocolVertexValueReading input vertex ⋙
    Functor.const ((Discrete PUnit)ᵒᵖ)

/-- No-unfold object API for a named finite protocol state carrier. -/
@[simp] theorem protocolVertexLocalReading_obj
    (input : ProtocolFamilyInput.{u}) (vertex : input.schema.Vertex)
    (X : ProtocolRealization input.schema input.observation) :
    ((protocolVertexLocalReading input vertex).obj (.protocol X)).obj
        (Opposite.op (Discrete.mk PUnit.unit)) =
      finiteLocalValue (X.State vertex) :=
  rfl

/-- No-unfold map API for the exact admitted protocol component at a named
vertex. -/
@[simp] theorem protocolVertexLocalReading_map_app
    (input : ProtocolFamilyInput.{u}) (vertex : input.schema.Vertex)
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y)
    (state : X.State vertex) :
    (((protocolVertexLocalReading input vertex).map f).app
        (Opposite.op (Discrete.mk PUnit.unit))) state =
      ProtocolRealization.app f.down.toSemanticHom
        (input.schema.vertexObject vertex) state :=
  rfl

/-- The protocol local components satisfy the named-edge coherence equation
because they come from the accepted semantic natural transformation. -/
theorem protocolVertexReading_edge_naturality
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) (state : X.State source) :
    (((protocolVertexLocalReading input target).map f).app
        (Opposite.op (Discrete.mk PUnit.unit))) (X.edgeAction edge state) =
      Y.edgeAction edge
        ((((protocolVertexLocalReading input source).map f).app
          (Opposite.op (Discrete.mk PUnit.unit))) state) := by
  simpa only [protocolVertexLocalReading_map_app] using
    congrFun (ProtocolRealization.edge_naturality
      f.down.toSemanticHom edge) state

/-- The protocol local component preserves the fixed observation at every
named vertex. -/
theorem protocolVertexReading_observation
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y)
    (vertex : input.schema.Vertex) (state : X.State vertex) :
    Y.observe vertex
        ((((protocolVertexLocalReading input vertex).map f).app
          (Opposite.op (Discrete.mk PUnit.unit))) state) =
      X.observe vertex state := by
  simpa only [protocolVertexLocalReading_map_app] using
    congrFun (ProtocolRealization.observation_app
      f.down.toSemanticHom vertex) state

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
