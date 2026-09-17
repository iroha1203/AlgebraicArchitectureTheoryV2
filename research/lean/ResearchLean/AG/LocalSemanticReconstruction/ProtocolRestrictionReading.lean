import ResearchLean.AG.LocalSemanticReconstruction.CSFiniteLocalReading
import Formal.Util.AssertStandardAxioms

/-!
# The finite protocol restriction reading

For a fixed protocol input, the quotient execution category is determined
before any realization.  Its opposite is therefore a parameter-owned
restriction index.  A realization supplies a finite state carrier at every
object and an actual restriction map for every quotient execution.  Every
admitted protocol morphism supplies the corresponding natural transformation.

This is the non-discrete protocol slice of the G-124(A--B) reading.  The fixed
observation target is not required to be finite, so it is not inserted into
the `FintypeCat`-valued diagram.  Observation preservation is instead exposed
as an exact law of the same local-reading component.  Thus this module does
not claim morphism assembly, a protocol equivalence, or the final four-branch
`Lambda_Theta` and `N_Theta`.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

universe u v

/-- The parameter-owned restriction index for a protocol is the opposite of
its quotient execution category. -/
abbrev ProtocolRestrictionIndex (input : ProtocolFamilyInput.{u}) :=
  input.schema.ExecutionCategoryᵒᵖ

/-- Every quotient execution object is represented by a schema vertex, hence
its realized state carrier is finite by the accepted protocol object premise. -/
instance protocolExecutionStateFinite
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    (q : input.schema.ExecutionCategory) : Finite (X.toFunctor.obj q) := by
  cases q with
  | mk vertex => exact X.state_finite vertex

/-- The actual finite state diagram on all quotient executions.  The double
opposite appears because `LocalModelCategory` is contravariant in its supplied
restriction category. -/
noncomputable def protocolRestrictionDiagram
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    LocalModelCategory (ProtocolRestrictionIndex input) FintypeCat.{u} where
  obj q := finiteLocalValue (X.toFunctor.obj q.unop.unop)
  map f := FintypeCat.homMk (X.toFunctor.map f.unop.unop)
  map_id q := by
    apply FintypeCat.hom_ext
    intro state
    exact congrFun (X.toFunctor.map_id q.unop.unop) state
  map_comp f g := by
    apply FintypeCat.hom_ext
    intro state
    exact congrFun (X.toFunctor.map_comp f.unop.unop g.unop.unop) state

/-- The exact natural transformation between finite execution diagrams read
from an admitted closed-family protocol morphism. -/
noncomputable def protocolRestrictionMap
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y) :
    protocolRestrictionDiagram input X ⟶
      protocolRestrictionDiagram input Y where
  app q := FintypeCat.homMk
    (ProtocolRealization.app f.down.toSemanticHom q.unop.unop)
  naturality := by
    intro q r g
    apply FintypeCat.hom_ext
    intro state
    exact congrFun (f.down.toSemanticHom.toNatTrans.naturality g.unop.unop) state

/-- Actual reading of the accepted protocol branch into its non-discrete
finite restriction diagrams. -/
noncomputable def protocolRestrictionReading
    (input : ProtocolFamilyInput.{u}) :
    ClosedFamilyLocalReading (.protocol input)
      (ProtocolRestrictionIndex input) FintypeCat.{u} where
  obj X := by
    cases X with
    | protocol realization => exact protocolRestrictionDiagram input realization
  map {X Y} f := by
    cases X with
    | protocol source =>
      cases Y with
      | protocol target => exact protocolRestrictionMap input f
  map_id X := by
    cases X with
    | protocol realization =>
      apply NatTrans.ext
      funext q
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
          apply NatTrans.ext
          funext q
          apply FintypeCat.hom_ext
          intro state
          rfl

/-- At a named vertex the execution diagram is exactly the accepted finite
state carrier. -/
@[simp] theorem protocolRestrictionDiagram_obj_vertex
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    (protocolRestrictionDiagram input X).obj
        (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) =
      finiteLocalValue (X.State vertex) :=
  rfl

/-- A named edge is read as its exact accepted one-step state action. -/
@[simp] theorem protocolRestrictionDiagram_map_edge
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) (state : X.State source) :
    (protocolRestrictionDiagram input X).map
        (input.schema.edgeMorphism edge).op.op state =
      X.edgeAction edge state :=
  rfl

/-- An arbitrary finite path is read as its exact accepted path action. -/
@[simp] theorem protocolRestrictionDiagram_map_path
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex}
    (path : Quiver.Path source target) (state : X.State source) :
    (protocolRestrictionDiagram input X).map
        (input.schema.pathMorphism path).op.op state =
      X.pathAction path state :=
  rfl

/-- Every component of the non-discrete reading is exactly the component of
the accepted semantic natural transformation. -/
@[simp] theorem protocolRestrictionReading_map_app
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y)
    (q : input.schema.ExecutionCategory) (state : X.toFunctor.obj q) :
    ((protocolRestrictionReading input).map f).app
        (Opposite.op (Opposite.op q)) state =
      ProtocolRealization.app f.down.toSemanticHom q state :=
  rfl

/-- The named-edge square is naturality of the actual non-discrete local
reading, stated without unfolding that reading. -/
theorem protocolRestrictionReading_edge_naturality
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) (state : X.State source) :
    ((protocolRestrictionReading input).map f).app
        (Opposite.op (Opposite.op (input.schema.vertexObject target)))
        ((protocolRestrictionDiagram input X).map
          (input.schema.edgeMorphism edge).op.op state) =
      (protocolRestrictionDiagram input Y).map
          (input.schema.edgeMorphism edge).op.op
        (((protocolRestrictionReading input).map f).app
          (Opposite.op (Opposite.op (input.schema.vertexObject source))) state) := by
  simpa only [protocolRestrictionDiagram_map_edge,
    protocolRestrictionReading_map_app] using
      congrFun (ProtocolRealization.edge_naturality
        f.down.toSemanticHom edge) state

/-- The same non-discrete local-reading component preserves the fixed
protocol observation. -/
theorem protocolRestrictionReading_observation
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y)
    (vertex : input.schema.Vertex) (state : X.State vertex) :
    Y.observe vertex
        (((protocolRestrictionReading input).map f).app
          (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) state) =
      X.observe vertex state := by
  simpa only [protocolRestrictionReading_map_app] using
    congrFun (ProtocolRealization.observation_app
      f.down.toSemanticHom vertex) state

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
