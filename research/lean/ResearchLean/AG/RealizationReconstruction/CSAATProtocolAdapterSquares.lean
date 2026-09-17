import ResearchLean.AG.RealizationReconstruction.CSAATForwardMorphisms
import ResearchLean.AG.RealizationReconstruction.FixedFProtocolConnection
import Formal.Util.AssertStandardAxioms

/-!
# Directed protocol adapter squares

The adapters remain arbitrary forward morphisms.  Only a later specialization
needs invertible endpoint changes.  Every statement keeps the fixed schema
edge/path names literally unchanged.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace ProtocolAATForwardMorphism

/-- P1 stated entirely in the named-operation forward interface. -/
def DirectedAdapterSquare {input : ProtocolFamilyInput.{u}}
    {X Y X' Y' : ProtocolRealization input.schema input.observation}
    (q : ProtocolAATForwardMorphism X Y)
    (q' : ProtocolAATForwardMorphism X' Y')
    (a : ProtocolAATForwardMorphism X X')
    (b : ProtocolAATForwardMorphism Y Y') : Prop :=
  comp q b = comp a q'

/-- The directed named-operation square is exactly the independently defined
semantic adapter square, with no invertibility assumption on any side. -/
theorem directedAdapterSquare_iff_semantic
    {input : ProtocolFamilyInput.{u}}
    {X Y X' Y' : ProtocolRealization input.schema input.observation}
    (q : ProtocolAATForwardMorphism X Y)
    (q' : ProtocolAATForwardMorphism X' Y')
    (a : ProtocolAATForwardMorphism X X')
    (b : ProtocolAATForwardMorphism Y Y') :
    DirectedAdapterSquare q q' a b ↔
      FixedFProtocolConnection.AdapterSquare
        q.toSemanticHom q'.toSemanticHom a.toSemanticHom b.toSemanticHom := by
  constructor
  · intro square
    have semantic := congrArg toSemanticHom square
    simpa using semantic
  · intro square
    have forward := congrArg ofSemanticHom square
    simpa using forward

/-- P1 at each named control point, stated using the primitive state maps. -/
theorem DirectedAdapterSquare.state
    {input : ProtocolFamilyInput.{u}}
    {X Y X' Y' : ProtocolRealization input.schema input.observation}
    {q : ProtocolAATForwardMorphism X Y}
    {q' : ProtocolAATForwardMorphism X' Y'}
    {a : ProtocolAATForwardMorphism X X'}
    {b : ProtocolAATForwardMorphism Y Y'}
    (square : DirectedAdapterSquare q q' a b)
    (vertex : input.schema.Vertex) (state : X.State vertex) :
    b.stateMap vertex (q.stateMap vertex state) =
      q'.stateMap vertex (a.stateMap vertex state) := by
  have semantic :=
    (directedAdapterSquare_iff_semantic q q' a b).1 square
  exact (FixedFProtocolConnection.adapterSquare_iff_totalMaps _ _ _ _).1 semantic
    (input.schema.vertexObject vertex) state

/-- Both adapter routes preserve the same literal named edge execution. -/
theorem DirectedAdapterSquare.namedEdge_execution
    {input : ProtocolFamilyInput.{u}}
    {X Y X' Y' : ProtocolRealization input.schema input.observation}
    {q : ProtocolAATForwardMorphism X Y}
    {q' : ProtocolAATForwardMorphism X' Y'}
    {a : ProtocolAATForwardMorphism X X'}
    {b : ProtocolAATForwardMorphism Y Y'}
    (square : DirectedAdapterSquare q q' a b)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) (state : X.State source) :
    b.stateMap target
        (protocolEdgeAATFunction Y edge (q.stateMap source state)) =
      q'.stateMap target
        (protocolEdgeAATFunction X' edge (a.stateMap source state)) := by
  rw [b.edge_naturality edge, q'.edge_naturality edge]
  exact congrArg (protocolEdgeAATFunction Y' edge)
    (square.state source state)

/-- The two adapter routes give the same observation at every named vertex. -/
theorem DirectedAdapterSquare.observation
    {input : ProtocolFamilyInput.{u}}
    {X Y X' Y' : ProtocolRealization input.schema input.observation}
    {q : ProtocolAATForwardMorphism X Y}
    {q' : ProtocolAATForwardMorphism X' Y'}
    {a : ProtocolAATForwardMorphism X X'}
    {b : ProtocolAATForwardMorphism Y Y'}
    (square : DirectedAdapterSquare q q' a b)
    (vertex : input.schema.Vertex) (state : X.State vertex) :
    protocolObserveAATFunction Y' vertex
        (b.stateMap vertex (q.stateMap vertex state)) =
      protocolObserveAATFunction Y' vertex
        (q'.stateMap vertex (a.stateMap vertex state)) :=
  congrArg (protocolObserveAATFunction Y' vertex) (square.state vertex state)

/-- The generator-level square extends to every finite path while retaining
the same path name on all four sides. -/
theorem DirectedAdapterSquare.path_execution
    {input : ProtocolFamilyInput.{u}}
    {X Y X' Y' : ProtocolRealization input.schema input.observation}
    {q : ProtocolAATForwardMorphism X Y}
    {q' : ProtocolAATForwardMorphism X' Y'}
    {a : ProtocolAATForwardMorphism X X'}
    {b : ProtocolAATForwardMorphism Y Y'}
    (square : DirectedAdapterSquare q q' a b)
    {source target : input.schema.Vertex}
    (path : Quiver.Path source target) (state : X.State source) :
    b.stateMap target
        (Y.pathAction path (q.stateMap source state)) =
      q'.stateMap target
        (X'.pathAction path (a.stateMap source state)) := by
  calc
    b.stateMap target (Y.pathAction path (q.stateMap source state)) =
        Y'.pathAction path (b.stateMap source (q.stateMap source state)) := by
      exact congrFun (ProtocolRealization.path_naturality b.toSemanticHom path)
        (q.stateMap source state)
    _ = Y'.pathAction path
        (q'.stateMap source (a.stateMap source state)) :=
      congrArg (Y'.pathAction path) (square.state source state)
    _ = q'.stateMap target
        (X'.pathAction path (a.stateMap source state)) := by
      exact (congrFun
        (ProtocolRealization.path_naturality q'.toSemanticHom path)
        (a.stateMap source state)).symm

/-- Canonical forward P1 for arbitrary semantic adapters and arbitrary
semantic endpoint maps. -/
theorem ofSemanticHom_directedAdapterSquare_iff
    {input : ProtocolFamilyInput.{u}}
    {X Y X' Y' : ProtocolRealization input.schema input.observation}
    (q : X ⟶ Y) (q' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') :
    DirectedAdapterSquare (ofSemanticHom q) (ofSemanticHom q')
        (ofSemanticHom a) (ofSemanticHom b) ↔
      FixedFProtocolConnection.AdapterSquare q q' a b := by
  simpa using directedAdapterSquare_iff_semantic
    (ofSemanticHom q) (ofSemanticHom q') (ofSemanticHom a) (ofSemanticHom b)

/-- Exact n1015 P1 specialization: adapters stay arbitrary while only the
endpoint changes are required to be genuine semantic isomorphisms. -/
theorem ofSemanticHom_invertibleAdapterSquare_iff
    {input : ProtocolFamilyInput.{u}}
    {X Y X' Y' : ProtocolRealization input.schema input.observation}
    (q : X ⟶ Y) (q' : X' ⟶ Y') (a : X ≅ X') (b : Y ≅ Y') :
    DirectedAdapterSquare (ofSemanticHom q) (ofSemanticHom q')
        (ofSemanticHom a.hom) (ofSemanticHom b.hom) ↔
      FixedFProtocolConnection.InvertibleAdapterSquare q q' a b := by
  exact ofSemanticHom_directedAdapterSquare_iff q q' a.hom b.hom

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end ProtocolAATForwardMorphism

end AAT.AG.RealizationReconstruction
