import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticAssembly

/-!
# Indexed diagnostic covariance, d1--d3

This module packages the K2 outputs as the target interpretation required by
G-111 `(d1)`, exposes the vertexwise endpoint group homomorphism `(d2)`, and
records the relation-relative target data equations `(d3)`.  The target
interpretation is constructed, rather than accepted as a theorem argument or
structure field.  Reselection, coherence, and vanishing are the next layer.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

namespace IndexedBaseDiagramHom

/--
`(d1)`: the K2 outputs assembled as an ordinary diagnostic interpretation on
the already fixed target base diagram.
-/
noncomputable def transportedInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    IndexedDiagnosticInterpretation E where
  package := hom.transportedPackage source
  vertexBase := hom.transportedPackage_vertexBase source
  edgeLift := hom.transportedEdgeLift source
  edgeOver := hom.transportedEdgeLift_isHomLift source
  edgeStrong := hom.transportedEdgeLift_isStronglyCocartesian source
  comparator := hom.transportedComparator source

/-- `(d2)`: the generated endpoint group homomorphism at one fixed vertex. -/
noncomputable def endpointAction
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageFiberAut (source.package vertex) →*
      PackageFiberAut ((hom.transportedInterpretation source).package vertex) :=
  coreFiberFunctorPackageAutHom
    (indexedFiberAction (hom.vertexIndex vertex))
    (source.fiberPackage vertex)

/-- The `(d1)` target package is the K2 vertexwise generated package. -/
@[simp]
theorem transportedInterpretation_package
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    (hom.transportedInterpretation source).package vertex =
      hom.transportedPackage source vertex := rfl

/-- The `(d1)` target edge is the K2 generating-square image. -/
@[simp]
theorem transportedInterpretation_edgeLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j : G.Vertex}
    (edge : G.Edge i j) :
    (hom.transportedInterpretation source).edgeLift edge =
      hom.transportedEdgeLift source edge := rfl

/-- The `(d2)` endpoint action preserves the identity automorphism. -/
@[simp]
theorem endpointAction_one
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    hom.endpointAction source vertex 1 = 1 :=
  map_one (hom.endpointAction source vertex)

/-- The `(d2)` endpoint action preserves automorphism multiplication. -/
@[simp]
theorem endpointAction_mul
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (first second : PackageFiberAut (source.package vertex)) :
    hom.endpointAction source vertex (first * second) =
      hom.endpointAction source vertex first *
        hom.endpointAction source vertex second :=
  map_mul (hom.endpointAction source vertex) first second

/--
`(d3)`: every target comparator is the endpoint action applied to the authored
source comparator.
-/
@[simp]
theorem transportedInterpretation_comparator
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (cell : G.TwoCell) :
    (hom.transportedInterpretation source).comparator cell =
      hom.endpointAction source (G.twoTarget cell) (source.comparator cell) :=
  rfl

/-- The path lift of the `(d1)` interpretation is the recursively generated K2 path lift. -/
@[simp]
theorem transportedInterpretation_pathLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (hom.transportedInterpretation source).pathLift path =
      hom.transportedPathLift source path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.pathLift,
        IndexedBaseDiagramHom.transportedPathLift,
        transportedInterpretation_edgeLift, inductionHypothesis]

/--
`(d3)`: the target interpretation's declared-cell base equation is the fixed
target diagram relation, realized by the K2 transported path lifts.
-/
theorem transportedInterpretation_twoCellBase
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (cell : G.TwoCell) :
    ((hom.transportedInterpretation source).pathLift (G.twoLeft cell)).base =
      ((hom.transportedInterpretation source).pathLift (G.twoRight cell)).base :=
  by simpa using hom.transportedTwoCellBase source cell

/-- The target edge qualification remains a generated theorem of `(d1)`. -/
theorem transportedInterpretation_edgeStrong
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j : G.Vertex}
    (edge : G.Edge i j) :
    (packageProjection U).IsStronglyCocartesian (E.edge edge)
      ((hom.transportedInterpretation source).edgeLift edge) :=
  hom.transportedEdgeLift_isStronglyCocartesian source edge

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
