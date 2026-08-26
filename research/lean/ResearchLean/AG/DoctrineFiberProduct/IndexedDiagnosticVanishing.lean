import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticCoherence
import ResearchLean.AG.TransportCoherence.VanishingCoherence

/-!
# Indexed diagnostic obstruction vanishing

This module proves G-111 `(d6)`.  It embeds the finite indexed 0/1/2-skeleton
into the existing obstruction presentation without changing vertices, edges,
packages, or comparators.  The independent raw-defect orbit definition and its
proved equivalence with coherentizability can therefore be used directly.

The adapter does not impose common-fiber incidence.  The source vanishing
hypothesis is consumed to obtain a source coherent reselection; `(d5)` maps
that reselection and its actual path equation to the target, which then yields
target obstruction vanishing.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence
open TransportCoherence

private theorem stronglyCocartesian_map_of_strongLift
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    {P Q : AATCorePackage U} (base : X ⟶ Y)
    (lift : PackageTotalHom P Q)
    [hStrong : (packageProjection U).IsStronglyCocartesian base lift] :
    (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map lift) lift := by
  subst_hom_lift (packageProjection U) base lift
  infer_instance

namespace IndexedBasePath

/-- Forget only the name of an indexed finite path, retaining every edge. -/
def toPresentedPath {G : IndexedBaseShape.{u}} {i j : G.Vertex} :
    IndexedBasePath G i j → PresentedPath G.Edge i j
  | .nil vertex => .nil vertex
  | .cons edge tail => .cons edge tail.toPresentedPath

end IndexedBasePath

namespace IndexedBaseTwoShape

/-- The existing obstruction-theory presentation on the same indexed 2-skeleton. -/
abbrev toFiniteTransportPresentation (G : IndexedBaseTwoShape.{u}) :
    FiniteTransportPresentation.{u} where
  Vertex := G.Vertex
  vertexFintype := G.vertexFintype
  Edge := G.Edge
  edgeFintype := G.edgeFintype
  TwoCell := G.TwoCell
  twoCellFintype := G.twoCellFintype
  twoSource := G.twoSource
  twoTarget := G.twoTarget
  twoLeft := fun cell => (G.twoLeft cell).toPresentedPath
  twoRight := fun cell => (G.twoRight cell).toPresentedPath
  ThreeCell := ULift.{u} PEmpty
  threeCellFintype := inferInstance
  threeSource := fun cell => nomatch cell.down
  threeTarget := fun cell => nomatch cell.down
  threeStart := fun cell => nomatch cell.down
  threeFinish := fun cell => nomatch cell.down
  threeLeft := fun cell => nomatch cell.down
  threeRight := fun cell => nomatch cell.down

end IndexedBaseTwoShape

namespace IndexedDiagnosticInterpretation

/-- The indexed source lift data viewed by the independent obstruction theory. -/
noncomputable abbrev toAdmissibleLiftData
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D) :
    AdmissibleLiftData G.toFiniteTransportPresentation U where
  package := source.package
  edgeLift := source.edgeLift
  edgeStrong := by
    intro i j edge
    letI : (packageProjection U).IsStronglyCocartesian
        (D.edge edge) (source.edgeLift edge) := source.edgeStrong edge
    exact stronglyCocartesian_map_of_strongLift
      (D.edge edge) (source.edgeLift edge)

/-- The obstruction adapter evaluates every path by the same total morphism. -/
@[simp]
theorem toAdmissibleLiftData_pathLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    source.toAdmissibleLiftData.pathLift path.toPresentedPath =
      source.pathLift path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedBasePath.toPresentedPath,
        AdmissibleLiftData.pathLift, pathLift, inductionHypothesis]

/-- The indexed interpretation as ordinary admissible obstruction data. -/
noncomputable abbrev toAdmissibleTransportData
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D) :
    AdmissibleTransportData G.toFiniteTransportPresentation U where
  lift := source.toAdmissibleLiftData
  twoCellBase := fun cell => by
    simpa only [IndexedBaseTwoShape.toFiniteTransportPresentation,
      toAdmissibleLiftData_pathLift] using source.twoCellBase cell
  comparator := source.comparator

/-- Edge reselections are unchanged by the obstruction adapter. -/
@[simp]
theorem toAdmissibleTransportData_reselection_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) (i j : G.Vertex)
    (edge : G.Edge i j) :
    (reselection : EdgeReselection source.toAdmissibleTransportData.lift)
        i j edge = reselection i j edge := rfl

/-- The obstruction adapter evaluates every reselected path identically. -/
@[simp]
theorem toAdmissibleTransportData_reselectedPathLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    TransportCoherence.reselectedPathLift
        source.toAdmissibleTransportData.lift reselection path.toPresentedPath =
      source.reselectedPathLift reselection path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedBasePath.toPresentedPath,
        TransportCoherence.reselectedPathLift,
        TransportCoherence.reselectLiftData,
        AdmissibleLiftData.pathLift,
        TransportCoherence.reselectedEdgeLift,
        reselectedPathLift, reselectedEdgeLift]
      exact congrArg
        (fun tailLift =>
          ((source.edgeLift edge).comp
            (PackageFiberAut.hom (reselection _ _ edge))).comp tailLift)
        inductionHypothesis

/-- Native indexed coherence is exactly the adapter's package-level equation. -/
theorem indexedCoherentAt_iff_adaptedCoherentAt
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    source.IndexedCoherentAt reselection ↔
      CoherentAt source.toAdmissibleTransportData reselection := by
  constructor
  · intro coherent cell
    change
      (TransportCoherence.reselectedPathLift source.toAdmissibleLiftData
          reselection (G.twoLeft cell).toPresentedPath).comp
          (PackageFiberAut.hom (source.comparator cell)) =
        TransportCoherence.reselectedPathLift source.toAdmissibleLiftData
          reselection (G.twoRight cell).toPresentedPath
    rw [source.toAdmissibleTransportData_reselectedPathLift reselection,
      source.toAdmissibleTransportData_reselectedPathLift reselection]
    exact coherent cell
  · intro coherent cell
    rw [← source.toAdmissibleTransportData_reselectedPathLift reselection,
      ← source.toAdmissibleTransportData_reselectedPathLift reselection]
    exact coherent cell

end IndexedDiagnosticInterpretation

namespace IndexedBaseDiagramHom

/-- `(d6)`: indexed transport preserves the independent obstruction-orbit vanishing. -/
theorem indexedTransportObstructionVanishes_transport
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (vanishes : TransportObstructionVanishes
      source.toAdmissibleTransportData) :
    TransportObstructionVanishes
      (hom.transportedInterpretation source).toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable] at vanishes ⊢
  rcases vanishes with ⟨reselection, coherent⟩
  have sourceCoherent : source.IndexedCoherentAt reselection :=
    (source.indexedCoherentAt_iff_adaptedCoherentAt reselection).2 coherent
  exact ⟨hom.transportedReselection source reselection,
    (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
      (hom.transportedInterpretation source)
        (hom.transportedReselection source reselection)).1
      (hom.indexedCoherentAt_transport source reselection sourceCoherent)⟩

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
