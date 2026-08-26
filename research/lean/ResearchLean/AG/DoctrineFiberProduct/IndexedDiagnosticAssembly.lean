import ResearchLean.AG.DoctrineFiberProduct.IndexedBaseDiagram
import ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeRaw
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticBaseChangeAutomorphism

/-!
# Coherent indexed diagnostic assembly

This module supplies G-111 K2.  A source diagnostic interpretation is indexed
by a previously fixed diagnostic-free base diagram.  Its authored data is the
source package family, source edge lifts with their local qualification, and
source comparator values.  A previously fixed diagram hom then generates the
target packages, edge lifts, qualifications, comparator values, and the target
declared-cell base equation from the same pointwise indexed action.

No target package, lift, qualification, comparator, reselection, coherence, or
vanishing value is accepted as input.  In particular, packages need not lie in
one common source fiber: every vertex is transported along its own index and
every edge is transported through its generating commutative square.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/--
Ordinary source diagnostic data over a fixed G-111 base diagram.  The base
diagram supplies the declared 2-cell relation; this structure adds only source
packages, locally qualified edge lifts, and authored source comparators.
-/
structure IndexedDiagnosticInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) where
  /-- Source package at every diagnostic vertex. -/
  package : G.Vertex → AATCorePackage U
  /-- Each source package lies over its already fixed diagram vertex. -/
  vertexBase : ∀ vertex, packagePoint (package vertex) = D.vertex vertex
  /-- Source lift of every generating diagnostic edge. -/
  edgeLift : {i j : G.Vertex} → G.Edge i j →
    PackageTotalHom (package i) (package j)
  /-- Each source edge lift lies over the corresponding fixed base edge. -/
  edgeOver : ∀ {i j : G.Vertex} (edge : G.Edge i j),
    (packageProjection U).IsHomLift (D.edge edge) (edgeLift edge)
  /-- The ordinary local strong-cocartesian qualification of each source edge. -/
  edgeStrong : ∀ {i j : G.Vertex} (edge : G.Edge i j),
    (packageProjection U).IsStronglyCocartesian (D.edge edge) (edgeLift edge)
  /-- Authored source comparator at each declared 2-cell endpoint. -/
  comparator : (cell : G.TwoCell) →
    PackageFiberAut (package (G.twoTarget cell))

namespace IndexedDiagnosticInterpretation

/-- Repackage one source vertex as an object of its fixed diagram fiber. -/
def fiberPackage {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (vertex : G.Vertex) : CoreFiber (D.vertex vertex) :=
  ⟨source.package vertex, source.vertexBase vertex⟩

/-- Evaluate the source package lift along a finite base path. -/
def pathLift {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D) :
    {i j : G.Vertex} → IndexedBasePath G.toIndexedBaseShape i j →
      PackageTotalHom (source.package i) (source.package j)
  | _, _, .nil vertex => PackageTotalHom.id (source.package vertex)
  | _, _, .cons edge tail => (source.edgeLift edge).comp (source.pathLift tail)

/-- Source path lifts lie over the path already fixed by the base diagram. -/
theorem pathLift_isHomLift {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D : IndexedBaseDiagram G U}
    (source : IndexedDiagnosticInterpretation D) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (packageProjection U).IsHomLift (D.path path) (source.pathLift path) := by
  induction path with
  | nil vertex =>
      apply CategoryTheory.IsHomLift.of_commsq
        (packageProjection U) (𝟙 (D.vertex vertex))
        (PackageTotalHom.id (source.package vertex))
        (source.vertexBase vertex) (source.vertexBase vertex)
      change (𝟙 _) ≫ eqToHom (source.vertexBase vertex) =
        eqToHom (source.vertexBase vertex) ≫ 𝟙 _
      simp
  | cons edge tail inductionHypothesis =>
      letI : (packageProjection U).IsHomLift
          (D.edge edge) (source.edgeLift edge) := source.edgeOver edge
      letI : (packageProjection U).IsHomLift
          (D.path tail) (source.pathLift tail) := inductionHypothesis
      exact CategoryTheory.IsHomLift.comp
        (p := packageProjection U) (D.edge edge) (D.path tail)
        (source.edgeLift edge) (source.pathLift tail)

/-- The source declared-cell base equation is exactly the fixed diagram relation. -/
theorem twoCellBase {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (cell : G.TwoCell) :
    (source.pathLift (G.twoLeft cell)).base =
      (source.pathLift (G.twoRight cell)).base := by
  let left := source.pathLift (G.twoLeft cell)
  let right := source.pathLift (G.twoRight cell)
  letI : (packageProjection U).IsHomLift
      (D.path (G.twoLeft cell)) left := source.pathLift_isHomLift _
  letI : (packageProjection U).IsHomLift
      (D.path (G.twoRight cell)) right := source.pathLift_isHomLift _
  have leftFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (D.path (G.twoLeft cell)) left
  have rightFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (D.path (G.twoRight cell)) right
  calc
    left.base = eqToHom (source.vertexBase (G.twoSource cell)) ≫
        D.path (G.twoLeft cell) ≫
          eqToHom (source.vertexBase (G.twoTarget cell)).symm := by
      simpa only [packageProjection_map] using leftFac
    _ = eqToHom (source.vertexBase (G.twoSource cell)) ≫
        D.path (G.twoRight cell) ≫
          eqToHom (source.vertexBase (G.twoTarget cell)).symm := by
      rw [D.relation_path cell]
    _ = right.base := by
      simpa only [packageProjection_map] using rightFac.symm

end IndexedDiagnosticInterpretation

namespace IndexedBaseDiagramHom

/-- The validated pointwise index at one vertex of a coherent diagram hom. -/
def vertexIndex {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    ValidatedIndexedBaseHom U (D.vertex vertex) (E.vertex vertex) :=
  .ofTerm (.leaf (hom.app vertex))

/-- The validated generating square used by the K2 edge action. -/
def validatedEdgeSquare {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    {i j : G.Vertex} (edge : G.Edge i j) :
    ValidatedIndexedBaseSquare U (hom.app i) (D.edge edge) (E.edge edge)
      (hom.app j) :=
  .ofTerm (.leaf (hom.naturality edge).symm)

/-- K2 target package generated by the pointwise action at one vertex. -/
noncomputable def transportedPackage {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    AATCorePackage U :=
  ((indexedFiberAction (hom.vertexIndex vertex)).obj
    (source.fiberPackage vertex)).1

/-- The generated target package lies over the fixed target diagram vertex. -/
theorem transportedPackage_vertexBase {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    packagePoint (hom.transportedPackage source vertex) = E.vertex vertex :=
  ((indexedFiberAction (hom.vertexIndex vertex)).obj
    (source.fiberPackage vertex)).2

/-- K2 target edge generated by transporting the source lift through its square. -/
noncomputable def transportedEdgeLift {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j : G.Vertex}
    (edge : G.Edge i j) :
    PackageTotalHom (hom.transportedPackage source i)
      (hom.transportedPackage source j) :=
  indexedSquareTotalMap (hom.validatedEdgeSquare edge)
    (source.fiberPackage i) (source.fiberPackage j)
    (source.edgeLift edge) (source.edgeOver edge)

/-- Every generated K2 target edge lies over the fixed target base edge. -/
theorem transportedEdgeLift_isHomLift {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j : G.Vertex}
    (edge : G.Edge i j) :
    (packageProjection U).IsHomLift (E.edge edge)
      (hom.transportedEdgeLift source edge) :=
  indexedSquareTotalMap_isHomLift (hom.validatedEdgeSquare edge)
    (source.fiberPackage i) (source.fiberPackage j)
    (source.edgeLift edge) (source.edgeOver edge)

/-- Every generated K2 target edge retains the source local qualification. -/
theorem transportedEdgeLift_isStronglyCocartesian
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j : G.Vertex}
    (edge : G.Edge i j) :
    (packageProjection U).IsStronglyCocartesian (E.edge edge)
      (hom.transportedEdgeLift source edge) :=
  indexedSquareTotalMap_isStronglyCocartesian
    (hom.validatedEdgeSquare edge) (source.fiberPackage i)
    (source.fiberPackage j) (source.edgeLift edge) (source.edgeOver edge)
    (source.edgeStrong edge)

/-- Evaluate the generated target lifts along a finite base path. -/
noncomputable def transportedPathLift {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    {i j : G.Vertex} → IndexedBasePath G.toIndexedBaseShape i j →
      PackageTotalHom (hom.transportedPackage source i)
        (hom.transportedPackage source j)
  | _, _, .nil vertex => PackageTotalHom.id (hom.transportedPackage source vertex)
  | _, _, .cons edge tail =>
      (hom.transportedEdgeLift source edge).comp
        (hom.transportedPathLift source tail)

/-- Generated target path lifts lie over the target diagram path. -/
theorem transportedPathLift_isHomLift {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (packageProjection U).IsHomLift (E.path path)
      (hom.transportedPathLift source path) := by
  induction path with
  | nil vertex =>
      apply CategoryTheory.IsHomLift.of_commsq
        (packageProjection U) (𝟙 (E.vertex vertex))
        (PackageTotalHom.id (hom.transportedPackage source vertex))
        (hom.transportedPackage_vertexBase source vertex)
        (hom.transportedPackage_vertexBase source vertex)
      change (𝟙 _) ≫ eqToHom (hom.transportedPackage_vertexBase source vertex) =
        eqToHom (hom.transportedPackage_vertexBase source vertex) ≫ 𝟙 _
      simp
  | cons edge tail inductionHypothesis =>
      letI : (packageProjection U).IsHomLift
          (E.edge edge) (hom.transportedEdgeLift source edge) :=
        hom.transportedEdgeLift_isHomLift source edge
      letI : (packageProjection U).IsHomLift
          (E.path tail) (hom.transportedPathLift source tail) :=
        inductionHypothesis
      exact CategoryTheory.IsHomLift.comp
        (p := packageProjection U) (E.edge edge) (E.path tail)
        (hom.transportedEdgeLift source edge)
        (hom.transportedPathLift source tail)

/--
The K2 target declared-cell equation is canonically realized from the target
diagram relation.  It is not generated from an arbitrary raw square family.
-/
theorem transportedTwoCellBase {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (cell : G.TwoCell) :
    (hom.transportedPathLift source (G.twoLeft cell)).base =
      (hom.transportedPathLift source (G.twoRight cell)).base := by
  let left := hom.transportedPathLift source (G.twoLeft cell)
  let right := hom.transportedPathLift source (G.twoRight cell)
  letI : (packageProjection U).IsHomLift
      (E.path (G.twoLeft cell)) left := hom.transportedPathLift_isHomLift source _
  letI : (packageProjection U).IsHomLift
      (E.path (G.twoRight cell)) right := hom.transportedPathLift_isHomLift source _
  have leftFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (E.path (G.twoLeft cell)) left
  have rightFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (E.path (G.twoRight cell)) right
  calc
    left.base = eqToHom
          (hom.transportedPackage_vertexBase source (G.twoSource cell)) ≫
        E.path (G.twoLeft cell) ≫
          eqToHom
            (hom.transportedPackage_vertexBase source (G.twoTarget cell)).symm := by
      simpa only [packageProjection_map] using leftFac
    _ = eqToHom
          (hom.transportedPackage_vertexBase source (G.twoSource cell)) ≫
        E.path (G.twoRight cell) ≫
          eqToHom
            (hom.transportedPackage_vertexBase source (G.twoTarget cell)).symm := by
      rw [E.relation_path cell]
    _ = right.base := by
      simpa only [packageProjection_map] using rightFac.symm

/-- K2 target comparator generated by the vertex action at the cell endpoint. -/
noncomputable def transportedComparator {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (cell : G.TwoCell) :
    PackageFiberAut (hom.transportedPackage source (G.twoTarget cell)) :=
  coreFiberFunctorPackageAutHom
    (indexedFiberAction (hom.vertexIndex (G.twoTarget cell)))
    (source.fiberPackage (G.twoTarget cell)) (source.comparator cell)

/-- The K2 target comparator is definitionally the generated endpoint action. -/
@[simp]
theorem transportedComparator_eq {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {D E : IndexedBaseDiagram G U}
    (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (cell : G.TwoCell) :
    hom.transportedComparator source cell =
      coreFiberFunctorPackageAutHom
        (indexedFiberAction (hom.vertexIndex (G.twoTarget cell)))
        (source.fiberPackage (G.twoTarget cell)) (source.comparator cell) := rfl

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
