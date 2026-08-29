import ResearchLean.AG.DoctrineFiberProduct.UpperRefinementBCGeometry
import ResearchLean.AG.CrossStageCoherence.UpperObstruction

/-!
# Finite upper refinement base-change problems

This module supplies the raw finite problem interface used by G-115.  The
source core data form an actual functor from the free path category of a finite
presentation into one `CoreFiber`.  Source, base-route, and pulled-route
geometry data are separately qualified G-109 data with one fixed coefficient
ring.

Only route-internal geometry naturality is stored.  No route-between component,
factorization triangle, comparator equation, invertibility statement, orbit
law, or non-liftability certificate belongs to the raw problem.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

/-- A vertex of a presentation, wrapped to retain the presentation parameter. -/
structure PresentedPathObject (P : FiniteTransportPresentation.{u}) where
  /-- The underlying vertex. -/
  vertex : P.Vertex

/-- The free category whose morphisms are finite presented paths. -/
abbrev PresentedPathCategory (P : FiniteTransportPresentation.{u}) :=
  PresentedPathObject P

noncomputable instance presentedPathCategory
    (P : FiniteTransportPresentation.{u}) :
    Category.{u} (PresentedPathCategory P) where
  Hom i j := P.Path i.vertex j.vertex
  id i := .nil i.vertex
  comp first second := first.append second
  id_comp := by
    intro _ _ path
    rfl
  comp_id := by
    intro _ _ path
    exact PresentedPath.append_nil path
  assoc := by
    intro _ _ _ _ first second third
    exact PresentedPath.append_assoc first second third

/-- Regard one generator as a morphism in the free path category. -/
def presentedEdgePath {P : FiniteTransportPresentation.{u}}
    {i j : P.Vertex} (edge : P.Edge i j) :
    (⟨i⟩ : PresentedPathCategory P) ⟶ ⟨j⟩ :=
  .cons edge (.nil j)

/--
Fixed-coefficient G-109 transport data over an actual core-fiber diagram.

The geometry object at each vertex has the diagram object's core definitionally.
The one non-definitional projection datum states that each geometry edge forgets
to the corresponding actual fiber morphism.
-/
structure FixedCoefficientTwoLayerTransportOver
    (P : FiniteTransportPresentation.{u})
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (diagram : PresentedPathCategory P ⥤ CoreFiber X)
    (k : Type v) [CommRing k]
    (geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k) where
  /-- Qualified geometry lift on every generator. -/
  edgeLift : {i j : P.Vertex} → (edge : P.Edge i j) →
    GeometryTotalHom (geometry i).package (geometry j).package
  /-- Every geometry edge projects to the actual core-fiber diagram edge. -/
  edge_base : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (edgeLift edge).base = (diagram.map (presentedEdgePath edge)).1
  /-- Independent geometry-stage cocartesian qualification. -/
  edgeGeometryStrong : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (geometryProjection U).IsStronglyCocartesian
      (edgeLift edge).base (edgeLift edge)
  /-- Independent core-stage cocartesian qualification. -/
  edgeCoreStrong : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (packageProjection U).IsStronglyCocartesian
      (edgeLift edge).base.base (edgeLift edge).base
  /-- Parallel paths agree after the composite projection. -/
  twoCellBase : ∀ cell : P.TwoCell,
    ((TwoLayerLiftData.pathLift {
      geometry := fun i => (geometry i).package
      edgeLift := edgeLift
      edgeGeometryStrong := edgeGeometryStrong
      edgeCoreStrong := edgeCoreStrong
    } (P.twoLeft cell)).base.base) =
    ((TwoLayerLiftData.pathLift {
      geometry := fun i => (geometry i).package
      edgeLift := edgeLift
      edgeGeometryStrong := edgeGeometryStrong
      edgeCoreStrong := edgeCoreStrong
    } (P.twoRight cell)).base.base)
  /-- Authored G-109 comparator internal to this route. -/
  comparator : (cell : P.TwoCell) →
    CompositeFiberAut ((geometry (P.twoTarget cell)).package)
  /-- Every edge fixes the coefficient ring pointwise. -/
  edge_coefficient_id : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (edgeLift edge).geometry.coefficientHom = RingHom.id k
  /-- Every authored comparator fixes the coefficient ring pointwise. -/
  comparator_coefficient_id : ∀ cell : P.TwoCell,
    (CompositeFiberAut.hom (comparator cell)).geometry.coefficientHom =
      RingHom.id k

namespace FixedCoefficientTwoLayerTransportOver

/-- Forget the fixed diagram and coefficient evidence to obtain G-109 lift data. -/
noncomputable def toTwoLayerLiftData
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry) :
    TwoLayerLiftData.{u, v} P U where
  geometry i := (geometry i).package
  edgeLift := data.edgeLift
  edgeGeometryStrong := data.edgeGeometryStrong
  edgeCoreStrong := data.edgeCoreStrong

/-- Forget only the extra projection and coefficient evidence. -/
noncomputable def toTwoLayerTransportData
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry) :
    TwoLayerTransportData.{u, v} P U where
  lift := data.toTwoLayerLiftData
  twoCellBase := data.twoCellBase
  comparator := data.comparator

/-- The resulting G-109 edge is the stored qualified geometry edge. -/
@[simp] theorem toTwoLayerTransportData_edgeLift
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry)
    {i j : P.Vertex} (edge : P.Edge i j) :
    data.toTwoLayerTransportData.lift.edgeLift edge = data.edgeLift edge := rfl

/-- The stored edge projects to the actual source-fiber diagram morphism. -/
theorem edge_projection
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    (data : FixedCoefficientTwoLayerTransportOver P diagram k geometry)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (data.toTwoLayerTransportData.lift.edgeLift edge).base =
      (diagram.map (presentedEdgePath edge)).1 :=
  data.edge_base edge

end FixedCoefficientTwoLayerTransportOver

/-- Core diagram obtained along the base reverse route and G-112 reindexing. -/
noncomputable def ActiveRefinementBCContext.baseCoreDiagram
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    {P : FiniteTransportPresentation.{u}}
    (source : PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.targetPointAt ctx.source)) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) :=
  source ⋙ (ctx.legacyRegime).reverseBase ⋙
    exact_bottom_semantic_global_reindex_functor
      (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst

/-- Core diagram obtained along G-112 reindexing and the pulled reverse route. -/
noncomputable def ActiveRefinementBCContext.pulledCoreDiagram
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    {P : FiniteTransportPresentation.{u}}
    (source : PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.targetPointAt ctx.source)) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) :=
  source ⋙ exact_bottom_semantic_global_reindex_functor
      (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst ⋙
    (ctx.legacyRegime).reversePullback

/--
The raw finite upper problem over one active refinement context and coefficient
ring.  The three G-109 data sets are indexed by actual core-fiber diagrams.
-/
structure UpperRefinementBCProblemData
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (P : FiniteTransportPresentation.{u}) (k : CommRingCat.{v}) where
  /-- Chosen root vertex. -/
  root : P.Vertex
  /-- Every vertex is reached by a directed path from the root. -/
  rootPath : (i : P.Vertex) → P.Path root i
  /-- Actual source diagram in the selected target core fiber. -/
  sourceFiberDiagram : PresentedPathCategory P ⥤
    CoreFiber (ctx.configuration.targetPointAt ctx.source)
  /-- Individual actual-route geometry legs at every source package. -/
  legData : (i : P.Vertex) → ActiveRefinementBCGeometryLegData ctx
    (sourceFiberDiagram.obj ⟨i⟩) k
  /-- Qualified common-source G-109 data with vertical core projection. -/
  sourceTransport : FixedCoefficientTwoLayerTransportOver P
    sourceFiberDiagram k (fun i => (legData i).commonTarget)
  /-- Qualified G-109 data on the base reverse route. -/
  baseTransport : FixedCoefficientTwoLayerTransportOver P
    (ctx.baseCoreDiagram sourceFiberDiagram) k
    (fun i => (legData i).baseSource)
  /-- Qualified G-109 data on the pulled reverse route. -/
  pulledTransport : FixedCoefficientTwoLayerTransportOver P
    (ctx.pulledCoreDiagram sourceFiberDiagram) k
    (fun i => (legData i).pulledSource)
  /-- Full geometry naturality internal to the base route. -/
  base_naturality : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (baseTransport.edgeLift edge))
        (legData j).baseLeg =
      RefinementGeometryHom.comp (legData i).baseLeg
        ((exactGeometryToRefinementGeometry U).map
          (sourceTransport.edgeLift edge))
  /-- Full geometry naturality internal to the pulled route. -/
  pulled_naturality : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (pulledTransport.edgeLift edge))
        (legData j).pulledLeg =
      RefinementGeometryHom.comp (legData i).pulledLeg
        ((exactGeometryToRefinementGeometry U).map
          (sourceTransport.edgeLift edge))

/-- A finite upper problem packages its finite presentation and one coefficient ring. -/
structure UpperRefinementBCProblem
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) where
  /-- Finite 0/1/2/3-cell presentation. -/
  presentation : FiniteTransportPresentation.{u}
  /-- The single coefficient ring used by every object, edge, leg, and comparator. -/
  coefficient : CommRingCat.{v}
  /-- Raw problem data over the fixed presentation and coefficient ring. -/
  data : UpperRefinementBCProblemData ctx presentation coefficient

namespace UpperRefinementBCProblemData

/-- Common-source G-109 transport data extracted from the raw problem. -/
noncomputable def sourceData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
    TwoLayerTransportData.{u, v} P U :=
  problem.sourceTransport.toTwoLayerTransportData

/-- Base-route G-109 transport data extracted from the raw problem. -/
noncomputable def baseData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
    TwoLayerTransportData.{u, v} P U :=
  problem.baseTransport.toTwoLayerTransportData

/-- Pulled-route G-109 transport data extracted from the raw problem. -/
noncomputable def pulledData
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
    TwoLayerTransportData.{u, v} P U :=
  problem.pulledTransport.toTwoLayerTransportData

/-- Base-route full naturality projects to the actual package routes. -/
theorem base_naturality_projection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    ((exactPackageToRefinement U).map
        (problem.baseTransport.edgeLift edge).base).comp
        (ctx.baseCompositeLegAt (problem.sourceFiberDiagram.obj ⟨j⟩)) =
      (ctx.baseCompositeLegAt (problem.sourceFiberDiagram.obj ⟨i⟩)).comp
        ((exactPackageToRefinement U).map
          (problem.sourceTransport.edgeLift edge).base) := by
  exact congrArg RefinementGeometryHom.base
    (problem.base_naturality edge)

/-- Pulled-route full naturality projects to the actual package routes. -/
theorem pulled_naturality_projection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    ((exactPackageToRefinement U).map
        (problem.pulledTransport.edgeLift edge).base).comp
        (ctx.pulledCompositeLegAt (problem.sourceFiberDiagram.obj ⟨j⟩)) =
      (ctx.pulledCompositeLegAt (problem.sourceFiberDiagram.obj ⟨i⟩)).comp
        ((exactPackageToRefinement U).map
          (problem.sourceTransport.edgeLift edge).base) := by
  exact congrArg RefinementGeometryHom.base
    (problem.pulled_naturality edge)

/-- Generator naturality extends to every path on the base route. -/
theorem base_path_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.baseData.lift.pathLift path))
        (problem.legData j).baseLeg =
      RefinementGeometryHom.comp (problem.legData i).baseLeg
        ((exactGeometryToRefinementGeometry U).map
          (problem.sourceData.lift.pathLift path)) := by
  induction path with
  | nil vertex =>
      change (𝟙 (⟨(problem.legData vertex).baseSource.package⟩ :
          RefinementGeometryCategory U)) ≫ (problem.legData vertex).baseLeg =
        (problem.legData vertex).baseLeg ≫
          𝟙 (⟨(problem.legData vertex).commonTarget.package⟩ :
            RefinementGeometryCategory U)
      rw [Category.id_comp, Category.comp_id]
  | cons edge tail inductionHypothesis =>
      change (((exactGeometryToRefinementGeometry U).map
          (problem.baseTransport.edgeLift edge)) ≫
          ((exactGeometryToRefinementGeometry U).map
            (problem.baseData.lift.pathLift tail))) ≫
          (problem.legData _).baseLeg =
        (problem.legData _).baseLeg ≫
          (((exactGeometryToRefinementGeometry U).map
            (problem.sourceTransport.edgeLift edge)) ≫
            ((exactGeometryToRefinementGeometry U).map
              (problem.sourceData.lift.pathLift tail)))
      calc
        _ = ((exactGeometryToRefinementGeometry U).map
              (problem.baseTransport.edgeLift edge)) ≫
            (((exactGeometryToRefinementGeometry U).map
              (problem.baseData.lift.pathLift tail)) ≫
              (problem.legData _).baseLeg) := Category.assoc _ _ _
        _ = ((exactGeometryToRefinementGeometry U).map
              (problem.baseTransport.edgeLift edge)) ≫
            ((problem.legData _).baseLeg ≫
              ((exactGeometryToRefinementGeometry U).map
                (problem.sourceData.lift.pathLift tail))) :=
          congrArg _ inductionHypothesis
        _ = (((exactGeometryToRefinementGeometry U).map
              (problem.baseTransport.edgeLift edge)) ≫
              (problem.legData _).baseLeg) ≫
            ((exactGeometryToRefinementGeometry U).map
              (problem.sourceData.lift.pathLift tail)) :=
          (Category.assoc _ _ _).symm
        _ = ((problem.legData _).baseLeg ≫
              ((exactGeometryToRefinementGeometry U).map
                (problem.sourceTransport.edgeLift edge))) ≫
            ((exactGeometryToRefinementGeometry U).map
              (problem.sourceData.lift.pathLift tail)) :=
          congrArg (fun hom => hom ≫
            ((exactGeometryToRefinementGeometry U).map
              (problem.sourceData.lift.pathLift tail)))
            (problem.base_naturality edge)
        _ = _ := Category.assoc _ _ _

/-- Generator naturality extends to every path on the pulled route. -/
theorem pulled_path_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.pulledData.lift.pathLift path))
        (problem.legData j).pulledLeg =
      RefinementGeometryHom.comp (problem.legData i).pulledLeg
        ((exactGeometryToRefinementGeometry U).map
          (problem.sourceData.lift.pathLift path)) := by
  induction path with
  | nil vertex =>
      change (𝟙 (⟨(problem.legData vertex).pulledSource.package⟩ :
          RefinementGeometryCategory U)) ≫ (problem.legData vertex).pulledLeg =
        (problem.legData vertex).pulledLeg ≫
          𝟙 (⟨(problem.legData vertex).commonTarget.package⟩ :
            RefinementGeometryCategory U)
      rw [Category.id_comp, Category.comp_id]
  | cons edge tail inductionHypothesis =>
      change (((exactGeometryToRefinementGeometry U).map
          (problem.pulledTransport.edgeLift edge)) ≫
          ((exactGeometryToRefinementGeometry U).map
            (problem.pulledData.lift.pathLift tail))) ≫
          (problem.legData _).pulledLeg =
        (problem.legData _).pulledLeg ≫
          (((exactGeometryToRefinementGeometry U).map
            (problem.sourceTransport.edgeLift edge)) ≫
            ((exactGeometryToRefinementGeometry U).map
              (problem.sourceData.lift.pathLift tail)))
      calc
        _ = ((exactGeometryToRefinementGeometry U).map
              (problem.pulledTransport.edgeLift edge)) ≫
            (((exactGeometryToRefinementGeometry U).map
              (problem.pulledData.lift.pathLift tail)) ≫
              (problem.legData _).pulledLeg) := Category.assoc _ _ _
        _ = ((exactGeometryToRefinementGeometry U).map
              (problem.pulledTransport.edgeLift edge)) ≫
            ((problem.legData _).pulledLeg ≫
              ((exactGeometryToRefinementGeometry U).map
                (problem.sourceData.lift.pathLift tail))) :=
          congrArg _ inductionHypothesis
        _ = (((exactGeometryToRefinementGeometry U).map
              (problem.pulledTransport.edgeLift edge)) ≫
              (problem.legData _).pulledLeg) ≫
            ((exactGeometryToRefinementGeometry U).map
              (problem.sourceData.lift.pathLift tail)) :=
          (Category.assoc _ _ _).symm
        _ = ((problem.legData _).pulledLeg ≫
              ((exactGeometryToRefinementGeometry U).map
                (problem.sourceTransport.edgeLift edge))) ≫
            ((exactGeometryToRefinementGeometry U).map
              (problem.sourceData.lift.pathLift tail)) :=
          congrArg (fun hom => hom ≫
            ((exactGeometryToRefinementGeometry U).map
              (problem.sourceData.lift.pathLift tail)))
            (problem.pulled_naturality edge)
        _ = _ := Category.assoc _ _ _

end UpperRefinementBCProblemData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
