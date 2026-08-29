import ResearchLean.AG.DoctrineFiberProduct.UpperRefinementBCProblem

/-!
# Actual solutions of finite upper refinement base-change problems

This module first reconstructs the package projections of the two route-internal
naturality equations from the G-112 reindexing factor graph and the G-114
reverse-map factor graph.  The proof does not use the raw geometry naturality
fields.

It then fixes the actual route-between solution contract.  Components,
factorization triangles, edge naturality, and authored-comparator intertwining
belong to the solution, never to the raw problem.  Nil, path, append, and
authored two-cell pasting equations are derived separately.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

/-! ## Exact vertical composition and relative refinement lifts -/

/-- Exact vertical precomposition agrees with relative precomposition. -/
theorem refinementPackageHomOfOver_precomp
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    {f : PointedRefinementHom X Y}
    {first second : CoreFiber X} {target : CoreFiber Y}
    (vertical : first ⟶ second) (hom : RefinementOverHom f second target) :
    ((exactPackageToRefinement U).map vertical.1).comp
        (refinementPackageHomOfOver hom) =
      refinementPackageHomOfOver (RefinementOverHom.precomp vertical hom) := by
  apply RefinementPackageHom.ext
  · dsimp [RefinementPackageHom.comp, refinementPackageHomOfOver]
    letI : (refinementPackageProjection U).IsHomLift
        (PointedRefinementHom.id X)
        ((exactPackageToRefinement U).map vertical.1) :=
      exactVerticalComparison_isHomLift vertical
    have hfac := CategoryTheory.IsHomLift.fac'
      (refinementPackageProjection U) (PointedRefinementHom.id X)
      ((exactPackageToRefinement U).map vertical.1)
    change
      ((refinementPackageProjection U).map
          ((exactPackageToRefinement U).map vertical.1)) ≫
          (exactPointedToRefinement U).map (eqToHom second.2) ≫
          hom.lower ≫
          (exactPointedToRefinement U).map (eqToHom target.2.symm) =
        (exactPointedToRefinement U).map (eqToHom first.2) ≫
          hom.lower ≫
          (exactPointedToRefinement U).map (eqToHom target.2.symm)
    rw [hfac, exactPointedToRefinement_map_eqToHom,
      exactPointedToRefinement_map_eqToHom,
      exactPointedToRefinement_map_eqToHom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl
  · rfl

/-- Exact vertical postcomposition agrees with relative postcomposition. -/
theorem refinementPackageHomOfOver_postcomp
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {first second : CoreFiber Y}
    (hom : RefinementOverHom f source first) (vertical : first ⟶ second) :
    (refinementPackageHomOfOver hom).comp
        ((exactPackageToRefinement U).map vertical.1) =
      refinementPackageHomOfOver (RefinementOverHom.postcomp hom vertical) := by
  apply RefinementPackageHom.ext
  · dsimp [RefinementPackageHom.comp, refinementPackageHomOfOver]
    letI : (refinementPackageProjection U).IsHomLift
        (PointedRefinementHom.id Y)
        ((exactPackageToRefinement U).map vertical.1) :=
      exactVerticalComparison_isHomLift vertical
    have hfac := CategoryTheory.IsHomLift.fac'
      (refinementPackageProjection U) (PointedRefinementHom.id Y)
      ((exactPackageToRefinement U).map vertical.1)
    change
      (exactPointedToRefinement U).map (eqToHom source.2) ≫
          hom.lower ≫
          (exactPointedToRefinement U).map (eqToHom first.2.symm) ≫
          ((refinementPackageProjection U).map
            ((exactPackageToRefinement U).map vertical.1)) =
        (exactPointedToRefinement U).map (eqToHom source.2) ≫
          hom.lower ≫
          (exactPointedToRefinement U).map (eqToHom second.2.symm)
    rw [hfac, exactPointedToRefinement_map_eqToHom,
      exactPointedToRefinement_map_eqToHom,
      exactPointedToRefinement_map_eqToHom]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl
  · rfl

/-! ## Full package factor graphs for the two routes -/

/-- Naturality of the base composite route from the two predecessor factor graphs. -/
theorem ActiveRefinementBCContext.baseCompositeLegAt_naturality
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    {first second : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    (vertical : first ⟶ second) :
    ((exactPackageToRefinement U).map
        ((exact_bottom_semantic_global_reindex_functor
          (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst).map
            ((ctx.legacyRegime).reverseBase.map vertical)).1).comp
        (ctx.baseCompositeLegAt second) =
      (ctx.baseCompositeLegAt first).comp
        ((exactPackageToRefinement U).map vertical.1) := by
  have hexact := congrArg (fun hom =>
      (exactPackageToRefinement U).map hom)
    (exact_bottom_semantic_global_reindex_map_fac
      (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
      ((ctx.legacyRegime).reverseBase.map vertical))
  simp only [Functor.map_comp] at hexact
  have hrefine :
      ((exactPackageToRefinement U).map
          ((ctx.legacyRegime).reverseBase.map vertical).1).comp
          (refinementPackageHomOfOver
            ((ctx.legacyRegime).baseCleavage.lift second).hom) =
        (refinementPackageHomOfOver
          ((ctx.legacyRegime).baseCleavage.lift first).hom).comp
          ((exactPackageToRefinement U).map vertical.1) := by
    change
      ((exactPackageToRefinement U).map
          ((ctx.legacyRegime).baseCleavage.reverseMap vertical).1).comp
          (refinementPackageHomOfOver
            ((ctx.legacyRegime).baseCleavage.lift second).hom) =
        (refinementPackageHomOfOver
          ((ctx.legacyRegime).baseCleavage.lift first).hom).comp
          ((exactPackageToRefinement U).map vertical.1)
    rw [refinementPackageHomOfOver_precomp,
      refinementPackageHomOfOver_postcomp,
      (ctx.legacyRegime).baseCleavage.reverseMap_fac vertical]
  let routeMap := (exactPackageToRefinement U).map
    ((exact_bottom_semantic_global_reindex_functor
      (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst).map
        ((ctx.legacyRegime).reverseBase.map vertical)).1
  let liftFirst := (exactPackageToRefinement U).map
    (exact_bottom_semantic_global_selected_lift
      (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
      ((ctx.legacyRegime).reverseBase.obj first)).hom
  let liftSecond := (exactPackageToRefinement U).map
    (exact_bottom_semantic_global_selected_lift
      (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
      ((ctx.legacyRegime).reverseBase.obj second)).hom
  let reverseMap := (exactPackageToRefinement U).map
    ((ctx.legacyRegime).reverseBase.map vertical).1
  let baseFirst := refinementPackageHomOfOver
    ((ctx.legacyRegime).baseCleavage.lift first).hom
  let baseSecond := refinementPackageHomOfOver
    ((ctx.legacyRegime).baseCleavage.lift second).hom
  let sourceMap := (exactPackageToRefinement U).map vertical.1
  change routeMap ≫ (liftSecond ≫ baseSecond) =
    (liftFirst ≫ baseFirst) ≫ sourceMap
  change routeMap ≫ liftSecond = liftFirst ≫ reverseMap at hexact
  change reverseMap ≫ baseSecond = baseFirst ≫ sourceMap at hrefine
  calc
    _ = (routeMap ≫ liftSecond) ≫ baseSecond :=
      (Category.assoc _ _ _).symm
    _ = (liftFirst ≫ reverseMap) ≫ baseSecond :=
      congrArg (fun hom => hom ≫ baseSecond) hexact
    _ = liftFirst ≫ (reverseMap ≫ baseSecond) := Category.assoc _ _ _
    _ = liftFirst ≫ (baseFirst ≫ sourceMap) :=
      congrArg (fun hom => liftFirst ≫ hom) hrefine
    _ = _ := (Category.assoc _ _ _).symm

/-- Naturality of the pulled composite route from the two predecessor factor graphs. -/
theorem ActiveRefinementBCContext.pulledCompositeLegAt_naturality
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    {first second : CoreFiber
      (ctx.configuration.targetPointAt ctx.source)}
    (vertical : first ⟶ second) :
    ((exactPackageToRefinement U).map
        ((ctx.legacyRegime).reversePullback.map
          ((exact_bottom_semantic_global_reindex_functor
            (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst).map
              vertical)).1).comp
        (ctx.pulledCompositeLegAt second) =
      (ctx.pulledCompositeLegAt first).comp
        ((exactPackageToRefinement U).map vertical.1) := by
  let pullMap :=
    (exact_bottom_semantic_global_reindex_functor
      (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst).map
        vertical
  have hrefine :
      ((exactPackageToRefinement U).map
          ((ctx.legacyRegime).reversePullback.map pullMap).1).comp
          (refinementPackageHomOfOver
            ((ctx.legacyRegime).pulledCleavage.lift
              ((exact_bottom_semantic_global_reindex_functor
                (ctx.configuration.pointedConfigurationAt
                  ctx.source).pullbackFst).obj second)).hom) =
        (refinementPackageHomOfOver
          ((ctx.legacyRegime).pulledCleavage.lift
            ((exact_bottom_semantic_global_reindex_functor
              (ctx.configuration.pointedConfigurationAt
                ctx.source).pullbackFst).obj first)).hom).comp
          ((exactPackageToRefinement U).map pullMap.1) := by
    change
      ((exactPackageToRefinement U).map
          ((ctx.legacyRegime).pulledCleavage.reverseMap pullMap).1).comp
          (refinementPackageHomOfOver
            ((ctx.legacyRegime).pulledCleavage.lift
              ((exact_bottom_semantic_global_reindex_functor
                (ctx.configuration.pointedConfigurationAt
                  ctx.source).pullbackFst).obj second)).hom) =
        (refinementPackageHomOfOver
          ((ctx.legacyRegime).pulledCleavage.lift
            ((exact_bottom_semantic_global_reindex_functor
              (ctx.configuration.pointedConfigurationAt
                ctx.source).pullbackFst).obj first)).hom).comp
          ((exactPackageToRefinement U).map pullMap.1)
    rw [refinementPackageHomOfOver_precomp,
      refinementPackageHomOfOver_postcomp,
      (ctx.legacyRegime).pulledCleavage.reverseMap_fac pullMap]
  have hexact := congrArg (fun hom =>
      (exactPackageToRefinement U).map hom)
    (exact_bottom_semantic_global_reindex_map_fac
      (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
      vertical)
  simp only [Functor.map_comp] at hexact
  let routeMap := (exactPackageToRefinement U).map
    ((ctx.legacyRegime).reversePullback.map pullMap).1
  let pulledFirst := refinementPackageHomOfOver
    ((ctx.legacyRegime).pulledCleavage.lift
      ((exact_bottom_semantic_global_reindex_functor
        (ctx.configuration.pointedConfigurationAt
          ctx.source).pullbackFst).obj first)).hom
  let pulledSecond := refinementPackageHomOfOver
    ((ctx.legacyRegime).pulledCleavage.lift
      ((exact_bottom_semantic_global_reindex_functor
        (ctx.configuration.pointedConfigurationAt
          ctx.source).pullbackFst).obj second)).hom
  let exactMap := (exactPackageToRefinement U).map pullMap.1
  let liftFirst := (exactPackageToRefinement U).map
    (exact_bottom_semantic_global_selected_lift
      (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
      first).hom
  let liftSecond := (exactPackageToRefinement U).map
    (exact_bottom_semantic_global_selected_lift
      (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
      second).hom
  let sourceMap := (exactPackageToRefinement U).map vertical.1
  change routeMap ≫ (pulledSecond ≫ liftSecond) =
    (pulledFirst ≫ liftFirst) ≫ sourceMap
  change routeMap ≫ pulledSecond = pulledFirst ≫ exactMap at hrefine
  change exactMap ≫ liftSecond = liftFirst ≫ sourceMap at hexact
  calc
    _ = (routeMap ≫ pulledSecond) ≫ liftSecond :=
      (Category.assoc _ _ _).symm
    _ = (pulledFirst ≫ exactMap) ≫ liftSecond :=
      congrArg (fun hom => hom ≫ liftSecond) hrefine
    _ = pulledFirst ≫ (exactMap ≫ liftSecond) := Category.assoc _ _ _
    _ = pulledFirst ≫ (liftFirst ≫ sourceMap) :=
      congrArg (fun hom => pulledFirst ≫ hom) hexact
    _ = _ := (Category.assoc _ _ _).symm

namespace UpperRefinementBCProblemData

/-- The stored base-route package projection is the predecessor factor graph. -/
theorem base_naturality_factor_graph
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
  rw [problem.baseTransport.edge_base, problem.sourceTransport.edge_base]
  simpa [ActiveRefinementBCContext.baseCoreDiagram] using
    ctx.baseCompositeLegAt_naturality
      (problem.sourceFiberDiagram.map (presentedEdgePath edge))

/-- The stored pulled-route package projection is the predecessor factor graph. -/
theorem pulled_naturality_factor_graph
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
  rw [problem.pulledTransport.edge_base, problem.sourceTransport.edge_base]
  simpa [ActiveRefinementBCContext.pulledCoreDiagram] using
    ctx.pulledCompositeLegAt_naturality
      (problem.sourceFiberDiagram.map (presentedEdgePath edge))

end UpperRefinementBCProblemData

/-! ## Actual route-between solutions -/

/--
An actual solution of one finite upper refinement base-change problem.

The structure contains no invertibility, orbit, or non-liftability field.
-/
structure UpperRefinementBCSolution
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    (problem : UpperRefinementBCProblem.{u, v} ctx) where
  /-- Vertical geometry component between the two actual route objects. -/
  component : (i : problem.presentation.Vertex) →
    GeometryTotalHom
      (problem.data.legData i).baseSource.package
      (problem.data.legData i).pulledSource.package
  /-- The component projects to the canonical G-114 mate. -/
  component_base : ∀ i,
    (component i).base =
      (ctx.mate.app
        (problem.data.sourceFiberDiagram.obj
          (⟨i⟩ : PresentedPathCategory problem.presentation))).1
  /-- Every component fixes the common coefficient ring pointwise. -/
  component_coefficient_id : ∀ i,
    (component i).geometry.coefficientHom = RingHom.id problem.coefficient
  /-- Full geometry factorization triangle at every vertex. -/
  triangle : ∀ i,
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map (component i))
        (problem.data.legData i).pulledLeg =
      (problem.data.legData i).baseLeg
  /-- Route-between naturality on every generator. -/
  edge_naturality : ∀ {i j : problem.presentation.Vertex}
      (edge : problem.presentation.Edge i j),
    (problem.data.baseTransport.edgeLift edge).comp (component j) =
      (component i).comp (problem.data.pulledTransport.edgeLift edge)
  /-- The route-between components intertwine the authored G-109 comparators. -/
  comparator_intertwining : ∀ cell : problem.presentation.TwoCell,
    (CompositeFiberAut.hom
      (problem.data.baseTransport.comparator cell)).comp
        (component (problem.presentation.twoTarget cell)) =
      (component (problem.presentation.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (problem.data.pulledTransport.comparator cell))

namespace UpperRefinementBCSolution

/-- Route-between naturality on the empty path. -/
theorem nil_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {problem : UpperRefinementBCProblem.{u, v} ctx}
    (solution : UpperRefinementBCSolution problem)
    (i : problem.presentation.Vertex) :
    (problem.data.baseData.lift.pathLift (.nil i)).comp
        (solution.component i) =
      (solution.component i).comp
        (problem.data.pulledData.lift.pathLift (.nil i)) := by
  change (GeometryTotalHom.id
      (problem.data.legData i).baseSource.package).comp
      (solution.component i) =
    (solution.component i).comp (GeometryTotalHom.id
      (problem.data.legData i).pulledSource.package)
  exact (@Category.id_comp
    (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
    _ _ (solution.component i)).trans
      (@Category.comp_id
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (solution.component i)).symm

/-- Generator naturality extends to every finite path. -/
theorem path_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {problem : UpperRefinementBCProblem.{u, v} ctx}
    (solution : UpperRefinementBCSolution problem)
    {i j : problem.presentation.Vertex}
    (path : problem.presentation.Path i j) :
    (problem.data.baseData.lift.pathLift path).comp
        (solution.component j) =
      (solution.component i).comp
        (problem.data.pulledData.lift.pathLift path) := by
  induction path with
  | nil vertex => exact solution.nil_naturality vertex
  | cons edge tail inductionHypothesis =>
      change ((problem.data.baseTransport.edgeLift edge).comp
          (problem.data.baseData.lift.pathLift tail)).comp
          (solution.component _) =
        (solution.component _).comp
          ((problem.data.pulledTransport.edgeLift edge).comp
            (problem.data.pulledData.lift.pathLift tail))
      calc
        _ = (problem.data.baseTransport.edgeLift edge).comp
            ((problem.data.baseData.lift.pathLift tail).comp
              (solution.component _)) := @Category.assoc
          (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ _ _ (problem.data.baseTransport.edgeLift edge)
          (problem.data.baseData.lift.pathLift tail)
          (solution.component _)
        _ = (problem.data.baseTransport.edgeLift edge).comp
            ((solution.component _).comp
              (problem.data.pulledData.lift.pathLift tail)) :=
          congrArg _ inductionHypothesis
        _ = ((problem.data.baseTransport.edgeLift edge).comp
              (solution.component _)).comp
            (problem.data.pulledData.lift.pathLift tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (problem.data.baseTransport.edgeLift edge)
            (solution.component _)
            (problem.data.pulledData.lift.pathLift tail)).symm
        _ = ((solution.component _).comp
              (problem.data.pulledTransport.edgeLift edge)).comp
            (problem.data.pulledData.lift.pathLift tail) :=
          congrArg (fun hom => hom.comp
            (problem.data.pulledData.lift.pathLift tail))
            (solution.edge_naturality edge)
        _ = _ := @Category.assoc
          (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ _ _ (solution.component _)
          (problem.data.pulledTransport.edgeLift edge)
          (problem.data.pulledData.lift.pathLift tail)

/-- Naturality of an appended path, with both path equations used explicitly. -/
theorem append_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {problem : UpperRefinementBCProblem.{u, v} ctx}
    (solution : UpperRefinementBCSolution problem)
    {i j k : problem.presentation.Vertex}
    (first : problem.presentation.Path i j)
    (second : problem.presentation.Path j k) :
    (problem.data.baseData.lift.pathLift (first.append second)).comp
        (solution.component k) =
      (solution.component i).comp
        (problem.data.pulledData.lift.pathLift (first.append second)) := by
  rw [problem.data.baseData.lift.pathLift_append,
    problem.data.pulledData.lift.pathLift_append]
  calc
    _ = (problem.data.baseData.lift.pathLift first).comp
        ((problem.data.baseData.lift.pathLift second).comp
          (solution.component k)) := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (problem.data.baseData.lift.pathLift first)
      (problem.data.baseData.lift.pathLift second)
      (solution.component k)
    _ = (problem.data.baseData.lift.pathLift first).comp
        ((solution.component j).comp
          (problem.data.pulledData.lift.pathLift second)) :=
      congrArg _ (solution.path_naturality second)
    _ = ((problem.data.baseData.lift.pathLift first).comp
          (solution.component j)).comp
        (problem.data.pulledData.lift.pathLift second) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (problem.data.baseData.lift.pathLift first)
        (solution.component j)
        (problem.data.pulledData.lift.pathLift second)).symm
    _ = ((solution.component i).comp
          (problem.data.pulledData.lift.pathLift first)).comp
        (problem.data.pulledData.lift.pathLift second) :=
      congrArg (fun hom => hom.comp
        (problem.data.pulledData.lift.pathLift second))
        (solution.path_naturality first)
    _ = _ := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (solution.component i)
      (problem.data.pulledData.lift.pathLift first)
      (problem.data.pulledData.lift.pathLift second)

/-- Pasting a left authored two-cell path respects the comparator intertwining. -/
theorem authored_twoCell_pasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {problem : UpperRefinementBCProblem.{u, v} ctx}
    (solution : UpperRefinementBCSolution problem)
    (cell : problem.presentation.TwoCell) :
    ((problem.data.baseData.lift.pathLift
        (problem.presentation.twoLeft cell)).comp
      (CompositeFiberAut.hom
        (problem.data.baseData.comparator cell))).comp
        (solution.component (problem.presentation.twoTarget cell)) =
      (solution.component (problem.presentation.twoSource cell)).comp
        ((problem.data.pulledData.lift.pathLift
          (problem.presentation.twoLeft cell)).comp
        (CompositeFiberAut.hom
          (problem.data.pulledData.comparator cell))) := by
  calc
    _ = (problem.data.baseData.lift.pathLift
          (problem.presentation.twoLeft cell)).comp
        ((CompositeFiberAut.hom
          (problem.data.baseData.comparator cell)).comp
          (solution.component (problem.presentation.twoTarget cell))) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _
        (problem.data.baseData.lift.pathLift
          (problem.presentation.twoLeft cell))
        (CompositeFiberAut.hom
          (problem.data.baseData.comparator cell))
        (solution.component (problem.presentation.twoTarget cell))
    _ = (problem.data.baseData.lift.pathLift
          (problem.presentation.twoLeft cell)).comp
        ((solution.component (problem.presentation.twoTarget cell)).comp
          (CompositeFiberAut.hom
            (problem.data.pulledData.comparator cell))) :=
      congrArg _ (solution.comparator_intertwining cell)
    _ = ((problem.data.baseData.lift.pathLift
          (problem.presentation.twoLeft cell)).comp
          (solution.component (problem.presentation.twoTarget cell))).comp
        (CompositeFiberAut.hom
          (problem.data.pulledData.comparator cell)) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _
        (problem.data.baseData.lift.pathLift
          (problem.presentation.twoLeft cell))
        (solution.component (problem.presentation.twoTarget cell))
        (CompositeFiberAut.hom
          (problem.data.pulledData.comparator cell))).symm
    _ = ((solution.component (problem.presentation.twoSource cell)).comp
          (problem.data.pulledData.lift.pathLift
            (problem.presentation.twoLeft cell))).comp
        (CompositeFiberAut.hom
          (problem.data.pulledData.comparator cell)) :=
      congrArg (fun hom => hom.comp
        (CompositeFiberAut.hom
          (problem.data.pulledData.comparator cell)))
        (solution.path_naturality (problem.presentation.twoLeft cell))
    _ = _ := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (solution.component (problem.presentation.twoSource cell))
      (problem.data.pulledData.lift.pathLift
        (problem.presentation.twoLeft cell))
      (CompositeFiberAut.hom
        (problem.data.pulledData.comparator cell))

end UpperRefinementBCSolution

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
