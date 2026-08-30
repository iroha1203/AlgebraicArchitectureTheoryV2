import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCartesian

/-!
# Unconditional finite geometry naturality for G-115

The generated exact and realized-refinement geometry legs are Cartesian, so
the two literal reverse routes inherit Cartesianity.  This removes the
temporary Cartesian arguments from the finite geometry edges and their mate
naturality theorem.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence

namespace UpperGeometryCleavage

set_option maxHeartbeats 3000000

/-- The literal generated base-first geometry route is strongly Cartesian. -/
theorem baseRouteGeometryHom_isStronglyCartesian
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (show RefinementPackageHom
          ⟨(baseRouteGeometry ctx target).core⟩ ⟨target.geometry.core⟩ from
        (baseRouteGeometryHom ctx target).base)
      (show (⟨baseRouteGeometry ctx target⟩ : RefinementGeometryCategory U) ⟶
          ⟨target.geometry⟩ from baseRouteGeometryHom ctx target) := by
  unfold baseRouteGeometryHom
  letI hexact : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (baseRouteExactGeometryHom ctx target)).base)
      ((exactGeometryToRefinementGeometry U).map
        (baseRouteExactGeometryHom ctx target)) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      ((exactPackageToRefinement U).map
        (exactBaseHom (baseRefinementGeometry ctx target)
          (baseRouteExactArrow ctx target)))
      ((exactGeometryToRefinementGeometry U).map
        (generatedExactGeometryHom (baseRefinementGeometry ctx target)
          (baseRouteExactArrow ctx target)))
    exact generatedExactGeometryHom_isStronglyCartesian
      (baseRefinementGeometry ctx target) (baseRouteExactArrow ctx target)
  letI hrefinement : (refinementGeometryProjection U).IsStronglyCartesian
      (show RefinementPackageHom ⟨(baseRefinementGeometry ctx target).core⟩
          ⟨target.geometry.core⟩ from (baseRefinementGeometryHom ctx target).base)
      (show (⟨baseRefinementGeometry ctx target⟩ : RefinementGeometryCategory U) ⟶
          ⟨target.geometry⟩ from baseRefinementGeometryHom ctx target) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      (refinementBaseHom target.geometry
        (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
        target.packagePoint_eq)
      (show (⟨refinementSourceGeometry target.geometry
          (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
          target.packagePoint_eq⟩ : RefinementGeometryCategory U) ⟶
        ⟨target.geometry⟩ from generatedRefinementGeometryHom target.geometry
          (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
          target.packagePoint_eq)
    exact generatedRefinementGeometryHom_isStronglyCartesian
      target.geometry (ctx.configuration.baseRefinementAt ctx.source)
      ctx.condition target.packagePoint_eq
  exact CategoryTheory.Functor.IsStronglyCartesian.comp
    (refinementGeometryProjection U)

/-- The literal generated pulled-first geometry route is strongly Cartesian. -/
theorem pulledRouteGeometryHom_isStronglyCartesian
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (show RefinementPackageHom
          ⟨(pulledRouteGeometry ctx target).core⟩ ⟨target.geometry.core⟩ from
        (pulledRouteGeometryHom ctx target).base)
      (show (⟨pulledRouteGeometry ctx target⟩ : RefinementGeometryCategory U) ⟶
          ⟨target.geometry⟩ from pulledRouteGeometryHom ctx target) := by
  unfold pulledRouteGeometryHom
  letI hrefinement : (refinementGeometryProjection U).IsStronglyCartesian
      (show RefinementPackageHom ⟨(pulledRouteGeometry ctx target).core⟩
          ⟨(pullbackTargetGeometry ctx target).core⟩ from
        (pulledRefinementGeometryHom ctx target).base)
      (show (⟨pulledRouteGeometry ctx target⟩ : RefinementGeometryCategory U) ⟶
          ⟨pullbackTargetGeometry ctx target⟩ from
        pulledRefinementGeometryHom ctx target) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      (refinementBaseHom (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target))
      (show (⟨refinementSourceGeometry (pullbackTargetGeometry ctx target)
          (ctx.configuration.pulledRefinementAt ctx.source)
          (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
          (pullbackTargetGeometry_packagePoint_eq ctx target)⟩ :
            RefinementGeometryCategory U) ⟶
        ⟨pullbackTargetGeometry ctx target⟩ from
          generatedRefinementGeometryHom (pullbackTargetGeometry ctx target)
            (ctx.configuration.pulledRefinementAt ctx.source)
            (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
            (pullbackTargetGeometry_packagePoint_eq ctx target))
    exact generatedRefinementGeometryHom_isStronglyCartesian
      (pullbackTargetGeometry ctx target)
      (ctx.configuration.pulledRefinementAt ctx.source)
      (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
      (pullbackTargetGeometry_packagePoint_eq ctx target)
  letI hexact : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (pullbackTargetGeometryHom ctx target)).base)
      ((exactGeometryToRefinementGeometry U).map
        (pullbackTargetGeometryHom ctx target)) := by
    change (refinementGeometryProjection U).IsStronglyCartesian
      ((exactPackageToRefinement U).map
        (exactBaseHom target.geometry (pullbackTargetExactArrow ctx target)))
      ((exactGeometryToRefinementGeometry U).map
        (generatedExactGeometryHom target.geometry
          (pullbackTargetExactArrow ctx target)))
    exact generatedExactGeometryHom_isStronglyCartesian target.geometry
      (pullbackTargetExactArrow ctx target)
  exact CategoryTheory.Functor.IsStronglyCartesian.comp
    (refinementGeometryProjection U)

end UpperGeometryCleavage

namespace UpperRefinementBCProblemData

set_option maxHeartbeats 3000000

/-- Unconditional exact base-route geometry edge generated by G-115. -/
noncomputable def generatedBaseGeometryEdgeUnconditional
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (problem.generatedBaseRouteGeometryAt i)
      (problem.generatedBaseRouteGeometryAt j) :=
  problem.generatedBaseGeometryEdge edge
    (UpperGeometryCleavage.baseRouteGeometryHom_isStronglyCartesian
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))

/-- Unconditional exact pulled-route geometry edge generated by G-115. -/
noncomputable def generatedPulledGeometryEdgeUnconditional
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (problem.generatedPulledRouteGeometryAt i)
      (problem.generatedPulledRouteGeometryAt j) :=
  problem.generatedPulledGeometryEdge edge
    (UpperGeometryCleavage.pulledRouteGeometryHom_isStronglyCartesian
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))

/-- The unconditional generated base edge satisfies its full geometry factor
law. -/
theorem generatedBaseGeometryEdgeUnconditional_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedBaseGeometryEdgeUnconditional edge))
        (UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)) =
      RefinementGeometryHom.comp
        (UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i))
        ((exactGeometryToRefinementGeometry U).map
          (problem.sourceTransport.edgeLift edge)) := by
  exact problem.generatedBaseGeometryEdge_fac edge
    (UpperGeometryCleavage.baseRouteGeometryHom_isStronglyCartesian
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))

/-- The unconditional generated pulled edge satisfies its full geometry factor
law. -/
theorem generatedPulledGeometryEdgeUnconditional_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedPulledGeometryEdgeUnconditional edge))
        (UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j)) =
      RefinementGeometryHom.comp
        (UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i))
        ((exactGeometryToRefinementGeometry U).map
          (problem.sourceTransport.edgeLift edge)) := by
  exact problem.generatedPulledGeometryEdge_fac edge
    (UpperGeometryCleavage.pulledRouteGeometryHom_isStronglyCartesian
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))

/-- The generated upper geometry mate is natural on every finite authored
edge, with no caller-supplied Cartesian certificates. -/
theorem generatedUpperGeometryMateAt_edge_naturality_unconditional
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (problem.generatedBaseGeometryEdgeUnconditional edge).comp
        (problem.generatedUpperGeometryMateAt j) =
      (problem.generatedUpperGeometryMateAt i).comp
        (problem.generatedPulledGeometryEdgeUnconditional edge) := by
  exact problem.generatedUpperGeometryMateAt_edge_naturality edge
    (UpperGeometryCleavage.baseRouteGeometryHom_isStronglyCartesian
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))
    (UpperGeometryCleavage.pulledRouteGeometryHom_isStronglyCartesian
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
      (problem.generatedTargetGeometryAt j))

end UpperRefinementBCProblemData
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
