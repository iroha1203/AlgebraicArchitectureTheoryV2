import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFiniteCartesianNaturality
import ResearchLean.AG.DoctrineFiberProduct.UpperRefinementBCSolution

/-!
# Authored comparator compatibility for the generated G-115 mate

The raw finite problem keeps independently authored route geometries and
comparators, while the G-115 cleavage constructs canonical geometry route
objects.  This module compares each authored endpoint with its generated
counterpart by the generated route's Cartesian universal property.  For an
actual solution, Cartesian uniqueness then identifies the solution component
followed by the pulled comparison with the base comparison followed by the
generated mate.  Pasting this square with the authored comparator equation
gives the required comparator compatibility without replacing either authored
comparator by a canonical or identity comparator.

## Implementation notes

The endpoint comparisons point from authored to generated route objects.  This
direction is forced by the generated route homs' Cartesian universal property.
An endpoint cast or a comparison stored in the raw problem was rejected because
either would discard the complete geometry fields or move the route-between
conclusion into input data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence

namespace UpperRefinementBCProblemData

set_option maxHeartbeats 3000000

/-- Cartesian comparison from the authored base endpoint to the generated base
endpoint, before exactification. -/
noncomputable def generatedBaseGeometryComparisonRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    RefinementGeometryHom (problem.legData i).baseSource.package
      (problem.generatedBaseRouteGeometryAt i) := by
  let localCtx := ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩)
  let target := problem.generatedTargetGeometryAt i
  let route := UpperGeometryCleavage.baseRouteGeometryHom localCtx target
  let candidate := (problem.legData i).baseLeg
  letI hcart := UpperGeometryCleavage.baseRouteGeometryHom_isStronglyCartesian
    localCtx target
  letI hcand := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  have hfac :
      ((exactPackageToRefinement U).map
          (problem.generatedBaseCoreIsoAt i).inv.1).comp route.base =
        candidate.base := by
    change ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.baseRouteComparisonCoreInv localCtx target).1).comp
          (UpperGeometryCleavage.baseRouteGeometryHom localCtx target).base =
      (problem.legData i).baseLeg.base
    rw [UpperGeometryCleavage.baseRouteComparisonCoreInv_toRefinement]
    simpa [localCtx, target, UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      ActiveRefinementBCContext.baseCompositeLegAt] using
        UpperGeometryCleavage.baseRouteComparisonInv_fac localCtx target
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U) route.base route
    (g := (exactPackageToRefinement U).map
      (problem.generatedBaseCoreIsoAt i).inv.1)
    (f' := candidate.base) hfac.symm candidate

/-- The authored-to-generated base comparison has the exact inverse endpoint
transport as its lower projection. -/
theorem generatedBaseGeometryComparisonRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    (problem.generatedBaseGeometryComparisonRefinementAt i).base =
      (exactPackageToRefinement U).map
        (problem.generatedBaseCoreIsoAt i).inv.1 := by
  let localCtx := ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩)
  let target := problem.generatedTargetGeometryAt i
  let route := UpperGeometryCleavage.baseRouteGeometryHom localCtx target
  let candidate := (problem.legData i).baseLeg
  letI hcart := UpperGeometryCleavage.baseRouteGeometryHom_isStronglyCartesian
    localCtx target
  letI hcand := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  have hfac :
      ((exactPackageToRefinement U).map
          (problem.generatedBaseCoreIsoAt i).inv.1).comp route.base =
        candidate.base := by
    change ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.baseRouteComparisonCoreInv localCtx target).1).comp
          (UpperGeometryCleavage.baseRouteGeometryHom localCtx target).base =
      (problem.legData i).baseLeg.base
    rw [UpperGeometryCleavage.baseRouteComparisonCoreInv_toRefinement]
    simpa [localCtx, target, UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      ActiveRefinementBCContext.baseCompositeLegAt] using
        UpperGeometryCleavage.baseRouteComparisonInv_fac localCtx target
  unfold generatedBaseGeometryComparisonRefinementAt
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (problem.generatedBaseCoreIsoAt i).inv.1)
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U) route.base route
      hfac.symm
      candidate)).symm

/-- Exact geometry comparison from the authored base endpoint to the generated
base endpoint. -/
noncomputable def generatedBaseGeometryComparisonAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    GeometryTotalHom (problem.legData i).baseSource.package
      (problem.generatedBaseRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (problem.generatedBaseCoreIsoAt i).inv.1
    (problem.generatedBaseGeometryComparisonRefinementAt i)
    (problem.generatedBaseGeometryComparisonRefinementAt_base i)

/-- Re-embedding the exact base comparison recovers the complete Cartesian
factor. -/
theorem generatedBaseGeometryComparisonAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (problem.generatedBaseGeometryComparisonAt i) =
      problem.generatedBaseGeometryComparisonRefinementAt i := by
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The complete base endpoint comparison factors the literal authored route
leg through the generated route leg. -/
theorem generatedBaseGeometryComparisonAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedBaseGeometryComparisonAt i))
        (UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)) =
      (problem.legData i).baseLeg := by
  rw [problem.generatedBaseGeometryComparisonAt_toRefinement]
  let localCtx := ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩)
  let target := problem.generatedTargetGeometryAt i
  let route := UpperGeometryCleavage.baseRouteGeometryHom localCtx target
  let candidate := (problem.legData i).baseLeg
  letI hcart := UpperGeometryCleavage.baseRouteGeometryHom_isStronglyCartesian
    localCtx target
  letI hcand := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  have hfac :
      ((exactPackageToRefinement U).map
          (problem.generatedBaseCoreIsoAt i).inv.1).comp route.base =
        candidate.base := by
    change ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.baseRouteComparisonCoreInv localCtx target).1).comp
          (UpperGeometryCleavage.baseRouteGeometryHom localCtx target).base =
      (problem.legData i).baseLeg.base
    rw [UpperGeometryCleavage.baseRouteComparisonCoreInv_toRefinement]
    simpa [localCtx, target, UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      ActiveRefinementBCContext.baseCompositeLegAt] using
        UpperGeometryCleavage.baseRouteComparisonInv_fac localCtx target
  unfold generatedBaseGeometryComparisonRefinementAt
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U) route.base route hfac.symm candidate

/-- Cartesian comparison from the authored pulled endpoint to the generated
pulled endpoint, before exactification. -/
noncomputable def generatedPulledGeometryComparisonRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    RefinementGeometryHom (problem.legData i).pulledSource.package
      (problem.generatedPulledRouteGeometryAt i) := by
  let localCtx := ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩)
  let target := problem.generatedTargetGeometryAt i
  let route := UpperGeometryCleavage.pulledRouteGeometryHom localCtx target
  let candidate := (problem.legData i).pulledLeg
  letI hcart := UpperGeometryCleavage.pulledRouteGeometryHom_isStronglyCartesian
    localCtx target
  letI hcand := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  have hfac :
      ((exactPackageToRefinement U).map
          (problem.generatedPulledCoreIsoAt i).inv.1).comp route.base =
        candidate.base := by
    change ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.pulledRouteComparisonCoreInv localCtx target).1).comp
          (UpperGeometryCleavage.pulledRouteGeometryHom localCtx target).base =
      (problem.legData i).pulledLeg.base
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreInv_toRefinement]
    simpa [localCtx, target, UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      ActiveRefinementBCContext.pulledCompositeLegAt] using
        UpperGeometryCleavage.pulledRouteComparisonInv_fac localCtx target
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U) route.base route
    (g := (exactPackageToRefinement U).map
      (problem.generatedPulledCoreIsoAt i).inv.1)
    (f' := candidate.base) hfac.symm candidate

/-- The authored-to-generated pulled comparison has the exact inverse endpoint
transport as its lower projection. -/
theorem generatedPulledGeometryComparisonRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    (problem.generatedPulledGeometryComparisonRefinementAt i).base =
      (exactPackageToRefinement U).map
        (problem.generatedPulledCoreIsoAt i).inv.1 := by
  let localCtx := ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩)
  let target := problem.generatedTargetGeometryAt i
  let route := UpperGeometryCleavage.pulledRouteGeometryHom localCtx target
  let candidate := (problem.legData i).pulledLeg
  letI hcart := UpperGeometryCleavage.pulledRouteGeometryHom_isStronglyCartesian
    localCtx target
  letI hcand := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  have hfac :
      ((exactPackageToRefinement U).map
          (problem.generatedPulledCoreIsoAt i).inv.1).comp route.base =
        candidate.base := by
    change ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.pulledRouteComparisonCoreInv localCtx target).1).comp
          (UpperGeometryCleavage.pulledRouteGeometryHom localCtx target).base =
      (problem.legData i).pulledLeg.base
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreInv_toRefinement]
    simpa [localCtx, target, UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      ActiveRefinementBCContext.pulledCompositeLegAt] using
        UpperGeometryCleavage.pulledRouteComparisonInv_fac localCtx target
  unfold generatedPulledGeometryComparisonRefinementAt
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (problem.generatedPulledCoreIsoAt i).inv.1)
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U) route.base route hfac.symm candidate)).symm

/-- Exact geometry comparison from the authored pulled endpoint to the generated
pulled endpoint. -/
noncomputable def generatedPulledGeometryComparisonAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    GeometryTotalHom (problem.legData i).pulledSource.package
      (problem.generatedPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (problem.generatedPulledCoreIsoAt i).inv.1
    (problem.generatedPulledGeometryComparisonRefinementAt i)
    (problem.generatedPulledGeometryComparisonRefinementAt_base i)

/-- Re-embedding the exact pulled comparison recovers the complete Cartesian
factor. -/
theorem generatedPulledGeometryComparisonAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (problem.generatedPulledGeometryComparisonAt i) =
      problem.generatedPulledGeometryComparisonRefinementAt i := by
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The complete pulled endpoint comparison factors the literal authored route
leg through the generated route leg. -/
theorem generatedPulledGeometryComparisonAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}} (problem : UpperRefinementBCProblemData ctx P k)
    (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedPulledGeometryComparisonAt i))
        (UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)) =
      (problem.legData i).pulledLeg := by
  rw [problem.generatedPulledGeometryComparisonAt_toRefinement]
  let localCtx := ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩)
  let target := problem.generatedTargetGeometryAt i
  let route := UpperGeometryCleavage.pulledRouteGeometryHom localCtx target
  let candidate := (problem.legData i).pulledLeg
  letI hcart := UpperGeometryCleavage.pulledRouteGeometryHom_isStronglyCartesian
    localCtx target
  letI hcand := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  have hfac :
      ((exactPackageToRefinement U).map
          (problem.generatedPulledCoreIsoAt i).inv.1).comp route.base =
        candidate.base := by
    change ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.pulledRouteComparisonCoreInv localCtx target).1).comp
          (UpperGeometryCleavage.pulledRouteGeometryHom localCtx target).base =
      (problem.legData i).pulledLeg.base
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreInv_toRefinement]
    simpa [localCtx, target, UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      ActiveRefinementBCContext.pulledCompositeLegAt] using
        UpperGeometryCleavage.pulledRouteComparisonInv_fac localCtx target
  unfold generatedPulledGeometryComparisonRefinementAt
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U) route.base route hfac.symm candidate

end UpperRefinementBCProblemData

namespace UpperRefinementBCSolution

set_option maxHeartbeats 3000000

/-- The two authored-to-generated endpoint comparisons identify an actual
solution component with the generated G-115 mate at the package level. -/
theorem generated_component_base_square
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {problem : UpperRefinementBCProblem.{u, v} ctx}
    (solution : UpperRefinementBCSolution problem)
    (i : problem.presentation.Vertex) :
    ((problem.data.generatedBaseGeometryComparisonAt i).comp
        (problem.data.generatedUpperGeometryMateAt i)).base =
      ((solution.component i).comp
        (problem.data.generatedPulledGeometryComparisonAt i)).base := by
  change (problem.data.generatedBaseCoreIsoAt i).inv.1 ≫
      (problem.data.generatedUpperGeometryMateAt i).base =
    (solution.component i).base ≫
      (problem.data.generatedPulledCoreIsoAt i).inv.1
  rw [problem.data.generatedUpperGeometryMateAt_base,
    solution.component_base i]
  have hcore :
      (problem.data.generatedBaseCoreIsoAt i).inv ≫
          UpperGeometryCleavage.generatedRouteCoreMate
            (ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩))
            (problem.data.generatedTargetGeometryAt i) =
        ctx.mate.app (problem.data.sourceFiberDiagram.obj ⟨i⟩) ≫
          (problem.data.generatedPulledCoreIsoAt i).inv := by
    rw [← problem.data.generatedConjugateCoreMateAt_eq_generated]
    unfold UpperRefinementBCProblemData.generatedConjugateCoreMateAt
    simp
  exact congrArg (fun hom => hom.1) hcore

/-- An actual solution and the canonical generated mate form the full geometry
comparison square.  The proof uses both endpoint comparison factors and the
solution triangle through the generated pulled route's Cartesian uniqueness. -/
theorem generated_component_geometry_square
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {problem : UpperRefinementBCProblem.{u, v} ctx}
    (solution : UpperRefinementBCSolution problem)
    (i : problem.presentation.Vertex) :
    (problem.data.generatedBaseGeometryComparisonAt i).comp
        (problem.data.generatedUpperGeometryMateAt i) =
      (solution.component i).comp
        (problem.data.generatedPulledGeometryComparisonAt i) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  let localCtx := ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩)
  let target := problem.data.generatedTargetGeometryAt i
  let route := UpperGeometryCleavage.pulledRouteGeometryHom localCtx target
  let left := (exactGeometryToRefinementGeometry U).map
    ((problem.data.generatedBaseGeometryComparisonAt i).comp
      (problem.data.generatedUpperGeometryMateAt i))
  let right := (exactGeometryToRefinementGeometry U).map
    ((solution.component i).comp
      (problem.data.generatedPulledGeometryComparisonAt i))
  have hbase : left.base = right.base := by
    change (exactPackageToRefinement U).map
        (((problem.data.generatedBaseGeometryComparisonAt i).comp
          (problem.data.generatedUpperGeometryMateAt i)).base) =
      (exactPackageToRefinement U).map
        (((solution.component i).comp
          (problem.data.generatedPulledGeometryComparisonAt i)).base)
    exact congrArg (fun hom => (exactPackageToRefinement U).map hom)
      (solution.generated_component_base_square i)
  letI hcart := UpperGeometryCleavage.pulledRouteGeometryHom_isStronglyCartesian
    localCtx target
  letI hleft := UpperGeometryCleavage.refinementGeometryHom_isHomLift left
  letI hright := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    left.base right hbase.symm
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U) route.base route left.base
  dsimp [left, right]
  change ((((exactGeometryToRefinementGeometry U).map
        (problem.data.generatedBaseGeometryComparisonAt i)) ≫
      ((exactGeometryToRefinementGeometry U).map
        (problem.data.generatedUpperGeometryMateAt i))) ≫ route) =
    ((((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
      ((exactGeometryToRefinementGeometry U).map
        (problem.data.generatedPulledGeometryComparisonAt i))) ≫ route)
  dsimp [route, localCtx, target]
  have hmate := problem.data.generatedUpperGeometryMateAt_triangle i
  change ((exactGeometryToRefinementGeometry U).map
      (problem.data.generatedUpperGeometryMateAt i)) ≫
        UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩))
          (problem.data.generatedTargetGeometryAt i) =
      UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩))
        (problem.data.generatedTargetGeometryAt i) at hmate
  have hbaseFac := problem.data.generatedBaseGeometryComparisonAt_fac i
  change ((exactGeometryToRefinementGeometry U).map
      (problem.data.generatedBaseGeometryComparisonAt i)) ≫
        UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩))
          (problem.data.generatedTargetGeometryAt i) =
      (problem.data.legData i).baseLeg at hbaseFac
  have hpulledFac := problem.data.generatedPulledGeometryComparisonAt_fac i
  change ((exactGeometryToRefinementGeometry U).map
      (problem.data.generatedPulledGeometryComparisonAt i)) ≫
        UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩))
          (problem.data.generatedTargetGeometryAt i) =
      (problem.data.legData i).pulledLeg at hpulledFac
  have htriangle := solution.triangle i
  change ((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
      (problem.data.legData i).pulledLeg =
    (problem.data.legData i).baseLeg at htriangle
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (problem.data.generatedBaseGeometryComparisonAt i)) ≫
        (((exactGeometryToRefinementGeometry U).map
          (problem.data.generatedUpperGeometryMateAt i)) ≫
          UpperGeometryCleavage.pulledRouteGeometryHom
            (ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩))
            (problem.data.generatedTargetGeometryAt i)) := Category.assoc _ _ _
    _ = ((exactGeometryToRefinementGeometry U).map
          (problem.data.generatedBaseGeometryComparisonAt i)) ≫
        UpperGeometryCleavage.baseRouteGeometryHom
          (ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩))
          (problem.data.generatedTargetGeometryAt i) := congrArg _ hmate
    _ = (problem.data.legData i).baseLeg := hbaseFac
    _ = ((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
        (problem.data.legData i).pulledLeg := htriangle.symm
    _ = ((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
        (((exactGeometryToRefinementGeometry U).map
          (problem.data.generatedPulledGeometryComparisonAt i)) ≫
          UpperGeometryCleavage.pulledRouteGeometryHom
            (ctx.retarget (problem.data.sourceFiberDiagram.obj ⟨i⟩))
            (problem.data.generatedTargetGeometryAt i)) :=
      congrArg _ hpulledFac.symm
    _ = _ := (Category.assoc _ _ _).symm

/-- Pasting the generated comparison square with the actual authored
comparator equation intertwines both authored comparators with the canonical
generated mate.  No comparator is regenerated or replaced. -/
theorem generated_authored_comparator_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {problem : UpperRefinementBCProblem.{u, v} ctx}
    (solution : UpperRefinementBCSolution problem)
    (cell : problem.presentation.TwoCell) :
    ((CompositeFiberAut.hom
        (problem.data.baseTransport.comparator cell)).comp
      (problem.data.generatedBaseGeometryComparisonAt
        (problem.presentation.twoTarget cell))).comp
        (problem.data.generatedUpperGeometryMateAt
          (problem.presentation.twoTarget cell)) =
      ((solution.component (problem.presentation.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (problem.data.pulledTransport.comparator cell))).comp
        (problem.data.generatedPulledGeometryComparisonAt
          (problem.presentation.twoTarget cell)) := by
  calc
    _ = (CompositeFiberAut.hom
          (problem.data.baseTransport.comparator cell)).comp
        ((problem.data.generatedBaseGeometryComparisonAt
            (problem.presentation.twoTarget cell)).comp
          (problem.data.generatedUpperGeometryMateAt
            (problem.presentation.twoTarget cell))) :=
      @Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ _ _ _
    _ = (CompositeFiberAut.hom
          (problem.data.baseTransport.comparator cell)).comp
        ((solution.component (problem.presentation.twoTarget cell)).comp
          (problem.data.generatedPulledGeometryComparisonAt
            (problem.presentation.twoTarget cell))) :=
      congrArg _ (solution.generated_component_geometry_square
        (problem.presentation.twoTarget cell))
    _ = ((CompositeFiberAut.hom
          (problem.data.baseTransport.comparator cell)).comp
        (solution.component (problem.presentation.twoTarget cell))).comp
          (problem.data.generatedPulledGeometryComparisonAt
            (problem.presentation.twoTarget cell)) :=
      (@Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ _ _ _).symm
    _ = ((solution.component (problem.presentation.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (problem.data.pulledTransport.comparator cell))).comp
          (problem.data.generatedPulledGeometryComparisonAt
            (problem.presentation.twoTarget cell)) :=
      congrArg (fun hom => hom.comp
        (problem.data.generatedPulledGeometryComparisonAt
          (problem.presentation.twoTarget cell)))
        (solution.comparator_intertwining cell)

end UpperRefinementBCSolution
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
