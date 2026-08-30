import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleFiniteComparators
import ResearchLean.AG.DoctrineFiberProduct.UpperRefinementBCSolution

/-!
# Generated route core edges for the compatible locus

This module conjugates the two G-114 core diagrams onto the pointwise route
geometries generated from the certificate-free G-115 input.  The resulting
edge factor graphs use the actual source diagram map and the theorem-generated
naturality of the two composite route legs; no route transport or naturality
certificate is accepted from the caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- Exact comparison from the generated base-route endpoint to the G-114 base
endpoint. -/
noncomputable def generatedBaseRouteCoreIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.baseRouteCoreFiber
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i) ≅
      (ctx.baseCoreDiagram input.sourceFiberDiagram).obj ⟨i⟩ :=
  UpperGeometryCleavage.baseRouteComparisonCoreIso
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- Exact comparison from the generated pulled-route endpoint to the G-114
pulled endpoint. -/
noncomputable def generatedPulledRouteCoreIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.pulledRouteCoreFiber
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i) ≅
      (ctx.pulledCoreDiagram input.sourceFiberDiagram).obj ⟨i⟩ :=
  UpperGeometryCleavage.pulledRouteComparisonCoreIso
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- The G-114 base core diagram conjugated onto the generated base-route
endpoints. -/
noncomputable def generatedBaseRouteCoreDiagram
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) where
  obj W := UpperGeometryCleavage.baseRouteCoreFiber
    (ctx.retarget (input.sourceFiberDiagram.obj W))
    (input.sourceTargetGeometryAt W.vertex)
  map {W V} path :=
    (input.generatedBaseRouteCoreIsoAt W.vertex).hom ≫
      (ctx.baseCoreDiagram input.sourceFiberDiagram).map path ≫
        (input.generatedBaseRouteCoreIsoAt V.vertex).inv
  map_id W := by simp
  map_comp first second := by simp [Category.assoc]

/-- The G-114 pulled core diagram conjugated onto the generated pulled-route
endpoints. -/
noncomputable def generatedPulledRouteCoreDiagram
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) where
  obj W := UpperGeometryCleavage.pulledRouteCoreFiber
    (ctx.retarget (input.sourceFiberDiagram.obj W))
    (input.sourceTargetGeometryAt W.vertex)
  map {W V} path :=
    (input.generatedPulledRouteCoreIsoAt W.vertex).hom ≫
      (ctx.pulledCoreDiagram input.sourceFiberDiagram).map path ≫
        (input.generatedPulledRouteCoreIsoAt V.vertex).inv
  map_id W := by simp
  map_comp first second := by simp [Category.assoc]

/-- A generated base-route core edge factors the literal route leg through the
actual source edge. -/
theorem generatedBaseRouteCoreEdge_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (exactPackageToRefinement U).map
        (input.generatedBaseRouteCoreDiagram.map
          (presentedEdgePath edge)).1 ≫
        (input.generatedBaseRouteLegAt j).base =
      (input.generatedBaseRouteLegAt i).base ≫
        (exactPackageToRefinement U).map
          (input.sourceTransport.edgeLift edge).base := by
  change ((exactPackageToRefinement U).map
      ((input.generatedBaseRouteCoreIsoAt i).hom.1 ≫
        ((ctx.baseCoreDiagram input.sourceFiberDiagram).map
          (presentedEdgePath edge)).1 ≫
        (input.generatedBaseRouteCoreIsoAt j).inv.1) ≫ _) = _
  rw [Functor.map_comp, Functor.map_comp]
  dsimp only [generatedBaseRouteCoreIsoAt,
    UpperGeometryCleavage.baseRouteComparisonCoreIso]
  have hInv : (exactPackageToRefinement U).map
        (UpperGeometryCleavage.baseRouteComparisonCoreInv
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨j⟩))
          (input.sourceTargetGeometryAt j)).1 ≫
        (input.generatedBaseRouteLegAt j).base =
      ctx.baseCompositeLegAt (input.sourceFiberDiagram.obj ⟨j⟩) := by
    rw [UpperGeometryCleavage.baseRouteComparisonCoreInv_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber, sourceTargetGeometryAt,
      generatedBaseRouteLegAt,
      ActiveRefinementBCContext.baseCompositeLegAt] using
        UpperGeometryCleavage.baseRouteComparisonInv_fac
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨j⟩))
          (input.sourceTargetGeometryAt j)
  have hNat :
      ((exactPackageToRefinement U).map
          ((ctx.baseCoreDiagram input.sourceFiberDiagram).map
            (presentedEdgePath edge)).1).comp
          (ctx.baseCompositeLegAt (input.sourceFiberDiagram.obj ⟨j⟩)) =
        (ctx.baseCompositeLegAt
          (input.sourceFiberDiagram.obj ⟨i⟩)).comp
          ((exactPackageToRefinement U).map
            (input.sourceTransport.edgeLift edge).base) := by
    rw [input.sourceTransport.edge_base]
    simpa [ActiveRefinementBCContext.baseCoreDiagram] using
      ctx.baseCompositeLegAt_naturality
        (input.sourceFiberDiagram.map (presentedEdgePath edge))
  change (exactPackageToRefinement U).map
      ((ctx.baseCoreDiagram input.sourceFiberDiagram).map
        (presentedEdgePath edge)).1 ≫
      ctx.baseCompositeLegAt (input.sourceFiberDiagram.obj ⟨j⟩) =
    ctx.baseCompositeLegAt (input.sourceFiberDiagram.obj ⟨i⟩) ≫
      (exactPackageToRefinement U).map
        (input.sourceTransport.edgeLift edge).base at hNat
  have hHom : (exactPackageToRefinement U).map
        (UpperGeometryCleavage.baseRouteComparisonCoreHom
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
          (input.sourceTargetGeometryAt i)).1 ≫
        ctx.baseCompositeLegAt (input.sourceFiberDiagram.obj ⟨i⟩) =
      (input.generatedBaseRouteLegAt i).base := by
    rw [UpperGeometryCleavage.baseRouteComparisonCoreHom_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber, sourceTargetGeometryAt,
      generatedBaseRouteLegAt,
      ActiveRefinementBCContext.baseCompositeLegAt] using
        UpperGeometryCleavage.baseRouteComparisonHom_fac
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
          (input.sourceTargetGeometryAt i)
  simp only [Category.assoc]
  rw [hInv, hNat]
  rw [← Category.assoc, hHom]

/-- A generated pulled-route core edge factors the literal route leg through
the same actual source edge. -/
theorem generatedPulledRouteCoreEdge_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (exactPackageToRefinement U).map
        (input.generatedPulledRouteCoreDiagram.map
          (presentedEdgePath edge)).1 ≫
        (input.generatedPulledRouteLegAt j).base =
      (input.generatedPulledRouteLegAt i).base ≫
        (exactPackageToRefinement U).map
          (input.sourceTransport.edgeLift edge).base := by
  change ((exactPackageToRefinement U).map
      ((input.generatedPulledRouteCoreIsoAt i).hom.1 ≫
        ((ctx.pulledCoreDiagram input.sourceFiberDiagram).map
          (presentedEdgePath edge)).1 ≫
        (input.generatedPulledRouteCoreIsoAt j).inv.1) ≫ _) = _
  rw [Functor.map_comp, Functor.map_comp]
  dsimp only [generatedPulledRouteCoreIsoAt,
    UpperGeometryCleavage.pulledRouteComparisonCoreIso]
  have hInv : (exactPackageToRefinement U).map
        (UpperGeometryCleavage.pulledRouteComparisonCoreInv
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨j⟩))
          (input.sourceTargetGeometryAt j)).1 ≫
        (input.generatedPulledRouteLegAt j).base =
      ctx.pulledCompositeLegAt (input.sourceFiberDiagram.obj ⟨j⟩) := by
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreInv_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber, sourceTargetGeometryAt,
      generatedPulledRouteLegAt,
      ActiveRefinementBCContext.pulledCompositeLegAt] using
        UpperGeometryCleavage.pulledRouteComparisonInv_fac
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨j⟩))
          (input.sourceTargetGeometryAt j)
  have hNat :
      ((exactPackageToRefinement U).map
          ((ctx.pulledCoreDiagram input.sourceFiberDiagram).map
            (presentedEdgePath edge)).1).comp
          (ctx.pulledCompositeLegAt
            (input.sourceFiberDiagram.obj ⟨j⟩)) =
        (ctx.pulledCompositeLegAt
          (input.sourceFiberDiagram.obj ⟨i⟩)).comp
          ((exactPackageToRefinement U).map
            (input.sourceTransport.edgeLift edge).base) := by
    rw [input.sourceTransport.edge_base]
    simpa [ActiveRefinementBCContext.pulledCoreDiagram] using
      ctx.pulledCompositeLegAt_naturality
        (input.sourceFiberDiagram.map (presentedEdgePath edge))
  change (exactPackageToRefinement U).map
      ((ctx.pulledCoreDiagram input.sourceFiberDiagram).map
        (presentedEdgePath edge)).1 ≫
      ctx.pulledCompositeLegAt (input.sourceFiberDiagram.obj ⟨j⟩) =
    ctx.pulledCompositeLegAt (input.sourceFiberDiagram.obj ⟨i⟩) ≫
      (exactPackageToRefinement U).map
        (input.sourceTransport.edgeLift edge).base at hNat
  have hHom : (exactPackageToRefinement U).map
        (UpperGeometryCleavage.pulledRouteComparisonCoreHom
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
          (input.sourceTargetGeometryAt i)).1 ≫
        ctx.pulledCompositeLegAt (input.sourceFiberDiagram.obj ⟨i⟩) =
      (input.generatedPulledRouteLegAt i).base := by
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreHom_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber, sourceTargetGeometryAt,
      generatedPulledRouteLegAt,
      ActiveRefinementBCContext.pulledCompositeLegAt] using
        UpperGeometryCleavage.pulledRouteComparisonHom_fac
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
          (input.sourceTargetGeometryAt i)
  simp only [Category.assoc]
  rw [hInv, hNat]
  rw [← Category.assoc, hHom]

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
