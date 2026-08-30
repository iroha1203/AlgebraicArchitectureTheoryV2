import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFiniteMate

/-!
# Finite core naturality of the generated upper geometry mate

The generated route endpoints are compared with the actual G-114 route
diagrams at every finite-presentation vertex.  Conjugating the actual diagrams
by these exact fiber isomorphisms produces the literal core diagrams underlying
the generated geometry family.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperRefinementBCProblemData

set_option maxHeartbeats 3000000

/-- Exact comparison from the generated base endpoint to the actual G-114 endpoint. -/
noncomputable def generatedBaseCoreIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.baseRouteCoreFiber
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i) ≅
      (ctx.baseCoreDiagram problem.sourceFiberDiagram).obj ⟨i⟩ := by
  exact UpperGeometryCleavage.baseRouteBaseMateIso
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

/-- Exact comparison from the generated pulled endpoint to the actual G-114 endpoint. -/
noncomputable def generatedPulledCoreIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.pulledRouteCoreFiber
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i) ≅
      (ctx.pulledCoreDiagram problem.sourceFiberDiagram).obj ⟨i⟩ := by
  exact UpperGeometryCleavage.pulledRoutePulledMateIso
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

/-- The actual base diagram conjugated onto the generated base endpoints. -/
noncomputable def generatedBaseCoreDiagram
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) where
  obj W := UpperGeometryCleavage.baseRouteCoreFiber
    (ctx.retarget (problem.sourceFiberDiagram.obj W))
    (problem.generatedTargetGeometryAt W.vertex)
  map {W V} path :=
    (problem.generatedBaseCoreIsoAt W.vertex).hom ≫
      (ctx.baseCoreDiagram problem.sourceFiberDiagram).map path ≫
        (problem.generatedBaseCoreIsoAt V.vertex).inv
  map_id W := by simp
  map_comp first second := by simp [Category.assoc]

/-- The actual pulled diagram conjugated onto the generated pulled endpoints. -/
noncomputable def generatedPulledCoreDiagram
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) where
  obj W := UpperGeometryCleavage.pulledRouteCoreFiber
    (ctx.retarget (problem.sourceFiberDiagram.obj W))
    (problem.generatedTargetGeometryAt W.vertex)
  map {W V} path :=
    (problem.generatedPulledCoreIsoAt W.vertex).hom ≫
      (ctx.pulledCoreDiagram problem.sourceFiberDiagram).map path ≫
        (problem.generatedPulledCoreIsoAt V.vertex).inv
  map_id W := by simp
  map_comp first second := by simp [Category.assoc]

/-- The exact G-114 mate conjugated onto the two generated endpoint families. -/
noncomputable def generatedConjugateCoreMateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    (problem.generatedBaseCoreDiagram.obj ⟨i⟩) ⟶
      (problem.generatedPulledCoreDiagram.obj ⟨i⟩) :=
  (problem.generatedBaseCoreIsoAt i).hom ≫
    ctx.mate.app (problem.sourceFiberDiagram.obj ⟨i⟩) ≫
      (problem.generatedPulledCoreIsoAt i).inv

/-- The conjugated exact core mate is natural along every presented path. -/
theorem generatedConjugateCoreMateAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    problem.generatedBaseCoreDiagram.map path ≫
        problem.generatedConjugateCoreMateAt j =
      problem.generatedConjugateCoreMateAt i ≫
        problem.generatedPulledCoreDiagram.map path := by
  dsimp [generatedBaseCoreDiagram, generatedPulledCoreDiagram,
    generatedConjugateCoreMateAt]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [ActiveRefinementBCContext.baseCoreDiagram,
    ActiveRefinementBCContext.pulledCoreDiagram, Functor.comp_map]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg
      (fun hom => (problem.generatedBaseCoreIsoAt i).hom ≫ hom ≫
        (problem.generatedPulledCoreIsoAt j).inv)
      (ctx.mate.naturality (problem.sourceFiberDiagram.map path))

/-- The finite natural transformation carried by the conjugated G-114 mate. -/
noncomputable def generatedConjugateCoreMate
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
  problem.generatedBaseCoreDiagram ⟶ problem.generatedPulledCoreDiagram where
  app W := problem.generatedConjugateCoreMateAt W.vertex
  naturality _ _ path := problem.generatedConjugateCoreMateAt_naturality path

end UpperRefinementBCProblemData
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
