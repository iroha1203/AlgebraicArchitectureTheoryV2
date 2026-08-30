import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateGeometry
import ResearchLean.AG.DoctrineFiberProduct.UpperRefinementBCProblem

/-!
# Pointwise generated upper geometry mates on a finite presentation

This module evaluates the G-115-generated target geometry and upper mate at
every vertex of an existing finite upper problem. It deliberately does not
identify the generated route geometries with the problem's independently
authored route geometries. Later comparison maps must supply that bridge and
prove edge and comparator naturality.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence

namespace UpperRefinementBCProblemData

set_option maxHeartbeats 3000000

/-- The common target geometry at one vertex, tied to the retargeted G-114 context. -/
def generatedTargetGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.TargetGeometry
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩)) where
  geometry := (problem.legData i).commonTarget.package
  core_eq := rfl

/-- The generated base-route geometry at one finite-presentation vertex. -/
noncomputable def generatedBaseRouteGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    GeometryPackage.{u, v} U :=
  UpperGeometryCleavage.baseRouteGeometry
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

/-- The generated pulled-route geometry at one finite-presentation vertex. -/
noncomputable def generatedPulledRouteGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    GeometryPackage.{u, v} U :=
  UpperGeometryCleavage.pulledRouteGeometry
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

/-- The canonical G-115 geometry mate at one finite-presentation vertex. -/
noncomputable def generatedUpperGeometryMateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    GeometryTotalHom (problem.generatedBaseRouteGeometryAt i)
      (problem.generatedPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.upperGeometryMate
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

/-- The pointwise mate projects to the generated exact core mate. -/
theorem generatedUpperGeometryMateAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    (problem.generatedUpperGeometryMateAt i).base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).1 :=
  rfl

/-- The generated base-route geometry retains the common coefficient ring. -/
theorem generatedBaseRouteGeometryAt_coefficient_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    (problem.generatedBaseRouteGeometryAt i).Coefficient = k := by
  unfold generatedBaseRouteGeometryAt UpperGeometryCleavage.baseRouteGeometry
  rw [UpperGeometryCleavage.exactSourceGeometry_coefficient_eq]
  unfold UpperGeometryCleavage.baseRefinementGeometry
  rw [UpperGeometryCleavage.refinementSourceGeometry_coefficient_eq]
  rfl

/-- The generated pulled-route geometry retains the common coefficient ring. -/
theorem generatedPulledRouteGeometryAt_coefficient_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    (problem.generatedPulledRouteGeometryAt i).Coefficient = k := by
  unfold generatedPulledRouteGeometryAt UpperGeometryCleavage.pulledRouteGeometry
  rw [UpperGeometryCleavage.refinementSourceGeometry_coefficient_eq]
  unfold UpperGeometryCleavage.pullbackTargetGeometry
  rw [UpperGeometryCleavage.exactSourceGeometry_coefficient_eq]
  rfl

/-- The pointwise generated mate satisfies the full geometry route triangle. -/
theorem generatedUpperGeometryMateAt_triangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (problem.generatedUpperGeometryMateAt i))
        (UpperGeometryCleavage.pulledRouteGeometryHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)) =
      UpperGeometryCleavage.baseRouteGeometryHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i) := by
  exact UpperGeometryCleavage.upperGeometryMate_fac
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

/-- The pointwise core mate sits in the generated comparison square with G-114. -/
theorem generatedUpperGeometryMateAt_comparison_square
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    ((exactPackageToRefinement U).map
        (problem.generatedUpperGeometryMateAt i).base).comp
        (UpperGeometryCleavage.pulledRouteComparisonHom
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)) =
      (UpperGeometryCleavage.baseRouteComparisonHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).comp
        (UpperGeometryCleavage.retargetedContext
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i)).refinementMateAtTarget := by
  rw [problem.generatedUpperGeometryMateAt_base]
  simpa using UpperGeometryCleavage.generatedRouteCoreMate_comparison_square
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

end UpperRefinementBCProblemData
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
