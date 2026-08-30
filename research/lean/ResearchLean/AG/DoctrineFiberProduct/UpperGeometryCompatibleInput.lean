import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFiniteCartesianNaturality

/-!
# Certificate-free compatible input for G-115

This module starts the revision-4 compatible locus.  Its input contains only a
finite source diagram and one fixed-coefficient G-109 transport on that source.
In particular, neither reverse-route legs nor their Cartesian qualifications,
comparators, endpoint comparisons, solutions, or cochains are stored.

The two reverse-route geometries and their legs are generated pointwise from
the G-112 exact and G-114 realized-refinement cleavages.  Their strong
Cartesian qualifications are consequently theorems about the constructors,
not certificates accepted from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

/-- Data of a geometry-compatible finite source.  The only comparator family
is the authored comparator already contained in `sourceTransport`. -/
structure UpperGeometryCompatibleProblemInputData
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U)
    (P : FiniteTransportPresentation.{u}) (k : CommRingCat.{v}) where
  /-- Chosen root vertex. -/
  root : P.Vertex
  /-- Every vertex is reached by a directed path from the root. -/
  rootPath : (i : P.Vertex) → P.Path root i
  /-- Source packages form an actual diagram in the selected target fiber. -/
  sourceFiberDiagram : PresentedPathCategory P ⥤
    CoreFiber (ctx.configuration.targetPointAt ctx.source)
  /-- Source geometry at every vertex, over the corresponding diagram object. -/
  sourceGeometry : (i : P.Vertex) →
    FixedCoefficientGeometryAt (sourceFiberDiagram.obj ⟨i⟩).1 k
  /-- The single authored two-layer transport, including its single comparator
  family and coefficient-identity laws. -/
  sourceTransport : FixedCoefficientTwoLayerTransportOver P
    sourceFiberDiagram k sourceGeometry

/-- A certificate-free input packages its finite presentation and coefficient
ring together with one compatible source transport. -/
structure UpperGeometryCompatibleProblemInput
    {U : AtomCarrier.{u}} (ctx : ActiveRefinementBCContext U) where
  /-- Finite 0/1/2/3-cell presentation. -/
  presentation : FiniteTransportPresentation.{u}
  /-- Coefficient ring fixed by source edges and authored comparators. -/
  coefficient : CommRingCat.{v}
  /-- Source-only compatible data. -/
  data : UpperGeometryCompatibleProblemInputData ctx presentation coefficient

namespace UpperGeometryCompatibleProblemInputData

/-- The source geometry regarded as geometry on the actual target package of
the retargeted active context. -/
def sourceTargetGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.TargetGeometry
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩)) where
  geometry := (input.sourceGeometry i).package
  core_eq := rfl

/-- Base-first reverse-route geometry generated from the source input. -/
noncomputable def generatedBaseRouteGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryPackage.{u, v} U :=
  UpperGeometryCleavage.baseRouteGeometry
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- Pulled-first reverse-route geometry generated from the source input. -/
noncomputable def generatedPulledRouteGeometryAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    GeometryPackage.{u, v} U :=
  UpperGeometryCleavage.pulledRouteGeometry
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- Literal generated base-first route leg to the authored source geometry. -/
noncomputable def generatedBaseRouteLegAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom (input.generatedBaseRouteGeometryAt i)
      (input.sourceGeometry i).package :=
  UpperGeometryCleavage.baseRouteGeometryHom
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- Literal generated pulled-first route leg to the authored source geometry. -/
noncomputable def generatedPulledRouteLegAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    RefinementGeometryHom (input.generatedPulledRouteGeometryAt i)
      (input.sourceGeometry i).package :=
  UpperGeometryCleavage.pulledRouteGeometryHom
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- The generated base-first leg is strongly Cartesian; no certificate is an
input field or theorem argument. -/
theorem generatedBaseRouteLegAt_isStronglyCartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base
      (input.generatedBaseRouteLegAt i) := by
  exact UpperGeometryCleavage.baseRouteGeometryHom_isStronglyCartesian
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- The generated pulled-first leg is strongly Cartesian; no certificate is an
input field or theorem argument. -/
theorem generatedPulledRouteLegAt_isStronglyCartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base
      (input.generatedPulledRouteLegAt i) := by
  exact UpperGeometryCleavage.pulledRouteGeometryHom_isStronglyCartesian
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i)

/-- The generated base-route geometry retains the input coefficient ring. -/
theorem generatedBaseRouteGeometryAt_coefficient_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedBaseRouteGeometryAt i).Coefficient = k := by
  unfold generatedBaseRouteGeometryAt UpperGeometryCleavage.baseRouteGeometry
  rw [UpperGeometryCleavage.exactSourceGeometry_coefficient_eq]
  unfold UpperGeometryCleavage.baseRefinementGeometry
  rw [UpperGeometryCleavage.refinementSourceGeometry_coefficient_eq]
  rfl

/-- The generated pulled-route geometry retains the input coefficient ring. -/
theorem generatedPulledRouteGeometryAt_coefficient_eq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.generatedPulledRouteGeometryAt i).Coefficient = k := by
  unfold generatedPulledRouteGeometryAt UpperGeometryCleavage.pulledRouteGeometry
  rw [UpperGeometryCleavage.refinementSourceGeometry_coefficient_eq]
  unfold UpperGeometryCleavage.pullbackTargetGeometry
  rw [UpperGeometryCleavage.exactSourceGeometry_coefficient_eq]
  rfl

end UpperGeometryCompatibleProblemInputData
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
