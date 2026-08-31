import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSolutionEquivalence

/-!
# Carrier-value obstruction for the G-115 decision fixture

The generated exact and realized-refinement geometry transports preserve the
underlying support, axis, and observable carrier values by heterogeneous
equality.  Consequently the theorem-generated compatible solution cannot have
a component whose support, axis, or observable value differs from equality
transport.  This is independent of the chosen finite presentation, authored
edge, comparator, or raw cochain.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCleavage

/-- The generated base route preserves every support carrier value. -/
theorem baseRouteForwardSupportComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (support : W.ctx.Support) :
    HEq ((baseRouteGeometryHom ctx target).geometry.supportComp W support)
      support := by
  have hExact := generatedExactSupportComp_heq
    (baseRefinementGeometry ctx target) (baseRouteExactArrow ctx target) W support
  have hRefinement := generatedRefinementSupportComp_heq target.geometry
    (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
    target.packagePoint_eq
    (refinementGeometryContextForward
      ((exactGeometryToRefinementGeometry U).map
        (baseRouteExactGeometryHom ctx target)).base W)
    (((exactGeometryToRefinementGeometry U).map
      (baseRouteExactGeometryHom ctx target)).geometry.supportComp W support)
  exact hRefinement.trans hExact

/-- The generated base route preserves every axis carrier value. -/
theorem baseRouteForwardAxisComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (axis : W.ctx.Axis) :
    HEq ((baseRouteGeometryHom ctx target).geometry.axisComp W axis) axis := by
  have hExact := generatedExactAxisComp_heq
    (baseRefinementGeometry ctx target) (baseRouteExactArrow ctx target) W axis
  have hRefinement := generatedRefinementAxisComp_heq target.geometry
    (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
    target.packagePoint_eq
    (refinementGeometryContextForward
      ((exactGeometryToRefinementGeometry U).map
        (baseRouteExactGeometryHom ctx target)).base W)
    (((exactGeometryToRefinementGeometry U).map
      (baseRouteExactGeometryHom ctx target)).geometry.axisComp W axis)
  exact hRefinement.trans hExact

/-- The generated base route preserves every observable carrier value. -/
theorem baseRouteForwardObservableComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (observable : W.ctx.Observable) :
    HEq ((baseRouteGeometryHom ctx target).geometry.observableComp W observable)
      observable := by
  have hExact := generatedExactObservableComp_heq
    (baseRefinementGeometry ctx target) (baseRouteExactArrow ctx target) W observable
  have hRefinement := generatedRefinementObservableComp_heq target.geometry
    (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
    target.packagePoint_eq
    (refinementGeometryContextForward
      ((exactGeometryToRefinementGeometry U).map
        (baseRouteExactGeometryHom ctx target)).base W)
    (((exactGeometryToRefinementGeometry U).map
      (baseRouteExactGeometryHom ctx target)).geometry.observableComp W observable)
  exact hRefinement.trans hExact

/-- Every support value of the generated route mate is equality transport. -/
theorem upperGeometryMateSupportComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (support : W.ctx.Support) :
    HEq (upperGeometryMateSupportComp ctx target W support) support := by
  have hForward := baseRouteForwardSupportComp_heq ctx target W support
  have hBackward := pulledRouteBackwardSupportComp_heq ctx target
    (refinementGeometryContextForward (baseRouteGeometryHom ctx target).base W)
    ((baseRouteGeometryHom ctx target).geometry.supportComp W support)
  exact hBackward.trans hForward

/-- Every axis value of the generated route mate is equality transport. -/
theorem upperGeometryMateAxisComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (axis : W.ctx.Axis) :
    HEq (upperGeometryMateAxisComp ctx target W axis) axis := by
  have hForward := baseRouteForwardAxisComp_heq ctx target W axis
  have hBackward := pulledRouteBackwardAxisComp_heq ctx target
    (refinementGeometryContextForward (baseRouteGeometryHom ctx target).base W)
    ((baseRouteGeometryHom ctx target).geometry.axisComp W axis)
  exact hBackward.trans hForward

/-- Every observable value of the generated route mate is equality transport. -/
theorem upperGeometryMateObservableComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (observable : W.ctx.Observable) :
    HEq (upperGeometryMateObservableComp ctx target W observable) observable := by
  have hForward := baseRouteForwardObservableComp_heq ctx target W observable
  have hBackward := pulledRouteBackwardObservableComp_heq ctx target
    (refinementGeometryContextForward (baseRouteGeometryHom ctx target).base W)
    ((baseRouteGeometryHom ctx target).geometry.observableComp W observable)
  exact hBackward.trans hForward

/-- The actual generated mate, after its base cast, still preserves every
support carrier value. -/
theorem upperGeometryMate_actual_supportComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (support : W.ctx.Support) :
    HEq ((upperGeometryMate ctx target).geometry.supportComp W support) support := by
  rw [upperGeometryMate_eq_explicit]
  exact upperGeometryMateSupportComp_heq ctx target W support

/-- The actual generated mate, after its base cast, still preserves every axis
carrier value. -/
theorem upperGeometryMate_actual_axisComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (axis : W.ctx.Axis) :
    HEq ((upperGeometryMate ctx target).geometry.axisComp W axis) axis := by
  rw [upperGeometryMate_eq_explicit]
  exact upperGeometryMateAxisComp_heq ctx target W axis

/-- The actual generated mate, after its base cast, still preserves every
observable carrier value. -/
theorem upperGeometryMate_actual_observableComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (baseRouteGeometry ctx target).site.category)
    (observable : W.ctx.Observable) :
    HEq ((upperGeometryMate ctx target).geometry.observableComp W observable)
      observable := by
  rw [upperGeometryMate_eq_explicit]
  exact upperGeometryMateObservableComp_heq ctx target W observable

end UpperGeometryCleavage

namespace UpperGeometryCompatibleProblemInputData

/-- The theorem-generated compatible solution preserves support carrier values
at every vertex, for every compatible input. -/
theorem generatedGeometryCompatibleSolution_supportComp_heq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedBaseRouteGeometryAt i).site.category)
    (support : W.ctx.Support) :
    HEq ((input.generatedGeometryCompatibleUpperRefinementBCSolution.component i).geometry.supportComp
      W support) support := by
  exact UpperGeometryCleavage.upperGeometryMate_actual_supportComp_heq
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i) W support

/-- The theorem-generated compatible solution preserves axis carrier values at
every vertex, for every compatible input. -/
theorem generatedGeometryCompatibleSolution_axisComp_heq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedBaseRouteGeometryAt i).site.category)
    (axis : W.ctx.Axis) :
    HEq ((input.generatedGeometryCompatibleUpperRefinementBCSolution.component i).geometry.axisComp
      W axis) axis := by
  exact UpperGeometryCleavage.upperGeometryMate_actual_axisComp_heq
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i) W axis

/-- The theorem-generated compatible solution preserves observable carrier
values at every vertex, for every compatible input. -/
theorem generatedGeometryCompatibleSolution_observableComp_heq
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedBaseRouteGeometryAt i).site.category)
    (observable : W.ctx.Observable) :
    HEq ((input.generatedGeometryCompatibleUpperRefinementBCSolution.component i).geometry.observableComp
      W observable) observable := by
  exact UpperGeometryCleavage.upperGeometryMate_actual_observableComp_heq
    (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
    (input.sourceTargetGeometryAt i) W observable

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
