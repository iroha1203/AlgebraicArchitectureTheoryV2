import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleDecisionFixtures

/-!
# Comparator-incoherent raw upper problem for G-115

This module separates the generated Cartesian route legs and their rigid
comparator-free mate from two independently authored route comparators.  The
negative fixture keeps every comparator-free solution equation, but assigns
the concrete nonidentity decision comparator only to the base route.  The
resulting global comparator equation has no solution.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 4000000

namespace UpperComparatorRawProblem

/-!
## Implementation notes

The raw problem deliberately stores the two route comparators independently.
They are absent from `UpperGeometryCompatibleProblemInputData`, where both
comparators must instead be generated from one source comparator.  Reusing
the compatible solution equivalence was rejected because it would regenerate
the coherent pulled comparator and erase the intended obstruction.

The pre-solution retains precisely the solution fields that do not mention a
route comparator.  Its uniqueness is proved from the generated pulled leg's
Cartesian universal property; it is not a certificate field of the problem.
-/

/-- A raw upper problem with independently authored route comparators over
the theorem-generated Cartesian legs and edges. -/
structure Data
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) where
  /-- Independently authored comparator on the base route. -/
  baseComparator : (cell : P.TwoCell) →
    CompositeFiberAut (input.generatedBaseRouteGeometryAt (P.twoTarget cell))
  /-- Independently authored comparator on the pulled route. -/
  pulledComparator : (cell : P.TwoCell) →
    CompositeFiberAut (input.generatedPulledRouteGeometryAt (P.twoTarget cell))
  /-- The base comparator fixes the common coefficient ring. -/
  baseComparator_coefficient_id : ∀ cell,
    (CompositeFiberAut.hom (baseComparator cell)).geometry.coefficientHom =
      RingHom.id k
  /-- The pulled comparator fixes the common coefficient ring. -/
  pulledComparator_coefficient_id : ∀ cell,
    (CompositeFiberAut.hom (pulledComparator cell)).geometry.coefficientHom =
      RingHom.id k

/-- All generated upper-solution data that do not mention either independently
authored route comparator. -/
structure ComparatorFreePreSolution
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (problem : Data input) where
  /-- Vertical complete-geometry component. -/
  component : (i : P.Vertex) →
    GeometryTotalHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i)
  /-- The component projects to the generated core mate. -/
  component_base : ∀ i,
    (component i).base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1
  /-- Every component fixes coefficients. -/
  component_coefficient_id : ∀ i,
    (component i).geometry.coefficientHom = RingHom.id k
  /-- The full generated route triangle. -/
  triangle : ∀ i,
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map (component i))
        (input.generatedPulledRouteLegAt i) =
      input.generatedBaseRouteLegAt i
  /-- Naturality along every generated edge. -/
  edge_naturality : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (input.generatedBaseRouteGeometryEdge edge).comp (component j) =
      (component i).comp (input.generatedPulledRouteGeometryEdge edge)
  /-- Empty-path naturality. -/
  nil_naturality : ∀ i,
    (input.generatedBaseRouteLiftData.pathLift (.nil i)).comp (component i) =
      (component i).comp
        (input.generatedPulledRouteLiftData.pathLift (.nil i))
  /-- Naturality for every appended path pair. -/
  append_naturality : ∀ {i j l : P.Vertex}
      (first : P.Path i j) (second : P.Path j l),
    (input.generatedBaseRouteLiftData.pathLift
        (first.append second)).comp (component l) =
      (component i).comp
        (input.generatedPulledRouteLiftData.pathLift
          (first.append second))

/-- A raw solution is a comparator-free pre-solution satisfying the one
remaining global comparator equation. -/
structure Solution
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (problem : Data input) extends ComparatorFreePreSolution problem where
  /-- Intertwining of the two independently authored route comparators. -/
  comparator_intertwining : ∀ cell : P.TwoCell,
    (CompositeFiberAut.hom (problem.baseComparator cell)).comp
        (component (P.twoTarget cell)) =
      (component (P.twoTarget cell)).comp
        (CompositeFiberAut.hom (problem.pulledComparator cell))

namespace ComparatorFreePreSolution

/-- The theorem-generated compatible solution supplies every comparator-free
field without inspecting the raw problem's independent comparators. -/
noncomputable def generated
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (problem : Data input) : ComparatorFreePreSolution problem := by
  let solution := input.generatedGeometryCompatibleUpperRefinementBCSolution
  exact {
    component := solution.component
    component_base := solution.component_base
    component_coefficient_id := solution.component_coefficient_id
    triangle := solution.triangle
    edge_naturality := solution.edge_naturality
    nil_naturality := solution.nil_naturality
    append_naturality := solution.append_naturality }

/-- Cartesian uniqueness fixes every comparator-free component to the
theorem-generated compatible mate. -/
theorem component_eq_generated
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {problem : Data input} (pre : ComparatorFreePreSolution problem)
    (i : P.Vertex) :
    pre.component i =
      input.generatedGeometryCompatibleUpperRefinementBCSolution.component i := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  let left := (exactGeometryToRefinementGeometry U).map (pre.component i)
  let right := (exactGeometryToRefinementGeometry U).map
    (input.generatedGeometryCompatibleUpperRefinementBCSolution.component i)
  have hbase : left.base = right.base := by
    change (exactPackageToRefinement U).map (pre.component i).base =
      (exactPackageToRefinement U).map
        (input.generatedGeometryCompatibleUpperRefinementBCSolution.component i).base
    exact congrArg (exactPackageToRefinement U).map
      ((pre.component_base i).trans
        (input.generatedGeometryCompatibleUpperRefinementBCSolution.component_base i).symm)
  letI hleft := UpperGeometryCleavage.refinementGeometryHom_isHomLift left
  letI hright :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      left.base right hbase.symm
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledRouteLegAt i) left.base
  change left.comp (input.generatedPulledRouteLegAt i) =
    right.comp (input.generatedPulledRouteLegAt i)
  exact (pre.triangle i).trans
    (input.generatedGeometryCompatibleUpperRefinementBCSolution.triangle i).symm

end ComparatorFreePreSolution

end UpperComparatorRawProblem

namespace UpperComparatorIncoherentWitness

open UpperComparatorRawProblem

/-- The positive decision input, reused only for its generated local
Cartesian legs, mate, and edge equations. -/
noncomputable abbrev input := UpperDecisionWitness.problem.data

/-- The negative raw problem keeps the concrete nonidentity base comparator
but authors the pulled comparator independently as the identity. -/
noncomputable def problem : Data input where
  baseComparator _ :=
    input.generatedBaseRouteComparator UpperDecisionWitness.DecisionCell.comparison
  pulledComparator _ := 1
  baseComparator_coefficient_id _ :=
    UpperDecisionWitness.generated_base_comparator_coefficient_id
  pulledComparator_coefficient_id _ := rfl

/-- The rigid comparator-free pre-solution. -/
noncomputable def preSolution : ComparatorFreePreSolution problem :=
  ComparatorFreePreSolution.generated problem

/-- Every candidate comparator-free component is fixed to the named
pre-solution component by Cartesian uniqueness. -/
theorem preSolution_component_unique
    (candidate : ComparatorFreePreSolution problem)
    (i : UpperDecisionWitness.presentation.Vertex) :
    candidate.component i = preSolution.component i := by
  rw [candidate.component_eq_generated, preSolution.component_eq_generated]

/-- The independently authored base comparator fires on the concrete
signature axis while the pulled comparator is the identity. -/
theorem comparator_axis_incoherent :
    (CompositeFiberAut.hom
      (problem.baseComparator UpperDecisionWitness.DecisionCell.comparison)).base.upper.axisMap
        (1 : Fin 4) = (2 : Fin 4) ∧
    (CompositeFiberAut.hom
      (problem.pulledComparator UpperDecisionWitness.DecisionCell.comparison)).base.upper.axisMap
        (1 : Fin 4) = (1 : Fin 4) := by
  constructor
  · exact UpperDecisionWitness.generated_base_comparator_axis_fires
  · rfl

/-- The global comparator equation has no solution.  The contradiction uses
the concrete axis firing and injectivity of the candidate component's exact
upper axis equivalence. -/
theorem no_solution : ¬ Nonempty (Solution problem) := by
  rintro ⟨solution⟩
  have hintertwining := solution.comparator_intertwining
    UpperDecisionWitness.DecisionCell.comparison
  have haxis := congrArg
    (fun hom : GeometryTotalHom
        (input.generatedBaseRouteGeometryAt PUnit.unit)
        (input.generatedPulledRouteGeometryAt PUnit.unit) =>
      hom.base.upper.axisMap (1 : Fin 4)) hintertwining
  change
    (solution.component PUnit.unit).base.upper.axisMap
        ((CompositeFiberAut.hom
          (problem.baseComparator
            UpperDecisionWitness.DecisionCell.comparison)).base.upper.axisMap
              (1 : Fin 4)) =
      (CompositeFiberAut.hom
        (problem.pulledComparator
          UpperDecisionWitness.DecisionCell.comparison)).base.upper.axisMap
        ((solution.component PUnit.unit).base.upper.axisMap (1 : Fin 4)) at haxis
  rw [comparator_axis_incoherent.1] at haxis
  change (solution.component PUnit.unit).base.upper.axisMap (2 : Fin 4) =
    (solution.component PUnit.unit).base.upper.axisMap (1 : Fin 4) at haxis
  rw [solution.toComparatorFreePreSolution.component_eq_generated PUnit.unit]
    at haxis
  rw [input.generatedGeometryCompatibleUpperRefinementBCSolution.component_base
    PUnit.unit] at haxis
  let routeIso := UpperGeometryCleavage.generatedRouteCoreMateIso
    (UpperDecisionWitness.context.retarget
      (input.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
    (input.sourceTargetGeometryAt PUnit.unit)
  have routeAxisInjective :
      Function.Injective routeIso.hom.1.upper.axisMap := by
    intro first second equality
    have leftInverse (axis : Fin 4) :
        routeIso.inv.1.upper.axisMap
            (routeIso.hom.1.upper.axisMap axis) = axis := by
      have identity := congrArg
        (fun hom => hom.1.upper.axisMap axis) routeIso.hom_inv_id
      exact identity
    calc
      first = routeIso.inv.1.upper.axisMap
          (routeIso.hom.1.upper.axisMap first) := (leftInverse first).symm
      _ = routeIso.inv.1.upper.axisMap
          (routeIso.hom.1.upper.axisMap second) := congrArg _ equality
      _ = second := leftInverse second
  exact (show (2 : Fin 4) ≠ 1 by decide)
    (routeAxisInjective haxis)

end UpperComparatorIncoherentWitness

/-! ## Card-named negative artifacts -/

/-- Card-named comparator-incoherent raw problem. -/
noncomputable def upperComparatorIncoherentProblem :=
  UpperComparatorIncoherentWitness.problem

/-- Card-named rigid comparator-free pre-solution. -/
noncomputable def upperComparatorIncoherentPreSolution :=
  UpperComparatorIncoherentWitness.preSolution

/-- The card-named negative raw problem has no solution. -/
theorem upperComparatorIncoherentProblem_noSolution :
    ¬ Nonempty (UpperComparatorRawProblem.Solution
      upperComparatorIncoherentProblem) :=
  UpperComparatorIncoherentWitness.no_solution

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
