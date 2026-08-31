import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryPairedCoefficientLaws

/-!
# Full paired coefficient-trivial upper reselections for G-115

This module packages the G-115 revision 8 clause (c) relation without storing
its final raw-cochain conclusion.  A full pair consists of the actual endpoint
intertwining precursor together with three pair-dependent consequences: a
reselected path-leg triangle, reselected authored-comparator pasting, and
coefficient triviality of the actual raw-cochain square.

Each consequence is regenerated from the endpoint relation and the existing
solution and route laws.  Callers cannot supply triangle, comparator, or
coefficient certificates independently.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-- The solution triangle whiskered by an actual paired reselected path. -/
def ReselectedPathLegTriangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  ∀ {i j : P.Vertex} (path : P.Path i j),
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedBaseRouteLiftData
            base.toUpperEdgeReselection path))
        (input.generatedBaseRouteLegAt j) =
      RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map (solution.component i))
        (RefinementGeometryHom.comp
          ((exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              pulled.toUpperEdgeReselection path))
          (input.generatedPulledRouteLegAt j))

/-- Endpoint intertwining and the actual solution triangle generate the
reselected path-leg triangle; no triangle certificate is accepted. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedPath_legTriangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : CoefficientTrivialUpperReselectionEndpointIntertwining
      solution base pulled) :
    ReselectedPathLegTriangle solution base pulled := by
  intro i j path
  have pathNaturality := congrArg
    (fun hom => (exactGeometryToRefinementGeometry U).map hom)
    (paired.reselectedPath_naturality path)
  have mappedPathNaturality :
      ((exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.generatedBaseRouteLiftData
          base.toUpperEdgeReselection path)) ≫
        ((exactGeometryToRefinementGeometry U).map (solution.component j)) =
      ((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedPulledRouteLiftData
            pulled.toUpperEdgeReselection path)) := by
    simpa only [Functor.map_comp] using pathNaturality
  change
    ((exactGeometryToRefinementGeometry U).map
      (upperReselectedPathLift input.generatedBaseRouteLiftData
        base.toUpperEdgeReselection path)) ≫
        input.generatedBaseRouteLegAt j =
      ((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedPulledRouteLiftData
            pulled.toUpperEdgeReselection path)) ≫
          input.generatedPulledRouteLegAt j
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedBaseRouteLiftData
            base.toUpperEdgeReselection path)) ≫
        (((exactGeometryToRefinementGeometry U).map
          (solution.component j)) ≫ input.generatedPulledRouteLegAt j) := by
      exact congrArg
        (fun leg => ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedBaseRouteLiftData
            base.toUpperEdgeReselection path)) ≫ leg)
        (solution.triangle j).symm
    _ = ((((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedBaseRouteLiftData
            base.toUpperEdgeReselection path)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (solution.component j))) ≫ input.generatedPulledRouteLegAt j) := by
      simp only [Category.assoc]
    _ = ((((exactGeometryToRefinementGeometry U).map
          (solution.component i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.generatedPulledRouteLiftData
            pulled.toUpperEdgeReselection path))) ≫
          input.generatedPulledRouteLegAt j) := by
      rw [mappedPathNaturality]
    _ = _ := by simp only [Category.assoc]

/-- Pasting an actual reselected left path with the literal authored
comparator commutes with the actual solution component. -/
def ReselectedAuthoredComparatorPasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  ∀ cell : P.TwoCell,
    ((upperReselectedPathLift input.generatedBaseRouteLiftData
        base.toUpperEdgeReselection (P.twoLeft cell)).comp
      (CompositeFiberAut.hom
        (input.generatedBaseRouteComparator cell))).comp
        (solution.component (P.twoTarget cell)) =
      (solution.component (P.twoSource cell)).comp
        ((upperReselectedPathLift input.generatedPulledRouteLiftData
          pulled.toUpperEdgeReselection (P.twoLeft cell)).comp
            (CompositeFiberAut.hom
              (input.generatedPulledRouteComparator cell)))

/-- Endpoint intertwining and the literal authored comparator equation
generate reselected authored-comparator pasting. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedAuthoredComparator_pasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : CoefficientTrivialUpperReselectionEndpointIntertwining
      solution base pulled) :
    ReselectedAuthoredComparatorPasting solution base pulled := by
  intro cell
  let baseLeft := upperReselectedPathLift input.generatedBaseRouteLiftData
    base.toUpperEdgeReselection (P.twoLeft cell)
  let pulledLeft := upperReselectedPathLift input.generatedPulledRouteLiftData
    pulled.toUpperEdgeReselection (P.twoLeft cell)
  let baseComparator := CompositeFiberAut.hom
    (input.generatedBaseRouteComparator cell)
  let pulledComparator := CompositeFiberAut.hom
    (input.generatedPulledRouteComparator cell)
  change ((baseLeft.comp baseComparator).comp
      (solution.component (P.twoTarget cell))) =
    (solution.component (P.twoSource cell)).comp
      (pulledLeft.comp pulledComparator)
  calc
    _ = baseLeft.comp (baseComparator.comp
        (solution.component (P.twoTarget cell))) :=
      @Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ baseLeft baseComparator
        (solution.component (P.twoTarget cell))
    _ = baseLeft.comp ((solution.component (P.twoTarget cell)).comp
        pulledComparator) := by
      rw [solution.comparator_intertwining cell]
    _ = (baseLeft.comp (solution.component (P.twoTarget cell))).comp
        pulledComparator :=
      (@Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ baseLeft (solution.component (P.twoTarget cell))
        pulledComparator).symm
    _ = ((solution.component (P.twoSource cell)).comp pulledLeft).comp
        pulledComparator := by
      rw [paired.reselectedPath_naturality (P.twoLeft cell)]
    _ = _ :=
      @Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (solution.component (P.twoSource cell)) pulledLeft
        pulledComparator

/-- Both sides of the actual raw-cochain component square fix the coefficient
ring pointwise. -/
def RawCochainComponentCoefficientTrivial
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  ∀ cell : P.TwoCell,
    (((CompositeFiberAut.hom
      (upperRawDefectCochain input.generatedBaseRouteData
        base.toUpperEdgeReselection cell)).comp
          (solution.component (P.twoTarget cell))).geometry.coefficientHom =
        RingHom.id k) ∧
    (((solution.component (P.twoTarget cell)).comp
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.generatedPulledRouteData
          pulled.toUpperEdgeReselection cell))).geometry.coefficientHom =
        RingHom.id k)

/-- The full transparent paired relation required by G-115 revision 8 clause
(c), prior to paired-orbit and endpoint-conjugation transport. -/
def PairedCoefficientTrivialUpperReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  CoefficientTrivialUpperReselectionEndpointIntertwining solution base pulled ∧
  ReselectedPathLegTriangle solution base pulled ∧
  ReselectedAuthoredComparatorPasting solution base pulled ∧
  RawCochainComponentCoefficientTrivial solution base pulled

/-- The endpoint relation generates every conjunct of the full pair from the
actual solution and route laws. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.toPaired
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (endpoint : CoefficientTrivialUpperReselectionEndpointIntertwining
      solution base pulled) :
    PairedCoefficientTrivialUpperReselection solution base pulled := by
  refine ⟨endpoint, endpoint.reselectedPath_legTriangle,
    endpoint.reselectedAuthoredComparator_pasting, ?_⟩
  intro cell
  exact upperRawDefectCochain_component_square_coefficient_id
    solution base pulled cell

/-- The identity pair is a full paired coefficient-trivial reselection. -/
theorem pairedCoefficientTrivialUpperReselection_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input) :
    PairedCoefficientTrivialUpperReselection solution
      (CoefficientTrivialUpperEdgeReselection.one
        input.generatedBaseRouteTransport)
      (CoefficientTrivialUpperEdgeReselection.one
        input.generatedPulledRouteTransport) :=
  CoefficientTrivialUpperReselectionEndpointIntertwining.toPaired
    (coefficientTrivialUpperReselectionEndpointIntertwining_one solution)

/-- Pointwise vertical multiplication preserves the full paired relation. -/
theorem PairedCoefficientTrivialUpperReselection.mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {baseFirst baseSecond :
      GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulledFirst pulledSecond :
      GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (first : PairedCoefficientTrivialUpperReselection solution
      baseFirst pulledFirst)
    (second : PairedCoefficientTrivialUpperReselection solution
      baseSecond pulledSecond) :
    PairedCoefficientTrivialUpperReselection solution
      (CoefficientTrivialUpperEdgeReselection.mul baseFirst baseSecond)
      (CoefficientTrivialUpperEdgeReselection.mul pulledFirst pulledSecond) :=
  CoefficientTrivialUpperReselectionEndpointIntertwining.toPaired
    (CoefficientTrivialUpperReselectionEndpointIntertwining.mul
      first.1 second.1)

/-- A full pair still yields the separately proved actual raw-cochain
intertwining theorem. -/
theorem PairedCoefficientTrivialUpperReselection.upperRawDefectCochain_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : PairedCoefficientTrivialUpperReselection solution base pulled)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (upperRawDefectCochain input.generatedBaseRouteData
        base.toUpperEdgeReselection cell)).comp
        (solution.component (P.twoTarget cell)) =
      (solution.component (P.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain input.generatedPulledRouteData
            pulled.toUpperEdgeReselection cell)) :=
  CoefficientTrivialUpperReselectionEndpointIntertwining.upperRawDefectCochain_intertwining
    paired.1 cell

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The named generated comparator pair fires the full paired relation and
retains its independently proved nonidentity base reselection. -/
theorem generatedComparatorUpperReselections_paired_fires :
    UpperGeometryCompatibleProblemInputData.PairedCoefficientTrivialUpperReselection
      solution generatedBaseComparatorCoefficientTrivialUpperReselection
        generatedPulledComparatorCoefficientTrivialUpperReselection :=
  UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining.toPaired
    generatedComparatorUpperReselections_endpointIntertwining_fires

/-- The named full pair fires the actual raw-cochain theorem. -/
theorem generatedComparatorUpperReselections_paired_rawCochain_fires
    (cell : problem.presentation.TwoCell) :
    (CompositeFiberAut.hom
      (upperRawDefectCochain problem.data.generatedBaseRouteData
        generatedBaseComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
          cell)).comp
        (solution.component (problem.presentation.twoTarget cell)) =
      (solution.component (problem.presentation.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain problem.data.generatedPulledRouteData
            generatedPulledComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
              cell)) :=
  UpperGeometryCompatibleProblemInputData.PairedCoefficientTrivialUpperReselection.upperRawDefectCochain_intertwining
    generatedComparatorUpperReselections_paired_fires cell

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
