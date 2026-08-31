import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleDecisionFixtures

/-!
# Qualified comparator descent for the G-115 upper geometry route

This module separates the local qualification of the two authored route
transports from the route-between comparator descent equation.  The positive
pair is the theorem-generated pair already carried by an actual solution.  The
negative pair keeps the generated pulled route data and changes only its
authored comparator to the identity.

## Implementation notes

`UpperComparatorDescentAt` is the complete `GeometryTotalHom` equality already
present in both solution contracts; a carrierwise predicate would lose the
route law that the three concrete evaluations are meant to refute.  The
negative transport is therefore a full qualified transport copied from the
generated pulled route, rather than an unqualified automorphism pair or a
custom raw problem.  Its failure is proved downstream and is never accepted as
an incoherence certificate.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence
open UpperGeometryCompatibleProblemInputData

universe u v

/-- Descent of two individually qualified authored route comparators along an
actual family of vertical geometry components. -/
def UpperComparatorDescentAt
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {baseDiagram pulledDiagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {baseGeometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (baseDiagram.obj ⟨i⟩).1 k}
    {pulledGeometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (pulledDiagram.obj ⟨i⟩).1 k}
    (baseTransport : FixedCoefficientTwoLayerTransportOver P
      baseDiagram k baseGeometry)
    (pulledTransport : FixedCoefficientTwoLayerTransportOver P
      pulledDiagram k pulledGeometry)
    (component : (i : P.Vertex) → GeometryTotalHom
      (baseGeometry i).package (pulledGeometry i).package)
    (cell : P.TwoCell) : Prop :=
  (CompositeFiberAut.hom (baseTransport.comparator cell)).comp
      (component (P.twoTarget cell)) =
    (component (P.twoTarget cell)).comp
      (CompositeFiberAut.hom (pulledTransport.comparator cell))

namespace UpperRefinementBCSolution

/-- The literal actual-solution comparator field is qualified comparator
descent for the problem's two authored route transports. -/
theorem comparatorDescentAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {problem : UpperRefinementBCProblem.{u, v} ctx}
    (solution : UpperRefinementBCSolution problem)
    (cell : problem.presentation.TwoCell) :
    UpperComparatorDescentAt problem.data.baseTransport
      problem.data.pulledTransport solution.component cell :=
  solution.comparator_intertwining cell

end UpperRefinementBCSolution

namespace UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution

/-- The theorem-generated compatible solution also lies in the qualified
comparator descent locus. -/
theorem comparatorDescentAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (cell : P.TwoCell) :
    UpperComparatorDescentAt input.generatedBaseRouteTransport
      input.generatedPulledRouteTransport solution.component cell :=
  solution.comparator_intertwining cell

end UpperGeometryCompatibleProblemInputData.GeometryCompatibleUpperRefinementBCSolution

namespace UpperGeometryCompatibleProblemInputData

/-- The independently qualified pulled route with all comparator-independent
data unchanged and with the authored comparator replaced by identity. -/
noncomputable def generatedPulledIdentityComparatorTransport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    FixedCoefficientTwoLayerTransportOver P
      input.generatedPulledRouteCoreDiagram k
      input.generatedPulledRouteFixedGeometryAt where
  edgeLift := input.generatedPulledRouteTransport.edgeLift
  edge_base := input.generatedPulledRouteTransport.edge_base
  edgeGeometryStrong := input.generatedPulledRouteTransport.edgeGeometryStrong
  edgeCoreStrong := input.generatedPulledRouteTransport.edgeCoreStrong
  twoCellBase := input.generatedPulledRouteTransport.twoCellBase
  comparator _ := 1
  edge_coefficient_id := input.generatedPulledRouteTransport.edge_coefficient_id
  comparator_coefficient_id _ := by
    rfl

/-- The only changed authored datum of the copied pulled transport is its
identity comparator. -/
@[simp] theorem generatedPulledIdentityComparatorTransport_comparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.generatedPulledIdentityComparatorTransport.comparator cell = 1 :=
  rfl

/-- The replacement identity comparator retains the fixed-coefficient
qualification required of an authored route comparator. -/
theorem generatedPulledIdentityComparator_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.generatedPulledIdentityComparatorTransport.comparator cell)).geometry.coefficientHom =
        RingHom.id k :=
  input.generatedPulledIdentityComparatorTransport.comparator_coefficient_id cell

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The named theorem-generated pair is in the comparator descent locus. -/
theorem upperDecisionSolution_comparatorDescentAt :
    UpperComparatorDescentAt problem.data.generatedBaseRouteTransport
      problem.data.generatedPulledRouteTransport solution.component
      DecisionCell.comparison :=
  solution.comparatorDescentAt DecisionCell.comparison

/-! ## Carrierwise failure for the identity-comparator companion -/

/-- The solution component is injective on total support carriers.  This is
not a pointwise accident: postcomposition with the pulled route leg is the
realization-exact base route leg by the solution triangle. -/
theorem solution_supportSigmaMap_injective :
    Function.Injective
      (refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))) := by
  intro first second equality
  apply generatedBaseRealizationExact.supportSigmaEquiv.injective
  rw [← generatedBaseRoute_supportSigmaMap_eq]
  rw [← solution.triangle PUnit.unit]
  simp only [refinementSupportSigmaMap_comp, equality]

/-- The solution component is injective on total axis carriers, by the same
route-factorization argument. -/
theorem solution_axisSigmaMap_injective :
    Function.Injective
      (refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))) := by
  intro first second equality
  apply generatedBaseRealizationExact.axisSigmaEquiv.injective
  rw [← generatedBaseRoute_axisSigmaMap_eq]
  rw [← solution.triangle PUnit.unit]
  simp only [refinementAxisSigmaMap_comp, equality]

/-- The solution component is injective on total observable carriers, by the
same route-factorization argument. -/
theorem solution_observableSigmaMap_injective :
    Function.Injective
      (refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))) := by
  intro first second equality
  apply generatedBaseRealizationExact.observableSigmaEquiv.injective
  rw [← generatedBaseRoute_observableSigmaMap_eq]
  rw [← solution.triangle PUnit.unit]
  simp only [refinementObservableSigmaMap_comp, equality]

/-- The actual named solution component preserves the carrier of every total
support value.  This is the sigma-map form of the reviewed pointwise
carrier-conservativity theorem. -/
theorem solution_supportSigmaMap_carrier_conservative
    (value : Σ W :
      (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category,
      W.ctx.Support) :
    HEq
      (refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit)) value).2
      value.2 := by
  rcases value with ⟨W, support⟩
  exact solution_support_carrier_conservative W support

/-- The actual named solution component preserves the carrier of every total
axis value. -/
theorem solution_axisSigmaMap_carrier_conservative
    (value : Σ W :
      (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category,
      W.ctx.Axis) :
    HEq
      (refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit)) value).2
      value.2 := by
  rcases value with ⟨W, axis⟩
  exact solution_axis_carrier_conservative W axis

/-- The actual named solution component preserves the carrier of every total
observable value. -/
theorem solution_observableSigmaMap_carrier_conservative
    (value : Σ W :
      (problem.data.generatedBaseRouteGeometryAt PUnit.unit).site.category,
      W.ctx.Observable) :
    HEq
      (refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit)) value).2
      value.2 := by
  rcases value with ⟨W, observable⟩
  exact solution_observable_carrier_conservative W observable

/-- On support carriers, the generated base comparator followed by the actual
solution component differs from the actual component followed by the identity
comparator. -/
theorem generatedBaseIdentityPair_support_incoherent :
    HEq
      (refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))
        (refinementSupportSigmaMap
          ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
            (CompositeFiberAut.hom
              (problem.data.generatedBaseRouteTransport.comparator
                DecisionCell.comparison)))
          (generatedBaseSupportValue (1 : Fin 4)))).2
      (refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteTransport.comparator
              DecisionCell.comparison)))
        (generatedBaseSupportValue (1 : Fin 4))).2 ∧
    HEq
      (refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))
        (generatedBaseSupportValue (1 : Fin 4))).2
      (generatedBaseSupportValue (1 : Fin 4)).2 ∧
    refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          ((CompositeFiberAut.hom
            (problem.data.generatedBaseRouteTransport.comparator
              DecisionCell.comparison)).comp
            (solution.component PUnit.unit)))
        (generatedBaseSupportValue (1 : Fin 4)) ≠
      refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          ((solution.component PUnit.unit).comp
            (CompositeFiberAut.hom
              (problem.data.generatedPulledIdentityComparatorTransport.comparator
                DecisionCell.comparison))))
        (generatedBaseSupportValue (1 : Fin 4)) := by
  refine ⟨solution_supportSigmaMap_carrier_conservative _,
    solution_supportSigmaMap_carrier_conservative _, ?_⟩
  intro equality
  apply generated_base_comparator_local_support_ne_input
  apply solution_supportSigmaMap_injective
  simpa [refinementSupportSigmaMap_comp] using equality

/-- The same qualified route pair fails descent on axis carriers. -/
theorem generatedBaseIdentityPair_axis_incoherent :
    HEq
      (refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))
        (refinementAxisSigmaMap
          ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
            (CompositeFiberAut.hom
              (problem.data.generatedBaseRouteTransport.comparator
                DecisionCell.comparison)))
          (generatedBaseAxisValue (1 : Fin 4)))).2
      (refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteTransport.comparator
              DecisionCell.comparison)))
        (generatedBaseAxisValue (1 : Fin 4))).2 ∧
    HEq
      (refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))
        (generatedBaseAxisValue (1 : Fin 4))).2
      (generatedBaseAxisValue (1 : Fin 4)).2 ∧
    refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          ((CompositeFiberAut.hom
            (problem.data.generatedBaseRouteTransport.comparator
              DecisionCell.comparison)).comp
            (solution.component PUnit.unit)))
        (generatedBaseAxisValue (1 : Fin 4)) ≠
      refinementAxisSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          ((solution.component PUnit.unit).comp
            (CompositeFiberAut.hom
              (problem.data.generatedPulledIdentityComparatorTransport.comparator
                DecisionCell.comparison))))
        (generatedBaseAxisValue (1 : Fin 4)) := by
  refine ⟨solution_axisSigmaMap_carrier_conservative _,
    solution_axisSigmaMap_carrier_conservative _, ?_⟩
  intro equality
  apply generated_base_comparator_local_axis_ne_input
  apply solution_axisSigmaMap_injective
  simpa [refinementAxisSigmaMap_comp] using equality

/-- The same qualified route pair fails descent on observable carriers. -/
theorem generatedBaseIdentityPair_observable_incoherent :
    HEq
      (refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))
        (refinementObservableSigmaMap
          ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
            (CompositeFiberAut.hom
              (problem.data.generatedBaseRouteTransport.comparator
                DecisionCell.comparison)))
          (generatedBaseObservableValue (1 : Fin 4)))).2
      (refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (CompositeFiberAut.hom
            (problem.data.generatedBaseRouteTransport.comparator
              DecisionCell.comparison)))
        (generatedBaseObservableValue (1 : Fin 4))).2 ∧
    HEq
      (refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          (solution.component PUnit.unit))
        (generatedBaseObservableValue (1 : Fin 4))).2
      (generatedBaseObservableValue (1 : Fin 4)).2 ∧
    refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          ((CompositeFiberAut.hom
            (problem.data.generatedBaseRouteTransport.comparator
              DecisionCell.comparison)).comp
            (solution.component PUnit.unit)))
        (generatedBaseObservableValue (1 : Fin 4)) ≠
      refinementObservableSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map
          ((solution.component PUnit.unit).comp
            (CompositeFiberAut.hom
              (problem.data.generatedPulledIdentityComparatorTransport.comparator
                DecisionCell.comparison))))
        (generatedBaseObservableValue (1 : Fin 4)) := by
  refine ⟨solution_observableSigmaMap_carrier_conservative _,
    solution_observableSigmaMap_carrier_conservative _, ?_⟩
  intro equality
  apply generated_base_comparator_local_observable_ne_input
  apply solution_observableSigmaMap_injective
  simpa [refinementObservableSigmaMap_comp] using equality

/-- The generated base transport and identity-comparator pulled transport are
both individually qualified, but their actual route components do not satisfy
comparator descent. -/
theorem generatedBaseIdentityPair_not_comparatorDescentAt :
    ¬ UpperComparatorDescentAt problem.data.generatedBaseRouteTransport
      problem.data.generatedPulledIdentityComparatorTransport
      solution.component DecisionCell.comparison := by
  intro descent
  exact generatedBaseIdentityPair_support_incoherent.2.2
    (congrArg
      (fun hom => refinementSupportSigmaMap
        ((exactGeometryToRefinementGeometry FiniteModel.carrier).map hom)
        (generatedBaseSupportValue (1 : Fin 4))) descent)

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
