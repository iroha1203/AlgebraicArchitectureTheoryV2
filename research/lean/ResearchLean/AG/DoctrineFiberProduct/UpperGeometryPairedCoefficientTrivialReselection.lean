import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCoefficientTrivialReselection
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleComparatorIncoherence

/-!
# Paired coefficient-trivial upper reselections for G-115

This module supplies an endpoint-component precursor for G-115 revision 8
clause (c).  It is not yet the clause's full paired relation: it isolates the
literal endpoint equation relating one actual coefficient-trivial reselection
on each theorem-generated route.  Identity and multiplication laws are joined
by named nonidentity positive and negative decision instances, so the
precursor is neither an identity-only artifact nor an automatically inhabited
predicate.

## Implementation notes

The relation is kept as an edgewise equation between complete
`GeometryTotalHom`s.  Storing an opaque membership witness would hide the
route-between law, while a core-only equation would lose the geometry and
coefficient surfaces needed by the later raw-cochain theorem.  Path
naturality is therefore derived from the solution's actual edge equation and
the paired endpoint equation rather than added as a field.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace UpperGeometryCompatibleProblemInputData

/-- The endpoint-component precursor to G-115 revision 8 clause (c): base and
pulled actual coefficient-trivial reselections intertwine the vertical
solution component at every edge target.

This transparent complete-geometry equation is kept separate from the full
paired relation, which must additionally consume the solution triangle,
authored comparator, and coefficient-component law in the subsequent
raw-cochain construction. -/
def CoefficientTrivialUpperReselectionEndpointIntertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (CompositeFiberAut.hom
      (base.toUpperEdgeReselection i j edge)).comp
        (solution.component j) =
      (solution.component j).comp
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge))

/-- G-115 revision 8 clause (c) identity closure: the two identity actual
reselections form a paired coefficient-trivial reselection for every actual
compatible solution. -/
theorem coefficientTrivialUpperReselectionEndpointIntertwining_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input) :
    CoefficientTrivialUpperReselectionEndpointIntertwining solution
      (CoefficientTrivialUpperEdgeReselection.one
        input.generatedBaseRouteTransport)
      (CoefficientTrivialUpperEdgeReselection.one
        input.generatedPulledRouteTransport) := by
  intro i j edge
  change (GeometryTotalHom.id _).comp (solution.component j) =
    (solution.component j).comp (GeometryTotalHom.id _)
  exact (@Category.id_comp
    (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
    _ _ (solution.component j)).trans
      (@Category.comp_id
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (solution.component j)).symm

/-- G-115 revision 8 clause (c) vertical-composition closure: the pointwise
product of two paired coefficient-trivial reselections is again paired. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {baseFirst baseSecond :
      GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulledFirst pulledSecond :
      GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (first : CoefficientTrivialUpperReselectionEndpointIntertwining solution
      baseFirst pulledFirst)
    (second : CoefficientTrivialUpperReselectionEndpointIntertwining solution
      baseSecond pulledSecond) :
    CoefficientTrivialUpperReselectionEndpointIntertwining solution
      (CoefficientTrivialUpperEdgeReselection.mul baseFirst baseSecond)
      (CoefficientTrivialUpperEdgeReselection.mul pulledFirst pulledSecond) := by
  intro i j edge
  simp only [CoefficientTrivialUpperEdgeReselection.mul_toUpperEdgeReselection,
    Pi.mul_apply, compositeFiberAut_hom_mul]
  calc
    ((CompositeFiberAut.hom
        (baseSecond.toUpperEdgeReselection i j edge)).comp
      (CompositeFiberAut.hom
        (baseFirst.toUpperEdgeReselection i j edge))).comp
        (solution.component j) =
      (CompositeFiberAut.hom
        (baseSecond.toUpperEdgeReselection i j edge)).comp
        ((CompositeFiberAut.hom
          (baseFirst.toUpperEdgeReselection i j edge)).comp
            (solution.component j)) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _
        (CompositeFiberAut.hom
          (baseSecond.toUpperEdgeReselection i j edge))
        (CompositeFiberAut.hom
          (baseFirst.toUpperEdgeReselection i j edge))
        (solution.component j)
    _ = (CompositeFiberAut.hom
        (baseSecond.toUpperEdgeReselection i j edge)).comp
          ((solution.component j).comp
            (CompositeFiberAut.hom
              (pulledFirst.toUpperEdgeReselection i j edge))) :=
      congrArg _ (first edge)
    _ = ((CompositeFiberAut.hom
          (baseSecond.toUpperEdgeReselection i j edge)).comp
            (solution.component j)).comp
          (CompositeFiberAut.hom
            (pulledFirst.toUpperEdgeReselection i j edge)) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _
        (CompositeFiberAut.hom
          (baseSecond.toUpperEdgeReselection i j edge))
        (solution.component j)
        (CompositeFiberAut.hom
          (pulledFirst.toUpperEdgeReselection i j edge))).symm
    _ = ((solution.component j).comp
          (CompositeFiberAut.hom
            (pulledSecond.toUpperEdgeReselection i j edge))).comp
          (CompositeFiberAut.hom
            (pulledFirst.toUpperEdgeReselection i j edge)) :=
      congrArg (fun hom => hom.comp
        (CompositeFiberAut.hom
          (pulledFirst.toUpperEdgeReselection i j edge))) (second edge)
    _ = (solution.component j).comp
        ((CompositeFiberAut.hom
          (pulledSecond.toUpperEdgeReselection i j edge)).comp
            (CompositeFiberAut.hom
              (pulledFirst.toUpperEdgeReselection i j edge))) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (solution.component j)
        (CompositeFiberAut.hom
          (pulledSecond.toUpperEdgeReselection i j edge))
        (CompositeFiberAut.hom
          (pulledFirst.toUpperEdgeReselection i j edge))

/-- G-115 revision 8 clause (c) edge law: a paired reselection preserves the
actual solution edge-naturality square.  The proof consumes both the original
solution edge equation and the paired endpoint equation. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedEdge_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : CoefficientTrivialUpperReselectionEndpointIntertwining solution base pulled)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift input.generatedBaseRouteLiftData
      base.toUpperEdgeReselection edge).comp (solution.component j) =
      (solution.component i).comp
        (upperReselectedEdgeLift input.generatedPulledRouteLiftData
          pulled.toUpperEdgeReselection edge) := by
  rw [upperReselectedEdgeLift_eq, upperReselectedEdgeLift_eq]
  calc
    ((input.generatedBaseRouteGeometryEdge edge).comp
        (CompositeFiberAut.hom
          (base.toUpperEdgeReselection i j edge))).comp
          (solution.component j) =
      (input.generatedBaseRouteGeometryEdge edge).comp
        ((CompositeFiberAut.hom
          (base.toUpperEdgeReselection i j edge)).comp
            (solution.component j)) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (input.generatedBaseRouteGeometryEdge edge)
        (CompositeFiberAut.hom
          (base.toUpperEdgeReselection i j edge))
        (solution.component j)
    _ = (input.generatedBaseRouteGeometryEdge edge).comp
        ((solution.component j).comp
          (CompositeFiberAut.hom
            (pulled.toUpperEdgeReselection i j edge))) :=
      congrArg _ (paired edge)
    _ = ((input.generatedBaseRouteGeometryEdge edge).comp
          (solution.component j)).comp
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge)) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (input.generatedBaseRouteGeometryEdge edge)
        (solution.component j)
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge))).symm
    _ = ((solution.component i).comp
          (input.generatedPulledRouteGeometryEdge edge)).comp
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge)) :=
      congrArg (fun hom => hom.comp
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge)))
        (solution.edge_naturality edge)
    _ = (solution.component i).comp
        ((input.generatedPulledRouteGeometryEdge edge).comp
          (CompositeFiberAut.hom
            (pulled.toUpperEdgeReselection i j edge))) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (solution.component i)
        (input.generatedPulledRouteGeometryEdge edge)
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge))

/-- G-115 revision 8 clause (c) path-concatenation closure: the paired
reselection intertwines every reselected path.  The induction consumes the
actual solution edge equation at each generator and the paired endpoint law. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedPath_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : CoefficientTrivialUpperReselectionEndpointIntertwining solution base pulled)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift input.generatedBaseRouteLiftData
      base.toUpperEdgeReselection path).comp (solution.component j) =
      (solution.component i).comp
        (upperReselectedPathLift input.generatedPulledRouteLiftData
          pulled.toUpperEdgeReselection path) := by
  induction path with
  | nil vertex =>
      change (GeometryTotalHom.id _).comp (solution.component vertex) =
        (solution.component vertex).comp (GeometryTotalHom.id _)
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (solution.component vertex)).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ (solution.component vertex)).symm
  | @cons source middle target edge tail inductionHypothesis =>
      change ((upperReselectedEdgeLift input.generatedBaseRouteLiftData
          base.toUpperEdgeReselection edge).comp
        (upperReselectedPathLift input.generatedBaseRouteLiftData
          base.toUpperEdgeReselection tail)).comp
          (solution.component target) =
        (solution.component source).comp
          ((upperReselectedEdgeLift input.generatedPulledRouteLiftData
            pulled.toUpperEdgeReselection edge).comp
          (upperReselectedPathLift input.generatedPulledRouteLiftData
            pulled.toUpperEdgeReselection tail))
      calc
        _ = (upperReselectedEdgeLift input.generatedBaseRouteLiftData
              base.toUpperEdgeReselection edge).comp
            ((upperReselectedPathLift input.generatedBaseRouteLiftData
              base.toUpperEdgeReselection tail).comp
                (solution.component target)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _
            (upperReselectedEdgeLift input.generatedBaseRouteLiftData
              base.toUpperEdgeReselection edge)
            (upperReselectedPathLift input.generatedBaseRouteLiftData
              base.toUpperEdgeReselection tail)
            (solution.component target)
        _ = (upperReselectedEdgeLift input.generatedBaseRouteLiftData
              base.toUpperEdgeReselection edge).comp
            ((solution.component middle).comp
              (upperReselectedPathLift input.generatedPulledRouteLiftData
                pulled.toUpperEdgeReselection tail)) :=
          congrArg _ inductionHypothesis
        _ = ((upperReselectedEdgeLift input.generatedBaseRouteLiftData
                base.toUpperEdgeReselection edge).comp
              (solution.component middle)).comp
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              pulled.toUpperEdgeReselection tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _
            (upperReselectedEdgeLift input.generatedBaseRouteLiftData
              base.toUpperEdgeReselection edge)
            (solution.component middle)
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              pulled.toUpperEdgeReselection tail)).symm
        _ = ((solution.component source).comp
              (upperReselectedEdgeLift input.generatedPulledRouteLiftData
                pulled.toUpperEdgeReselection edge)).comp
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              pulled.toUpperEdgeReselection tail) :=
          congrArg (fun hom => hom.comp
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              pulled.toUpperEdgeReselection tail))
            (paired.reselectedEdge_naturality edge)
        _ = _ :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (solution.component source)
            (upperReselectedEdgeLift input.generatedPulledRouteLiftData
              pulled.toUpperEdgeReselection edge)
            (upperReselectedPathLift input.generatedPulledRouteLiftData
              pulled.toUpperEdgeReselection tail)

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- On the one-vertex decision presentation, the authored generated base
comparator defines an actual edge-indexed coefficient-trivial reselection.
The one-vertex specialization is essential: for a general presentation a
two-cell comparator belongs only to its own target fiber. -/
noncomputable def generatedBaseComparatorCoefficientTrivialUpperReselection :
    UpperGeometryCompatibleProblemInputData.GeneratedBaseCoefficientTrivialUpperEdgeReselection
      problem.data where
  toUpperEdgeReselection := fun _ _ _ =>
    problem.data.generatedBaseRouteFixedComparator DecisionCell.comparison
  coefficient_id := fun _ => generated_base_comparator_coefficient_id

/-- On the same one-vertex decision presentation, the authored generated
pulled comparator defines the companion coefficient-trivial reselection. -/
noncomputable def generatedPulledComparatorCoefficientTrivialUpperReselection :
    UpperGeometryCompatibleProblemInputData.GeneratedPulledCoefficientTrivialUpperEdgeReselection
      problem.data where
  toUpperEdgeReselection := fun _ _ _ =>
    problem.data.generatedPulledRouteFixedComparator DecisionCell.comparison
  coefficient_id := fun _ =>
    problem.data.generatedPulledRouteFixedComparator_coefficient_id
      DecisionCell.comparison

/-- In the named decision fixture, the generated base comparator reselection
is genuinely nonidentity. -/
theorem generatedBaseComparatorCoefficientTrivialUpperReselection_ne_one :
    generatedBaseComparatorCoefficientTrivialUpperReselection ≠
      CoefficientTrivialUpperEdgeReselection.one
        problem.data.generatedBaseRouteTransport := by
  intro equality
  have edgeEquality := congrArg
    (fun reselection => reselection.toUpperEdgeReselection
      PUnit.unit PUnit.unit DecisionEdge.twist) equality
  exact generated_base_comparator_ne_one edgeEquality

/-- The named generated comparator pair is a concrete nonidentity positive
instance of endpoint intertwining. -/
theorem generatedComparatorUpperReselections_endpointIntertwining_fires :
    UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining
      solution
      generatedBaseComparatorCoefficientTrivialUpperReselection
      generatedPulledComparatorCoefficientTrivialUpperReselection := by
  intro i j edge
  exact solution.comparator_intertwining DecisionCell.comparison

/-- Keeping the same nonidentity generated base comparator while selecting the
identity on the pulled route is a concrete negative endpoint instance.  Its
failure is inherited from the independently established complete comparator
descent obstruction on exactly these generated route geometries. -/
theorem generatedBaseComparatorPulledIdentity_not_endpointIntertwining :
    ¬ UpperGeometryCompatibleProblemInputData.CoefficientTrivialUpperReselectionEndpointIntertwining
      solution
      generatedBaseComparatorCoefficientTrivialUpperReselection
      (CoefficientTrivialUpperEdgeReselection.one
        problem.data.generatedPulledRouteTransport) := by
  intro paired
  apply generatedBaseIdentityPair_not_comparatorDescentAt
  exact paired (i := PUnit.unit) (j := PUnit.unit) DecisionEdge.twist

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
