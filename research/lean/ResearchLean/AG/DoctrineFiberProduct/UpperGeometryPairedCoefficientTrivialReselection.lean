import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCoefficientTrivialReselection
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSolutionContracts

/-!
# Paired coefficient-trivial upper reselections for G-115

This module begins G-115 revision 8 clause (c).  A paired reselection is not a
new orbit certificate: it is the literal endpoint-component naturality
equation relating one actual coefficient-trivial reselection on each of the
two theorem-generated routes.  The identity pair is constructed for every
geometry-compatible actual solution, and paired reselections are closed under
the existing pointwise vertical product.

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

/-- G-115 revision 8 clause (c)'s principal relation: base and pulled actual
coefficient-trivial reselections intertwine the vertical solution component
at every edge target. -/
def PairedCoefficientTrivialUpperReselection
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
theorem pairedCoefficientTrivialUpperReselection_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input) :
    PairedCoefficientTrivialUpperReselection solution
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
theorem PairedCoefficientTrivialUpperReselection.reselectedEdge_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : PairedCoefficientTrivialUpperReselection solution base pulled)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift input.generatedBaseRouteLiftData
      base.toUpperEdgeReselection edge).comp (solution.component j) =
      (solution.component i).comp
        (upperReselectedEdgeLift input.generatedPulledRouteLiftData
          pulled.toUpperEdgeReselection edge) := by
  unfold upperReselectedEdgeLift
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
theorem PairedCoefficientTrivialUpperReselection.reselectedPath_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : PairedCoefficientTrivialUpperReselection solution base pulled)
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

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
