import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredCochainTransport
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFullPairedReselection

/-!
# Canonical-authored full paired upper reselections for G-115

This module defines the canonical-authored counterpart of the generated
four-conjunct paired relation.  Every conjunct is stated directly on the
independently constructed canonical-authored route objects; the relation is
not defined as the inverse image of the generated relation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-- Canonical-authored base and pulled reselections intertwine the actual
canonical solution component at every edge target. -/
def CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : CanonicalUpperRefinementBCSolution input)
    (base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (CompositeFiberAut.hom
      (base.toUpperEdgeReselection i j edge)).comp
        (solution.component j) =
      (solution.component j).comp
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge))

/-- Identity canonical-authored reselections satisfy endpoint
intertwining. -/
theorem canonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : CanonicalUpperRefinementBCSolution input) :
    CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
      solution
      (CoefficientTrivialUpperEdgeReselection.one
        input.canonicalAuthoredBaseRouteTransport)
      (CoefficientTrivialUpperEdgeReselection.one
        input.canonicalAuthoredPulledRouteTransport) := by
  intro i j edge
  change (GeometryTotalHom.id _).comp (solution.component j) =
    (solution.component j).comp (GeometryTotalHom.id _)
  exact (@Category.id_comp
    (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
    _ _ (solution.component j)).trans
      (@Category.comp_id
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (solution.component j)).symm

/-- Pointwise multiplication preserves canonical-authored endpoint
intertwining. -/
theorem CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : CanonicalUpperRefinementBCSolution input}
    {baseFirst baseSecond :
      CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulledFirst pulledSecond :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (first :
      CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
        solution baseFirst pulledFirst)
    (second :
      CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
        solution baseSecond pulledSecond) :
    CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
      solution
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
              (pulledFirst.toUpperEdgeReselection i j edge))) := by
      rw [first edge]
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
            (pulledFirst.toUpperEdgeReselection i j edge)) := by
      rw [second edge]
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

/-- Endpoint intertwining preserves each actual canonical-authored
reselected edge square. -/
theorem CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.reselectedEdge_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (paired :
      CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
        solution base pulled)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift input.canonicalAuthoredBaseRouteLiftData
      base.toUpperEdgeReselection edge).comp (solution.component j) =
      (solution.component i).comp
        (upperReselectedEdgeLift input.canonicalAuthoredPulledRouteLiftData
          pulled.toUpperEdgeReselection edge) := by
  rw [upperReselectedEdgeLift_eq_for_g115,
    upperReselectedEdgeLift_eq_for_g115]
  calc
    ((input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
        (CompositeFiberAut.hom
          (base.toUpperEdgeReselection i j edge))).comp
          (solution.component j) =
      (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
        ((CompositeFiberAut.hom
          (base.toUpperEdgeReselection i j edge)).comp
            (solution.component j)) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (input.canonicalAuthoredBaseRouteGeometryEdge edge)
        (CompositeFiberAut.hom
          (base.toUpperEdgeReselection i j edge))
        (solution.component j)
    _ = (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
        ((solution.component j).comp
          (CompositeFiberAut.hom
            (pulled.toUpperEdgeReselection i j edge))) := by
      rw [paired edge]
    _ = ((input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
          (solution.component j)).comp
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge)) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (input.canonicalAuthoredBaseRouteGeometryEdge edge)
        (solution.component j)
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge))).symm
    _ = ((solution.component i).comp
          (input.canonicalAuthoredPulledRouteGeometryEdge edge)).comp
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge)) := by
      rw [solution.edge_naturality edge]
    _ = (solution.component i).comp
        ((input.canonicalAuthoredPulledRouteGeometryEdge edge).comp
          (CompositeFiberAut.hom
            (pulled.toUpperEdgeReselection i j edge))) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (solution.component i)
        (input.canonicalAuthoredPulledRouteGeometryEdge edge)
        (CompositeFiberAut.hom
          (pulled.toUpperEdgeReselection i j edge))

/-- Canonical-authored endpoint intertwining extends to every reselected
path. -/
theorem CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.reselectedPath_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (paired :
      CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
        solution base pulled)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
      base.toUpperEdgeReselection path).comp (solution.component j) =
      (solution.component i).comp
        (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
          pulled.toUpperEdgeReselection path) := by
  induction path with
  | nil vertex =>
      rw [upperReselectedPathLift_nil_for_g115,
        upperReselectedPathLift_nil_for_g115]
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (solution.component vertex)).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ (solution.component vertex)).symm
  | @cons source middle target edge tail inductionHypothesis =>
      rw [upperReselectedPathLift_cons_for_g115,
        upperReselectedPathLift_cons_for_g115]
      calc
        _ = (upperReselectedEdgeLift
              input.canonicalAuthoredBaseRouteLiftData
              base.toUpperEdgeReselection edge).comp
            ((upperReselectedPathLift
              input.canonicalAuthoredBaseRouteLiftData
              base.toUpperEdgeReselection tail).comp
                (solution.component target)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _
            (upperReselectedEdgeLift
              input.canonicalAuthoredBaseRouteLiftData
              base.toUpperEdgeReselection edge)
            (upperReselectedPathLift
              input.canonicalAuthoredBaseRouteLiftData
              base.toUpperEdgeReselection tail)
            (solution.component target)
        _ = (upperReselectedEdgeLift
              input.canonicalAuthoredBaseRouteLiftData
              base.toUpperEdgeReselection edge).comp
            ((solution.component middle).comp
              (upperReselectedPathLift
                input.canonicalAuthoredPulledRouteLiftData
                pulled.toUpperEdgeReselection tail)) := by
          rw [inductionHypothesis]
        _ = ((upperReselectedEdgeLift
                input.canonicalAuthoredBaseRouteLiftData
                base.toUpperEdgeReselection edge).comp
              (solution.component middle)).comp
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              pulled.toUpperEdgeReselection tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _
            (upperReselectedEdgeLift
              input.canonicalAuthoredBaseRouteLiftData
              base.toUpperEdgeReselection edge)
            (solution.component middle)
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              pulled.toUpperEdgeReselection tail)).symm
        _ = ((solution.component source).comp
              (upperReselectedEdgeLift
                input.canonicalAuthoredPulledRouteLiftData
                pulled.toUpperEdgeReselection edge)).comp
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              pulled.toUpperEdgeReselection tail) := by
          rw [paired.reselectedEdge_naturality edge]
        _ = _ :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (solution.component source)
            (upperReselectedEdgeLift
              input.canonicalAuthoredPulledRouteLiftData
              pulled.toUpperEdgeReselection edge)
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              pulled.toUpperEdgeReselection tail)

/-- The canonical solution triangle whiskered by an actual
canonical-authored reselected path. -/
def CanonicalAuthoredReselectedPathLegTriangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : CanonicalUpperRefinementBCSolution input)
    (base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  ∀ {i j : P.Vertex} (path : P.Path i j),
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
            base.toUpperEdgeReselection path))
        (input.canonicalAuthoredBaseRouteGeometryHomAt j) =
      RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map (solution.component i))
        (RefinementGeometryHom.comp
          ((exactGeometryToRefinementGeometry U).map
            (upperReselectedPathLift
              input.canonicalAuthoredPulledRouteLiftData
              pulled.toUpperEdgeReselection path))
          (input.canonicalAuthoredPulledRouteGeometryHomAt j))

/-- Endpoint intertwining and the canonical solution triangle generate the
canonical-authored path-leg triangle. -/
theorem CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.reselectedPath_legTriangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (paired :
      CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
        solution base pulled) :
    CanonicalAuthoredReselectedPathLegTriangle solution base pulled := by
  intro i j path
  have pathNaturality := congrArg
    (fun hom => (exactGeometryToRefinementGeometry U).map hom)
    (paired.reselectedPath_naturality path)
  have mappedPathNaturality :
      ((exactGeometryToRefinementGeometry U).map
        (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
          base.toUpperEdgeReselection path)) ≫
        ((exactGeometryToRefinementGeometry U).map (solution.component j)) =
      ((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift
            input.canonicalAuthoredPulledRouteLiftData
            pulled.toUpperEdgeReselection path)) := by
    simpa only [Functor.map_comp] using pathNaturality
  change
    ((exactGeometryToRefinementGeometry U).map
      (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
        base.toUpperEdgeReselection path)) ≫
        input.canonicalAuthoredBaseRouteGeometryHomAt j =
      ((exactGeometryToRefinementGeometry U).map (solution.component i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift
            input.canonicalAuthoredPulledRouteLiftData
            pulled.toUpperEdgeReselection path)) ≫
          input.canonicalAuthoredPulledRouteGeometryHomAt j
  calc
    _ = ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
            base.toUpperEdgeReselection path)) ≫
        (((exactGeometryToRefinementGeometry U).map
          (solution.component j)) ≫
            input.canonicalAuthoredPulledRouteGeometryHomAt j) := by
      exact congrArg
        (fun leg => ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
            base.toUpperEdgeReselection path)) ≫ leg)
        (solution.triangle j).symm
    _ = ((((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
            base.toUpperEdgeReselection path)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (solution.component j))) ≫
            input.canonicalAuthoredPulledRouteGeometryHomAt j) := by
      simp only [Category.assoc]
    _ = ((((exactGeometryToRefinementGeometry U).map
          (solution.component i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (upperReselectedPathLift
            input.canonicalAuthoredPulledRouteLiftData
            pulled.toUpperEdgeReselection path))) ≫
              input.canonicalAuthoredPulledRouteGeometryHomAt j) := by
      rw [mappedPathNaturality]
    _ = _ := by simp only [Category.assoc]

/-- Pasting a canonical-authored reselected left path with the literal
canonical-authored comparator commutes with the canonical solution. -/
def CanonicalAuthoredReselectedAuthoredComparatorPasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : CanonicalUpperRefinementBCSolution input)
    (base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  ∀ cell : P.TwoCell,
    ((upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
        base.toUpperEdgeReselection (P.twoLeft cell)).comp
      (input.canonicalAuthoredBaseRouteComparator cell)).comp
        (solution.component (P.twoTarget cell)) =
      (solution.component (P.twoSource cell)).comp
        ((upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
          pulled.toUpperEdgeReselection (P.twoLeft cell)).comp
            (input.canonicalAuthoredPulledRouteComparator cell))

/-- Endpoint intertwining and literal canonical-authored comparator
intertwining generate reselected comparator pasting. -/
theorem CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.reselectedAuthoredComparator_pasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (paired :
      CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
        solution base pulled) :
    CanonicalAuthoredReselectedAuthoredComparatorPasting
      solution base pulled := by
  intro cell
  let baseLeft := upperReselectedPathLift
    input.canonicalAuthoredBaseRouteLiftData base.toUpperEdgeReselection
      (P.twoLeft cell)
  let pulledLeft := upperReselectedPathLift
    input.canonicalAuthoredPulledRouteLiftData pulled.toUpperEdgeReselection
      (P.twoLeft cell)
  let baseComparator := input.canonicalAuthoredBaseRouteComparator cell
  let pulledComparator := input.canonicalAuthoredPulledRouteComparator cell
  change ((baseLeft.comp baseComparator).comp
      (solution.component (P.twoTarget cell))) =
    (solution.component (P.twoSource cell)).comp
      (pulledLeft.comp pulledComparator)
  calc
    _ = baseLeft.comp (baseComparator.comp
        (solution.component (P.twoTarget cell))) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ baseLeft baseComparator
        (solution.component (P.twoTarget cell))
    _ = baseLeft.comp ((solution.component (P.twoTarget cell)).comp
        pulledComparator) := by
      rw [solution.comparator_intertwining cell]
    _ = (baseLeft.comp (solution.component (P.twoTarget cell))).comp
        pulledComparator :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ baseLeft (solution.component (P.twoTarget cell))
        pulledComparator).symm
    _ = ((solution.component (P.twoSource cell)).comp pulledLeft).comp
        pulledComparator := by
      rw [paired.reselectedPath_naturality (P.twoLeft cell)]
    _ = _ :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (solution.component (P.twoSource cell)) pulledLeft
        pulledComparator

/-- Both canonical-authored raw-cochain square composites fix the coefficient
ring pointwise. -/
def CanonicalAuthoredRawCochainComponentCoefficientTrivial
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : CanonicalUpperRefinementBCSolution input)
    (base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  ∀ cell : P.TwoCell,
    (((CompositeFiberAut.hom
      (upperRawDefectCochain input.canonicalAuthoredBaseRouteData
        base.toUpperEdgeReselection cell)).comp
          (solution.component (P.twoTarget cell))).geometry.coefficientHom =
        RingHom.id k) ∧
    (((solution.component (P.twoTarget cell)).comp
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.canonicalAuthoredPulledRouteData
          pulled.toUpperEdgeReselection cell))).geometry.coefficientHom =
        RingHom.id k)

/-- The native canonical-authored four-conjunct paired relation. -/
def CanonicalAuthoredPairedCoefficientTrivialUpperReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : CanonicalUpperRefinementBCSolution input)
    (base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input) :
    Prop :=
  CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
      solution base pulled ∧
  CanonicalAuthoredReselectedPathLegTriangle solution base pulled ∧
  CanonicalAuthoredReselectedAuthoredComparatorPasting solution base pulled ∧
  CanonicalAuthoredRawCochainComponentCoefficientTrivial solution base pulled

/-- The canonical-authored endpoint relation generates every conjunct of the
native full pair from the actual solution and route laws. -/
theorem CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.toPaired
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (endpoint :
      CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining
        solution base pulled) :
    CanonicalAuthoredPairedCoefficientTrivialUpperReselection
      solution base pulled := by
  refine ⟨endpoint, endpoint.reselectedPath_legTriangle,
    endpoint.reselectedAuthoredComparator_pasting, ?_⟩
  intro cell
  have baseRaw := base.upperRawDefectCochain_coefficient_id cell
  have pulledRaw := pulled.upperRawDefectCochain_coefficient_id cell
  have baseRaw' :
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.canonicalAuthoredBaseRouteData
          base.toUpperEdgeReselection cell)).geometry.coefficientHom =
        RingHom.id k := by
    simpa only [input.canonicalAuthoredBaseRouteTransport_toTwoLayerTransportData]
      using baseRaw
  have pulledRaw' :
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.canonicalAuthoredPulledRouteData
          pulled.toUpperEdgeReselection cell)).geometry.coefficientHom =
        RingHom.id k := by
    simpa only [input.canonicalAuthoredPulledRouteTransport_toTwoLayerTransportData]
      using pulledRaw
  constructor
  · change
      (solution.component
        (P.twoTarget cell)).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain input.canonicalAuthoredBaseRouteData
            base.toUpperEdgeReselection cell)).geometry.coefficientHom =
          RingHom.id k
    rw [solution.component_coefficient_id, baseRaw']
    exact RingHom.id_comp _
  · change
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.canonicalAuthoredPulledRouteData
          pulled.toUpperEdgeReselection cell)).geometry.coefficientHom.comp
        (solution.component
          (P.twoTarget cell)).geometry.coefficientHom = RingHom.id k
    rw [pulledRaw', solution.component_coefficient_id]
    exact RingHom.id_comp _

/-- The identity canonical-authored pair is a full pair. -/
theorem canonicalAuthoredPairedCoefficientTrivialUpperReselection_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : CanonicalUpperRefinementBCSolution input) :
    CanonicalAuthoredPairedCoefficientTrivialUpperReselection solution
      (CoefficientTrivialUpperEdgeReselection.one
        input.canonicalAuthoredBaseRouteTransport)
      (CoefficientTrivialUpperEdgeReselection.one
        input.canonicalAuthoredPulledRouteTransport) :=
  CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.toPaired
    (canonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining_one
      solution)

/-- Pointwise multiplication preserves the full canonical-authored paired
relation. -/
theorem CanonicalAuthoredPairedCoefficientTrivialUpperReselection.mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : CanonicalUpperRefinementBCSolution input}
    {baseFirst baseSecond :
      CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulledFirst pulledSecond :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (first : CanonicalAuthoredPairedCoefficientTrivialUpperReselection
      solution baseFirst pulledFirst)
    (second : CanonicalAuthoredPairedCoefficientTrivialUpperReselection
      solution baseSecond pulledSecond) :
    CanonicalAuthoredPairedCoefficientTrivialUpperReselection solution
      (CoefficientTrivialUpperEdgeReselection.mul baseFirst baseSecond)
      (CoefficientTrivialUpperEdgeReselection.mul pulledFirst pulledSecond) :=
  CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.toPaired
    (CanonicalAuthoredCoefficientTrivialUpperReselectionEndpointIntertwining.mul
      first.1 second.1)

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
