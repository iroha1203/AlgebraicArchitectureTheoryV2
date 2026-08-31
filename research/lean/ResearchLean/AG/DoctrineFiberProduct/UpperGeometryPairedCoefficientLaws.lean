import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryPairedRawCochainIntertwining

/-!
# Coefficient laws for paired upper raw cochains

This module records the coefficient component of the actual G-115 paired
raw-cochain square.  Coefficient-trivial edge reselections propagate through
actual reselected paths and their canonical two-cell comparators.  Combining
those laws with the authored route-comparator coefficient laws shows that the
actual raw defects fix the common coefficient ring.  The generated solution's
coefficient law then proves that both composites in the raw-cochain square
also fix the coefficient ring.

## Implementation notes

The proofs use the existing G-109 edge, path, canonical-comparator, and raw
cochain constructions directly.  No coefficient certificate is added to the
paired endpoint relation, and no conclusion is obtained merely by projecting
the raw-cochain intertwining equality.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace CoefficientTrivialUpperEdgeReselection

/-- A coefficient-trivial reselection keeps the coefficient component of each
actual reselected edge equal to the identity.  This consumes both the route
edge coefficient law and the selected target automorphism's coefficient law. -/
theorem upperReselectedEdgeLift_coefficient_id
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    (reselection : CoefficientTrivialUpperEdgeReselection data)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift data.toTwoLayerLiftData
      reselection.toUpperEdgeReselection edge).geometry.coefficientHom =
        RingHom.id k := by
  rw [upperReselectedEdgeLift_eq_for_g115]
  change
    (CompositeFiberAut.hom
      (reselection.toUpperEdgeReselection i j edge)).geometry.coefficientHom.comp
      (data.edgeLift edge).geometry.coefficientHom = RingHom.id k
  rw [reselection.coefficient_id edge, data.edge_coefficient_id edge]
  exact RingHom.id_comp _

/-- Coefficient identity propagates from the actual reselected generators to
every actual reselected path. -/
theorem upperReselectedPathLift_coefficient_id
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    (reselection : CoefficientTrivialUpperEdgeReselection data)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift data.toTwoLayerLiftData
      reselection.toUpperEdgeReselection path).geometry.coefficientHom =
        RingHom.id k := by
  induction path with
  | nil vertex =>
      rw [upperReselectedPathLift_nil_for_g115]
      rfl
  | @cons source middle target edge tail inductionHypothesis =>
      rw [upperReselectedPathLift_cons_for_g115]
      change
        (upperReselectedPathLift data.toTwoLayerLiftData
          reselection.toUpperEdgeReselection tail).geometry.coefficientHom.comp
          (upperReselectedEdgeLift data.toTwoLayerLiftData
            reselection.toUpperEdgeReselection edge).geometry.coefficientHom =
          RingHom.id k
      rw [inductionHypothesis,
        reselection.upperReselectedEdgeLift_coefficient_id edge]
      exact RingHom.id_comp _

/-- The actual canonical two-cell comparator generated from a
coefficient-trivial reselection fixes the common coefficient ring. -/
theorem upperCanonicalTwoCellComparator_coefficient_id
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    (reselection : CoefficientTrivialUpperEdgeReselection data)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (upperCanonicalTwoCellComparator data.toTwoLayerTransportData
        reselection.toUpperEdgeReselection cell)).geometry.coefficientHom =
        RingHom.id k := by
  have factorization := congrArg
    (fun hom => hom.geometry.coefficientHom)
    (upperCanonicalTwoCellComparator_fac data.toTwoLayerTransportData
      reselection.toUpperEdgeReselection cell)
  change
    (CompositeFiberAut.hom
      (upperCanonicalTwoCellComparator data.toTwoLayerTransportData
        reselection.toUpperEdgeReselection cell)).geometry.coefficientHom.comp
      (upperReselectedPathLift data.toTwoLayerLiftData
        reselection.toUpperEdgeReselection
        (P.twoLeft cell)).geometry.coefficientHom =
    (upperReselectedPathLift data.toTwoLayerLiftData
      reselection.toUpperEdgeReselection
      (P.twoRight cell)).geometry.coefficientHom at factorization
  rw [reselection.upperReselectedPathLift_coefficient_id,
    reselection.upperReselectedPathLift_coefficient_id] at factorization
  have coefficient_comp_id :
      (CompositeFiberAut.hom
        (upperCanonicalTwoCellComparator data.toTwoLayerTransportData
          reselection.toUpperEdgeReselection cell)).geometry.coefficientHom.comp
          (RingHom.id k) =
        (CompositeFiberAut.hom
          (upperCanonicalTwoCellComparator data.toTwoLayerTransportData
            reselection.toUpperEdgeReselection cell)).geometry.coefficientHom := by
    ext value
    rfl
  rw [coefficient_comp_id] at factorization
  exact factorization

/-- The inverse of the actual canonical two-cell comparator generated from a
coefficient-trivial reselection also fixes the common coefficient ring. -/
theorem upperCanonicalTwoCellComparator_inv_coefficient_id
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    (reselection : CoefficientTrivialUpperEdgeReselection data)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (upperCanonicalTwoCellComparator data.toTwoLayerTransportData
        reselection.toUpperEdgeReselection cell)⁻¹).geometry.coefficientHom =
        RingHom.id k := by
  let canonical := upperCanonicalTwoCellComparator
    data.toTwoLayerTransportData reselection.toUpperEdgeReselection cell
  have cancellation := congrArg
    (fun hom => hom.geometry.coefficientHom) canonical.1.inv_hom_id
  change
    (CompositeFiberAut.hom canonical).geometry.coefficientHom.comp
      (CompositeFiberAut.hom canonical⁻¹).geometry.coefficientHom =
        RingHom.id k at cancellation
  rw [reselection.upperCanonicalTwoCellComparator_coefficient_id cell]
    at cancellation
  have id_comp_coefficient :
      (RingHom.id k).comp
          (CompositeFiberAut.hom canonical⁻¹).geometry.coefficientHom =
        (CompositeFiberAut.hom canonical⁻¹).geometry.coefficientHom := by
    ext value
    rfl
  rw [id_comp_coefficient] at cancellation
  simpa only [canonical] using cancellation

/-- The actual G-109 raw defect generated from a coefficient-trivial
reselection fixes the common coefficient ring.  The proof separately consumes
the route's authored-comparator coefficient law and the generated canonical
comparator's inverse coefficient law. -/
theorem upperRawDefectCochain_coefficient_id
    {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {diagram : PresentedPathCategory P ⥤ CoreFiber X}
    {k : Type v} [CommRing k]
    {geometry : (i : P.Vertex) →
      FixedCoefficientGeometryAt (diagram.obj ⟨i⟩).1 k}
    {data : FixedCoefficientTwoLayerTransportOver P diagram k geometry}
    (reselection : CoefficientTrivialUpperEdgeReselection data)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (upperRawDefectCochain data.toTwoLayerTransportData
        reselection.toUpperEdgeReselection cell)).geometry.coefficientHom =
        RingHom.id k := by
  simp only [upperRawDefectCochain, upperRawTwoCellDefect,
    compositeFiberAut_hom_mul]
  change
    (CompositeFiberAut.hom
      (data.comparator cell)).geometry.coefficientHom.comp
      (CompositeFiberAut.hom
        (upperCanonicalTwoCellComparator data.toTwoLayerTransportData
          reselection.toUpperEdgeReselection cell)⁻¹).geometry.coefficientHom =
      RingHom.id k
  rw [data.comparator_coefficient_id,
    reselection.upperCanonicalTwoCellComparator_inv_coefficient_id cell]
  exact RingHom.id_comp _

end CoefficientTrivialUpperEdgeReselection

namespace UpperGeometryCompatibleProblemInputData

/-- Both composites in the generated actual raw-cochain/component square fix
the common coefficient ring.  The base and pulled proofs use their respective
coefficient-trivial reselections and generated route comparator laws; both
then consume the actual solution component's coefficient law. -/
theorem upperRawDefectCochain_component_square_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    (((CompositeFiberAut.hom
      (upperRawDefectCochain input.generatedBaseRouteData
        base.toUpperEdgeReselection cell)).comp
          (solution.component (P.twoTarget cell))).geometry.coefficientHom =
        RingHom.id k) ∧
    (((solution.component (P.twoTarget cell)).comp
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.generatedPulledRouteData
          pulled.toUpperEdgeReselection cell))).geometry.coefficientHom =
        RingHom.id k) := by
  have baseRaw :
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.generatedBaseRouteData
          base.toUpperEdgeReselection cell)).geometry.coefficientHom =
        RingHom.id k := by
    simpa only [generatedBaseRouteData] using
      base.upperRawDefectCochain_coefficient_id cell
  have pulledRaw :
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.generatedPulledRouteData
          pulled.toUpperEdgeReselection cell)).geometry.coefficientHom =
        RingHom.id k := by
    simpa only [generatedPulledRouteData] using
      pulled.upperRawDefectCochain_coefficient_id cell
  constructor
  · change
      (solution.component
        (P.twoTarget cell)).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain input.generatedBaseRouteData
            base.toUpperEdgeReselection cell)).geometry.coefficientHom =
          RingHom.id k
    rw [solution.component_coefficient_id, baseRaw]
    exact RingHom.id_comp _
  · change
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.generatedPulledRouteData
          pulled.toUpperEdgeReselection cell)).geometry.coefficientHom.comp
        (solution.component
          (P.twoTarget cell)).geometry.coefficientHom = RingHom.id k
    rw [pulledRaw, solution.component_coefficient_id]
    exact RingHom.id_comp _

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
