import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredFullPairedTransport
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryPairedRestrictedOrbit

/-!
# Witness-bearing paired restricted points for G-115

A restricted point retains the actual solution, both actual reselections, and
their native four-conjunct paired proof.  Endpoint conjugation transports all
three data fields.  Raw cochains and existential suborbit membership are
therefore projections of a prior witness correspondence.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace UpperGeometryCompatibleProblemInputData

/-- An actual point of the canonical-authored paired restricted locus. -/
structure CanonicalAuthoredPairedRestrictedPoint
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) where
  solution : CanonicalUpperRefinementBCSolution input
  base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input
  pulled : CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input
  paired : CanonicalAuthoredPairedCoefficientTrivialUpperReselection
    solution base pulled

/-- An actual point of the generated paired restricted locus. -/
structure GeneratedPairedRestrictedPoint
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) where
  solution : GeometryCompatibleUpperRefinementBCSolution input
  base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input
  pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input
  paired : PairedCoefficientTrivialUpperReselection solution base pulled

/-- Transport a complete canonical-authored restricted point forward. -/
noncomputable def canonicalAuthoredPairedRestrictedPointForward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (point : CanonicalAuthoredPairedRestrictedPoint input) :
    GeneratedPairedRestrictedPoint input where
  solution := input.canonicalSolutionForward point.solution
  base := input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
    point.base
  pulled := input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
    point.pulled
  paired :=
    input.canonicalAuthoredPairedCoefficientTrivialUpperReselection_forward_transport
      point.paired

/-- Return a complete generated restricted point to the independently
authored canonical routes. -/
noncomputable def canonicalAuthoredPairedRestrictedPointBackward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (point : GeneratedPairedRestrictedPoint input) :
    CanonicalAuthoredPairedRestrictedPoint input where
  solution := input.generatedSolutionBackward point.solution
  base := input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
    point.base
  pulled := input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
    point.pulled
  paired :=
    input.canonicalAuthoredPairedCoefficientTrivialUpperReselection_backward_transport
      point.paired

/-- Backward after forward recovers the whole canonical-authored witness. -/
theorem canonicalAuthoredPairedRestrictedPointBackward_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (point : CanonicalAuthoredPairedRestrictedPoint input) :
    input.canonicalAuthoredPairedRestrictedPointBackward
        (input.canonicalAuthoredPairedRestrictedPointForward point) = point := by
  cases point
  simp only [canonicalAuthoredPairedRestrictedPointForward,
    canonicalAuthoredPairedRestrictedPointBackward,
    input.generatedSolutionBackward_canonicalSolutionForward,
    input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward_forward,
    input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward_forward]

/-- Forward after backward recovers the whole generated witness. -/
theorem canonicalAuthoredPairedRestrictedPointForward_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (point : GeneratedPairedRestrictedPoint input) :
    input.canonicalAuthoredPairedRestrictedPointForward
        (input.canonicalAuthoredPairedRestrictedPointBackward point) = point := by
  cases point
  simp only [canonicalAuthoredPairedRestrictedPointForward,
    canonicalAuthoredPairedRestrictedPointBackward,
    input.canonicalSolutionForward_generatedSolutionBackward,
    input.canonicalAuthoredBaseCoefficientTrivialReselectionForward_backward,
    input.canonicalAuthoredPulledCoefficientTrivialReselectionForward_backward]

/-- Endpoint conjugation gives an equivalence of the complete actual
witness-bearing paired restricted loci. -/
noncomputable def canonicalAuthoredGeneratedPairedRestrictedPointEquiv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    CanonicalAuthoredPairedRestrictedPoint input ≃
      GeneratedPairedRestrictedPoint input where
  toFun := input.canonicalAuthoredPairedRestrictedPointForward
  invFun := input.canonicalAuthoredPairedRestrictedPointBackward
  left_inv := input.canonicalAuthoredPairedRestrictedPointBackward_forward
  right_inv := input.canonicalAuthoredPairedRestrictedPointForward_backward

/-- The base raw cochain carried by a canonical-authored restricted point. -/
noncomputable def CanonicalAuthoredPairedRestrictedPoint.baseCochain
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (point : CanonicalAuthoredPairedRestrictedPoint input) :
    UpperDefectCochain input.canonicalAuthoredBaseRouteData :=
  upperRawDefectCochain input.canonicalAuthoredBaseRouteData
    point.base.toUpperEdgeReselection

/-- The pulled raw cochain carried by a canonical-authored restricted point. -/
noncomputable def CanonicalAuthoredPairedRestrictedPoint.pulledCochain
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (point : CanonicalAuthoredPairedRestrictedPoint input) :
    UpperDefectCochain input.canonicalAuthoredPulledRouteData :=
  upperRawDefectCochain input.canonicalAuthoredPulledRouteData
    point.pulled.toUpperEdgeReselection

/-- The base raw cochain carried by a generated restricted point. -/
noncomputable def GeneratedPairedRestrictedPoint.baseCochain
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (point : GeneratedPairedRestrictedPoint input) :
    UpperDefectCochain input.generatedBaseRouteData :=
  upperRawDefectCochain input.generatedBaseRouteData
    point.base.toUpperEdgeReselection

/-- The pulled raw cochain carried by a generated restricted point. -/
noncomputable def GeneratedPairedRestrictedPoint.pulledCochain
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (point : GeneratedPairedRestrictedPoint input) :
    UpperDefectCochain input.generatedPulledRouteData :=
  upperRawDefectCochain input.generatedPulledRouteData
    point.pulled.toUpperEdgeReselection

/-- Base cochain coordinates commute with transport of the retained point. -/
theorem canonicalAuthoredPairedRestrictedPoint_baseCochain_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (point : CanonicalAuthoredPairedRestrictedPoint input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt (P.twoTarget cell)
        (point.baseCochain cell) =
      (input.canonicalAuthoredPairedRestrictedPointForward point).baseCochain
        cell := by
  exact input.canonicalAuthoredBaseUpperRawDefectCochain_forward point.base cell

/-- Pulled cochain coordinates commute with transport of the retained point. -/
theorem canonicalAuthoredPairedRestrictedPoint_pulledCochain_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (point : CanonicalAuthoredPairedRestrictedPoint input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt (P.twoTarget cell)
        (point.pulledCochain cell) =
      (input.canonicalAuthoredPairedRestrictedPointForward point).pulledCochain
        cell := by
  exact input.canonicalAuthoredPulledUpperRawDefectCochain_forward
    point.pulled cell

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
