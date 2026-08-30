import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleComparatorMapLaws

/-!
# Finite compatible comparator families

This module applies the two G-115-local Cartesian pullback homomorphisms to the
single authored comparator family in the source transport.  It thereby
constructs the base-first and pulled-first comparator families without adding
either family to the compatible input.  Their factorization laws explicitly
show that the authored source comparator is consumed at every two-cell.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- Base-first comparator family obtained by Cartesian pullback of the single
authored source comparator family. -/
noncomputable def generatedBaseRouteComparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    CompositeFiberAut
      (input.generatedBaseRouteGeometryAt (P.twoTarget cell)) :=
  input.generatedBaseCompositeFiberAutHomAt (P.twoTarget cell)
    (input.sourceTransport.comparator cell)

/-- Pulled-first comparator family obtained independently from the same source
comparator family. -/
noncomputable def generatedPulledRouteComparator
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    CompositeFiberAut
      (input.generatedPulledRouteGeometryAt (P.twoTarget cell)) :=
  input.generatedPulledCompositeFiberAutHomAt (P.twoTarget cell)
    (input.sourceTransport.comparator cell)

/-- Normalize the base-first finite comparator to the pointwise generated
Cartesian pullback. -/
@[simp] theorem generatedBaseRouteComparator_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.generatedBaseRouteComparator cell =
      input.generatedBaseCompositeFiberAutAt (P.twoTarget cell)
        (input.sourceTransport.comparator cell) := rfl

/-- Normalize the pulled-first finite comparator to the pointwise generated
Cartesian pullback. -/
@[simp] theorem generatedPulledRouteComparator_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.generatedPulledRouteComparator cell =
      input.generatedPulledCompositeFiberAutAt (P.twoTarget cell)
        (input.sourceTransport.comparator cell) := rfl

/-- The base-first finite comparator factors its literal generated route leg
through the authored source comparator at the same two-cell. -/
theorem generatedBaseRouteComparator_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedBaseRouteComparator cell))).comp
        (input.generatedBaseRouteLegAt (P.twoTarget cell)) =
      (input.generatedBaseRouteLegAt (P.twoTarget cell)).comp
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.sourceTransport.comparator cell))) := by
  rw [input.generatedBaseRouteComparator_apply]
  exact input.generatedBaseCompositeFiberAutAt_fac
    (P.twoTarget cell) (input.sourceTransport.comparator cell)

/-- The pulled-first finite comparator factors its literal generated route leg
through the same authored source comparator at the same two-cell. -/
theorem generatedPulledRouteComparator_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedPulledRouteComparator cell))).comp
        (input.generatedPulledRouteLegAt (P.twoTarget cell)) =
      (input.generatedPulledRouteLegAt (P.twoTarget cell)).comp
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.sourceTransport.comparator cell))) := by
  rw [input.generatedPulledRouteComparator_apply]
  exact input.generatedPulledCompositeFiberAutAt_fac
    (P.twoTarget cell) (input.sourceTransport.comparator cell)

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
