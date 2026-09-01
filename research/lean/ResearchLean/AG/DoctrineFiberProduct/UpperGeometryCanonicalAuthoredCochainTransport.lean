import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredTransportLaws
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredReselectedPathTransport

/-!
# Canonical-authored comparator and cochain transport

This module transports the literal authored comparator, the canonical
reselected comparator, and hence the raw defect cochain between the actual
canonical-authored and generated routes.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace CompositeFiberAut

/-- An intertwining square identifies the conjugate of a composite-fiber
automorphism without requiring a caller-supplied equality in the target
subgroup. -/
theorem conjugationEquiv_eq_of_intertwining
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (source : CompositeFiberAut G)
    (target : CompositeFiberAut H)
    (intertwining :
      (CompositeFiberAut.hom source).comp iso.hom =
        iso.hom.comp (CompositeFiberAut.hom target)) :
    conjugationEquiv iso source = target := by
  apply Subtype.ext
  apply Iso.ext
  change ((iso.inv.comp (CompositeFiberAut.hom source)).comp iso.hom) =
    CompositeFiberAut.hom target
  calc
    ((iso.inv.comp (CompositeFiberAut.hom source)).comp iso.hom) =
        iso.inv.comp
          ((CompositeFiberAut.hom source).comp iso.hom) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ iso.inv (CompositeFiberAut.hom source) iso.hom
    _ = iso.inv.comp
        (iso.hom.comp (CompositeFiberAut.hom target)) :=
      congrArg (fun hom => iso.inv.comp hom) intertwining
    _ = CompositeFiberAut.hom target :=
      iso.inv_hom_id_assoc (CompositeFiberAut.hom target)

end CompositeFiberAut

/-- If two parallel factors are transported by endpoint isomorphisms, the
conjugate of an endomorphism relating them relates their transported factors. -/
theorem conjugatedFactorization
    {C : Type u} [Category.{v} C]
    {source target source' target' : C}
    (sourceIso : source ≅ source') (targetIso : target ≅ target')
    (left right : source ⟶ target) (left' right' : source' ⟶ target')
    (automorphism : target ⟶ target)
    (leftNaturality : left ≫ targetIso.hom = sourceIso.hom ≫ left')
    (rightNaturality : right ≫ targetIso.hom = sourceIso.hom ≫ right')
    (factorization : left ≫ automorphism = right) :
    left' ≫ ((targetIso.inv ≫ automorphism) ≫ targetIso.hom) = right' := by
  have leftInverse := inverseNaturality_of_naturality sourceIso targetIso
    left left' leftNaturality
  calc
    left' ≫ ((targetIso.inv ≫ automorphism) ≫ targetIso.hom) =
        ((left' ≫ targetIso.inv) ≫ automorphism) ≫ targetIso.hom := by
      simp only [Category.assoc]
    _ = ((sourceIso.inv ≫ left) ≫ automorphism) ≫ targetIso.hom := by
      rw [leftInverse]
    _ = (sourceIso.inv ≫ (left ≫ automorphism)) ≫ targetIso.hom := by
      simp only [Category.assoc]
    _ = (sourceIso.inv ≫ right) ≫ targetIso.hom := by
      rw [factorization]
    _ = sourceIso.inv ≫ (right ≫ targetIso.hom) :=
      Category.assoc _ _ _
    _ = sourceIso.inv ≫ (sourceIso.hom ≫ right') := by
      rw [rightNaturality]
    _ = right' := sourceIso.inv_hom_id_assoc right'

namespace UpperGeometryCompatibleProblemInputData

/-- Forward exact conjugation sends the literal canonical-authored base
comparator wrapper to the generated base comparator. -/
theorem canonicalAuthoredBaseRouteFixedComparator_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt (P.twoTarget cell)
        (input.canonicalAuthoredBaseRouteFixedComparator cell) =
      input.generatedBaseRouteComparator cell := by
  exact CompositeFiberAut.conjugationEquiv_eq_of_intertwining
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
      (P.twoTarget cell))
    (input.canonicalAuthoredBaseRouteFixedComparator cell)
    (input.generatedBaseRouteComparator cell)
    (input.canonicalAuthoredBaseRouteComparator_exact_conjugation cell)

/-- Forward exact conjugation sends the literal canonical-authored pulled
comparator wrapper to the generated pulled comparator. -/
theorem canonicalAuthoredPulledRouteFixedComparator_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt (P.twoTarget cell)
        (input.canonicalAuthoredPulledRouteFixedComparator cell) =
      input.generatedPulledRouteComparator cell := by
  exact CompositeFiberAut.conjugationEquiv_eq_of_intertwining
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
      (P.twoTarget cell))
    (input.canonicalAuthoredPulledRouteFixedComparator cell)
    (input.generatedPulledRouteComparator cell)
    (input.canonicalAuthoredPulledRouteComparator_exact_conjugation cell)

/-- Inverse exact conjugation returns the generated base comparator to the
literal canonical-authored wrapper. -/
theorem canonicalAuthoredBaseRouteFixedComparator_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.canonicalAuthoredBaseCompositeFiberAutBackwardAt (P.twoTarget cell)
        (input.generatedBaseRouteComparator cell) =
      input.canonicalAuthoredBaseRouteFixedComparator cell := by
  rw [← input.canonicalAuthoredBaseRouteFixedComparator_forward cell]
  exact input.canonicalAuthoredBaseCompositeFiberAutBackwardAt_forward
    (P.twoTarget cell) (input.canonicalAuthoredBaseRouteFixedComparator cell)

/-- Inverse exact conjugation returns the generated pulled comparator to the
literal canonical-authored wrapper. -/
theorem canonicalAuthoredPulledRouteFixedComparator_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (cell : P.TwoCell) :
    input.canonicalAuthoredPulledCompositeFiberAutBackwardAt (P.twoTarget cell)
        (input.generatedPulledRouteComparator cell) =
      input.canonicalAuthoredPulledRouteFixedComparator cell := by
  rw [← input.canonicalAuthoredPulledRouteFixedComparator_forward cell]
  exact input.canonicalAuthoredPulledCompositeFiberAutBackwardAt_forward
    (P.twoTarget cell) (input.canonicalAuthoredPulledRouteFixedComparator cell)

/-- Forward exact conjugation carries the canonical comparator generated by a
canonical-authored base reselection to the canonical comparator generated by
its transported reselection. -/
theorem canonicalAuthoredBaseUpperCanonicalTwoCellComparator_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt (P.twoTarget cell)
        (upperCanonicalTwoCellComparator input.canonicalAuthoredBaseRouteData
          reselection.toUpperEdgeReselection cell) =
      upperCanonicalTwoCellComparator input.generatedBaseRouteData
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
          reselection).toUpperEdgeReselection cell := by
  let generatedReselection :=
    (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
      reselection).toUpperEdgeReselection
  let generatedLeft := upperReselectedPathLift input.generatedBaseRouteLiftData
    generatedReselection (P.twoLeft cell)
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      generatedLeft.base.base generatedLeft :=
    (upperReselectLiftData input.generatedBaseRouteLiftData
      generatedReselection).pathLift_compositeStrong (P.twoLeft cell)
  apply CompositeFiberAut.ext_of_strong_fac generatedLeft
  change
    (upperReselectedPathLift input.generatedBaseRouteLiftData
      generatedReselection (P.twoLeft cell)).comp
        (CompositeFiberAut.hom
          (input.canonicalAuthoredBaseCompositeFiberAutForwardAt
            (P.twoTarget cell)
            (upperCanonicalTwoCellComparator
              input.canonicalAuthoredBaseRouteData
              reselection.toUpperEdgeReselection cell))) =
      (upperReselectedPathLift input.generatedBaseRouteLiftData
        generatedReselection (P.twoLeft cell)).comp
          (CompositeFiberAut.hom
            (upperCanonicalTwoCellComparator input.generatedBaseRouteData
              generatedReselection cell))
  have generatedFac := upperCanonicalTwoCellComparator_fac
    input.generatedBaseRouteData generatedReselection cell
  change
    (upperReselectedPathLift input.generatedBaseRouteLiftData
      generatedReselection (P.twoLeft cell)).comp
        (CompositeFiberAut.hom
          (upperCanonicalTwoCellComparator input.generatedBaseRouteData
            generatedReselection cell)) =
      upperReselectedPathLift input.generatedBaseRouteLiftData
        generatedReselection (P.twoRight cell) at generatedFac
  rw [generatedFac,
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt_hom]
  exact conjugatedFactorization
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
      (P.twoSource cell))
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
      (P.twoTarget cell))
    (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
      reselection.toUpperEdgeReselection (P.twoLeft cell))
    (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
      reselection.toUpperEdgeReselection (P.twoRight cell))
    generatedLeft
    (upperReselectedPathLift input.generatedBaseRouteLiftData
      generatedReselection (P.twoRight cell))
    (CompositeFiberAut.hom
      (upperCanonicalTwoCellComparator input.canonicalAuthoredBaseRouteData
        reselection.toUpperEdgeReselection cell))
    (input.canonicalAuthoredBaseReselectedPath_forward_naturality
      reselection (P.twoLeft cell))
    (input.canonicalAuthoredBaseReselectedPath_forward_naturality
      reselection (P.twoRight cell))
    (upperCanonicalTwoCellComparator_fac input.canonicalAuthoredBaseRouteData
      reselection.toUpperEdgeReselection cell)

/-- Forward exact conjugation carries the canonical comparator generated by a
canonical-authored pulled reselection to the canonical comparator generated by
its transported reselection. -/
theorem canonicalAuthoredPulledUpperCanonicalTwoCellComparator_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt (P.twoTarget cell)
        (upperCanonicalTwoCellComparator input.canonicalAuthoredPulledRouteData
          reselection.toUpperEdgeReselection cell) =
      upperCanonicalTwoCellComparator input.generatedPulledRouteData
        (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
          reselection).toUpperEdgeReselection cell := by
  let generatedReselection :=
    (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
      reselection).toUpperEdgeReselection
  let generatedLeft := upperReselectedPathLift input.generatedPulledRouteLiftData
    generatedReselection (P.twoLeft cell)
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      generatedLeft.base.base generatedLeft :=
    (upperReselectLiftData input.generatedPulledRouteLiftData
      generatedReselection).pathLift_compositeStrong (P.twoLeft cell)
  apply CompositeFiberAut.ext_of_strong_fac generatedLeft
  change
    (upperReselectedPathLift input.generatedPulledRouteLiftData
      generatedReselection (P.twoLeft cell)).comp
        (CompositeFiberAut.hom
          (input.canonicalAuthoredPulledCompositeFiberAutForwardAt
            (P.twoTarget cell)
            (upperCanonicalTwoCellComparator
              input.canonicalAuthoredPulledRouteData
              reselection.toUpperEdgeReselection cell))) =
      (upperReselectedPathLift input.generatedPulledRouteLiftData
        generatedReselection (P.twoLeft cell)).comp
          (CompositeFiberAut.hom
            (upperCanonicalTwoCellComparator input.generatedPulledRouteData
              generatedReselection cell))
  have generatedFac := upperCanonicalTwoCellComparator_fac
    input.generatedPulledRouteData generatedReselection cell
  change
    (upperReselectedPathLift input.generatedPulledRouteLiftData
      generatedReselection (P.twoLeft cell)).comp
        (CompositeFiberAut.hom
          (upperCanonicalTwoCellComparator input.generatedPulledRouteData
            generatedReselection cell)) =
      upperReselectedPathLift input.generatedPulledRouteLiftData
        generatedReselection (P.twoRight cell) at generatedFac
  rw [generatedFac,
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt_hom]
  exact conjugatedFactorization
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
      (P.twoSource cell))
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
      (P.twoTarget cell))
    (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
      reselection.toUpperEdgeReselection (P.twoLeft cell))
    (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
      reselection.toUpperEdgeReselection (P.twoRight cell))
    generatedLeft
    (upperReselectedPathLift input.generatedPulledRouteLiftData
      generatedReselection (P.twoRight cell))
    (CompositeFiberAut.hom
      (upperCanonicalTwoCellComparator input.canonicalAuthoredPulledRouteData
        reselection.toUpperEdgeReselection cell))
    (input.canonicalAuthoredPulledReselectedPath_forward_naturality
      reselection (P.twoLeft cell))
    (input.canonicalAuthoredPulledReselectedPath_forward_naturality
      reselection (P.twoRight cell))
    (upperCanonicalTwoCellComparator_fac input.canonicalAuthoredPulledRouteData
      reselection.toUpperEdgeReselection cell)

/-- Inverse exact conjugation returns a generated base canonical comparator to
the comparator generated by the backward-transported reselection. -/
theorem canonicalAuthoredBaseUpperCanonicalTwoCellComparator_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredBaseCompositeFiberAutBackwardAt (P.twoTarget cell)
        (upperCanonicalTwoCellComparator input.generatedBaseRouteData
          reselection.toUpperEdgeReselection cell) =
      upperCanonicalTwoCellComparator input.canonicalAuthoredBaseRouteData
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
          reselection).toUpperEdgeReselection cell := by
  let canonicalReselection :=
    input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward reselection
  have forwardLaw :=
    input.canonicalAuthoredBaseUpperCanonicalTwoCellComparator_forward
      canonicalReselection cell
  rw [input.canonicalAuthoredBaseCoefficientTrivialReselectionForward_backward]
    at forwardLaw
  have returned := congrArg
    (input.canonicalAuthoredBaseCompositeFiberAutBackwardAt (P.twoTarget cell))
    forwardLaw
  rw [input.canonicalAuthoredBaseCompositeFiberAutBackwardAt_forward]
    at returned
  exact returned.symm

/-- Inverse exact conjugation returns a generated pulled canonical comparator
to the comparator generated by the backward-transported reselection. -/
theorem canonicalAuthoredPulledUpperCanonicalTwoCellComparator_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedPulledCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredPulledCompositeFiberAutBackwardAt (P.twoTarget cell)
        (upperCanonicalTwoCellComparator input.generatedPulledRouteData
          reselection.toUpperEdgeReselection cell) =
      upperCanonicalTwoCellComparator input.canonicalAuthoredPulledRouteData
        (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
          reselection).toUpperEdgeReselection cell := by
  let canonicalReselection :=
    input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward reselection
  have forwardLaw :=
    input.canonicalAuthoredPulledUpperCanonicalTwoCellComparator_forward
      canonicalReselection cell
  rw [input.canonicalAuthoredPulledCoefficientTrivialReselectionForward_backward]
    at forwardLaw
  have returned := congrArg
    (input.canonicalAuthoredPulledCompositeFiberAutBackwardAt (P.twoTarget cell))
    forwardLaw
  rw [input.canonicalAuthoredPulledCompositeFiberAutBackwardAt_forward]
    at returned
  exact returned.symm

/-- Forward exact conjugation transports the actual canonical-authored base
raw defect cochain coordinate to the generated base coordinate. -/
theorem canonicalAuthoredBaseUpperRawDefectCochain_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt (P.twoTarget cell)
        (upperRawDefectCochain input.canonicalAuthoredBaseRouteData
          reselection.toUpperEdgeReselection cell) =
      upperRawDefectCochain input.generatedBaseRouteData
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
          reselection).toUpperEdgeReselection cell := by
  change
    CompositeFiberAut.conjugationMulEquiv
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
          (P.twoTarget cell))
        (upperRawDefectCochain input.canonicalAuthoredBaseRouteData
          reselection.toUpperEdgeReselection cell) = _
  simp only [upperRawDefectCochain, upperRawTwoCellDefect, map_mul, map_inv]
  change
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt (P.twoTarget cell)
        (input.canonicalAuthoredBaseRouteFixedComparator cell) *
      (input.canonicalAuthoredBaseCompositeFiberAutForwardAt (P.twoTarget cell)
        (upperCanonicalTwoCellComparator input.canonicalAuthoredBaseRouteData
          reselection.toUpperEdgeReselection cell))⁻¹ =
      input.generatedBaseRouteData.comparator cell *
        (upperCanonicalTwoCellComparator input.generatedBaseRouteData
          (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
            reselection).toUpperEdgeReselection cell)⁻¹
  have authored :
      input.canonicalAuthoredBaseCompositeFiberAutForwardAt (P.twoTarget cell)
          (input.canonicalAuthoredBaseRouteFixedComparator cell) =
        input.generatedBaseRouteData.comparator cell :=
    input.canonicalAuthoredBaseRouteFixedComparator_forward cell
  rw [authored,
    input.canonicalAuthoredBaseUpperCanonicalTwoCellComparator_forward]

/-- Forward exact conjugation transports the actual canonical-authored pulled
raw defect cochain coordinate to the generated pulled coordinate. -/
theorem canonicalAuthoredPulledUpperRawDefectCochain_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt (P.twoTarget cell)
        (upperRawDefectCochain input.canonicalAuthoredPulledRouteData
          reselection.toUpperEdgeReselection cell) =
      upperRawDefectCochain input.generatedPulledRouteData
        (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
          reselection).toUpperEdgeReselection cell := by
  change
    CompositeFiberAut.conjugationMulEquiv
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
          (P.twoTarget cell))
        (upperRawDefectCochain input.canonicalAuthoredPulledRouteData
          reselection.toUpperEdgeReselection cell) = _
  simp only [upperRawDefectCochain, upperRawTwoCellDefect, map_mul, map_inv]
  change
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt (P.twoTarget cell)
        (input.canonicalAuthoredPulledRouteFixedComparator cell) *
      (input.canonicalAuthoredPulledCompositeFiberAutForwardAt
        (P.twoTarget cell)
        (upperCanonicalTwoCellComparator input.canonicalAuthoredPulledRouteData
          reselection.toUpperEdgeReselection cell))⁻¹ =
      input.generatedPulledRouteData.comparator cell *
        (upperCanonicalTwoCellComparator input.generatedPulledRouteData
          (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
            reselection).toUpperEdgeReselection cell)⁻¹
  have authored :
      input.canonicalAuthoredPulledCompositeFiberAutForwardAt (P.twoTarget cell)
          (input.canonicalAuthoredPulledRouteFixedComparator cell) =
        input.generatedPulledRouteData.comparator cell :=
    input.canonicalAuthoredPulledRouteFixedComparator_forward cell
  rw [authored,
    input.canonicalAuthoredPulledUpperCanonicalTwoCellComparator_forward]

/-- Inverse exact conjugation returns a generated base raw defect coordinate
to the coordinate generated by the backward-transported reselection. -/
theorem canonicalAuthoredBaseUpperRawDefectCochain_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredBaseCompositeFiberAutBackwardAt (P.twoTarget cell)
        (upperRawDefectCochain input.generatedBaseRouteData
          reselection.toUpperEdgeReselection cell) =
      upperRawDefectCochain input.canonicalAuthoredBaseRouteData
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
          reselection).toUpperEdgeReselection cell := by
  let canonicalReselection :=
    input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward reselection
  have forwardLaw := input.canonicalAuthoredBaseUpperRawDefectCochain_forward
    canonicalReselection cell
  rw [input.canonicalAuthoredBaseCoefficientTrivialReselectionForward_backward]
    at forwardLaw
  have returned := congrArg
    (input.canonicalAuthoredBaseCompositeFiberAutBackwardAt (P.twoTarget cell))
    forwardLaw
  rw [input.canonicalAuthoredBaseCompositeFiberAutBackwardAt_forward]
    at returned
  exact returned.symm

/-- Inverse exact conjugation returns a generated pulled raw defect coordinate
to the coordinate generated by the backward-transported reselection. -/
theorem canonicalAuthoredPulledUpperRawDefectCochain_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedPulledCoefficientTrivialUpperEdgeReselection input)
    (cell : P.TwoCell) :
    input.canonicalAuthoredPulledCompositeFiberAutBackwardAt (P.twoTarget cell)
        (upperRawDefectCochain input.generatedPulledRouteData
          reselection.toUpperEdgeReselection cell) =
      upperRawDefectCochain input.canonicalAuthoredPulledRouteData
        (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
          reselection).toUpperEdgeReselection cell := by
  let canonicalReselection :=
    input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward reselection
  have forwardLaw := input.canonicalAuthoredPulledUpperRawDefectCochain_forward
    canonicalReselection cell
  rw [input.canonicalAuthoredPulledCoefficientTrivialReselectionForward_backward]
    at forwardLaw
  have returned := congrArg
    (input.canonicalAuthoredPulledCompositeFiberAutBackwardAt (P.twoTarget cell))
    forwardLaw
  rw [input.canonicalAuthoredPulledCompositeFiberAutBackwardAt_forward]
    at returned
  exact returned.symm

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
