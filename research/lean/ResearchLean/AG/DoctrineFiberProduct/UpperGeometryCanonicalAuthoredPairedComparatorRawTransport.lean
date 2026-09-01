import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredPairedEndpointPathTransport

/-!
# Comparator-pasting and raw-coefficient transport for canonical-authored pairs

This module transports the third and fourth conjuncts of the native
canonical-authored paired relation.  Both proofs consume the supplied source
fields directly: the comparator proof transports the literal authored
pasting, while the raw proof transports the actual raw cochain before reading
its coefficient component.  Neither route regenerates a destination pair
through `toPaired`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

/-- A square remains commutative after independently conjugating its source
and target legs. -/
theorem conjugatedPastingSquare
    {C : Type u} [Category.{v} C]
    {baseSource baseTarget pulledSource pulledTarget
      baseSource' baseTarget' pulledSource' pulledTarget' : C}
    (baseSourceIso : baseSource ≅ baseSource')
    (baseTargetIso : baseTarget ≅ baseTarget')
    (pulledSourceIso : pulledSource ≅ pulledSource')
    (pulledTargetIso : pulledTarget ≅ pulledTarget')
    (basePasting : baseSource ⟶ baseTarget)
    (sourceComponent : baseSource ⟶ pulledSource)
    (targetComponent : baseTarget ⟶ pulledTarget)
    (pulledPasting : pulledSource ⟶ pulledTarget)
    (square : basePasting ≫ targetComponent =
      sourceComponent ≫ pulledPasting) :
    ((baseSourceIso.inv ≫ basePasting) ≫ baseTargetIso.hom) ≫
        ((baseTargetIso.inv ≫ targetComponent) ≫ pulledTargetIso.hom) =
      ((baseSourceIso.inv ≫ sourceComponent) ≫ pulledSourceIso.hom) ≫
        ((pulledSourceIso.inv ≫ pulledPasting) ≫ pulledTargetIso.hom) := by
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    congrArg (fun middle => baseSourceIso.inv ≫ middle ≫ pulledTargetIso.hom)
      square

/-- Naturality of a path and its target comparator identifies the composite
with the conjugate of the source composite. -/
theorem conjugatedPathComparator
    {C : Type u} [Category.{v} C] {X Y X' Y' : C}
    (sourceIso : X ≅ X') (targetIso : Y ≅ Y')
    (path : X ⟶ Y) (path' : X' ⟶ Y')
    (comparator : Y ⟶ Y) (comparator' : Y' ⟶ Y')
    (pathNaturality : path ≫ targetIso.hom = sourceIso.hom ≫ path')
    (comparatorNaturality :
      comparator ≫ targetIso.hom = targetIso.hom ≫ comparator') :
    path' ≫ comparator' =
      (sourceIso.inv ≫ (path ≫ comparator)) ≫ targetIso.hom := by
  have comparatorConjugation :
      (targetIso.inv ≫ comparator) ≫ targetIso.hom = comparator' := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun hom => targetIso.inv ≫ hom) comparatorNaturality
  have transported := conjugatedPostcomposition_naturality sourceIso targetIso
    path path' comparator pathNaturality
  rw [comparatorConjugation] at transported
  have whiskered := congrArg (fun hom => sourceIso.inv ≫ hom) transported
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using whiskered.symm

namespace UpperGeometryCompatibleProblemInputData

/-- The supplied literal canonical-authored comparator pasting is carried to
the generated routes. -/
theorem canonicalAuthoredReselectedAuthoredComparatorPasting_forward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (pasting : CanonicalAuthoredReselectedAuthoredComparatorPasting
      solution base pulled) :
    ReselectedAuthoredComparatorPasting
      (input.canonicalSolutionForward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
        pulled) := by
  intro cell
  let canonicalBasePasting :=
    (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
      base.toUpperEdgeReselection (P.twoLeft cell)).comp
        (input.canonicalAuthoredBaseRouteComparator cell)
  let generatedBasePasting :=
    (upperReselectedPathLift input.generatedBaseRouteLiftData
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
        base).toUpperEdgeReselection (P.twoLeft cell)).comp
          (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))
  let canonicalPulledPasting :=
    (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
      pulled.toUpperEdgeReselection (P.twoLeft cell)).comp
        (input.canonicalAuthoredPulledRouteComparator cell)
  let generatedPulledPasting :=
    (upperReselectedPathLift input.generatedPulledRouteLiftData
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
        pulled).toUpperEdgeReselection (P.twoLeft cell)).comp
          (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell))
  have basePath := input.canonicalAuthoredBaseReselectedPath_forward_naturality
    base (P.twoLeft cell)
  have basePastingConjugation :
      generatedBasePasting =
        ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
          (P.twoSource cell)).comp canonicalBasePasting).comp
            (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
              (P.twoTarget cell)) := by
    simpa only [canonicalBasePasting, generatedBasePasting] using
      conjugatedPathComparator
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
          (P.twoSource cell))
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
          (P.twoTarget cell))
        _ _ _ _ basePath
        (input.canonicalAuthoredBaseRouteComparator_exact_conjugation cell)
  have pulledPath :=
    input.canonicalAuthoredPulledReselectedPath_forward_naturality
      pulled (P.twoLeft cell)
  have pulledPastingConjugation :
      generatedPulledPasting =
        ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
          (P.twoSource cell)).comp canonicalPulledPasting).comp
            (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
              (P.twoTarget cell)) := by
    simpa only [canonicalPulledPasting, generatedPulledPasting] using
      conjugatedPathComparator
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
          (P.twoSource cell))
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
          (P.twoTarget cell))
        _ _ _ _ pulledPath
        (input.canonicalAuthoredPulledRouteComparator_exact_conjugation cell)
  change generatedBasePasting.comp
      (input.canonicalSolutionForwardAt solution (P.twoTarget cell)) =
    (input.canonicalSolutionForwardAt solution (P.twoSource cell)).comp
      generatedPulledPasting
  rw [basePastingConjugation, pulledPastingConjugation,
    input.canonicalSolutionForwardAt_exact_normalization,
    input.canonicalSolutionForwardAt_exact_normalization]
  exact conjugatedPastingSquare
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
      (P.twoSource cell))
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
      (P.twoTarget cell))
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
      (P.twoSource cell))
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
      (P.twoTarget cell))
    canonicalBasePasting (solution.component (P.twoSource cell))
    (solution.component (P.twoTarget cell)) canonicalPulledPasting
    (pasting cell)

/-- The supplied generated literal-comparator pasting is returned to the
independently authored routes. -/
theorem canonicalAuthoredReselectedAuthoredComparatorPasting_backward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (pasting : ReselectedAuthoredComparatorPasting solution base pulled) :
    CanonicalAuthoredReselectedAuthoredComparatorPasting
      (input.generatedSolutionBackward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
        pulled) := by
  intro cell
  let generatedBasePasting :=
    (upperReselectedPathLift input.generatedBaseRouteLiftData
      base.toUpperEdgeReselection (P.twoLeft cell)).comp
        (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))
  let canonicalBasePasting :=
    (upperReselectedPathLift input.canonicalAuthoredBaseRouteLiftData
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
        base).toUpperEdgeReselection (P.twoLeft cell)).comp
          (input.canonicalAuthoredBaseRouteComparator cell)
  let generatedPulledPasting :=
    (upperReselectedPathLift input.generatedPulledRouteLiftData
      pulled.toUpperEdgeReselection (P.twoLeft cell)).comp
        (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell))
  let canonicalPulledPasting :=
    (upperReselectedPathLift input.canonicalAuthoredPulledRouteLiftData
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
        pulled).toUpperEdgeReselection (P.twoLeft cell)).comp
          (input.canonicalAuthoredPulledRouteComparator cell)
  have basePath := input.canonicalAuthoredBaseReselectedPath_backward_naturality
    base (P.twoLeft cell)
  have basePastingConjugation :
      canonicalBasePasting =
        ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
          (P.twoSource cell)).comp generatedBasePasting).comp
            (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
              (P.twoTarget cell)) := by
    simpa only [canonicalBasePasting, generatedBasePasting] using
      conjugatedPathComparator
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
          (P.twoSource cell)).symm
        (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
          (P.twoTarget cell)).symm
        _ _ _ _ basePath
        (input.canonicalAuthoredBaseRouteComparator_exact_conjugation_inv cell)
  have pulledPath :=
    input.canonicalAuthoredPulledReselectedPath_backward_naturality
      pulled (P.twoLeft cell)
  have pulledPastingConjugation :
      canonicalPulledPasting =
        ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
          (P.twoSource cell)).comp generatedPulledPasting).comp
            (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
              (P.twoTarget cell)) := by
    simpa only [canonicalPulledPasting, generatedPulledPasting] using
      conjugatedPathComparator
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
          (P.twoSource cell)).symm
        (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
          (P.twoTarget cell)).symm
        _ _ _ _ pulledPath
        (input.canonicalAuthoredPulledRouteComparator_exact_conjugation_inv cell)
  change canonicalBasePasting.comp
      (input.generatedSolutionBackwardAt solution (P.twoTarget cell)) =
    (input.generatedSolutionBackwardAt solution (P.twoSource cell)).comp
      canonicalPulledPasting
  rw [basePastingConjugation, pulledPastingConjugation,
    input.generatedSolutionBackwardAt_exact_normalization,
    input.generatedSolutionBackwardAt_exact_normalization]
  exact conjugatedPastingSquare
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
      (P.twoSource cell)).symm
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt
      (P.twoTarget cell)).symm
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
      (P.twoSource cell)).symm
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt
      (P.twoTarget cell)).symm
    generatedBasePasting (solution.component (P.twoSource cell))
    (solution.component (P.twoTarget cell)) generatedPulledPasting
    (pasting cell)

/-- The supplied canonical-authored raw-cochain coefficient square is carried
to the generated routes. -/
theorem canonicalAuthoredRawCochainComponentCoefficientTrivial_forward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : CanonicalUpperRefinementBCSolution input}
    {base : CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input}
    (raw : CanonicalAuthoredRawCochainComponentCoefficientTrivial
      solution base pulled) :
    RawCochainComponentCoefficientTrivial
      (input.canonicalSolutionForward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
        pulled) := by
  intro cell
  have source := raw cell
  constructor
  · change
      (input.canonicalSolutionForwardAt solution
        (P.twoTarget cell)).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain input.generatedBaseRouteData
            (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
              base).toUpperEdgeReselection cell)).geometry.coefficientHom =
        RingHom.id k
    rw [← input.canonicalAuthoredBaseUpperRawDefectCochain_forward base cell,
      input.canonicalSolutionForwardAt_exact_normalization,
      input.canonicalAuthoredBaseCompositeFiberAutForwardAt_hom]
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change
      ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
        (P.twoTarget cell)).geometry.coefficientHom.comp
        ((solution.component (P.twoTarget cell)).geometry.coefficientHom.comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
            (P.twoTarget cell)).geometry.coefficientHom)).comp
        ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell)).geometry.coefficientHom.comp
          ((CompositeFiberAut.hom
            (upperRawDefectCochain input.canonicalAuthoredBaseRouteData
              base.toUpperEdgeReselection cell)).geometry.coefficientHom.comp
            (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
              (P.twoTarget cell)).geometry.coefficientHom)) = RingHom.id k
    rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id]
    simpa only [RingHom.id_comp, RingHom.comp_id, RingHom.comp_assoc] using source.1
  · change
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.generatedPulledRouteData
          (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
            pulled).toUpperEdgeReselection cell)).geometry.coefficientHom.comp
        (input.canonicalSolutionForwardAt solution
          (P.twoTarget cell)).geometry.coefficientHom = RingHom.id k
    rw [← input.canonicalAuthoredPulledUpperRawDefectCochain_forward pulled cell,
      input.canonicalSolutionForwardAt_exact_normalization,
      input.canonicalAuthoredPulledCompositeFiberAutForwardAt_hom]
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change
      ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
        (P.twoTarget cell)).geometry.coefficientHom.comp
        ((CompositeFiberAut.hom
          (upperRawDefectCochain input.canonicalAuthoredPulledRouteData
            pulled.toUpperEdgeReselection cell)).geometry.coefficientHom.comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
            (P.twoTarget cell)).geometry.coefficientHom)).comp
        ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
          (P.twoTarget cell)).geometry.coefficientHom.comp
          ((solution.component (P.twoTarget cell)).geometry.coefficientHom.comp
            (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
              (P.twoTarget cell)).geometry.coefficientHom)) = RingHom.id k
    rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id]
    simpa only [RingHom.id_comp, RingHom.comp_id, RingHom.comp_assoc] using source.2

/-- The supplied generated raw-cochain coefficient square is returned to the
independently authored routes. -/
theorem canonicalAuthoredRawCochainComponentCoefficientTrivial_backward_transport
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (raw : RawCochainComponentCoefficientTrivial solution base pulled) :
    CanonicalAuthoredRawCochainComponentCoefficientTrivial
      (input.generatedSolutionBackward solution)
      (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward base)
      (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
        pulled) := by
  intro cell
  have source := raw cell
  constructor
  · change
      (input.generatedSolutionBackwardAt solution
        (P.twoTarget cell)).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain input.canonicalAuthoredBaseRouteData
            (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
              base).toUpperEdgeReselection cell)).geometry.coefficientHom =
        RingHom.id k
    rw [← input.canonicalAuthoredBaseUpperRawDefectCochain_backward base cell,
      input.generatedSolutionBackwardAt_exact_normalization,
      input.canonicalAuthoredBaseCompositeFiberAutBackwardAt_hom]
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change
      ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
        (P.twoTarget cell)).geometry.coefficientHom.comp
        ((solution.component (P.twoTarget cell)).geometry.coefficientHom.comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
            (P.twoTarget cell)).geometry.coefficientHom)).comp
        ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
          (P.twoTarget cell)).geometry.coefficientHom.comp
          ((CompositeFiberAut.hom
            (upperRawDefectCochain input.generatedBaseRouteData
              base.toUpperEdgeReselection cell)).geometry.coefficientHom.comp
            (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
              (P.twoTarget cell)).geometry.coefficientHom)) = RingHom.id k
    rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id]
    simpa only [RingHom.id_comp, RingHom.comp_id, RingHom.comp_assoc] using source.1
  · change
      (CompositeFiberAut.hom
        (upperRawDefectCochain input.canonicalAuthoredPulledRouteData
          (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
            pulled).toUpperEdgeReselection cell)).geometry.coefficientHom.comp
        (input.generatedSolutionBackwardAt solution
          (P.twoTarget cell)).geometry.coefficientHom = RingHom.id k
    rw [← input.canonicalAuthoredPulledUpperRawDefectCochain_backward pulled cell,
      input.generatedSolutionBackwardAt_exact_normalization,
      input.canonicalAuthoredPulledCompositeFiberAutBackwardAt_hom]
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change
      ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
        (P.twoTarget cell)).geometry.coefficientHom.comp
        ((CompositeFiberAut.hom
          (upperRawDefectCochain input.generatedPulledRouteData
            pulled.toUpperEdgeReselection cell)).geometry.coefficientHom.comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
            (P.twoTarget cell)).geometry.coefficientHom)).comp
        ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
          (P.twoTarget cell)).geometry.coefficientHom.comp
          ((solution.component (P.twoTarget cell)).geometry.coefficientHom.comp
            (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
              (P.twoTarget cell)).geometry.coefficientHom)) = RingHom.id k
    rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id]
    simpa only [RingHom.id_comp, RingHom.comp_id, RingHom.comp_assoc] using source.2

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
