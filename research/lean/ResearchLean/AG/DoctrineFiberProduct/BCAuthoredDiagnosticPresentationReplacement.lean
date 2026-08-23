import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticComparison
import ResearchLean.AG.DoctrineFiberProduct.BCPresentationReplacement

/-!
# Presentation replacement for the authored diagnostic comparison

This module keeps the semantic BC input, the G-106 transport datum, and the
complete authored comparator table fixed while changing only its finite BC
presentation.  It compares the generated diagnostic comparison through the
public direct-route and via-base-route isomorphisms.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 3000000

private theorem replacement_four_factor
    {C : Type*} [Category C]
    {A A' B B' : C}
    (directComparison : A ⟶ A')
    (replacementCanonical : A' ⟶ B')
    (canonical : A ⟶ B)
    (viaComparison : B ⟶ B')
    (raw : B ⟶ B) (replacementRaw : B' ⟶ B')
    (fold : B ⟶ B) (replacementFold : B' ⟶ B')
    (canonicalSquare : directComparison ≫ replacementCanonical =
      canonical ≫ viaComparison)
    (rawSquare : raw ≫ viaComparison = viaComparison ≫ replacementRaw)
    (foldSquare : fold ≫ viaComparison = viaComparison ≫ replacementFold) :
    directComparison ≫ replacementCanonical ≫ replacementRaw ≫
        replacementFold =
      (canonical ≫ raw ≫ fold) ≫ viaComparison := by
  calc
    _ = (directComparison ≫ replacementCanonical) ≫
          replacementRaw ≫ replacementFold := by simp only [Category.assoc]
    _ = (canonical ≫ viaComparison) ≫
          replacementRaw ≫ replacementFold := by rw [canonicalSquare]
    _ = canonical ≫ (viaComparison ≫ replacementRaw) ≫
          replacementFold := by simp only [Category.assoc]
    _ = canonical ≫ (raw ≫ viaComparison) ≫
          replacementFold := by rw [← rawSquare]
    _ = canonical ≫ raw ≫ (viaComparison ≫ replacementFold) := by
      simp only [Category.assoc]
    _ = canonical ≫ raw ≫ (fold ≫ viaComparison) := by rw [← foldSquare]
    _ = _ := by simp only [Category.assoc]

/-- The two provenance-indexed canonical mates form the replacement square. -/
theorem bcProvenanceCanonicalMate_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    (bcProvenanceDirectRouteComparison reference replacement).hom ≫
        bcProvenanceCanonicalMate replacement =
      bcProvenanceCanonicalMate reference ≫
        (bcProvenanceViaBaseRouteComparison reference replacement).hom := by
  simpa only [bcSelectedRebasedReplacementMate_eq_canonical] using
    bcProvenanceCanonicalMate_rebasedReplacement reference replacement

/-- Normalize the authored canonical mate onto the provenance-indexed routes. -/
theorem authoredSupportCanonicalMate_eq_provenance
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    authoredSupportCanonicalMate context =
      (authoredSupportDirectRouteProvenanceIso context).hom ≫
        Functor.whiskerLeft context.supportFunctor
          (bcProvenanceCanonicalMate context.realizationProvenance) ≫
        (authoredSupportViaBaseRouteProvenanceIso context).inv := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  unfold authoredSupportCanonicalMate
    authoredSupportDirectRouteProvenanceIso
    authoredSupportViaBaseRouteProvenanceIso
    bcProvenanceCanonicalMate AuthoredSupportContext.realizationProvenance
  change _ = (𝟙 _ ≫ _) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

/-- The canonical authored-support mate commutes with finite presentation replacement. -/
theorem authoredSupportCanonicalMate_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (replacement : BCRealizationProvenance context.square.semantic) :
    (authoredSupportDirectRouteReplacementComparison
        context replacement).hom ≫
      authoredSupportCanonicalMate (context.replacePresentation replacement) =
    authoredSupportCanonicalMate context ≫
      (authoredSupportViaBaseRouteReplacementComparison
        context replacement).hom := by
  rw [authoredSupportCanonicalMate_eq_provenance,
    authoredSupportCanonicalMate_eq_provenance]
  rcases replacement with ⟨replacementPresentation, replacement_eq⟩
  dsimp only [AuthoredSupportContext.replacePresentation,
    BCRealizationProvenance.toRealizableSquare]
  have replacementProvenance :
      (⟨⟨context.square.semantic, replacementPresentation,
          replacement_eq.symm⟩,
        context.lift, context.endpoint_eq⟩ :
          AuthoredSupportContext U).realizationProvenance =
        (⟨replacementPresentation, replacement_eq⟩ :
          BCRealizationProvenance context.square.semantic) := by
    congr
  rw [replacementProvenance]
  unfold authoredSupportDirectRouteReplacementComparison
    authoredSupportViaBaseRouteReplacementComparison
  dsimp only [AuthoredSupportContext.replacePresentation,
    BCRealizationProvenance.toRealizableSquare]
  simp [Category.assoc]
  have publicSquare := bcProvenanceCanonicalMate_replacement
    context.realizationProvenance
    (⟨replacementPresentation, replacement_eq⟩ :
      BCRealizationProvenance context.square.semantic)
  simpa [Functor.whiskerLeft_comp] using congrArg
    (Functor.whiskerLeft context.supportFunctor) publicSquare

/-- Normalize one raw via-base component onto the provenance-indexed route. -/
theorem authoredViaBaseRawDefectComponentAtCochain_eq_provenance
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (cochain : DefectCochain datum.toTransportData)
    (cell : datum.context.Category) :
    authoredViaBaseRawDefectComponentAtCochain datum cochain cell =
      (authoredSupportViaBaseRouteProvenanceIso datum.context).hom.app cell ≫
        (bcProvenanceViaBaseRoute datum.context.realizationProvenance).map
          (authoredRawDefectComponentAtCochain datum cochain cell.as) ≫
        (authoredSupportViaBaseRouteProvenanceIso datum.context).inv.app cell := by
  rcases datum with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  simp [authoredViaBaseRawDefectComponentAtCochain,
    authoredSupportViaBaseRouteProvenanceIso,
    bcProvenanceViaBaseRoute, AuthoredSupportContext.realizationProvenance]
  rfl

/-- The transported raw component is natural under the generated via-base route comparison. -/
theorem authoredViaBaseRawDefectComponentAtCochain_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic)
    (cochain : DefectCochain datum.toTransportData)
    (cell : datum.context.Category) :
    authoredViaBaseRawDefectComponentAtCochain datum cochain cell ≫
        (authoredSupportViaBaseRouteReplacementComparison
          datum.context replacement).hom.app cell =
      (authoredSupportViaBaseRouteReplacementComparison
          datum.context replacement).hom.app cell ≫
        authoredViaBaseRawDefectComponentAtCochain
          (datum.replacePresentation replacement) cochain cell := by
  rcases replacement with ⟨replacementPresentation, replacement_eq⟩
  rw [authoredViaBaseRawDefectComponentAtCochain_eq_provenance,
    authoredViaBaseRawDefectComponentAtCochain_eq_provenance]
  dsimp only [AuthoredBCDatumSquare.replacePresentation]
  have replacementProvenance :
      (datum.context.replacePresentation
          ⟨replacementPresentation, replacement_eq⟩).realizationProvenance =
        (⟨replacementPresentation, replacement_eq⟩ :
          BCRealizationProvenance datum.context.square.semantic) := by
    congr
  have rawComponent :
      authoredRawDefectComponentAtCochain
          ⟨datum.context.replacePresentation
              ⟨replacementPresentation, replacement_eq⟩,
            datum.twoCellBase, datum.authored⟩ cochain cell.as =
        authoredRawDefectComponentAtCochain datum cochain cell.as := rfl
  rw [replacementProvenance, rawComponent]
  unfold authoredSupportViaBaseRouteReplacementComparison
  simp [Category.assoc]
  have naturality :=
    (bcProvenanceViaBaseRouteComparison datum.context.realizationProvenance
      ⟨replacementPresentation, replacement_eq⟩).hom.naturality
        (authoredRawDefectComponentAtCochain datum cochain cell.as)
  simpa only [Category.assoc] using congrArg (fun morphism =>
    morphism ≫
      (authoredSupportViaBaseRouteProvenanceIso
        (datum.context.replacePresentation
          ⟨replacementPresentation, replacement_eq⟩)).inv.app cell) naturality

/-- Normalize one unified-fold via-base component onto the provenance-indexed route. -/
theorem authoredViaBaseUnifiedAxisFoldComponentAtCochain_eq_provenance
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (cochain : DefectCochain datum.toTransportData)
    (cell : datum.context.Category) :
    authoredViaBaseUnifiedAxisFoldComponentAtCochain datum cochain cell =
      (authoredSupportViaBaseRouteProvenanceIso datum.context).hom.app cell ≫
        (bcProvenanceViaBaseRoute datum.context.realizationProvenance).map
          (authoredUnifiedAxisFoldComponentAtCochain datum cochain cell.as) ≫
        (authoredSupportViaBaseRouteProvenanceIso datum.context).inv.app cell := by
  rcases datum with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  simp [authoredViaBaseUnifiedAxisFoldComponentAtCochain,
    authoredSupportViaBaseRouteProvenanceIso,
    bcProvenanceViaBaseRoute, AuthoredSupportContext.realizationProvenance]
  rfl

/-- The transported unified fold is natural under the generated via-base comparison. -/
theorem authoredViaBaseUnifiedAxisFoldComponentAtCochain_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic)
    (cochain : DefectCochain datum.toTransportData)
    (cell : datum.context.Category) :
    authoredViaBaseUnifiedAxisFoldComponentAtCochain datum cochain cell ≫
        (authoredSupportViaBaseRouteReplacementComparison
          datum.context replacement).hom.app cell =
      (authoredSupportViaBaseRouteReplacementComparison
          datum.context replacement).hom.app cell ≫
        authoredViaBaseUnifiedAxisFoldComponentAtCochain
          (datum.replacePresentation replacement) cochain cell := by
  rcases replacement with ⟨replacementPresentation, replacement_eq⟩
  rw [authoredViaBaseUnifiedAxisFoldComponentAtCochain_eq_provenance,
    authoredViaBaseUnifiedAxisFoldComponentAtCochain_eq_provenance]
  dsimp only [AuthoredBCDatumSquare.replacePresentation]
  have replacementProvenance :
      (datum.context.replacePresentation
          ⟨replacementPresentation, replacement_eq⟩).realizationProvenance =
        (⟨replacementPresentation, replacement_eq⟩ :
          BCRealizationProvenance datum.context.square.semantic) := by
    congr
  have foldComponent :
      authoredUnifiedAxisFoldComponentAtCochain
          ⟨datum.context.replacePresentation
              ⟨replacementPresentation, replacement_eq⟩,
            datum.twoCellBase, datum.authored⟩ cochain cell.as =
        authoredUnifiedAxisFoldComponentAtCochain datum cochain cell.as := rfl
  rw [replacementProvenance, foldComponent]
  unfold authoredSupportViaBaseRouteReplacementComparison
  simp [Category.assoc]
  have naturality :=
    (bcProvenanceViaBaseRouteComparison datum.context.realizationProvenance
      ⟨replacementPresentation, replacement_eq⟩).hom.naturality
        (authoredUnifiedAxisFoldComponentAtCochain datum cochain cell.as)
  simpa only [Category.assoc] using congrArg (fun morphism =>
    morphism ≫
      (authoredSupportViaBaseRouteProvenanceIso
        (datum.context.replacePresentation
          ⟨replacementPresentation, replacement_eq⟩)).inv.app cell) naturality

/-- The generated diagnostic comparison commutes with finite presentation replacement. -/
theorem authoredDiagnosticComparisonAtCochain_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic)
    (cochain : DefectCochain datum.toTransportData) :
    (authoredSupportDirectRouteReplacementComparison
        datum.context replacement).hom ≫
      authoredDiagnosticComparisonAtCochain
        (datum.replacePresentation replacement) cochain =
    authoredDiagnosticComparisonAtCochain datum cochain ≫
      (authoredSupportViaBaseRouteReplacementComparison
        datum.context replacement).hom := by
  apply NatTrans.ext
  funext cell
  rw [NatTrans.comp_app, NatTrans.comp_app]
  unfold authoredDiagnosticComparisonAtCochain
  rw [authoredComparisonOfComponents_app,
    authoredComparisonOfComponents_app]
  rw [authoredDiagnosticComparisonComponentAtCochain_eq_canonical_comp_raw_comp_fold,
    authoredDiagnosticComparisonComponentAtCochain_eq_canonical_comp_raw_comp_fold]
  have canonicalComponent := congrArg (fun transformation =>
    transformation.app cell)
      (authoredSupportCanonicalMate_replacement datum.context replacement)
  simp only [NatTrans.comp_app] at canonicalComponent
  have rawComponent :=
    authoredViaBaseRawDefectComponentAtCochain_replacement
      datum replacement cochain cell
  have foldComponent :=
    authoredViaBaseUnifiedAxisFoldComponentAtCochain_replacement
      datum replacement cochain cell
  exact replacement_four_factor _ _ _ _ _ _ _ _
    canonicalComponent rawComponent foldComponent

/-- The named generated diagnostic producer commutes with presentation replacement. -/
theorem generatedAuthoredDiagnosticComparison_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic) :
    (authoredSupportDirectRouteReplacementComparison
        datum.context replacement).hom ≫
      generatedAuthoredDiagnosticComparison
        (datum.replacePresentation replacement) =
    generatedAuthoredDiagnosticComparison datum ≫
      (authoredSupportViaBaseRouteReplacementComparison
        datum.context replacement).hom := by
  simpa only [generatedAuthoredDiagnosticComparison_apply,
    AuthoredBCDatumSquare.replacePresentation_toTransportData] using
      authoredDiagnosticComparisonAtCochain_replacement datum replacement
        (initialRawDefectCochain datum.toTransportData)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
