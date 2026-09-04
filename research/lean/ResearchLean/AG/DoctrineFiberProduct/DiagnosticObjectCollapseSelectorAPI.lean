import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticObjectCollapseProducer

/-!
# Diagnostic object-collapse selector API

This lightweight module supplies the missing inadmissible branch theorem next
to the producer layer.  Higher G-116 proofs can cover all three selector
branches without unfolding the selector definition.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- A firing component with inadmissible support readings selects the
identity. -/
theorem authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_of_not_admissible
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell)
    (fires : cochain cell ≠ 1)
    (inadmissible : ¬ CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell)) :
    authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell =
      𝟙 (input.context.supportObject cell) := by
  classical
  simp [authoredDiagnosticObjectCollapseComponentAtCochain,
    fires, inadmissible]

/-- Functorial transport carries idempotence of the selected raw component to
the authored via-base component.  This keeps the producer definition unfolding
inside its lightweight API layer. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp_of_raw_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (rawComp :
      authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell.as ≫
          authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell.as =
        authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell.as) :
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell =
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  simpa only [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain,
    ← Functor.map_comp] using congrArg
      (fun morphism =>
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map morphism))
      rawComp

/-- Equality of the selected canonical component with the identity forces the
underlying canonical object normalization to be the identity function. -/
theorem canonicalObjectNormalization_eq_id_of_supportComponent_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell))
    (equality : authoredSupportCanonicalNormalizationComponent
      input cell admissible = 𝟙 (input.context.supportObject cell)) :
    canonicalObjectNormalization (input.context.supportPackage cell) =
      _root_.id := by
  funext object
  have applied := congrArg
    (fun morphism : input.context.supportObject cell ⟶
        input.context.supportObject cell => morphism.1.upper.objectMap object)
    equality
  simpa [authoredSupportCanonicalNormalizationComponent,
    canonicalObjectNormalizationTotal] using applied

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
