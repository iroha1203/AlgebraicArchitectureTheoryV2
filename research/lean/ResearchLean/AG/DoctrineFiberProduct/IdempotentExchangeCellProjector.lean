import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeNormalization
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticObjectCollapseProducer

/-!
# G-116 cell projector idempotence

This module discharges G-116(c1).  It first proves idempotence of the selected
support component and then transports that equality through the two functors
defining the authored via-base component.  The resulting component is a
vertical core-fiber morphism, so its upper Atom equivalence is the identity.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- G-116(c1) API lemma: the support-package normalization component is
idempotent.  Its only non-computational premise is the declared
`CanonicalObjectNormalizationAdmissible` direction hypothesis. -/
theorem authoredSupportCanonicalNormalizationComponent_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell)) :
    authoredSupportCanonicalNormalizationComponent input cell admissible ≫
        authoredSupportCanonicalNormalizationComponent input cell admissible =
      authoredSupportCanonicalNormalizationComponent input cell admissible := by
  apply Subtype.ext
  exact canonicalObjectNormalizationTotal_comp
    (input.context.supportPackage cell) admissible

/-- A firing component with inadmissible support readings selects the
identity.  This is the public third-branch API complementary to the vanishing
and admissible-firing selector theorems. -/
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

/-- G-116(c1) API lemma: every selected raw support component is idempotent.
The selector's vanishing, admissible-firing, and inadmissible branches are all
discharged from its definition; no branch certificate is supplied by callers. -/
theorem authoredDiagnosticObjectCollapseComponentAtCochain_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell ≫
        authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell =
      authoredDiagnosticObjectCollapseComponentAtCochain input cochain cell := by
  classical
  by_cases vanishes : cochain cell = 1
  · rw [authoredDiagnosticObjectCollapseComponentAtCochain_eq_id
      input cochain cell vanishes]
    simp
  · by_cases admissible : CanonicalObjectNormalizationAdmissible
        (input.context.supportPackage cell)
    · rw [authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
          input cochain cell vanishes admissible,
        authoredSupportCanonicalNormalizationComponent_comp]
    · rw [authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_of_not_admissible
          input cochain cell vanishes admissible]
      simp

/-- G-116(c1): the transported cell projector `E_c` is idempotent for every
authored input, diagnostic cochain, and cell.  The proof uses functorial
transport of the selected raw component rather than re-proving the existing
gate and provenance identifications. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell =
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  simp only [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain,
    ← Functor.map_comp]
  rw [authoredDiagnosticObjectCollapseComponentAtCochain_comp]

/-- G-116(c1): the transported cell projector has the identity upper Atom
equivalence.  This follows from its vertical core-fiber typing, whose lift law
transports the identity lower Atom equivalence. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_atomEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
      input cochain cell).1.upper.atomEquiv = Equiv.refl U.Atom := by
  let vertical := authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
    input cochain cell
  change vertical.1.upper.atomEquiv = Equiv.refl U.Atom
  rw [vertical.1.atomEquiv_eq]
  letI : (packageProjection U).IsHomLift
      (𝟙 input.context.square.semantic.square.northeast) vertical.1 := vertical.2
  have hfac := CategoryTheory.IsHomLift.fac'
    (packageProjection U)
      (𝟙 input.context.square.semantic.square.northeast) vertical.1
  have hatom := congrArg (fun hom => hom.doctrineHom.atomEquiv) hfac
  simpa using hatom

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
