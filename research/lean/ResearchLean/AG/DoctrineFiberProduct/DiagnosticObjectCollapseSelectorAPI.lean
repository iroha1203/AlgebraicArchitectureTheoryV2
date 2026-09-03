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
open AtomFoundation TransportCoherence

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

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
