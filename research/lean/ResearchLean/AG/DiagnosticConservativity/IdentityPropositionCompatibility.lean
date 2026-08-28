import ResearchLean.AG.DiagnosticConservativity.IdentityCompatibility
import ResearchLean.AG.DiagnosticConservativity.ObstructionExactness

/-!
# G-113 revision 2 identity compatibility for coherence propositions

The G-112-mate reselection comparison from Cycle 12 is the generated inverse
identity transport.  This module uses that equality to transport arbitrary
coherence propositions and then constructs both directions of obstruction
vanishing by moving coherentizability witnesses through the same comparison.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-- The G-112-mate identity comparison on reselections is the inverse map of
the generated G-113 reselection equivalence. -/
theorem indexedDiagnosticIdentityMateReselectionUnitorEquivalence_apply_eq_inverseTransport
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      ((id D).transportedInterpretation source)) :
    indexedDiagnosticIdentityMateReselectionUnitorEquivalence D source
        targetReselection =
      (id D).inverseTransportedReselection source targetReselection := by
  rw [indexedDiagnosticIdentityMateReselectionUnitorEquivalence_eq_unitor,
    indexedDiagnosticIdentityReselectionUnitorEquivalence_eq_symm]
  rfl

/-- A target reselection is coherent exactly when its G-112-mate identity
comparison is coherent in the source interpretation. -/
theorem indexedDiagnosticIdentityCoherentAt_mate_unitor_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      ((id D).transportedInterpretation source)) :
    ((id D).transportedInterpretation source).IndexedCoherentAt
        targetReselection ↔
      source.IndexedCoherentAt
        (indexedDiagnosticIdentityMateReselectionUnitorEquivalence D source
          targetReselection) := by
  rw [
    indexedDiagnosticIdentityMateReselectionUnitorEquivalence_apply_eq_inverseTransport]
  exact indexedCoherentAt_inverseTransport_iff
    (id D) source targetReselection

/-- Obstruction vanishing is invariant under identity transport, with both
coherentizability directions generated through the G-112-mate reselection
comparison. -/
theorem indexedDiagnosticIdentityTransportObstructionVanishes_mate_unitor_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (D : IndexedBaseDiagram G U) (source : IndexedDiagnosticInterpretation D) :
    TransportObstructionVanishes source.toAdmissibleTransportData ↔
      TransportObstructionVanishes
        ((id D).transportedInterpretation source).toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable,
    transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨sourceReselection, sourceCoherent⟩
    have sourceIndexed : source.IndexedCoherentAt sourceReselection :=
      (source.indexedCoherentAt_iff_adaptedCoherentAt sourceReselection).2
        sourceCoherent
    let targetReselection :=
      (id D).transportedReselection source sourceReselection
    have targetIndexed :
        ((id D).transportedInterpretation source).IndexedCoherentAt
          targetReselection := by
      apply (indexedDiagnosticIdentityCoherentAt_mate_unitor_iff
        D source targetReselection).2
      simpa only [targetReselection,
        indexedDiagnosticIdentityMateReselectionUnitorEquivalence_apply_transport]
        using sourceIndexed
    exact ⟨targetReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        ((id D).transportedInterpretation source) targetReselection).1
        targetIndexed⟩
  · rintro ⟨targetReselection, targetCoherent⟩
    have targetIndexed :
        ((id D).transportedInterpretation source).IndexedCoherentAt
          targetReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        ((id D).transportedInterpretation source) targetReselection).2
        targetCoherent
    have sourceIndexed :=
      (indexedDiagnosticIdentityCoherentAt_mate_unitor_iff
        D source targetReselection).1 targetIndexed
    exact
      ⟨indexedDiagnosticIdentityMateReselectionUnitorEquivalence D source
          targetReselection,
        (source.indexedCoherentAt_iff_adaptedCoherentAt
          (indexedDiagnosticIdentityMateReselectionUnitorEquivalence D source
            targetReselection)).1 sourceIndexed⟩

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
