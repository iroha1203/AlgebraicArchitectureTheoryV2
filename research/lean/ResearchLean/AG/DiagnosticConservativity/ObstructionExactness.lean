import ResearchLean.AG.DiagnosticConservativity.CoherenceExactness

/-!
# G-113 revision 2 diagnostic obstruction exactness

Obstruction vanishing is coherentizability.  The Cycle 7 coherence equivalence,
together with the Cycle 6 inverse reselection, therefore identifies source and
transported obstruction vanishing for every indexed diagram hom.  The existing
all-hom conservativity and no-counterexample declarations remain available from
the reviewed revision-1 reflection package imported by the coherence layer.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-- Diagnostic obstruction vanishes exactly when its transported obstruction vanishes. -/
theorem indexedTransportObstructionVanishes_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) :
    TransportObstructionVanishes source.toAdmissibleTransportData ↔
      TransportObstructionVanishes
        (hom.transportedInterpretation source).toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable,
    transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨reselection, coherent⟩
    have sourceCoherent : source.IndexedCoherentAt reselection :=
      (source.indexedCoherentAt_iff_adaptedCoherentAt reselection).2 coherent
    exact ⟨hom.transportedReselection source reselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (hom.transportedInterpretation source)
        (hom.transportedReselection source reselection)).1
        ((hom.indexedCoherentAt_transport_iff source reselection).1
          sourceCoherent)⟩
  · rintro ⟨targetReselection, targetCoherent⟩
    have targetIndexed :
        (hom.transportedInterpretation source).IndexedCoherentAt
          targetReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (hom.transportedInterpretation source) targetReselection).2
        targetCoherent
    exact ⟨hom.inverseTransportedReselection source targetReselection,
      (source.indexedCoherentAt_iff_adaptedCoherentAt
        (hom.inverseTransportedReselection source targetReselection)).1
        ((hom.indexedCoherentAt_inverseTransport_iff source
          targetReselection).1 targetIndexed)⟩

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
