import ResearchLean.AG.DiagnosticConservativity.CochainExactness

/-!
# G-113 revision 2 diagnostic coherence exactness

The generated raw-defect cochain equivalence reflects the identity cochain,
so coherence reflects without importing the revision-1 reflection theorem.
The Cycle 6 inverse then extends the same iff to every target reselection,
with its target round trip used explicitly in both directions.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-- Source coherence is equivalent to coherence of its transported reselection. -/
theorem indexedCoherentAt_transport_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    source.IndexedCoherentAt reselection ↔
      (hom.transportedInterpretation source).IndexedCoherentAt
        (hom.transportedReselection source reselection) := by
  rw [source.indexedCoherentAt_iff_adaptedCoherentAt,
    (hom.transportedInterpretation source).indexedCoherentAt_iff_adaptedCoherentAt,
    coherentAt_iff_rawDefectCochain_eq_identity,
    coherentAt_iff_rawDefectCochain_eq_identity]
  constructor
  · intro sourceDefect
    rw [← hom.indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
      source reselection]
    rw [sourceDefect,
      hom.indexedDiagnosticDefectCochainEquivalence_identity source]
  · intro targetDefect
    apply (indexedDiagnosticDefectCochainEquivalence hom source).injective
    rw [hom.indexedDiagnosticDefectCochainEquivalence_rawDefectCochain
      source reselection]
    rw [targetDefect,
      hom.indexedDiagnosticDefectCochainEquivalence_identity source]

/-- Every target reselection is coherent exactly when its generated inverse is coherent. -/
theorem indexedCoherentAt_inverseTransport_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) :
    (hom.transportedInterpretation source).IndexedCoherentAt targetReselection ↔
      source.IndexedCoherentAt
        (hom.inverseTransportedReselection source targetReselection) := by
  constructor
  · intro targetCoherent
    apply (hom.indexedCoherentAt_transport_iff source
      (hom.inverseTransportedReselection source targetReselection)).2
    simpa only [hom.transportedReselection_inverseTransportedReselection]
      using targetCoherent
  · intro sourceCoherent
    have transported := (hom.indexedCoherentAt_transport_iff source
      (hom.inverseTransportedReselection source targetReselection)).1
      sourceCoherent
    simpa only [hom.transportedReselection_inverseTransportedReselection]
      using transported

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
