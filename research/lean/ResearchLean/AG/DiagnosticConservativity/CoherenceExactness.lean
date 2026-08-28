import ResearchLean.AG.DiagnosticConservativity.ReselectionExactness
import ResearchLean.AG.DoctrineFiberProduct.DiagnosticConservativityReflection

/-!
# G-113 revision 2 diagnostic coherence exactness

G-111 coherence preservation and the cartesian reflection theorem give the
coherence equivalence on every mapped reselection.  The Cycle 6 inverse then
extends the same iff to every target reselection, with its target round trip
used explicitly in both directions.
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
        (hom.transportedReselection source reselection) :=
  ⟨hom.indexedCoherentAt_transport source reselection,
    hom.indexedCoherentAt_reflect source reselection⟩

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
    apply hom.indexedCoherentAt_reflect source
      (hom.inverseTransportedReselection source targetReselection)
    simpa only [hom.transportedReselection_inverseTransportedReselection]
      using targetCoherent
  · intro sourceCoherent
    have transported := hom.indexedCoherentAt_transport source
      (hom.inverseTransportedReselection source targetReselection)
      sourceCoherent
    simpa only [hom.transportedReselection_inverseTransportedReselection]
      using transported

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
