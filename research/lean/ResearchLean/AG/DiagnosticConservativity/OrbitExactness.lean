import ResearchLean.AG.DiagnosticConservativity.CochainExactness

/-!
# G-113 revision 2 reselection-orbit exactness

The explicit reselection and cochain equivalences transport the complete
existential witness defining `InReselectionOrbit`.  Membership is therefore
equivalent for every mapped source cochain and, separately, for every arbitrary
target cochain.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/--
Conjunct `(g)` for a source cochain: the Cycle 9 cochain equivalence transports
the entire reselection orbit in both directions, using the Cycle 6 inverse
reselection rather than a supplied preimage.
-/
theorem indexedDiagnosticInReselectionOrbit_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (cochain : DefectCochain source.toAdmissibleTransportData) :
    InReselectionOrbit source.toAdmissibleTransportData cochain ↔
      InReselectionOrbit
        (hom.transportedInterpretation source).toAdmissibleTransportData
        (indexedDiagnosticDefectCochainEquivalence hom source cochain) := by
  constructor
  · rintro ⟨reselection, equality⟩
    refine ⟨hom.transportedReselection source reselection, ?_⟩
    rw [← indexedDiagnosticDefectCochainEquivalence_rawDefectCochain]
    exact congrArg (indexedDiagnosticDefectCochainEquivalence hom source) equality
  · rintro ⟨targetReselection, equality⟩
    refine ⟨hom.inverseTransportedReselection source targetReselection, ?_⟩
    rw [← indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain]
    rw [equality]
    exact (indexedDiagnosticDefectCochainEquivalence hom source).symm_apply_apply
      cochain

/--
Conjunct `(g)` for an arbitrary target cochain: target orbit membership is
equivalent to source membership of its generated inverse image.
-/
theorem indexedDiagnosticInReselectionOrbit_symm_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetCochain : DefectCochain
      (hom.transportedInterpretation source).toAdmissibleTransportData) :
    InReselectionOrbit
        (hom.transportedInterpretation source).toAdmissibleTransportData
        targetCochain ↔
      InReselectionOrbit source.toAdmissibleTransportData
        ((indexedDiagnosticDefectCochainEquivalence hom source).symm
          targetCochain) := by
  constructor
  · rintro ⟨targetReselection, equality⟩
    refine ⟨hom.inverseTransportedReselection source targetReselection, ?_⟩
    rw [← indexedDiagnosticDefectCochainEquivalence_symm_rawDefectCochain]
    exact congrArg (indexedDiagnosticDefectCochainEquivalence hom source).symm
      equality
  · rintro ⟨reselection, equality⟩
    refine ⟨hom.transportedReselection source reselection, ?_⟩
    rw [← indexedDiagnosticDefectCochainEquivalence_rawDefectCochain]
    have mapped := congrArg
      (indexedDiagnosticDefectCochainEquivalence hom source) equality
    simpa only [
      (indexedDiagnosticDefectCochainEquivalence hom source).apply_symm_apply]
      using mapped

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
