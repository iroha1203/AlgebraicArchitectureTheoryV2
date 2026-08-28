import ResearchLean.AG.DiagnosticConservativity.CompositionCompatibility
import ResearchLean.AG.DiagnosticConservativity.ObstructionExactness

/-!
# G-113 revision 2 proposition-level vertical-composition compatibility

The Cycle 14 G-112-mate compositor compares direct and successive
reselections.  Its compatibility with generated inverse reselection identifies
the two routes back to the source.  This yields coherence iff for every direct
target reselection and transports coherentizability witnesses in both
directions, giving obstruction-vanishing compatibility.

## Implementation notes

The proofs retain the mate comparator as the actual witness map.  They do not
obtain the proposition statements merely by composing the earlier all-hom
coherence or vanishing equivalences.  The reverse obstruction direction uses
the inverse of the generated comparator, so arbitrary successive witnesses are
covered rather than only witnesses already presented as forward images.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation
open CrossStageCoherence
open TransportCoherence

namespace IndexedBaseDiagramHom

/-- Successive inverse reselection through the G-112-mate compositor equals
direct-composite inverse reselection for every direct target reselection. -/
theorem indexedDiagnosticCompositionMateReselectionCompositorEquivalence_inverse
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      ((first.comp second).transportedInterpretation source)) :
    first.inverseTransportedReselection source
        (second.inverseTransportedReselection
          (first.transportedInterpretation source)
          (indexedDiagnosticCompositionMateReselectionCompositorEquivalence
            first second source directReselection)) =
      (first.comp second).inverseTransportedReselection source
        directReselection := by
  let sourceReselection :=
    (indexedDiagnosticReselectionEquivalence (first.comp second) source).symm
      directReselection
  have directRoundTrip :
      indexedDiagnosticReselectionEquivalence (first.comp second) source
          sourceReselection = directReselection := by
    exact (indexedDiagnosticReselectionEquivalence
      (first.comp second) source).apply_symm_apply directReselection
  have compositorEquation :=
    indexedDiagnosticCompositionMateReselectionCompositorEquivalence_apply
      first second source sourceReselection
  rw [directRoundTrip] at compositorEquation
  change (indexedDiagnosticReselectionEquivalence first source).symm
      ((indexedDiagnosticReselectionEquivalence second
        (first.transportedInterpretation source)).symm
          (indexedDiagnosticCompositionMateReselectionCompositorEquivalence
            first second source directReselection)) = sourceReselection
  rw [compositorEquation]
  simp only [MulEquiv.symm_apply_apply]

/-- A direct target reselection is coherent exactly when its G-112-mate
compositor image is coherent after successive transport. -/
theorem indexedDiagnosticCompositionCoherentAt_mate_compositor_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D)
    (directReselection : IndexedEdgeReselection
      ((first.comp second).transportedInterpretation source)) :
    ((first.comp second).transportedInterpretation source).IndexedCoherentAt
        directReselection ↔
      (second.transportedInterpretation
        (first.transportedInterpretation source)).IndexedCoherentAt
        (indexedDiagnosticCompositionMateReselectionCompositorEquivalence
          first second source directReselection) := by
  calc
    _ ↔ source.IndexedCoherentAt
        ((first.comp second).inverseTransportedReselection source
          directReselection) :=
      indexedCoherentAt_inverseTransport_iff
        (first.comp second) source directReselection
    _ ↔ source.IndexedCoherentAt
        (first.inverseTransportedReselection source
          (second.inverseTransportedReselection
            (first.transportedInterpretation source)
            (indexedDiagnosticCompositionMateReselectionCompositorEquivalence
              first second source directReselection))) := by
      rw [
        indexedDiagnosticCompositionMateReselectionCompositorEquivalence_inverse]
    _ ↔ (first.transportedInterpretation source).IndexedCoherentAt
        (second.inverseTransportedReselection
          (first.transportedInterpretation source)
          (indexedDiagnosticCompositionMateReselectionCompositorEquivalence
            first second source directReselection)) :=
      (indexedCoherentAt_inverseTransport_iff first source _).symm
    _ ↔ _ :=
      (indexedCoherentAt_inverseTransport_iff second
        (first.transportedInterpretation source) _).symm

/-- Obstruction vanishing is compatible with vertical composition, with both
coherentizability directions transported through the G-112-mate reselection
compositor. -/
theorem indexedDiagnosticCompositionTransportObstructionVanishes_mate_compositor_iff
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E F : IndexedBaseDiagram G U}
    (first : IndexedBaseDiagramHom D E)
    (second : IndexedBaseDiagramHom E F)
    (source : IndexedDiagnosticInterpretation D) :
    TransportObstructionVanishes
        ((first.comp second).transportedInterpretation source).toAdmissibleTransportData ↔
      TransportObstructionVanishes
        (second.transportedInterpretation
          (first.transportedInterpretation source)).toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable,
    transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨directReselection, directCoherent⟩
    have directIndexed :
        ((first.comp second).transportedInterpretation source).IndexedCoherentAt
          directReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        ((first.comp second).transportedInterpretation source)
        directReselection).2 directCoherent
    let successiveReselection :=
      indexedDiagnosticCompositionMateReselectionCompositorEquivalence
        first second source directReselection
    have successiveIndexed :
        (second.transportedInterpretation
          (first.transportedInterpretation source)).IndexedCoherentAt
            successiveReselection := by
      exact (indexedDiagnosticCompositionCoherentAt_mate_compositor_iff
        first second source directReselection).1 directIndexed
    exact ⟨successiveReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (second.transportedInterpretation
          (first.transportedInterpretation source)) successiveReselection).1
        successiveIndexed⟩
  · rintro ⟨successiveReselection, successiveCoherent⟩
    have successiveIndexed :
        (second.transportedInterpretation
          (first.transportedInterpretation source)).IndexedCoherentAt
            successiveReselection :=
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        (second.transportedInterpretation
          (first.transportedInterpretation source)) successiveReselection).2
        successiveCoherent
    let directReselection :=
      (indexedDiagnosticCompositionMateReselectionCompositorEquivalence
        first second source).symm successiveReselection
    have directIndexed :
        ((first.comp second).transportedInterpretation source).IndexedCoherentAt
          directReselection := by
      apply (indexedDiagnosticCompositionCoherentAt_mate_compositor_iff
        first second source directReselection).2
      simpa only [directReselection,
        (indexedDiagnosticCompositionMateReselectionCompositorEquivalence
          first second source).apply_symm_apply] using successiveIndexed
    exact ⟨directReselection,
      (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
        ((first.comp second).transportedInterpretation source)
        directReselection).1 directIndexed⟩

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
