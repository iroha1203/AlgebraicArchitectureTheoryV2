import Formal.Arch.Operation.AtomOperation
import Formal.Arch.Examples.AtomZeroCurvatureExamples

namespace Formal.Arch.AtomicExamples

/--
Presentation that observes every atom selected by the no-edge pure AAT surface
with a measurement-carrying status.
-/
def noEdgeFullAtomPresentation :
    AtomPresentation Component Edge Diagram where
  observed := fun observed =>
    noEdgePureAATSurface.atoms observed.atom ∧
      observed.observationStatus = ObservationStatus.observed ∧
      observed.measurementStatus = MeasurementStatus.measuredZero
  gaps := fun _ => False
  promotionBoundary := True
  validationBoundary := True
  rawCandidateBoundary := True
  nonConclusions := True

theorem noEdgeFullAtomSurfacePresented :
    AtomSurfacePresented noEdgePureAATSurface
      noEdgeFullAtomPresentation := by
  intro atom hAtom
  refine
    ⟨{ atom := atom
       observationStatus := ObservationStatus.observed
       measurementStatus := MeasurementStatus.measuredZero
       evidenceRef := "atom-operation:preserved"
       sourceBoundary := True
       nonConclusions := True },
      ?_, rfl, ?_⟩
  · exact ⟨hAtom, rfl, rfl⟩
  · simp [MeasurementStatus.SupportsMeasurement]

/-- Identity atom delta preserving exactly the no-edge pure surface atoms. -/
def noEdgeIdentityAtomDelta : AtomDelta Component Edge Diagram where
  created := fun _ => False
  removed := fun _ => False
  preserved := fun atom => noEdgePureAATSurface.atoms atom
  transformed := fun _ _ => False
  hidden := fun _ => False
  exposed := fun _ => False
  unknown := fun _ => False
  evidenceBoundary := True
  nonConclusions := True

def noEdgeIdentityPresentedAtomDelta :
    PresentedAtomDelta Component Edge Diagram where
  before := noEdgeFullAtomPresentation
  after := noEdgeFullAtomPresentation
  delta := noEdgeIdentityAtomDelta
  validationBoundary := True
  nonConclusions := True

def noEdgeAtomPresentationOperation :
    AtomPresentationOperation noEdgePureAATSurface where
  delta := noEdgeIdentityPresentedAtomDelta
  preservesSurface := by
    intro _hPresented atom hAtom
    exact hAtom
  preservedSurfaceObservedAfter := by
    intro atom hAtom _hPresented _hPreserved
    exact noEdgeFullAtomSurfacePresented atom hAtom
  operationBoundary := True
  nonConclusions := True

def noEdgeAtomAxiomatizedOperationPackage :
    AtomAxiomatizedOperationPackage
      noEdgeArchitectureLawModel Edge Diagram where
  aat := noEdgeAtomAxiomatizedAAT
  operation := noEdgeAtomPresentationOperation
  operationAxiomBoundary := True
  theoremPackageBoundary := True
  nonConclusions := True

theorem noEdgeAtomOperation_target_presented :
    AtomSurfacePresented noEdgePureAATSurface
      (AtomPresentationOperation.target noEdgeAtomPresentationOperation) := by
  exact
    AtomPresentationOperation.target_presented_of_source
      noEdgeAtomPresentationOperation noEdgeFullAtomSurfacePresented

theorem noEdgeAtomOperation_preservesSurfaceInvariant :
    PreservesInvariant
      (AtomPresentationOperation.source
        (surface := noEdgePureAATSurface))
      (AtomPresentationOperation.target
        (surface := noEdgePureAATSurface))
      (AtomPresentationOperation.atomSurfacePresentedHolds
        noEdgePureAATSurface)
      noEdgeAtomPresentationOperation () := by
  exact
    AtomPresentationOperation.preservesSurfaceInvariant
      noEdgeAtomPresentationOperation

theorem noEdgeAtomOperation_ops_mem_surfaceInvariant :
    Ops
      (AtomPresentationOperation.source
        (surface := noEdgePureAATSurface))
      (AtomPresentationOperation.target
        (surface := noEdgePureAATSurface))
      (AtomPresentationOperation.atomSurfacePresentedHolds
        noEdgePureAATSurface)
      (fun I : Unit => I = ())
      noEdgeAtomPresentationOperation := by
  exact
    AtomPresentationOperation.ops_mem_surfaceInvariant
      noEdgeAtomPresentationOperation

theorem noEdgeAtomAxiomatizedOperation_zeroCurvature :
    ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage
      noEdgeArchitectureLawModel := by
  exact
    AtomAxiomatizedOperationPackage.architectureZeroCurvatureTheoremPackage
      noEdgeAtomAxiomatizedOperationPackage

end Formal.Arch.AtomicExamples
