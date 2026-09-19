import ResearchLean.AG.ObstructionDiagnosticBridge.PointAtomContextContinuity
import ResearchLean.AG.ObstructionDiagnosticBridge.FaceEmptyCechNormalization
import Formal.Util.AssertStandardAxioms

/-!
# Actual coarse and fine nerves on the point-Atom site

This module connects the selected eight-point geometry to the actual
`TargetSupportedNerve` and `FaceEmptyAATCechCover` APIs.  The diagnostic side
uses the selected finite-example readings `Bool × Bool → Bool` and
`Bool × Bool → Bool × Bool`, with every chart supported on the whole reading
target as required by the paper design.  The Cech side uses the concrete
coarse/fine patches and their nonempty pair intersections on the eight-point
point-Atom space.

The face type is the complete geometric face index from Cycle 9: an inhabitant
would contain three distinct charts and an actual point in all three patches.
Its emptiness was proved by exhaustive geometry, so the face-empty Cech package
uses a complete index rather than an arbitrary supplied empty type.
-/

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace AAT.AG.ObstructionDiagnosticBridge
namespace PointAtomActualNerve

open CanonicalResolution Cohomology ResolutionInvariance
open SelectedFiniteGeometry PointAtomContextSupport

/-- Source of the selected coarse/fine diagnostic reading pair. -/
abbrev Source := Bool × Bool

/-- Coarse reading retaining only the Law-visible Boolean coordinate. -/
abbrev coarseReading : Reading Source where
  Target := Bool
  read := Prod.fst
  surjective target := ⟨(target, false), rfl⟩

/-- Fine reading retaining both Boolean source coordinates. -/
abbrev fineReading : Reading Source where
  Target := Source
  read := id
  surjective := Function.surjective_id

/-- The fine nerve uses all actual nonempty pair overlaps and the complete face index. -/
abbrev fineNerve : CoverNerve where
  Chart := FineChart
  EdgeComponent := Edge
  FaceComponent := CompleteFaceIndex FineChart finePatch
  edgeLeft := fineEdgeLeft
  edgeRight := fineEdgeRight
  faceEdge0 := isEmptyElim
  faceEdge1 := isEmptyElim
  faceEdge2 := isEmptyElim
  edgeOverlapComponent edge := Nonempty (fineOverlap edge)
  faceTripleOverlapComponent face := ∀ i, face.point ∈ finePatch (face.chart i)
  edgeOverlapComponent_holds := fineOverlapNonempty
  faceTripleOverlapComponent_holds face := face.point_mem

/-- The coarse nerve uses all actual nonempty pair overlaps and the complete face index. -/
abbrev coarseNerve : CoverNerve where
  Chart := CoarseChart
  EdgeComponent := CoarseEdge
  FaceComponent := CompleteFaceIndex CoarseChart coarsePatch
  edgeLeft := coarseEdgeLeft
  edgeRight := coarseEdgeRight
  faceEdge0 := isEmptyElim
  faceEdge1 := isEmptyElim
  faceEdge2 := isEmptyElim
  edgeOverlapComponent edge := Nonempty (coarseOverlap edge)
  faceTripleOverlapComponent face := ∀ i, face.point ∈ coarsePatch (face.chart i)
  edgeOverlapComponent_holds := coarseOverlapNonempty
  faceTripleOverlapComponent_holds face := face.point_mem

/-- Fine face indices are empty because the complete geometric index is empty. -/
instance fineNerveFaceIsEmpty : IsEmpty fineNerve.FaceComponent :=
  fineCompleteFaceIndexIsEmpty

/-- Coarse face indices are empty because the complete geometric index is empty. -/
instance coarseNerveFaceIsEmpty : IsEmpty coarseNerve.FaceComponent :=
  coarseCompleteFaceIndexIsEmpty

/-- Fine diagnostic nerve with every chart supported on the full fine target. -/
def fineSupportedNerve : TargetSupportedNerve fineReading where
  nerve := fineNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := Fintype.ofFinite _
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨(false, false), Set.mem_univ _⟩
  faceEdge0_left := isEmptyElim
  faceEdge0_right := isEmptyElim
  faceEdge1_right := isEmptyElim

/-- Coarse diagnostic nerve with every chart supported on the full coarse target. -/
def coarseSupportedNerve : TargetSupportedNerve coarseReading where
  nerve := coarseNerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := Fintype.ofFinite _
  chartSupport _ := Set.univ
  chartSupport_nonempty _ := ⟨false, Set.mem_univ _⟩
  faceEdge0_left := isEmptyElim
  faceEdge0_right := isEmptyElim
  faceEdge1_right := isEmptyElim

/-- Fine face indices are empty because the complete geometric index is empty. -/
instance fineSupportedFaceIsEmpty :
    IsEmpty fineSupportedNerve.nerve.FaceComponent :=
  fineNerveFaceIsEmpty

/-- Coarse face indices are empty because the complete geometric index is empty. -/
instance coarseSupportedFaceIsEmpty :
    IsEmpty coarseSupportedNerve.nerve.FaceComponent :=
  coarseNerveFaceIsEmpty

/-- The actual fine AAT Cech cover on the continuous point-Atom support site. -/
def fineCechCover :
    GeneratorPresentation.FaceEmptyAATCechCover
      fineSupportedNerve contextOpenSupport where
  base := Site.ContextCategoryObject.of contextPreorder baseContext
  chartContext chart :=
    Site.ContextCategoryObject.of contextPreorder (openContext (finePatch chart))
  edgeContext edge :=
    Site.ContextCategoryObject.of contextPreorder (openContext (fineOverlap edge))
  inclusion _ := homOfLE (openContext_le le_top)
  edgeLeftRestriction _ := homOfLE (openContext_le inf_le_left)
  edgeRightRestriction _ := homOfLE (openContext_le inf_le_right)
  chartSupportNonempty chart := by
    change Nonempty (contextSupport (openContext (finePatch chart)))
    rw [contextSupport_openContext]
    exact patchNonempty chart
  chartSupportPreconnected chart := by
    change PreconnectedSpace (contextSupport (openContext (finePatch chart)))
    rw [contextSupport_openContext]
    exact patchPreconnectedSpace chart
  edgeSupportNonempty edge := by
    change Nonempty (contextSupport (openContext (fineOverlap edge)))
    rw [contextSupport_openContext]
    exact fineOverlapNonempty edge
  edgeSupportPreconnected edge := by
    change PreconnectedSpace (contextSupport (openContext (fineOverlap edge)))
    rw [contextSupport_openContext]
    exact fineOverlapPreconnectedSpace edge

/-- The actual coarse AAT Cech cover on the continuous point-Atom support site. -/
def coarseCechCover :
    GeneratorPresentation.FaceEmptyAATCechCover
      coarseSupportedNerve contextOpenSupport where
  base := Site.ContextCategoryObject.of contextPreorder baseContext
  chartContext chart :=
    Site.ContextCategoryObject.of contextPreorder (openContext (coarsePatch chart))
  edgeContext edge :=
    Site.ContextCategoryObject.of contextPreorder (openContext (coarseOverlap edge))
  inclusion _ := homOfLE (openContext_le le_top)
  edgeLeftRestriction _ := homOfLE (openContext_le inf_le_left)
  edgeRightRestriction _ := homOfLE (openContext_le inf_le_right)
  chartSupportNonempty chart := by
    change Nonempty (contextSupport (openContext (coarsePatch chart)))
    rw [contextSupport_openContext]
    exact coarsePatchNonempty chart
  chartSupportPreconnected chart := by
    change PreconnectedSpace (contextSupport (openContext (coarsePatch chart)))
    rw [contextSupport_openContext]
    exact coarsePatchPreconnectedSpace chart
  edgeSupportNonempty edge := by
    change Nonempty (contextSupport (openContext (coarseOverlap edge)))
    rw [contextSupport_openContext]
    exact coarseOverlapNonempty edge
  edgeSupportPreconnected edge := by
    change PreconnectedSpace (contextSupport (openContext (coarseOverlap edge)))
    rw [contextSupport_openContext]
    exact coarseOverlapPreconnectedSpace edge

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.PointAtomActualNerve

end PointAtomActualNerve
end AAT.AG.ObstructionDiagnosticBridge
