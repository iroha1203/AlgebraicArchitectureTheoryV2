import ResearchLean.AG.ObstructionDiagnosticBridge.CombinedAtomContextContinuity
import ResearchLean.AG.ObstructionDiagnosticBridge.PointAtomActualNerve
import Formal.Util.AssertStandardAxioms

/-!
# Actual coarse and fine Cech covers on the combined Atom site

This module moves the Cycle 13 actual coarse and fine Cech covers from the
point-only site to the Cycle 16 site whose architecture object also contains
the selected primitive generator Atoms.  It reuses the same complete geometric
nerve indices and actual open patches, now interpreted through the combined
site's proved continuous support functor.

## Implementation notes

The diagnostic nerves are reused because their readings and geometric chart
indices are unchanged; rebuilding them would duplicate the fixed Cycle 13
input.  The Cech cover records are rebuilt rather than transported through an
unproved site equivalence.  Their contexts and restriction arrows therefore
live definitionally in the combined context category.  No H1 comparison is
claimed here; this module supplies the actual combined-site source needed by
that next obligation.
-/

noncomputable section

open CategoryTheory Set TopologicalSpace

namespace AAT.AG.ObstructionDiagnosticBridge
namespace CombinedAtomActualNerve

open SelectedFiniteGeometry
open PointAtomActualNerve
open CombinedAtomContextSupport

/-- Fine actual Cech cover on the combined point/generator site. -/
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

/-- Coarse actual Cech cover on the combined point/generator site. -/
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
  AAT.AG.ObstructionDiagnosticBridge.CombinedAtomActualNerve

end CombinedAtomActualNerve
end AAT.AG.ObstructionDiagnosticBridge
