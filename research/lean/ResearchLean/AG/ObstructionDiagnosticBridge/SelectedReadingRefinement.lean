import ResearchLean.AG.ObstructionDiagnosticBridge.PointAtomActualNerve
import ResearchLean.AG.ObstructionDiagnosticBridge.PointAtomLawInput
import ResearchLean.AG.ResolutionInvariance.GeneratedComparisonMap
import Formal.Util.AssertStandardAxioms

/-!
# Selected coarse-to-fine reading and cover refinement

This module records the actual refinement geometry used by G-125(C).  Fine
charts `a0` and `a1` lie over the joined coarse chart `c0`; the remaining
charts retain their names.  The internal fine edge `k` is contracted, while
the other three edges map to the corresponding coarse overlaps.

The same chart and edge maps define the supported-nerve morphism used by the
existing generated diagnostic comparison.  No cochain commutation or
cohomology conclusion is stored in the refinement data.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge
namespace SelectedReadingRefinement

open CanonicalResolution ResolutionInvariance
open SelectedFiniteGeometry PointAtomActualNerve PointAtomLawInput

/-- Fine charts mapped to the coarse chart that contains their actual patch. -/
def chartMap : FineChart → CoarseChart
  | .a0 | .a1 => .c0
  | .b => .c1
  | .c => .c2

/-- Every fine patch is contained in the coarse patch selected by `chartMap`. -/
theorem finePatch_le_coarsePatch_chartMap (chart : FineChart) :
    finePatch chart ≤ coarsePatch (chartMap chart) := by
  cases chart
  · exact finePatch_a0_le_coarsePatch_c0
  · exact finePatch_a1_le_coarsePatch_c0
  · exact le_of_eq finePatch_b_eq_coarsePatch_c1
  · exact le_of_eq finePatch_c_eq_coarsePatch_c2

/-- Fine edges mapped to coarse edges; the internal edge `k` is contracted. -/
def edgeMap : Edge → Option CoarseEdge
  | .k => none
  | .ab => some .ab
  | .bc => some .bc
  | .ac => some .ac

/-- The selected refinement as the existing canonical supported-nerve morphism. -/
def nerveMorphism :
    TargetSupportedNerveMorphism coarseReading fineReading coarse_coarser_fine
      coarseSupportedNerve fineSupportedNerve where
  chartMap := chartMap
  edgeMap := edgeMap
  faceMap := isEmptyElim
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    cases fineEdge <;> cases coarseEdge <;>
      simp [edgeMap, chartMap, fineSupportedNerve, coarseSupportedNerve,
        fineNerve, coarseNerve, fineEdgeLeft, coarseEdgeLeft] at hmap ⊢
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    cases fineEdge <;> cases coarseEdge <;>
      simp [edgeMap, chartMap, fineSupportedNerve, coarseSupportedNerve,
        fineNerve, coarseNerve, fineEdgeRight, coarseEdgeRight] at hmap ⊢
  edge_none_fiber := by
    intro fineEdge hmap
    cases fineEdge <;>
      simp [edgeMap, chartMap, fineSupportedNerve, fineNerve,
        fineEdgeLeft, fineEdgeRight] at hmap ⊢
  face_some_edge0 := by intro fineFace; exact isEmptyElim fineFace
  face_some_edge1 := by intro fineFace; exact isEmptyElim fineFace
  face_some_edge2 := by intro fineFace; exact isEmptyElim fineFace
  face_none_edge0 := by intro fineFace; exact isEmptyElim fineFace
  face_none_edge1 := by intro fineFace; exact isEmptyElim fineFace
  face_none_edge2 := by intro fineFace; exact isEmptyElim fineFace
  chartSupport_compatible := by
    intro fineChart fineTarget _
    exact Set.mem_univ _

/-- A mapped fine overlap is contained in its actual coarse overlap. -/
theorem fineOverlap_le_coarseOverlap_of_edgeMap_some
    (fineEdge : Edge) (coarseEdge : CoarseEdge)
    (hmap : edgeMap fineEdge = some coarseEdge) :
    fineOverlap fineEdge ≤ coarseOverlap coarseEdge := by
  cases fineEdge <;> cases coarseEdge <;>
    simp [edgeMap] at hmap
  · exact inf_le_inf finePatch_a1_le_coarsePatch_c0 le_rfl
  · exact le_rfl
  · exact inf_le_inf finePatch_a0_le_coarsePatch_c0 le_rfl

/-- The contracted edge overlap lies inside its common coarse chart. -/
theorem contractedOverlap_le_coarsePatch :
    fineOverlap .k ≤ coarsePatch .c0 := by
  exact le_trans inf_le_left finePatch_a0_le_coarsePatch_c0

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.SelectedReadingRefinement

end SelectedReadingRefinement
end AAT.AG.ObstructionDiagnosticBridge
