import ResearchLean.AG.ObstructionDiagnosticBridge.ActualCechReadingComparison
import ResearchLean.AG.ObstructionDiagnosticBridge.SelectedReadingRefinement
import ResearchLean.AG.ObstructionDiagnosticBridge.CombinedAtomSpecifiedObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Reading naturality on the selected combined-Atom input

This module instantiates the actual coarse-to-fine Cech map with the genuine
three-patch to four-patch refinement.  The diagnostic comparison is exactly
the existing `generatedComparisonH1Map` for the same supported-nerve
morphism.  Their H1 square commutes, and primitive transition/chart-state
data are transported degreewise to prove transport of the specified actual
and diagnostic classes.

`ConditionC` and bijectivity are not used here; those belong to G-125(C2).
-/

noncomputable section

open CategoryTheory

namespace AAT.AG.ObstructionDiagnosticBridge
namespace CombinedAtomReadingNaturality

open Cohomology ResolutionInvariance TwoPhase
open PointAtomLawInput PointAtomActualNerve
open CombinedAtomSpecifiedObstruction
open SelectedReadingRefinement
open SelectedFiniteGeometry CombinedAtomContextSupport

set_option maxHeartbeats 1000000

/-- Actual context restriction from a fine chart to its containing coarse chart. -/
def chartRestriction (chart : FineChart) :
    CombinedAtomActualNerve.fineCechCover.chartContext chart ⟶
      CombinedAtomActualNerve.coarseCechCover.chartContext (chartMap chart) :=
  homOfLE (openContext_le (finePatch_le_coarsePatch_chartMap chart))

/-- Actual context restriction from a mapped fine overlap to its coarse overlap. -/
def edgeRestriction (fineEdge : Edge) (coarseEdge : CoarseEdge)
    (hmap : edgeMap fineEdge = some coarseEdge) :
    CombinedAtomActualNerve.fineCechCover.edgeContext fineEdge ⟶
      CombinedAtomActualNerve.coarseCechCover.edgeContext coarseEdge :=
  homOfLE (openContext_le
    (fineOverlap_le_coarseOverlap_of_edgeMap_some fineEdge coarseEdge hmap))

/-- Actual coarse-to-fine H1 map induced by the selected cover refinement. -/
def actualH1Map :
    (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).AdditiveCechH1 →+
      (presentation.faceEmptyCechComplex
        CombinedAtomActualNerve.fineCechCover).AdditiveCechH1 :=
  presentation.actualCechRefinementH1Map nerveMorphism

/-- Diagnostic comparison is the existing generated H1 map for the same refinement. -/
def diagnosticH1Map :
    (coarseSupportedNerve.lawGeneratedComplex laws coarse_adequate).H1 →ₗ[ℚ]
      (fineSupportedNerve.lawGeneratedComplex laws fine_adequate).H1 :=
  nerveMorphism.generatedComparisonH1Map laws coarse_adequate fine_adequate

/-- The coordinate pullback on charts is the actual sheaf restriction. -/
theorem actualCechPullback0_apply
    (cochain : (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).Cn 0)
    (chart : FineChart) :
    presentation.actualCechPullback0
        (coarseCover := CombinedAtomActualNerve.coarseCechCover)
        (fineCover := CombinedAtomActualNerve.fineCechCover)
        nerveMorphism cochain chart =
      (presentation.aatLocallyConstantObstructionSheaf
        contextOpenSupport).carrier.toPresheaf.map (chartRestriction chart).op
          (cochain (chartMap chart)) := by
  letI := CombinedAtomActualNerve.fineCechCover.chartSupportNonempty chart
  letI := CombinedAtomActualNerve.fineCechCover.chartSupportPreconnected chart
  letI := CombinedAtomActualNerve.coarseCechCover.chartSupportNonempty (chartMap chart)
  letI := CombinedAtomActualNerve.coarseCechCover.chartSupportPreconnected (chartMap chart)
  apply (presentation.aatLocallyConstantObstructionSectionEquiv contextOpenSupport
    (CombinedAtomActualNerve.fineCechCover.chartContext chart)).injective
  rw [presentation.aatLocallyConstantObstructionSectionEquiv_restriction]
  rfl

/-- On a mapped edge, the coordinate pullback is the actual overlap restriction. -/
theorem actualCechPullback1_apply_of_some
    (cochain : (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).Cn 1)
    (fineEdge : Edge) (coarseEdge : CoarseEdge)
    (hmap : edgeMap fineEdge = some coarseEdge) :
    presentation.actualCechPullback1
        (coarseCover := CombinedAtomActualNerve.coarseCechCover)
        (fineCover := CombinedAtomActualNerve.fineCechCover)
        nerveMorphism cochain fineEdge =
      (presentation.aatLocallyConstantObstructionSheaf
        contextOpenSupport).carrier.toPresheaf.map
          (edgeRestriction fineEdge coarseEdge hmap).op
          (cochain coarseEdge) := by
  letI := CombinedAtomActualNerve.fineCechCover.edgeSupportNonempty fineEdge
  letI := CombinedAtomActualNerve.fineCechCover.edgeSupportPreconnected fineEdge
  letI := CombinedAtomActualNerve.coarseCechCover.edgeSupportNonempty coarseEdge
  letI := CombinedAtomActualNerve.coarseCechCover.edgeSupportPreconnected coarseEdge
  apply (presentation.aatLocallyConstantObstructionSectionEquiv contextOpenSupport
    (CombinedAtomActualNerve.fineCechCover.edgeContext fineEdge)).injective
  rw [presentation.aatLocallyConstantObstructionSectionEquiv_restriction]
  change (nerveMorphism.edgeMap fineEdge).elim 0
      (presentation.faceEmptyCechCochain1Equiv
        CombinedAtomActualNerve.coarseCechCover cochain) =
    presentation.faceEmptyCechCochain1Equiv
      CombinedAtomActualNerve.coarseCechCover cochain coarseEdge
  rw [show nerveMorphism.edgeMap fineEdge = some coarseEdge from hmap]
  rfl

/-- The contracted internal edge receives the zero actual section. -/
theorem actualCechPullback1_contracted
    (cochain : (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).Cn 1) :
    presentation.actualCechPullback1
        (coarseCover := CombinedAtomActualNerve.coarseCechCover)
        (fineCover := CombinedAtomActualNerve.fineCechCover)
        nerveMorphism cochain Edge.k =
      (0 : (presentation.faceEmptyCechComplex
        CombinedAtomActualNerve.fineCechCover).Cn 1) Edge.k := by
  letI := CombinedAtomActualNerve.fineCechCover.edgeSupportNonempty Edge.k
  letI := CombinedAtomActualNerve.fineCechCover.edgeSupportPreconnected Edge.k
  apply (presentation.aatLocallyConstantObstructionSectionEquiv contextOpenSupport
    (CombinedAtomActualNerve.fineCechCover.edgeContext Edge.k)).injective
  change (nerveMorphism.edgeMap Edge.k).elim 0
      (presentation.faceEmptyCechCochain1Equiv
        CombinedAtomActualNerve.coarseCechCover cochain) = 0
  rfl

/-- G-125(C1): the actual/diagnostic H1 comparison square commutes. -/
theorem h1_comparison_square :
    CombinedAtomH1Input.fineH1Map.comp actualH1Map =
      diagnosticH1Map.toAddMonoidHom.comp CombinedAtomH1Input.coarseH1Map :=
  presentation.actualCechDiagnosticH1_naturality nerveMorphism
    coarse_adequate fine_adequate

/-- Transport primitive transition and chart-state data by the actual refinement. -/
def mapLocalData (x : CoarseLocalData) : FineLocalData where
  transition := presentation.actualCechPullback1 nerveMorphism x.transition
  localState := presentation.actualCechPullback0 nerveMorphism x.localState

/-- The transported specified mismatch is the pullback of the coarse mismatch. -/
theorem mapLocalData_actualMismatch (x : CoarseLocalData) :
    (mapLocalData x).actualMismatch =
      presentation.actualCechPullback1 nerveMorphism x.actualMismatch := by
  rw [GeneratorPresentation.ActualCechAffineLocalData.actualMismatch,
    GeneratorPresentation.ActualCechAffineLocalData.actualMismatch]
  change
    presentation.actualCechPullback1 nerveMorphism x.transition +
        (presentation.faceEmptyCechComplex
          CombinedAtomActualNerve.fineCechCover).d 0
          (presentation.actualCechPullback0 nerveMorphism x.localState) =
      presentation.actualCechPullback1 nerveMorphism
        (x.transition +
          (presentation.faceEmptyCechComplex
            CombinedAtomActualNerve.coarseCechCover).d 0 x.localState)
  rw [map_add, presentation.actualCechPullback_comm0]

/-- The actual H1 map carries the specified coarse class to the transported fine class. -/
theorem actualH1Map_actualClass (x : CoarseLocalData) :
    actualH1Map x.actualClass = (mapLocalData x).actualClass := by
  rw [actualH1Map,
    GeneratorPresentation.ActualCechAffineLocalData.actualClass,
    GeneratorPresentation.actualCechRefinementH1Map_additiveH1Class,
    GeneratorPresentation.ActualCechAffineLocalData.actualClass]
  apply congrArg
  apply Subtype.ext
  exact (mapLocalData_actualMismatch x).symm

/-- C1 transports the existing coarse descent obstruction class to the fine one. -/
theorem actualH1Map_existingObstructionClass (x : CoarseLocalData) :
    actualH1Map (coarseExistingObstructionClass x) =
      fineExistingObstructionClass (mapLocalData x) := by
  rw [coarse_existing_obstruction_class_eq_actual_class,
    fine_existing_obstruction_class_eq_actual_class]
  exact actualH1Map_actualClass x

/-- C1 also transports the independently generated specified diagnostic class. -/
theorem diagnosticH1Map_diagnosticClass (x : CoarseLocalData) :
    diagnosticH1Map (x.diagnosticClass coarse_adequate) =
      (mapLocalData x).diagnosticClass fine_adequate := by
  rw [← x.h1_map_actual_class_eq_diagnostic_class coarse_adequate]
  rw [← (mapLocalData x).h1_map_actual_class_eq_diagnostic_class fine_adequate]
  rw [← actualH1Map_actualClass x]
  exact congrArg (fun map => map x.actualClass) h1_comparison_square.symm

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.CombinedAtomReadingNaturality

end CombinedAtomReadingNaturality
end AAT.AG.ObstructionDiagnosticBridge
