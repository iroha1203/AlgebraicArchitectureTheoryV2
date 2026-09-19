import ResearchLean.AG.ObstructionDiagnosticBridge.ActualCechH1Comparison
import ResearchLean.AG.ObstructionDiagnosticBridge.CombinedAtomActualNerve
import ResearchLean.AG.ObstructionDiagnosticBridge.PointAtomLawInput
import Formal.Util.AssertStandardAxioms

/-!
# Selected same-input H1 comparisons on the combined Atom site

This module instantiates the actual Cech-to-diagnostic cochain and H1 maps with
the selected nonconstant Law, its coarse and fine adequacy witnesses, and the
actual covers constructed on the combined point/generator site.  Consequently
the obstruction source, primitive presentation, Law evaluation, and diagnostic
nerve are all tied to the same fixed G-125 input.

## Implementation notes

The generic quotient construction is kept in `ActualCechH1Comparison`; this
module supplies only the selected input data.  Reusing the Cycle 13 point-only
Cech covers was rejected because their source site lacks generator Atoms.
Duplicating the law-generated complexes was also rejected: both targets are
the existing `TargetSupportedNerve.lawGeneratedComplex` values.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge
namespace CombinedAtomH1Input

open Cohomology TwoPhase
open PointAtomLawInput

/-- Fine actual Cech-to-diagnostic cochain map on the combined site. -/
def fineCochainMap :=
  presentation.actualCechCoefficientCochainMap
    CombinedAtomActualNerve.fineCechCover fine_adequate

/-- Coarse actual Cech-to-diagnostic cochain map on the combined site. -/
def coarseCochainMap :=
  presentation.actualCechCoefficientCochainMap
    CombinedAtomActualNerve.coarseCechCover coarse_adequate

/-- Fine additive H1 comparison for the selected combined input. -/
def fineH1Map :
    (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.fineCechCover).AdditiveCechH1 →+
      (PointAtomActualNerve.fineSupportedNerve.lawGeneratedComplex
        laws fine_adequate).H1 :=
  presentation.actualCechDiagnosticH1Map
    CombinedAtomActualNerve.fineCechCover fine_adequate

/-- Coarse additive H1 comparison for the selected combined input. -/
def coarseH1Map :
    (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).AdditiveCechH1 →+
      (PointAtomActualNerve.coarseSupportedNerve.lawGeneratedComplex
        laws coarse_adequate).H1 :=
  presentation.actualCechDiagnosticH1Map
    CombinedAtomActualNerve.coarseCechCover coarse_adequate

/-- Fine H1 comparison sends a represented actual class by the selected degree-one map.

The simp normal form exposes the existing diagnostic quotient representative.
-/
@[simp]
theorem fineH1Map_additiveH1Class
    (cocycle : (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.fineCechCover).CechCocycle 1) :
    fineH1Map
        ((presentation.faceEmptyCechComplex
          CombinedAtomActualNerve.fineCechCover).additiveH1Class cocycle) =
      (LinearMap.range
          (PointAtomActualNerve.fineSupportedNerve.lawGeneratedComplex
            laws fine_adequate).boundaryToCycles).mkQ
        (presentation.actualCechDiagnosticCyclesMap
          CombinedAtomActualNerve.fineCechCover fine_adequate
          ⟨cocycle.1, cocycle.2⟩) :=
  rfl

/-- Coarse H1 comparison sends a represented actual class by the selected degree-one map.

The simp normal form exposes the existing diagnostic quotient representative.
-/
@[simp]
theorem coarseH1Map_additiveH1Class
    (cocycle : (presentation.faceEmptyCechComplex
      CombinedAtomActualNerve.coarseCechCover).CechCocycle 1) :
    coarseH1Map
        ((presentation.faceEmptyCechComplex
          CombinedAtomActualNerve.coarseCechCover).additiveH1Class cocycle) =
      (LinearMap.range
          (PointAtomActualNerve.coarseSupportedNerve.lawGeneratedComplex
            laws coarse_adequate).boundaryToCycles).mkQ
        (presentation.actualCechDiagnosticCyclesMap
          CombinedAtomActualNerve.coarseCechCover coarse_adequate
          ⟨cocycle.1, cocycle.2⟩) :=
  rfl

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.CombinedAtomH1Input

end CombinedAtomH1Input
end AAT.AG.ObstructionDiagnosticBridge
