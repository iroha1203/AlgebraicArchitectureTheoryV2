import ResearchLean.AG.ObstructionDiagnosticBridge.ActualCechH1Comparison
import Formal.Util.AssertStandardAxioms

/-!
# Specified affine local data and its obstruction/diagnostic classes

For a face-empty actual Cech input, local affine data consist of a primitive
edge translation `xi` and one integral presentation-valued state on each chart.
The actual mismatch is `xi + d0 p`, the paper equation (1).  Its law-value
diagnostic is independently evaluated as the degree-one Law-value evaluation
of `xi` plus diagnostic `d0` of the degree-zero evaluation of `p`.  The cochain
comparison then proves that this formula equals the image of the actual
mismatch.

## Implementation notes

The transition is stored as a degree-one cochain rather than an H1 class.  This
keeps the obstruction derived from local comparison data and permits both zero
and nonzero classes.  Defining the mismatch as only `d0 p` was rejected because
it would force every specified class to vanish.  Face-index emptiness is used
only to prove the resulting mismatch is a cocycle; it does not choose its class.
The diagnostic is neither an independent input nor definitionally the image of
the actual cocycle: its Law-value generation formula is built first and its
agreement with that image is a theorem.
-/

noncomputable section

namespace AAT.AG.ObstructionDiagnosticBridge

open CanonicalResolution Cohomology ResolutionInvariance TwoPhase

universe u

namespace GeneratorPresentation

variable {Source : Type u} [Fintype Source]
variable {q : Reading Source} {laws : FiniteLawFamily Source}
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {D : TargetSupportedNerve q} {G : ContextOpenSupport S}
variable [IsEmpty D.nerve.FaceComponent]

/-- Primitive affine transition and chart-state data for the selected actual cover. -/
structure ActualCechAffineLocalData (P : GeneratorPresentation laws)
    (C : FaceEmptyAATCechCover D G) where
  transition : (P.faceEmptyCechComplex C).Cn 1
  localState : (P.faceEmptyCechComplex C).Cn 0

namespace ActualCechAffineLocalData

variable {P : GeneratorPresentation laws} {C : FaceEmptyAATCechCover D G}

/-- Paper equation (1): primitive transition plus the chart-state coboundary. -/
def actualMismatch (x : ActualCechAffineLocalData P C) :
    (P.faceEmptyCechComplex C).Cn 1 :=
  x.transition + (P.faceEmptyCechComplex C).d 0 x.localState

/-- Change only the local chart coordinates by an additive correction. -/
def adjustLocalState (x : ActualCechAffineLocalData P C)
    (correction : (P.faceEmptyCechComplex C).Cn 0) :
    ActualCechAffineLocalData P C where
  transition := x.transition
  localState := x.localState + correction

omit [Fintype Source] in
/-- Paper equation (2): changing local coordinates adds one coboundary. -/
theorem actual_mismatch_adjust_local_state
    (x : ActualCechAffineLocalData P C)
    (correction : (P.faceEmptyCechComplex C).Cn 0) :
    (x.adjustLocalState correction).actualMismatch =
      x.actualMismatch + (P.faceEmptyCechComplex C).d 0 correction := by
  simp [adjustLocalState, actualMismatch, map_add]
  abel

/-- The specified actual mismatch is a cocycle because the face index is empty. -/
def actualCocycle (x : ActualCechAffineLocalData P C) :
    (P.faceEmptyCechComplex C).CechCocycle 1 :=
  ⟨x.actualMismatch, by
    rw [P.faceEmptyCech_d1_eq_zero C]
    rfl⟩

/-- Actual obstruction class generated from the primitive affine local data. -/
def actualClass (x : ActualCechAffineLocalData P C) :
    (P.faceEmptyCechComplex C).AdditiveCechH1 :=
  (P.faceEmptyCechComplex C).additiveH1Class x.actualCocycle

omit [Fintype Source] in
/-- Changing local chart coordinates does not change the actual obstruction class. -/
theorem actual_class_adjust_local_state
    (x : ActualCechAffineLocalData P C)
    (correction : (P.faceEmptyCechComplex C).Cn 0) :
    (x.adjustLocalState correction).actualClass = x.actualClass := by
  change
    ((⟨(x.adjustLocalState correction).actualCocycle.1,
        (x.adjustLocalState correction).actualCocycle.2⟩ :
        (P.faceEmptyCechComplex C).CechCocycleSubgroup 1) :
      (P.faceEmptyCechComplex C).AdditiveCechH1) =
    ((⟨x.actualCocycle.1, x.actualCocycle.2⟩ :
        (P.faceEmptyCechComplex C).CechCocycleSubgroup 1) :
      (P.faceEmptyCechComplex C).AdditiveCechH1)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  refine ⟨correction, ?_⟩
  apply Subtype.ext
  change (x.adjustLocalState correction).actualMismatch - x.actualMismatch =
    (P.faceEmptyCechComplex C).d 0 correction
  rw [x.actual_mismatch_adjust_local_state correction]
  abel

/-- Law-value mismatch independently evaluated from transition and chart state. -/
def diagnosticMismatch (x : ActualCechAffineLocalData P C)
    (hadequate : laws.Adequate q) :
    D.EdgeCoordinate laws hadequate → ℚ :=
  P.actualCechCoefficientCochain1 C hadequate x.transition +
    D.lawGeneratedD0 laws hadequate
      (P.actualCechCoefficientCochain0 C hadequate x.localState)

omit [Fintype Source] in
/-- The actual comparison sends equation (1) to the Law-value generation formula. -/
theorem actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch
    (x : ActualCechAffineLocalData P C) (hadequate : laws.Adequate q) :
    P.actualCechCoefficientCochain1 C hadequate x.actualMismatch =
      x.diagnosticMismatch hadequate := by
  rw [actualMismatch, map_add, P.actualCechCoefficient_comm0]
  rfl

/-- Law-value diagnostic cocycle generated independently from the same local data. -/
def diagnosticCocycle (x : ActualCechAffineLocalData P C)
    (hadequate : laws.Adequate q) :
    LinearMap.ker (D.lawGeneratedComplex laws hadequate).d1 :=
  ⟨x.diagnosticMismatch hadequate, by
    rw [← x.actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch hadequate]
    exact (P.actualCechDiagnosticCyclesMap C hadequate
      ⟨x.actualCocycle.1, x.actualCocycle.2⟩).2⟩

/-- Diagnostic H1 class generated from the same local affine data. -/
def diagnosticClass (x : ActualCechAffineLocalData P C)
    (hadequate : laws.Adequate q) :
    (D.lawGeneratedComplex laws hadequate).H1 :=
  (LinearMap.range
    (D.lawGeneratedComplex laws hadequate).boundaryToCycles).mkQ
      (x.diagnosticCocycle hadequate)

/-- G-125(B1): the induced H1 map sends the specified obstruction class to its diagnostic. -/
theorem h1_map_actual_class_eq_diagnostic_class
    (x : ActualCechAffineLocalData P C) (hadequate : laws.Adequate q) :
    P.actualCechDiagnosticH1Map C hadequate x.actualClass =
      x.diagnosticClass hadequate := by
  rw [actualClass, P.actual_cech_diagnostic_h1_map_additive_h1_class]
  apply congrArg
  apply Subtype.ext
  exact x.actual_cech_coefficient_actual_mismatch_eq_diagnostic_mismatch hadequate

/-- G-125(B1): vanishing of the specified obstruction class implies diagnostic vanishing. -/
theorem diagnostic_class_eq_zero_of_actual_class_eq_zero
    (x : ActualCechAffineLocalData P C) (hadequate : laws.Adequate q)
    (hzero : x.actualClass = 0) :
    x.diagnosticClass hadequate = 0 := by
  rw [← x.h1_map_actual_class_eq_diagnostic_class hadequate, hzero, map_zero]

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation.ActualCechAffineLocalData

end ActualCechAffineLocalData
end GeneratorPresentation
end AAT.AG.ObstructionDiagnosticBridge
