import ResearchLean.AG.ObstructionDiagnosticBridge.ActualCechH1Comparison
import Formal.Util.AssertStandardAxioms

/-!
# Specified affine local data and its obstruction/diagnostic classes

For a face-empty actual Cech input, local affine data consist of a primitive
edge translation `xi` and one integral presentation-valued state on each chart.
The actual mismatch is `xi + d0 p`, the paper equation (1).  Its law-value
diagnostic is obtained by applying the already constructed degree-one
comparison, not by independently supplying a diagnostic cocycle.

## Implementation notes

The transition is stored as a degree-one cochain rather than an H1 class.  This
keeps the obstruction derived from local comparison data and permits both zero
and nonzero classes.  Defining the mismatch as only `d0 p` was rejected because
it would force every specified class to vanish.  Face-index emptiness is used
only to prove the resulting mismatch is a cocycle; it does not choose its class.
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

/-- Law-value diagnostic cocycle generated from the same actual mismatch. -/
def diagnosticCocycle (x : ActualCechAffineLocalData P C)
    (hadequate : laws.Adequate q) :
    LinearMap.ker (D.lawGeneratedComplex laws hadequate).d1 :=
  P.actualCechDiagnosticCyclesMap C hadequate
    ⟨x.actualCocycle.1, x.actualCocycle.2⟩

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
      x.diagnosticClass hadequate :=
  rfl

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
