import ResearchLean.AG.QualitySurface.TraceTransport

/-!
Cycle 5 evidence for `G-aat-quality-surface-01`.

The file fixes a finite state-separation witness: measured zero, unmeasured,
and trace-missing certificates can share the same visible scalar reading and
selected verdict while differing in actual measurement, selector state, support,
trace status, and next obligation.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace StateSeparation

/-! ## Certificate state components -/

/-- Visible verdict selected for the lossful display layer. -/
inductive StateVerdict where
  | acceptable
  deriving DecidableEq

/-- Whether the selected profile actually measured the predicate. -/
inductive MeasurementState where
  | measured
  | unmeasured
  deriving DecidableEq

/-- Whether the certificate selector applies at the selected profile. -/
inductive SelectorState where
  | selected
  | outside
  deriving DecidableEq

/-- Trace availability state for selected support. -/
inductive TraceStatus where
  | traced
  | noSelectedSupport
  | missingTrace
  deriving DecidableEq

/-- The next obligation exposed by the certificate state. -/
inductive ObligationKind where
  | none
  | measure
  | provideTrace
  deriving DecidableEq

/-- A finite support atom used by the trace-missing witness. -/
inductive StateAtom where
  | a
  deriving DecidableEq, Fintype

/-- Trace token used by the state-separation witness. -/
inductive StateTraceToken where
  | refA
  deriving DecidableEq

/--
Finite certificate tuple for the state-separation witness.

`visibleScalarReading` is a display convention. `actualMeasurement?` records
whether the selected measurement actually exists.
-/
structure QualityCertificate where
  visibleScalarReading : Nat
  verdict : StateVerdict
  measurementState : MeasurementState
  selectorState : SelectorState
  actualMeasurement? : Option Nat
  selectedSupport? : Option (Set StateAtom)
  traceField : StateAtom -> Option StateTraceToken
  traceStatus : TraceStatus
  obligation : ObligationKind

open StateVerdict MeasurementState SelectorState TraceStatus ObligationKind

/-- The selected support used by the trace-missing certificate. -/
def supportA : Set StateAtom :=
  fun atom => atom = StateAtom.a

/-- Empty trace field for certificates with no selected support. -/
def emptyTraceField : StateAtom -> Option StateTraceToken :=
  fun _ => none

/-- Trace field that is missing on the selected support atom. -/
def missingTraceField : StateAtom -> Option StateTraceToken :=
  fun _ => none

/-- A measured-zero certificate has an actual zero measurement. -/
def measuredZeroCert : QualityCertificate where
  visibleScalarReading := 0
  verdict := acceptable
  measurementState := measured
  selectorState := selected
  actualMeasurement? := some 0
  selectedSupport? := some (fun _ => False)
  traceField := emptyTraceField
  traceStatus := noSelectedSupport
  obligation := none

/-- An unmeasured certificate is outside the selected certificate selector. -/
def unmeasuredCert : QualityCertificate where
  visibleScalarReading := 0
  verdict := acceptable
  measurementState := unmeasured
  selectorState := outside
  actualMeasurement? := none
  selectedSupport? := none
  traceField := emptyTraceField
  traceStatus := noSelectedSupport
  obligation := measure

/-- A trace-missing certificate has selected support but lacks trace coverage. -/
def traceMissingCert : QualityCertificate where
  visibleScalarReading := 0
  verdict := acceptable
  measurementState := measured
  selectorState := selected
  actualMeasurement? := some 0
  selectedSupport? := some supportA
  traceField := missingTraceField
  traceStatus := missingTrace
  obligation := provideTrace

/-- A compact state signature protected under the certificate geometry. -/
def protectedStateSignature (c : QualityCertificate) :
    MeasurementState × SelectorState × Option Nat ×
      Option (Set StateAtom) × TraceStatus × ObligationKind :=
  (c.measurementState, c.selectorState, c.actualMeasurement?,
    c.selectedSupport?, c.traceStatus, c.obligation)

/-- The selected support, if any, has a missing trace in the actual trace field. -/
def SelectedTraceMissing (c : QualityCertificate) : Prop :=
  ∃ support, c.selectedSupport? = some support ∧
    TraceTransport.TraceMissingOn support c.traceField

/-! ## Structural facts for the three states -/

/-- Measured-zero has a genuine actual zero measurement. -/
theorem measuredZero_has_actual_zero :
    measuredZeroCert.actualMeasurement? = some 0 :=
  rfl

/-- Unmeasured has no actual measurement; its visible zero is a display value. -/
theorem unmeasured_has_no_actual_measurement :
    unmeasuredCert.actualMeasurement? = (Option.none : Option Nat) :=
  rfl

/-- Unmeasured is outside the selected certificate selector. -/
theorem unmeasured_selector_outside :
    unmeasuredCert.selectorState = outside :=
  rfl

/-- Measured-zero has no follow-up obligation. -/
theorem measuredZero_obligation_none :
    measuredZeroCert.obligation = ObligationKind.none :=
  rfl

/-- Unmeasured requires a measurement obligation rather than a zero certificate. -/
theorem unmeasured_obligation_measure :
    unmeasuredCert.obligation = ObligationKind.measure :=
  rfl

/-- Trace-missing has a selected support. -/
theorem traceMissing_has_selected_support :
    traceMissingCert.selectedSupport? = some supportA :=
  rfl

/-- Trace-missing also has an actual measured zero value. -/
theorem traceMissing_has_actual_zero :
    traceMissingCert.actualMeasurement? = some 0 :=
  rfl

/-- Trace-missing has a selected support and a missing trace status. -/
theorem traceMissing_has_selected_support_and_missing_trace :
    traceMissingCert.selectedSupport? = some supportA ∧
      TraceTransport.TraceMissingOn supportA traceMissingCert.traceField ∧
      traceMissingCert.traceStatus = missingTrace := by
  refine And.intro rfl ?_
  refine And.intro ?_ rfl
  exact ⟨StateAtom.a, rfl, rfl⟩

/-- Trace-missing requires a trace-provision obligation. -/
theorem traceMissing_obligation_provideTrace :
    traceMissingCert.obligation = provideTrace :=
  rfl

/-- Measured-zero does not have a selected trace-missing support. -/
theorem measuredZero_not_selectedTraceMissing :
    ¬ SelectedTraceMissing measuredZeroCert := by
  intro hmissing
  rcases hmissing with ⟨support, hsupport, atom, hatom, _htrace⟩
  have hset : (fun _ : StateAtom => False) = support :=
    Option.some.inj hsupport
  have hfalse : (fun _ : StateAtom => False) atom := by
    rw [hset]
    exact hatom
  exact hfalse

/-- Trace-missing has an actual missing trace on the selected support. -/
theorem traceMissing_selectedTraceMissing :
    SelectedTraceMissing traceMissingCert := by
  exact ⟨supportA, rfl, StateAtom.a, rfl, rfl⟩

/-- The three certificates share the same visible scalar reading. -/
theorem same_visibleScalar_three_states :
    measuredZeroCert.visibleScalarReading =
        unmeasuredCert.visibleScalarReading ∧
      measuredZeroCert.visibleScalarReading =
        traceMissingCert.visibleScalarReading :=
  And.intro rfl rfl

/-- The three certificates share the same selected verdict. -/
theorem same_verdict_three_states :
    measuredZeroCert.verdict = unmeasuredCert.verdict ∧
      measuredZeroCert.verdict = traceMissingCert.verdict :=
  And.intro rfl rfl

/-- The visible scalar / verdict layer identifies the three certificate states. -/
theorem same_scalar_verdict_three_states :
    measuredZeroCert.visibleScalarReading =
        unmeasuredCert.visibleScalarReading ∧
      measuredZeroCert.visibleScalarReading =
        traceMissingCert.visibleScalarReading ∧
      measuredZeroCert.verdict = unmeasuredCert.verdict ∧
      measuredZeroCert.verdict = traceMissingCert.verdict := by
  exact And.intro rfl (And.intro rfl (And.intro rfl rfl))

/-- Measured-zero and unmeasured have different protected signatures. -/
theorem measuredZero_state_ne_unmeasured :
    protectedStateSignature measuredZeroCert ≠
      protectedStateSignature unmeasuredCert := by
  intro h
  have hstate : MeasurementState.measured = MeasurementState.unmeasured :=
    congrArg Prod.fst h
  cases hstate

/-- Measured-zero and trace-missing have different protected signatures. -/
theorem measuredZero_state_ne_traceMissing :
    protectedStateSignature measuredZeroCert ≠
      protectedStateSignature traceMissingCert := by
  intro h
  have hstatus : TraceStatus.noSelectedSupport = TraceStatus.missingTrace :=
    congrArg (fun s => s.2.2.2.2.1) h
  cases hstatus

/-- Unmeasured and trace-missing have different protected signatures. -/
theorem unmeasured_state_ne_traceMissing :
    protectedStateSignature unmeasuredCert ≠
      protectedStateSignature traceMissingCert := by
  intro h
  have hstate : MeasurementState.unmeasured = MeasurementState.measured :=
    congrArg Prod.fst h
  cases hstate

/-- The protected state signatures are pairwise distinct. -/
theorem state_components_pairwise_distinct :
    protectedStateSignature measuredZeroCert ≠
        protectedStateSignature unmeasuredCert ∧
      protectedStateSignature measuredZeroCert ≠
        protectedStateSignature traceMissingCert ∧
      protectedStateSignature unmeasuredCert ≠
        protectedStateSignature traceMissingCert :=
  And.intro measuredZero_state_ne_unmeasured
    (And.intro measuredZero_state_ne_traceMissing
      unmeasured_state_ne_traceMissing)

/--
The three zero-looking certificates are separated by actual measurement,
selector state, trace-field evidence, and obligation.
-/
theorem zeroLooking_certificates_state_separated :
    measuredZeroCert.visibleScalarReading =
        unmeasuredCert.visibleScalarReading ∧
      measuredZeroCert.visibleScalarReading =
        traceMissingCert.visibleScalarReading ∧
      measuredZeroCert.verdict = unmeasuredCert.verdict ∧
      measuredZeroCert.verdict = traceMissingCert.verdict ∧
      measuredZeroCert.actualMeasurement? = some 0 ∧
      unmeasuredCert.actualMeasurement? = (Option.none : Option Nat) ∧
      traceMissingCert.actualMeasurement? = some 0 ∧
      unmeasuredCert.selectorState = outside ∧
      traceMissingCert.selectedSupport? = some supportA ∧
      SelectedTraceMissing traceMissingCert ∧
      ¬ SelectedTraceMissing measuredZeroCert ∧
      measuredZeroCert.obligation = ObligationKind.none ∧
      unmeasuredCert.obligation = ObligationKind.measure ∧
      traceMissingCert.obligation = provideTrace ∧
      protectedStateSignature measuredZeroCert ≠
          protectedStateSignature unmeasuredCert ∧
        protectedStateSignature measuredZeroCert ≠
          protectedStateSignature traceMissingCert ∧
        protectedStateSignature unmeasuredCert ≠
          protectedStateSignature traceMissingCert := by
  exact And.intro rfl
    (And.intro rfl
    (And.intro rfl
    (And.intro rfl
    (And.intro measuredZero_has_actual_zero
    (And.intro unmeasured_has_no_actual_measurement
    (And.intro traceMissing_has_actual_zero
    (And.intro unmeasured_selector_outside
    (And.intro traceMissing_has_selected_support
    (And.intro traceMissing_selectedTraceMissing
    (And.intro measuredZero_not_selectedTraceMissing
    (And.intro measuredZero_obligation_none
    (And.intro unmeasured_obligation_measure
    (And.intro traceMissing_obligation_provideTrace
      state_components_pairwise_distinct)))))))))))))

/-- Faithfulness of a scalar / verdict projection to protected state. -/
def ScalarVerdictFaithfulToState
    (r : QualityCertificate -> Nat)
    (v : QualityCertificate -> StateVerdict) : Prop :=
  ∀ c₁ c₂ : QualityCertificate,
    r c₁ = r c₂ ->
      v c₁ = v c₂ ->
        protectedStateSignature c₁ = protectedStateSignature c₂

/-- Faithfulness of a scalar / verdict projection to selected trace-missing state. -/
def ScalarVerdictFaithfulToTraceMissing
    (r : QualityCertificate -> Nat)
    (v : QualityCertificate -> StateVerdict) : Prop :=
  ∀ c₁ c₂ : QualityCertificate,
    r c₁ = r c₂ ->
      v c₁ = v c₂ ->
        (SelectedTraceMissing c₁ ↔ SelectedTraceMissing c₂)

/-- The visible scalar / verdict projection is not faithful to certificate state. -/
theorem scalarVerdict_not_faithful_to_certificateState :
    ¬ ScalarVerdictFaithfulToState
      (fun c => c.visibleScalarReading) (fun c => c.verdict) := by
  intro hfaithful
  have hstate :=
    hfaithful measuredZeroCert unmeasuredCert rfl rfl
  exact measuredZero_state_ne_unmeasured hstate

/--
The same scalar / verdict projection also cannot recover whether a selected
support has actual missing trace evidence.
-/
theorem scalarVerdict_not_faithful_to_traceMissingState :
    ¬ ScalarVerdictFaithfulToState
      (fun c => c.visibleScalarReading) (fun c => c.verdict) := by
  intro hfaithful
  have hstate :=
    hfaithful measuredZeroCert traceMissingCert rfl rfl
  exact measuredZero_state_ne_traceMissing hstate

/--
The visible scalar / verdict projection cannot recover selected trace-missing
evidence derived from `selectedSupport?` and the actual `traceField`.
-/
theorem scalarVerdict_not_faithful_to_selectedTraceMissing :
    ¬ ScalarVerdictFaithfulToTraceMissing
      (fun c => c.visibleScalarReading) (fun c => c.verdict) := by
  intro hfaithful
  have hiff :=
    hfaithful measuredZeroCert traceMissingCert rfl rfl
  have hmissingMeasuredZero : SelectedTraceMissing measuredZeroCert :=
    hiff.mpr traceMissing_selectedTraceMissing
  exact measuredZero_not_selectedTraceMissing hmissingMeasuredZero

end StateSeparation
end QualitySurface
end ResearchLean.AG
