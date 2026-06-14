import Formal.AG.Measurement.Profile

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v

/-!
PRD-8 R1 / AC3-AC4 verdict discipline.

`MeasurementVerdict` separates measured zero, measured nonzero, unmeasured,
unknown, and not-computed states by constructors with profile-relative payloads.
No theorem treats unmeasured as zero or unknown as nonzero.
-/

/-- VIII.Definition 3.1: profile-relative measurement verdicts. -/
inductive MeasurementVerdict (M : MeasurementProfile.{u, v}) (alpha : M.Domain) where
  | measured_zero :
      M.InScope alpha -> M.Zero alpha -> M.CertRef alpha ->
        MeasurementVerdict M alpha
  | measured_nonzero :
      M.InScope alpha -> M.NonZero alpha -> M.CertRef alpha ->
        MeasurementVerdict M alpha
  | unmeasured :
      M.OutOfScope alpha -> MeasurementVerdict M alpha
  | unknown :
      M.InScope alpha -> M.Undecided alpha -> MeasurementVerdict M alpha
  | not_computed :
      M.NotRunOrUnavailable alpha -> MeasurementVerdict M alpha

namespace MeasurementVerdict

/-- VIII.Principle 3.2: an unmeasured verdict is not a measured-zero verdict. -/
theorem unmeasured_ne_measured_zero {M : MeasurementProfile.{u, v}} {alpha : M.Domain}
    (hout : M.OutOfScope alpha) (hin : M.InScope alpha)
    (hz : M.Zero alpha) (cert : M.CertRef alpha) :
    MeasurementVerdict.unmeasured (M := M) (alpha := alpha) hout ≠
      MeasurementVerdict.measured_zero hin hz cert := by
  intro h
  cases h

/-- VIII.Principle 3.2: an unknown verdict is not a measured-nonzero verdict. -/
theorem unknown_ne_measured_nonzero {M : MeasurementProfile.{u, v}} {alpha : M.Domain}
    (hin : M.InScope alpha) (hundecided : M.Undecided alpha)
    (hnonzero : M.NonZero alpha) (cert : M.CertRef alpha) :
    MeasurementVerdict.unknown (M := M) (alpha := alpha) hin hundecided ≠
      MeasurementVerdict.measured_nonzero hin hnonzero cert := by
  intro h
  cases h

/-- VIII.Principle 3.2: a not-computed verdict is not an unmeasured verdict. -/
theorem not_computed_ne_unmeasured {M : MeasurementProfile.{u, v}} {alpha : M.Domain}
    (hnot : M.NotRunOrUnavailable alpha) (hout : M.OutOfScope alpha) :
    MeasurementVerdict.not_computed (M := M) (alpha := alpha) hnot ≠
      MeasurementVerdict.unmeasured hout := by
  intro h
  cases h

end MeasurementVerdict

/--
VIII.Definition 3.1: data attached to a selected verdict.

The optional fields are deliberately payload channels, not implicit conversions
between analytic readings and structural verdicts.
-/
structure VerdictData (M : MeasurementProfile.{u, v}) (alpha : M.Domain) where
  verdict : MeasurementVerdict M alpha
  method? : Option (M.SelectedMethod alpha)
  cert? : Option (M.CertRef alpha)

/-- VIII.Definition 3.3: structural verdicts remain separate from analytics. -/
inductive StructuralVerdict (M : MeasurementProfile.{u, v}) (alpha : M.Domain) where
  | fromMeasurement : MeasurementVerdict M alpha -> StructuralVerdict M alpha
  | structuralBoundary : M.InScope alpha -> Prop -> StructuralVerdict M alpha

/-- VIII.Definition 3.3: analytic readings are value readings, not verdicts. -/
structure AnalyticReading (M : MeasurementProfile.{u, v}) (alpha : M.Domain) where
  Value : Type v
  value : Value
  readingCertificate : Prop
  readingCertificate_holds : readingCertificate

end Measurement
end AAT.AG
