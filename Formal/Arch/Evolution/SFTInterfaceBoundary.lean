import Formal.Arch.Evolution.SFTField
import Formal.Arch.Signature.SignatureLawfulness

namespace Formal.Arch

universe u v w

/--
A selected AAT theorem-status package as it is exposed to SFT.

The record keeps theorem evidence, measured-zero evidence, unmeasured-axis
boundaries, tooling/report boundaries, and non-conclusions separate. SFT may
read this package as a local premise, but the package is not itself a forecast
correctness certificate.
-/
structure AATTheoremStatus where
  theoremPackage : Prop
  measuredZeroEvidence : Prop
  theoremBoundary : Prop
  unmeasuredAxisBoundary : Prop
  toolingBoundary : Prop
  nonConclusions : Prop

namespace AATTheoremStatus

/-- The selected AAT theorem package is available as theorem-status evidence. -/
def RecordsTheoremPackage (status : AATTheoremStatus) : Prop :=
  status.theoremPackage

/-- Selected measured-zero evidence remains explicit. -/
def RecordsMeasuredZeroEvidence (status : AATTheoremStatus) : Prop :=
  status.measuredZeroEvidence

/-- The AAT theorem boundary remains explicit. -/
def RecordsTheoremBoundary (status : AATTheoremStatus) : Prop :=
  status.theoremBoundary

/-- Unmeasured axes remain explicit rather than silently safe. -/
def RecordsUnmeasuredAxisBoundary (status : AATTheoremStatus) : Prop :=
  status.unmeasuredAxisBoundary

/-- Tooling/report assumptions remain boundary data, not stronger theorem status. -/
def RecordsToolingBoundary (status : AATTheoremStatus) : Prop :=
  status.toolingBoundary

/-- AAT-level non-conclusions remain explicit. -/
def RecordsNonConclusions (status : AATTheoremStatus) : Prop :=
  status.nonConclusions

/--
Read the existing Signature-integrated zero-curvature theorem package as an
AAT theorem-status item for SFT interface purposes.
-/
noncomputable def ofArchitectureZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    (measuredZeroEvidence theoremBoundary unmeasuredAxisBoundary
      toolingBoundary nonConclusions : Prop) :
    AATTheoremStatus where
  theoremPackage := ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X
  measuredZeroEvidence := measuredZeroEvidence
  theoremBoundary := theoremBoundary
  unmeasuredAxisBoundary := unmeasuredAxisBoundary
  toolingBoundary := toolingBoundary
  nonConclusions := nonConclusions

/-- The zero-curvature constructor exposes the stored theorem package. -/
theorem records_theoremPackage_of_architectureZeroCurvatureTheoremPackage
    {C : Type u} {A : Type v} {Obs : Type w}
    (X : ArchitectureSignature.ArchitectureLawModel C A Obs)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs]
    [DecidableRel X.G.edge] [DecidableRel X.GA.edge]
    [DecidableRel X.boundaryAllowed] [DecidableRel X.abstractionAllowed]
    {measuredZeroEvidence theoremBoundary unmeasuredAxisBoundary
      toolingBoundary nonConclusions : Prop}
    (hPackage : ArchitectureSignature.ArchitectureZeroCurvatureTheoremPackage X) :
    (ofArchitectureZeroCurvatureTheoremPackage X measuredZeroEvidence
      theoremBoundary unmeasuredAxisBoundary toolingBoundary
      nonConclusions).RecordsTheoremPackage :=
  hPackage

end AATTheoremStatus

/--
SFT-side forecast status exposed at the AAT/SFT interface.

The fields are intentionally proposition-valued. They track what an SFT
forecast package still owes: local premises, support/model boundaries,
trajectory safety, unmeasured-axis safety, theorem boundaries, tooling
boundaries, forecast boundaries, and non-conclusions.
-/
structure SFTForecastStatus where
  localPremise : Prop
  supportBoundary : Prop
  trajectorySafetyBoundary : Prop
  measuredAxisBoundary : Prop
  unmeasuredAxisBoundary : Prop
  theoremBoundary : Prop
  toolingBoundary : Prop
  forecastBoundary : Prop
  nonConclusions : Prop

namespace SFTForecastStatus

/-- The SFT forecast status records a local premise supplied by AAT. -/
def RecordsLocalPremise (status : SFTForecastStatus) : Prop :=
  status.localPremise

/-- Support/model assumptions remain explicit. -/
def RecordsSupportBoundary (status : SFTForecastStatus) : Prop :=
  status.supportBoundary

/-- Future trajectory safety remains an explicit boundary obligation. -/
def RecordsTrajectorySafetyBoundary (status : SFTForecastStatus) : Prop :=
  status.trajectorySafetyBoundary

/-- Measured-axis assumptions remain explicit. -/
def RecordsMeasuredAxisBoundary (status : SFTForecastStatus) : Prop :=
  status.measuredAxisBoundary

/-- Unmeasured-axis safety remains an explicit boundary obligation. -/
def RecordsUnmeasuredAxisBoundary (status : SFTForecastStatus) : Prop :=
  status.unmeasuredAxisBoundary

/-- The theorem/modeling boundary remains explicit on the SFT side. -/
def RecordsTheoremBoundary (status : SFTForecastStatus) : Prop :=
  status.theoremBoundary

/-- Tooling/report assumptions remain explicit on the SFT side. -/
def RecordsToolingBoundary (status : SFTForecastStatus) : Prop :=
  status.toolingBoundary

/-- Forecast correctness/calibration remains an explicit boundary obligation. -/
def RecordsForecastBoundary (status : SFTForecastStatus) : Prop :=
  status.forecastBoundary

/-- SFT forecast non-conclusions remain explicit. -/
def RecordsNonConclusions (status : SFTForecastStatus) : Prop :=
  status.nonConclusions

end SFTForecastStatus

/--
Boundary relation for reading AAT theorem status as an SFT local premise.

The relation preserves the one-way reading used by the SFT documents: AAT
theorem evidence can serve as a local premise, while trajectory safety,
unmeasured-axis safety, tooling boundaries, forecast boundaries, and
non-conclusions remain live obligations.
-/
structure AATToSFTInterfaceBoundary
    (aat : AATTheoremStatus) (forecast : SFTForecastStatus) : Prop where
  readsAATAsLocalPremise :
    aat.RecordsTheoremPackage -> forecast.RecordsLocalPremise
  preservesAATTheoremBoundary :
    aat.RecordsTheoremBoundary -> forecast.RecordsTheoremBoundary
  preservesMeasuredAxisBoundary :
    aat.RecordsMeasuredZeroEvidence -> forecast.RecordsMeasuredAxisBoundary
  preservesUnmeasuredAxisBoundary :
    aat.RecordsUnmeasuredAxisBoundary -> forecast.RecordsUnmeasuredAxisBoundary
  preservesToolingBoundary :
    aat.RecordsToolingBoundary -> forecast.RecordsToolingBoundary
  recordsSupportBoundary :
    forecast.RecordsSupportBoundary
  recordsTrajectorySafetyBoundary :
    forecast.RecordsTrajectorySafetyBoundary
  recordsForecastBoundary :
    forecast.RecordsForecastBoundary
  recordsNonConclusions :
    aat.RecordsNonConclusions -> forecast.RecordsNonConclusions

namespace AATToSFTInterfaceBoundary

variable {aat : AATTheoremStatus} {forecast : SFTForecastStatus}

/-- AAT theorem status is read as an SFT local premise, not as the full forecast. -/
theorem aat_theorem_status_as_local_premise
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hAAT : aat.RecordsTheoremPackage) :
    forecast.RecordsLocalPremise :=
  hBoundary.readsAATAsLocalPremise hAAT

/--
AAT lawfulness/theorem status alone does not discharge SFT trajectory safety:
the trajectory-safety boundary is still recorded by the interface package.
-/
theorem aat_lawfulness_alone_does_not_discharge_trajectory_safety_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast) :
    forecast.RecordsTrajectorySafetyBoundary :=
  hBoundary.recordsTrajectorySafetyBoundary

/--
Measured-zero AAT evidence does not discharge unmeasured-axis safety: the
unmeasured-axis boundary is preserved explicitly.
-/
theorem measured_zero_does_not_discharge_unmeasured_axis_safety_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hUnmeasured : aat.RecordsUnmeasuredAxisBoundary) :
    forecast.RecordsUnmeasuredAxisBoundary :=
  hBoundary.preservesUnmeasuredAxisBoundary hUnmeasured

/--
Tool/report output crossing the interface remains tooling-boundary data on the
SFT side, not stronger AAT theorem status.
-/
theorem tool_report_output_does_not_strengthen_aat_theorem_status
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hTooling : aat.RecordsToolingBoundary) :
    forecast.RecordsToolingBoundary :=
  hBoundary.preservesToolingBoundary hTooling

/-- AAT theorem-boundary records stay visible as SFT theorem-boundary records. -/
theorem preserves_theorem_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hTheoremBoundary : aat.RecordsTheoremBoundary) :
    forecast.RecordsTheoremBoundary :=
  hBoundary.preservesAATTheoremBoundary hTheoremBoundary

/-- Measured-axis evidence can be preserved without becoming unmeasured-axis safety. -/
theorem preserves_measured_axis_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hMeasured : aat.RecordsMeasuredZeroEvidence) :
    forecast.RecordsMeasuredAxisBoundary :=
  hBoundary.preservesMeasuredAxisBoundary hMeasured

/-- Forecast correctness/calibration remains an explicit SFT boundary. -/
theorem forecast_status_records_forecast_boundary
    (hBoundary : AATToSFTInterfaceBoundary aat forecast) :
    forecast.RecordsForecastBoundary :=
  hBoundary.recordsForecastBoundary

/-- Interface non-conclusions are preserved into SFT forecast status. -/
theorem interface_preserves_nonConclusions
    (hBoundary : AATToSFTInterfaceBoundary aat forecast)
    (hNonConclusions : aat.RecordsNonConclusions) :
    forecast.RecordsNonConclusions :=
  hBoundary.recordsNonConclusions hNonConclusions

end AATToSFTInterfaceBoundary

end Formal.Arch
