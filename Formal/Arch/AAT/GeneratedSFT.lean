import Formal.Arch.AAT.GeneratedSignature
import Formal.Arch.Evolution.SFTInterfaceBoundary

namespace Formal.Arch
namespace AAT

universe u v

namespace GeneratedArchitectureLawModel

/--
Theorem status exported from an Atom-generated law model to SFT.

The status is built from the generated `ArchitectureLawModel`; it is not a
separate hand-authored SFT premise and it is not a forecast-correctness
certificate.
-/
noncomputable def generatedAATTheoremStatusForSFT
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [hRelation : DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object)
    (theoremBoundary unmeasuredAxisBoundary toolingBoundary
      nonConclusions : Prop) :
    AATTheoremStatus := by
  letI : DecidableRel model.toArchitectureLawModel.G.edge := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.GA.edge := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.boundaryAllowed := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.abstractionAllowed := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  exact AATTheoremStatus.ofArchitectureZeroCurvatureTheoremPackage
    model.toArchitectureLawModel
    (ArchitectureSignature.RequiredSignatureAxesZero model.signatureOfGenerated)
    theoremBoundary unmeasuredAxisBoundary toolingBoundary nonConclusions

/-- Generated SFT theorem status records the generated theorem package. -/
theorem generatedAATTheoremStatusForSFT_recordsTheoremPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [hRelation : DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object)
    {theoremBoundary unmeasuredAxisBoundary toolingBoundary
      nonConclusions : Prop} :
    (model.generatedAATTheoremStatusForSFT theoremBoundary
      unmeasuredAxisBoundary toolingBoundary nonConclusions).RecordsTheoremPackage := by
  letI : DecidableRel model.toArchitectureLawModel.G.edge := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.GA.edge := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.boundaryAllowed := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.abstractionAllowed := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  exact
    ArchitectureSignature.architectureZeroCurvatureTheoremPackage_of_architectureLawful
      model.toArchitectureLawModel
      model.generatedArchitectureLawful

/-- Generated SFT theorem status records generated measured-zero evidence. -/
theorem generatedAATTheoremStatusForSFT_recordsMeasuredZeroEvidence
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [hRelation : DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object)
    {theoremBoundary unmeasuredAxisBoundary toolingBoundary
      nonConclusions : Prop} :
    (model.generatedAATTheoremStatusForSFT theoremBoundary
      unmeasuredAxisBoundary toolingBoundary
      nonConclusions).RecordsMeasuredZeroEvidence :=
  model.generated_requiredSignatureAxesZero

end GeneratedArchitectureLawModel

/--
SFT input boundary generated from an Atom-generated AAT law model.

This record packages what FieldSig/SFT may consume: generated theorem status
and explicit boundaries.  It deliberately does not say that AAT proves forecast
correctness.
-/
structure GeneratedSFTInput {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object) where
  theoremBoundary : Prop
  unmeasuredAxisBoundary : Prop
  toolingBoundary : Prop
  sftReadsGeneratedAAT : Prop
  sftReadsGeneratedAATEvidence : sftReadsGeneratedAAT
  sftDoesNotRedefineAtoms : Prop
  sftDoesNotRedefineAtomsEvidence : sftDoesNotRedefineAtoms
  sftDoesNotRedefineAAT : Prop
  sftDoesNotRedefineAATEvidence : sftDoesNotRedefineAAT
  forecastCorrectnessBoundary : Prop
  forecastCorrectnessBoundaryEvidence : forecastCorrectnessBoundary
  sftEventDoesNotCreateAtomsEvidence : system.noSFTEventCreatesAtoms
  nonConclusions : Prop

namespace GeneratedSFTInput

variable {system : AtomAxiomSystem.{u, v}}
variable {presentation : AtomShapePresentation system}
variable {object : GeneratedArchitectureObject presentation}
variable [DecidableEq system.Atom]
variable [DecidableRel (GeneratedRelation object)]
variable {model : GeneratedArchitectureLawModel object}

/-- The SFT-visible theorem status is computed from the generated law model. -/
noncomputable def theoremStatus
    (input : GeneratedSFTInput model) :
    AATTheoremStatus :=
  model.generatedAATTheoremStatusForSFT input.theoremBoundary
    input.unmeasuredAxisBoundary input.toolingBoundary input.nonConclusions

/-- The computed SFT theorem status is definitionally the generated status. -/
theorem theoremStatus_eq_generated
    (input : GeneratedSFTInput model) :
    input.theoremStatus =
      model.generatedAATTheoremStatusForSFT input.theoremBoundary
        input.unmeasuredAxisBoundary input.toolingBoundary
        input.nonConclusions := by
  rfl

/-- Generated SFT input exposes a theorem package generated from Atom data. -/
theorem theoremStatusFromGenerated
    (input : GeneratedSFTInput model) :
    input.theoremStatus.RecordsTheoremPackage :=
  model.generatedAATTheoremStatusForSFT_recordsTheoremPackage

/-- Generated SFT input exposes generated measured-zero evidence. -/
theorem measured_zero_from_generated
    (input : GeneratedSFTInput model) :
    input.theoremStatus.RecordsMeasuredZeroEvidence :=
  model.generatedAATTheoremStatusForSFT_recordsMeasuredZeroEvidence

/-- SFT reads the generated AAT package as input. -/
theorem reads_generated_aat (input : GeneratedSFTInput model) :
    input.sftReadsGeneratedAAT :=
  input.sftReadsGeneratedAATEvidence

/-- Generated AAT theorem status crosses the SFT interface as a local premise. -/
theorem reads_generated_aat_as_sft_local_premise
    (input : GeneratedSFTInput model)
    {forecast : SFTForecastStatus}
    (hBoundary :
      AATToSFTInterfaceBoundary input.theoremStatus forecast) :
    forecast.RecordsLocalPremise :=
  AATToSFTInterfaceBoundary.aat_theorem_status_as_local_premise
    hBoundary input.theoremStatusFromGenerated

/-- SFT does not redefine atoms when consuming generated AAT. -/
theorem sft_does_not_redefine_atoms (input : GeneratedSFTInput model) :
    input.sftDoesNotRedefineAtoms :=
  input.sftDoesNotRedefineAtomsEvidence

/-- SFT does not redefine AAT when consuming generated AAT. -/
theorem sft_does_not_redefine_aat (input : GeneratedSFTInput model) :
    input.sftDoesNotRedefineAAT :=
  input.sftDoesNotRedefineAATEvidence

/-- Forecast correctness remains outside the generated AAT theorem package. -/
theorem forecast_correctness_remains_boundary
    (input : GeneratedSFTInput model) :
    input.forecastCorrectnessBoundary :=
  input.forecastCorrectnessBoundaryEvidence

/-- SFT events do not create Atom existence. -/
theorem sft_event_does_not_create_atoms
    (input : GeneratedSFTInput model) :
    system.noSFTEventCreatesAtoms :=
  input.sftEventDoesNotCreateAtomsEvidence

end GeneratedSFTInput

end AAT
end Formal.Arch
