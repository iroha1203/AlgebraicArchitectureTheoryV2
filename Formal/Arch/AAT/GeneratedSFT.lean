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
    (measuredZeroEvidence theoremBoundary unmeasuredAxisBoundary
      toolingBoundary nonConclusions : Prop) :
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
    measuredZeroEvidence theoremBoundary unmeasuredAxisBoundary
    toolingBoundary nonConclusions

/-- Generated SFT theorem status records the generated theorem package. -/
theorem generatedAATTheoremStatusForSFT_recordsTheoremPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [hRelation : DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object)
    {measuredZeroEvidence theoremBoundary unmeasuredAxisBoundary
      toolingBoundary nonConclusions : Prop} :
    (model.generatedAATTheoremStatusForSFT measuredZeroEvidence
      theoremBoundary unmeasuredAxisBoundary toolingBoundary
      nonConclusions).RecordsTheoremPackage := by
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
    (model : GeneratedArchitectureLawModel object) where
  theoremStatus : AATTheoremStatus
  theoremStatusFromGenerated : theoremStatus.RecordsTheoremPackage
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
variable {model : GeneratedArchitectureLawModel object}

/-- SFT reads the generated AAT package as input. -/
theorem reads_generated_aat (input : GeneratedSFTInput model) :
    input.sftReadsGeneratedAAT :=
  input.sftReadsGeneratedAATEvidence

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
