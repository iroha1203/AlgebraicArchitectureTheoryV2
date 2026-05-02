import Formal.Arch.Flatness
import Formal.Arch.ArchitectureExtensionFormula
import Formal.Arch.Repair
import Formal.Arch.RepairSynthesis
import Formal.Arch.ComplexityTransfer
import Formal.Arch.ArchitectureEvolution

/-!
Documentation-facing entrypoints for the mathematical design Chapter 7 theorem
packages.

This module is intentionally thin.  Importing it exposes the representative
bounded theorem packages for sections 7.1 through 7.6 without adding new global
flatness, completeness, solver-completeness, or extractor-completeness claims.
-/

namespace Formal.Arch

namespace Chapter7TheoremPackages

/-- The six center theorem candidates listed in Chapter 7 of the design note. -/
inductive Candidate where
  | splitExtensionPreservation
  | nonSplitExtensionWitness
  | repairAsResplitting
  | complexityTransfer
  | noSolutionCertificate
  | architectureEvolution
  deriving DecidableEq, Repr

namespace Candidate

/-- Human-readable section number in `docs/aat_v2_mathematical_design.md`. -/
def designSection : Candidate -> String
  | splitExtensionPreservation => "7.1"
  | nonSplitExtensionWitness => "7.2"
  | repairAsResplitting => "7.3"
  | complexityTransfer => "7.4"
  | noSolutionCertificate => "7.5"
  | architectureEvolution => "7.6"

/-- Stable schematic name used by documentation and future API-index tables. -/
def schematicName : Candidate -> String
  | splitExtensionPreservation => "Split Extension Preservation"
  | nonSplitExtensionWitness => "Non-split Extension Witness"
  | repairAsResplitting => "Repair as Re-splitting"
  | complexityTransfer => "Complexity Transfer"
  | noSolutionCertificate => "No-solution Certificate"
  | architectureEvolution => "Architecture Evolution"

/-- Representative Lean declarations that serve as public entrypoints. -/
def representativeDeclarations : Candidate -> List String
  | splitExtensionPreservation =>
      ["SplitFeatureExtensionWithin",
       "architectureFlatWithin_of_splitFeatureExtensionWithin",
       "LawfulExtensionPreservesFlatness",
       "LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation"]
  | nonSplitExtensionWitness =>
      ["NonSplitExtensionWitnessPackage",
       "NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness",
       "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension",
       "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension"]
  | repairAsResplitting =>
      ["SelectedObstructionUniverse",
       "AdmissibleRepairRule",
       "repairStepDecreases_of_admissible",
       "extensionObstructionMeasure_decreases_of_admissible"]
  | complexityTransfer =>
      ["BoundedComplexityTransferPackage",
       "BoundedComplexityTransferPackage.complexityTransfer_selectedAlternative",
       "BoundedComplexityTransferPackage.no_free_elimination_bounded"]
  | noSolutionCertificate =>
      ["NoSolutionCertificate",
       "ValidNoSolutionCertificate",
       "NoSolutionCertificate.sound_of_valid"]
  | architectureEvolution =>
      ["ArchitectureTransition",
       "ArchitectureEvolution",
       "ArchitectureTransition.flatness_of_transitionPreservesFlatness",
       "ArchitectureTransition.reportedObstruction_of_drift",
       "eventuallyFlat_of_targetFlat",
       "evolutionPathPreservesFlatness"]

/-- Boundary reminder for reading each candidate as a bounded theorem package. -/
def nonConclusionBoundary : Candidate -> String
  | splitExtensionPreservation =>
      "coverage-aware ArchitectureFlatWithin only; no global flatness or extractor completeness"
  | nonSplitExtensionWitness =>
      "soundness plus bounded completeness under explicit coverage / exactness assumptions only"
  | repairAsResplitting =>
      "selected obstruction measure decrease only; no all-obstruction removal or termination"
  | complexityTransfer =>
      "selected runtime / semantic / policy transfer witnesses only; no global conservation or empirical cost theorem"
  | noSolutionCertificate =>
      "valid certificate soundness only; solver failure alone is not a no-solution proof"
  | architectureEvolution =>
      "selected transition / path predicates only; no automatic preservation for all transitions"

end Candidate

end Chapter7TheoremPackages

end Formal.Arch
