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

/--
A stable documentation-facing mapping from schematic names in Chapter 7 to the
Lean declarations that currently carry the corresponding bounded package.
-/
structure SchematicCorrespondence where
  schematic : String
  leanDeclarations : List String
  reading : String
  status : String
  deriving Repr

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

/--
Schematic-name to Lean-API correspondences for Chapter 7.

These rows are intentionally metadata only.  They stabilize how the design-note
schematic names are read against existing bounded Lean packages without adding
new theorems or global completeness claims.
-/
def schematicCorrespondences : Candidate -> List SchematicCorrespondence
  | splitExtensionPreservation =>
      [{ schematic := "SplitFeatureExtensionWithin U X F X'",
         leanDeclarations :=
          ["SplitFeatureExtensionWithin",
           "splitFeatureExtensionWithin_of_runtimeSemanticSplitPreservation"],
         reading :=
          "public bounded split-feature-extension package over an explicit component universe",
         status := "defined only / proved" },
       { schematic := "InteractionLawfulWithin U X F X'",
         leanDeclarations :=
          ["RuntimeSemanticSplitPreservation",
           "RuntimeInteractionProtected",
           "FeatureDiagramsCommute",
           "LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation"],
         reading :=
          "runtime interaction protection plus selected semantic diagram commutation",
         status := "defined only / proved" },
       { schematic := "ArchitectureFlatWithin U X'",
         leanDeclarations :=
          ["ArchitectureFlatWithin",
           "architectureFlatWithin_of_splitFeatureExtensionWithin",
           "LawfulExtensionPreservesFlatness"],
         reading :=
          "bounded architecture flatness relative to coverage and measured semantic diagrams",
         status := "defined only / proved" }]
  | nonSplitExtensionWitness =>
      [{ schematic := "ExtensionObstructionWitness X F X' w",
         leanDeclarations :=
          ["ExtensionObstructionWitness",
           "SelectedExtensionObstructionWitness",
           "NonSplitExtensionWitnessPackage.WitnessPredicate"],
         reading :=
          "selected obstruction witness inside an explicit witness universe",
         status := "defined only" },
       { schematic := "ExtensionWitnessComplete X F X'",
         leanDeclarations :=
          ["NonSplitExtensionWitnessPackage.coverageAssumptions",
           "NonSplitExtensionWitnessPackage.exactnessAssumptions",
           "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension"],
         reading :=
          "coverage and exactness assumptions required for the bounded completeness direction",
         status := "proved under package assumptions" }]
  | repairAsResplitting =>
      [{ schematic := "NonSplitExtensionWitness X F X' w",
         leanDeclarations :=
          ["SelectedObstructionUniverse",
           "NonSplitExtensionWitness"],
         reading :=
          "selected witness for the chosen obstruction universe, not all obstructions",
         status := "defined only" },
       { schematic := "AdmissibleRepairRule r w",
         leanDeclarations :=
          ["AdmissibleRepairRule",
           "repairStepDecreases_of_admissible",
           "extensionObstructionMeasure_decreases_of_admissible"],
         reading :=
          "selected-rule admissibility that proves decrease of the selected obstruction measure",
         status := "defined only / proved" }]
  | complexityTransfer =>
      [{ schematic := "ComplexityTransferredTo Runtime/Semantic/Policy t",
         leanDeclarations :=
          ["ComplexityTransferredTo",
           "ComplexityTransferTarget.runtime",
           "ComplexityTransferTarget.semantic",
           "ComplexityTransferTarget.policy",
           "ComplexityTransferredWithinSelectedTargets"],
         reading :=
          "selected transfer witness for one bounded diagnostic target axis",
         status := "defined only / proved" },
       { schematic := "Complexity Transfer theorem candidate",
         leanDeclarations :=
          ["BoundedComplexityTransferPackage",
           "BoundedComplexityTransferPackage.complexityTransfer_selectedAlternative",
           "BoundedComplexityTransferPackage.no_free_elimination_bounded"],
         reading :=
          "bounded alternative: proof elimination or selected runtime / semantic / policy transfer",
         status := "defined only / proved" }]
  | noSolutionCertificate =>
      [{ schematic := "ProducesNoSolutionCertificate C cert",
         leanDeclarations :=
          ["NoSolutionCertificate"],
         reading :=
          "proof-carrying no-solution certificate package, not solver failure alone",
         status := "defined only" },
       { schematic := "ValidNoSolutionCertificate cert C",
         leanDeclarations :=
          ["ValidNoSolutionCertificate",
           "NoSolutionCertificate.sound_of_valid"],
         reading :=
          "valid certificate soundness for the selected constraint system",
         status := "defined only / proved" }]
  | architectureEvolution =>
      [{ schematic := "TransitionPreservesFlatness t",
         leanDeclarations :=
          ["ArchitectureTransition.TransitionPreservesFlatness",
           "ArchitectureTransition.flatness_of_transitionPreservesFlatness"],
         reading :=
          "single-step preservation for a selected flatness predicate",
         status := "defined only / proved" },
       { schematic := "ReportedObstruction (ApplyTransition X t) w",
         leanDeclarations :=
          ["ArchitectureTransition.ReportedObstruction",
           "ArchitectureTransition.reportedObstruction_of_drift"],
         reading :=
          "drift-reporting theorem relative to selected drift evidence",
         status := "defined only / proved" },
       { schematic := "EventuallyFlat plan",
         leanDeclarations :=
          ["EventuallyFlat",
           "eventuallyFlat_of_targetFlat",
           "evolutionPathPreservesFlatness"],
         reading :=
          "bounded eventual flatness for a selected migration path or preserving path",
         status := "defined only / proved" }]

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
