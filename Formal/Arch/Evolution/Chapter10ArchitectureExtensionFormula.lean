import Formal.Arch.Extension.ArchitectureExtensionFormula

/-!
Documentation-facing entrypoint for the mathematical design Chapter 10
Structural Architecture Extension Formula package.

This module is intentionally thin. Importing it exposes the single-label and
multi-label structural classification theorems plus the bridge APIs that connect
selected filling, lifting, complexity-transfer, and residual-coverage payloads
to the extension-obstruction classification universe. It does not add disjoint
classification, global witness completeness, universe-wide obstruction
coverage, or extractor-completeness claims.
-/

namespace Formal.Arch

namespace Chapter10ArchitectureExtensionFormula

/--
A stable documentation-facing mapping from schematic names in Chapter 10 to the
Lean declarations that currently carry the corresponding bounded API.
-/
structure SchematicCorrespondence where
  schematic : String
  leanDeclarations : List String
  reading : String
  status : String
  deriving Repr

/-- The main Chapter 10 API groups exposed through this entrypoint. -/
inductive Candidate where
  | obstructionUniverse
  | nonSplitWitnessPackage
  | singleLabelClassification
  | multiLabelClassification
  | fillingFailureBridge
  | liftingFailureBridge
  | complexityTransferBridge
  | residualCoverageGapBridge
  deriving DecidableEq, Repr

namespace Candidate

/-- Human-readable section number in `docs/aat_v2_mathematical_design.md`. -/
def designSection : Candidate -> String
  | obstructionUniverse => "10"
  | nonSplitWitnessPackage => "10"
  | singleLabelClassification => "10"
  | multiLabelClassification => "10"
  | fillingFailureBridge => "10 / 9"
  | liftingFailureBridge => "10 / 9.2"
  | complexityTransferBridge => "10 / 7.4"
  | residualCoverageGapBridge => "10 / FeatureExtension coverage"

/-- Stable schematic name used by documentation and theorem-index tables. -/
def schematicName : Candidate -> String
  | obstructionUniverse => "Extension obstruction universe"
  | nonSplitWitnessPackage => "Non-split witness package"
  | singleLabelClassification => "Single-label structural classification"
  | multiLabelClassification => "Multi-label structural classification"
  | fillingFailureBridge => "Filling failure bridge"
  | liftingFailureBridge => "Lifting failure bridge"
  | complexityTransferBridge => "Complexity transfer bridge"
  | residualCoverageGapBridge => "Residual coverage gap bridge"

/-- Representative Lean declarations that serve as public entrypoints. -/
def representativeDeclarations : Candidate -> List String
  | obstructionUniverse =>
      ["ExtensionCoverage",
       "ExtensionObstructionClass",
       "ExtensionObstructionWitness",
       "MultiLabelExtensionObstructionWitness",
       "ExtensionObstructionWitness.toMultiLabel",
       "ExtensionObstructionWitness.toMultiLabel_label_iff",
       "ExtensionObstructionWitness.toMultiLabel_classifiesAs"]
  | nonSplitWitnessPackage =>
      ["SelectedSplitExtension",
       "SelectedExtensionObstructionWitness",
       "SelectedExtensionObstructionWitnessExists",
       "NonSplitExtensionWitnessPackage",
       "NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness",
       "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension",
       "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension"]
  | singleLabelClassification =>
      ["ClassifiedAsInheritedCore",
       "ClassifiedAsFeatureLocal",
       "ClassifiedAsInteraction",
       "ClassifiedAsLiftingFailure",
       "ClassifiedAsFillingFailure",
       "ClassifiedAsComplexityTransfer",
       "ClassifiedAsResidualCoverageGap",
       "ArchitectureExtensionFormula_structural"]
  | multiLabelClassification =>
      ["MultiLabelClassifiedAsInheritedCore",
       "MultiLabelClassifiedAsFeatureLocal",
       "MultiLabelClassifiedAsInteraction",
       "MultiLabelClassifiedAsLiftingFailure",
       "MultiLabelClassifiedAsFillingFailure",
       "MultiLabelClassifiedAsComplexityTransfer",
       "MultiLabelClassifiedAsResidualCoverageGap",
       "ArchitectureExtensionFormula_multilabel_structural"]
  | fillingFailureBridge =>
      ["FillingFailureWitnessPayload",
       "fillingFailureExtensionObstructionWitness",
       "fillingFailureExtensionObstructionWitness_classified",
       "FillingFailureRefutesSplit",
       "not_selectedSplitExtension_of_fillingFailurePayload",
       "FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage",
       "fillingFailureExtensionObstructionWitness_multilabel_classified"]
  | liftingFailureBridge =>
      ["LiftingFailureWitnessPayload",
       "liftingFailureExtensionObstructionWitness",
       "liftingFailureExtensionObstructionWitness_classified",
       "not_compatibleWithInterface_of_liftingFailurePayload",
       "liftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage",
       "liftingFailureExtensionObstructionWitness_multilabel_classified"]
  | complexityTransferBridge =>
      ["ComplexityTransferWitnessPayload",
       "complexityTransferExtensionObstructionWitness",
       "complexityTransferExtensionObstructionWitness_classified",
       "complexityTransferExtensionObstructionWitnessExists_of_transferredTo",
       "complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
       "complexityTransferExtensionObstructionWitness_multilabel_classified"]
  | residualCoverageGapBridge =>
      ["ResidualCoverageGapWitnessPayload",
       "residualCoverageGapExtensionObstructionWitness",
       "residualCoverageGapExtensionObstructionWitness_classified",
       "not_extensionCoverage_of_residualCoverageGapPayload",
       "residualCoverageGapExtensionObstructionWitnessExists_of_extensionCoverageWitnessExists",
       "residualCoverageGapExtensionObstructionWitnessExists_of_not_extensionCoverage",
       "residualCoverageGapExtensionObstructionWitness_multilabel_classified"]

/--
Schematic-name to Lean-API correspondences for Chapter 10.

These rows are metadata only. They stabilize how the design-note schematic names
are read against the existing bounded Lean API without adding new theorems,
disjointness, or global completeness claims.
-/
def schematicCorrespondences : Candidate -> List SchematicCorrespondence
  | obstructionUniverse =>
      [{ schematic := "ExtensionObstructionClass",
         leanDeclarations :=
          ["ExtensionObstructionClass",
           "ExtensionObstructionWitness",
           "MultiLabelExtensionObstructionWitness"],
         reading :=
          "bounded classification carrier for selected extension-obstruction witnesses",
         status := "defined only" },
       { schematic := "single-label witness embedded into multi-label layer",
         leanDeclarations :=
          ["ExtensionObstructionWitness.toMultiLabel",
           "ExtensionObstructionWitness.toMultiLabel_label_iff",
           "ExtensionObstructionWitness.toMultiLabel_classifiesAs"],
         reading :=
          "payload-preserving bridge from a selected single label to the corresponding multi-label witness",
         status := "defined only / proved" }]
  | nonSplitWitnessPackage =>
      [{ schematic := "selected non-split witness package",
         leanDeclarations :=
          ["NonSplitExtensionWitnessPackage",
           "NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness",
           "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension",
           "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension"],
         reading :=
          "soundness plus bounded completeness under explicit selected-witness coverage and exactness assumptions",
         status := "defined only / proved" }]
  | singleLabelClassification =>
      [{ schematic := "ArchitectureExtensionFormula_structural",
         leanDeclarations :=
          ["ArchitectureExtensionFormula_structural"],
         reading :=
          "every selected single-label witness is covered by at least one of the seven classification predicates",
         status := "proved" }]
  | multiLabelClassification =>
      [{ schematic := "ArchitectureExtensionFormula_multilabel_structural",
         leanDeclarations :=
          ["ArchitectureExtensionFormula_multilabel_structural"],
         reading :=
          "every selected multi-label witness is covered by at least one of the seven multi-label predicates",
         status := "proved" }]
  | fillingFailureBridge =>
      [{ schematic := "filling failure classified as extension obstruction",
         leanDeclarations :=
          ["FillingFailureWitnessPayload",
           "fillingFailureExtensionObstructionWitness",
           "fillingFailureExtensionObstructionWitness_classified",
           "fillingFailureExtensionObstructionWitness_multilabel_classified"],
         reading :=
          "selected diagram non-fillability payload embedded into the filling-failure classification layer",
         status := "defined only / proved" },
       { schematic := "filling failure refutes selected split",
         leanDeclarations :=
          ["FillingFailureRefutesSplit",
           "not_selectedSplitExtension_of_fillingFailurePayload",
           "FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage"],
         reading :=
          "split failure only under explicit bridge premise and selected payload coverage / exactness assumptions",
         status := "defined only / proved" }]
  | liftingFailureBridge =>
      [{ schematic := "lifting failure classified as extension obstruction",
         leanDeclarations :=
          ["LiftingFailureWitnessPayload",
           "liftingFailureExtensionObstructionWitness",
           "liftingFailureExtensionObstructionWitness_classified",
           "liftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage",
           "liftingFailureExtensionObstructionWitness_multilabel_classified"],
         reading :=
          "absence of a selected lifting preservation package embedded into the lifting-failure classification layer",
         status := "defined only / proved" }]
  | complexityTransferBridge =>
      [{ schematic := "complexity transfer classified as extension obstruction",
         leanDeclarations :=
          ["ComplexityTransferWitnessPayload",
           "complexityTransferExtensionObstructionWitness",
           "complexityTransferExtensionObstructionWitness_classified",
           "complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
           "complexityTransferExtensionObstructionWitness_multilabel_classified"],
         reading :=
          "selected runtime / semantic / policy transfer witness embedded into the complexity-transfer classification layer",
         status := "defined only / proved" }]
  | residualCoverageGapBridge =>
      [{ schematic := "residual coverage gap classified as extension obstruction",
         leanDeclarations :=
          ["ResidualCoverageGapWitnessPayload",
           "residualCoverageGapExtensionObstructionWitness",
           "residualCoverageGapExtensionObstructionWitness_classified",
           "residualCoverageGapExtensionObstructionWitnessExists_of_not_extensionCoverage",
           "residualCoverageGapExtensionObstructionWitness_multilabel_classified"],
         reading :=
          "selected extension-coverage diagnostic embedded into the residual-coverage-gap classification layer",
         status := "defined only / proved" }]

/-- Boundary reminder for reading each candidate as a bounded Chapter 10 API. -/
def nonConclusionBoundary : Candidate -> String
  | obstructionUniverse =>
      "selected witness carriers only; no universe-wide obstruction coverage or extractor completeness"
  | nonSplitWitnessPackage =>
      "soundness plus bounded completeness under explicit coverage / exactness assumptions only"
  | singleLabelClassification =>
      "coverage by at least one single-label predicate only; no disjoint decomposition or global completeness"
  | multiLabelClassification =>
      "multi-label coverage permits overlapping labels; no disjointness or singleton-label claim"
  | fillingFailureBridge =>
      "selected filling-failure payload bridge only; NonFillabilityWitnessFor alone does not refute arbitrary split predicates"
  | liftingFailureBridge =>
      "selected feature-step lifting failure only; no strict section equality, global split completeness, or all-step lifting"
  | complexityTransferBridge =>
      "selected runtime / semantic / policy transfer witnesses only; no global conservation or empirical cost theorem"
  | residualCoverageGapBridge =>
      "selected coverage diagnostic only; no static split failure, runtime / semantic flatness failure, or extractor completeness"

end Candidate

end Chapter10ArchitectureExtensionFormula

end Formal.Arch
