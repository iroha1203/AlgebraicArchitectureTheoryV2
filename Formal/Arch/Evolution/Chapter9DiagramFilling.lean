import Formal.Arch.Evolution.DiagramFiller
import Formal.Arch.Extension.SplitExtensionLifting
import Formal.Arch.Extension.ArchitectureExtensionFormula

/-!
Documentation-facing entrypoint for the mathematical design Chapter 9 diagram
filling and split-extension packages.

This module is intentionally thin. Importing it exposes the bounded diagram
filling, non-fillability witness, split-extension lifting, and filling-failure
bridge APIs used by Chapter 9 without adding global semantic completeness,
strict section / retraction equality, all-step lifting, or extractor-completeness
claims.
-/

namespace Formal.Arch

namespace Chapter9DiagramFilling

/--
A stable documentation-facing mapping from schematic names in Chapter 9 to the
Lean declarations that currently carry the corresponding bounded API.
-/
structure SchematicCorrespondence where
  schematic : String
  leanDeclarations : List String
  reading : String
  status : String
  deriving Repr

/-- The main Chapter 9 API groups exposed through this entrypoint. -/
inductive Candidate where
  | diagramFillingObstruction
  | splitExtensionLifting
  | fillingFailureBridge
  deriving DecidableEq, Repr

namespace Candidate

/-- Human-readable section number in `docs/aat_v2_mathematical_design.md`. -/
def designSection : Candidate -> String
  | diagramFillingObstruction => "9.1"
  | splitExtensionLifting => "9.2"
  | fillingFailureBridge => "9.1 / 9.2"

/-- Stable schematic name used by documentation and theorem-index tables. -/
def schematicName : Candidate -> String
  | diagramFillingObstruction => "Diagram filling and obstruction"
  | splitExtensionLifting => "Split extension as lifting and section"
  | fillingFailureBridge => "Filling failure bridge"

/-- Representative Lean declarations that serve as public entrypoints. -/
def representativeDeclarations : Candidate -> List String
  | diagramFillingObstruction =>
      ["ArchitectureDiagram",
       "DiagramFiller",
       "diagramFiller_observation_eq",
       "observationDifference_refutesDiagramFiller",
       "NonFillabilityWitness",
       "NonFillabilityWitnessFor",
       "obstructionAsNonFillability_sound",
       "observationDifference_nonFillabilityWitnessFor",
       "WitnessUniverseComplete",
       "obstructionAsNonFillability_complete_bounded"]
  | splitExtensionLifting =>
      ["FeatureSectionLaw",
       "FeatureViewSectionPackage",
       "ObservationalCoreRetraction",
       "SplitExtensionLiftingData",
       "SplitExtensionLiftingData.featureSection_observes",
       "SplitExtensionLiftingData.coreRetraction_observes_coreEmbedding",
       "SplitExtensionLiftingData.interfaceFactorization_holds",
       "SplitExtensionLiftingData.preservesRequiredInvariants_holds",
       "LiftsFeatureStep",
       "PreservesCoreInvariants",
       "SplitExtensionLifting",
       "SplitExtensionLiftingPreservationPackage",
       "SplitExtensionLifting_preservationPackage"]
  | fillingFailureBridge =>
      ["FillingFailureWitnessPayload",
       "fillingFailureExtensionObstructionWitness",
       "ClassifiedAsFillingFailure",
       "fillingFailureExtensionObstructionWitness_classified",
       "FillingFailureRefutesSplit",
       "not_selectedSplitExtension_of_fillingFailurePayload",
       "FillingFailureBridgePackage",
       "FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage",
       "FillingFailureBridgePackage.selectedExtensionObstructionWitnessExists_of_selectedPayloadExists"]

/--
Schematic-name to Lean-API correspondences for Chapter 9.

These rows are metadata only. They stabilize how the design-note schematic names
are read against the existing bounded Lean API without adding new theorems or
global completeness claims.
-/
def schematicCorrespondences : Candidate -> List SchematicCorrespondence
  | diagramFillingObstruction =>
      [{ schematic := "DiagramFiller D",
         leanDeclarations :=
          ["ArchitectureDiagram",
           "DiagramFiller"],
         reading :=
          "finite semantic diagram fillability via generated path homotopy",
         status := "defined only" },
       { schematic := "Obs D.lhs != Obs D.rhs refutes DiagramFiller D",
         leanDeclarations :=
          ["diagramFiller_observation_eq",
           "observationDifference_refutesDiagramFiller"],
         reading :=
          "selected observation difference refutes fillability under explicit generator-preservation assumptions",
         status := "proved" },
       { schematic := "NonFillabilityWitnessFor D w",
         leanDeclarations :=
          ["NonFillabilityWitness",
           "NonFillabilityWitnessFor",
           "obstructionAsNonFillability_sound",
           "observationDifference_nonFillabilityWitnessFor"],
         reading :=
          "sound non-fillability witness for one selected diagram and witness value",
         status := "defined only / proved" },
       { schematic := "WitnessUniverseComplete U D",
         leanDeclarations :=
          ["WitnessUniverseComplete",
           "obstructionAsNonFillability_complete_bounded"],
         reading :=
          "bounded converse only under an explicit finite witness-universe completeness premise",
         status := "defined only / proved" }]
  | splitExtensionLifting =>
      [{ schematic := "q o s approx[O_F] id_F",
         leanDeclarations :=
          ["FeatureSectionLaw",
           "FeatureViewSectionPackage",
           "FeatureViewSectionPackage.featureSection_observes",
           "SplitExtensionLiftingData.featureSection_observes"],
         reading :=
          "observation-relative selected feature section law, not strict equality",
         status := "defined only / proved" },
       { schematic := "r o i approx[O_X] id_X",
         leanDeclarations :=
          ["ObservationalCoreRetraction",
           "SplitExtensionLiftingData.coreRetraction_observes_coreEmbedding"],
         reading :=
          "observation-relative core retraction law on embedded core components",
         status := "defined only / proved" },
       { schematic := "selected feature operations lift to X'",
         leanDeclarations :=
          ["SelectedFeatureStep",
           "LiftedExtensionStep",
           "LiftsFeatureStep",
           "PreservesCoreInvariants",
           "SplitExtensionLifting",
           "SplitExtensionLiftingPreservationPackage",
           "SplitExtensionLifting_preservationPackage"],
         reading :=
          "bounded lifting and feature/core preservation for one selected feature step",
         status := "defined only / proved" },
       { schematic := "interface factorization and coverage accessors",
         leanDeclarations :=
          ["SplitExtensionLiftingData.interfaceFactorization_holds",
           "SplitExtensionLiftingData.preservesRequiredInvariants_holds",
           "CompatibleWithInterface.liftedEdge_holds",
           "CompatibleWithInterface.interfaceFactorization_holds",
           "CompatibleWithInterface.coverageAssumptions_holds",
           "CompatibleWithInterface.coreInvariantPreserved_holds"],
         reading :=
          "docs-facing accessors for explicit package fields and selected-step assumptions",
         status := "proved" }]
  | fillingFailureBridge =>
      [{ schematic := "diagram filling failure classified as extension obstruction",
         leanDeclarations :=
          ["FillingFailureWitnessPayload",
           "fillingFailureExtensionObstructionWitness",
           "ClassifiedAsFillingFailure",
           "fillingFailureExtensionObstructionWitness_classified"],
         reading :=
          "selected diagram non-fillability payload embedded into the extension-obstruction classification universe",
         status := "defined only / proved" },
       { schematic := "filling failure refutes selected split predicate",
         leanDeclarations :=
          ["FillingFailureRefutesSplit",
           "not_selectedSplitExtension_of_fillingFailurePayload"],
         reading :=
          "non-split conclusion only under an explicit bridge premise supplied by the surrounding package",
         status := "defined only / proved" },
       { schematic := "FillingFailureBridgePackage to NonSplitExtensionWitnessPackage",
         leanDeclarations :=
          ["FillingFailureBridgePackage",
           "FillingFailureBridgePackage.SelectedWitness",
           "FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage",
           "FillingFailureBridgePackage.selectedExtensionObstructionWitnessExists_of_selectedPayloadExists"],
         reading :=
          "bounded bridge into the generic non-split witness package under selected payload coverage and exactness assumptions",
         status := "defined only / proved" }]

/-- Boundary reminder for reading each candidate as a bounded Chapter 9 API. -/
def nonConclusionBoundary : Candidate -> String
  | diagramFillingObstruction =>
      "selected finite diagram and witness universe only; no global semantic completeness or extractor completeness"
  | splitExtensionLifting =>
      "observation-relative section / retraction and selected-step lifting only; no strict equality, unique decomposition, or all-step lifting"
  | fillingFailureBridge =>
      "selected filling-failure payload bridge only; NonFillabilityWitnessFor alone does not refute an arbitrary split predicate"

end Candidate

end Chapter9DiagramFilling

end Formal.Arch
