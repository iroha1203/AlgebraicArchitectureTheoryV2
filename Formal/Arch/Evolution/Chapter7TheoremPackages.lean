import Formal.Arch.AAT.GeneratedFeatureExtension
import Formal.Arch.AAT.GeneratedSynthesis
import Formal.Arch.Evolution.Chapter9DiagramFilling
import Formal.Arch.Extension.Flatness
import Formal.Arch.Extension.ArchitectureExtensionFormula
import Formal.Arch.Repair.Repair
import Formal.Arch.Repair.RepairSynthesis
import Formal.Arch.Signature.ComplexityTransfer
import Formal.Arch.Evolution.ArchitectureEvolution

/-!
Documentation-facing entrypoints for the mathematical design Chapter 7 theorem
packages.

This module is intentionally thin.  Importing it exposes the representative
bounded theorem packages for sections 7.1 through 7.6 and the Atom-generated
wrappers that feed generated inputs into those packages, without adding new
global flatness, completeness, solver-completeness, or extractor-completeness
claims.
-/

namespace Formal.Arch

universe u v

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

/--
Atom-generated specialization of the Chapter 7 split-extension preservation
entrypoint.
-/
theorem generatedSplitFeatureExtension_flatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (model : AAT.GeneratedArchitectureLawModel object) :
    ArchitectureFlatWithin
      object.generatedIdentityExtensionFlatnessModel
      object.generatedIdentityExtensionComponentUniverse := by
  exact model.generatedFeatureExtension_architectureFlatWithin

/--
Generated split feature extension packages keep the Chapter 7 non-conclusion
boundary.
-/
theorem generatedSplitFeatureExtension_recordsNonConclusions
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (model : AAT.GeneratedArchitectureLawModel object) :
    SplitFeatureExtensionWithinNonConclusions
      object.generatedIdentityStaticSplitFeatureExtension
      object.generatedIdentityExtensionComponentUniverse := by
  exact model.generatedSplitFeatureExtension_recordsNonConclusions

/--
Generated operations expose the AtomShape transformation used by the Chapter 7
operation / evolution reading.
-/
theorem generatedOperation_atomShape_transformed
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (carrier : AAT.GeneratedCarrier source) :
    operation.shapeTransform
      (AtomShapeOf presentation carrier.val)
      (AtomShapeOf presentation (operation.atomMap carrier).val) := by
  exact operation.atomShape_transformed carrier

/--
Generated operations expose the AtomShape-coordinate distance between each
source carrier and its mapped target carrier.
-/
theorem generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (carrier : AAT.GeneratedCarrier source) :
    operation.mappedCarrierShapeDistance carrier =
      AAT.GeneratedAtomShapeCoordinate.mismatchCount
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation carrier.val))
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation (operation.atomMap carrier).val)) := by
  exact operation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount carrier

/--
Target carriers outside the source atom map are still primitive atoms of the
target generated object.
-/
theorem generatedOperation_unmapped_target_atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (targetCarrier : AAT.GeneratedCarrier target)
    (hUnmapped : operation.TargetCarrierUnmapped targetCarrier) :
    system.Primitive targetCarrier.val :=
  operation.unmapped_target_atom_primitive targetCarrier hUnmapped

/--
Generated operations induce the existing AAT operation transport package
between generated AAT cores.
-/
def generatedOperation_toOperationTransportPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedOperation source target)
    (sourceModel : AAT.GeneratedArchitectureLawModel source)
    (targetModel : AAT.GeneratedArchitectureLawModel target) :
    AAT.OperationTransportPackage
      sourceModel.generatedAATCore
      targetModel.generatedAATCore :=
  operation.toOperationTransportPackage sourceModel targetModel

/-- Generated repairs target port / slot / valence-level repair problems. -/
theorem generatedRepair_target_shapeLevel
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (repair : AAT.GeneratedRepair source target) :
    repair.repairTarget.shapeLevel := by
  exact repair.target_shapeLevel

/-- Generated repairs clear their selected generated repair target. -/
def generatedRepair_clears_selected_target
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (repair : AAT.GeneratedRepair source target) :
    AAT.GeneratedRepairTargetCleared
      repair.operation repair.repairTarget := by
  exact repair.clears_selected_target

/--
Generated repairs induce the existing AAT repair-clearing package at the
generated target object.
-/
def generatedRepair_toRepairClearingPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {source target : AAT.GeneratedArchitectureObject presentation}
    (repair : AAT.GeneratedRepair source target)
    (targetModel : AAT.GeneratedArchitectureLawModel target) :
    AAT.RepairClearingPackage
      targetModel.generatedAATCore
      (AAT.GeneratedArchitectureObject presentation)
      Unit
      source
      target :=
  repair.toRepairClearingPackage targetModel

/-- Pre-molecule generated repair problems remain shape-level targets. -/
theorem generatedRepairFromProblem_shapeLevel
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (repair : AAT.GeneratedRepairFromProblem configuration target) :
    repair.repairProblem.shapeLevel := by
  exact repair.problem_shapeLevel

/-- Generated repairs from failed pre-molecule configurations clear the selected problem. -/
def generatedRepairFromProblem_clears_selected_problem
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (repair : AAT.GeneratedRepairFromProblem configuration target) :
    AAT.GeneratedRepairProblemCleared
      repair.operation repair.repairProblem := by
  exact repair.clears_selected_problem

/--
Generated repair problem operations expose the AtomShape-coordinate distance
between failed-configuration carriers and their mapped target carriers.
-/
theorem generatedRepairProblemOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedRepairProblemOperation configuration target)
    (carrier : AAT.GeneratedRepairProblemCarrier configuration) :
    operation.mappedCarrierShapeDistance carrier =
      AAT.GeneratedAtomShapeCoordinate.mismatchCount
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation carrier.val))
        (AAT.GeneratedAtomShapeCoordinate.ofShape
          (AtomShapeOf presentation (operation.atomMap carrier).val)) := by
  exact operation.mappedCarrierShapeDistance_eq_coordinate_mismatchCount carrier

/--
Target carriers outside a repair source atom map are still primitive atoms of
the generated target object.
-/
theorem generatedRepairProblemOperation_unmapped_target_atom_primitive
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (operation : AAT.GeneratedRepairProblemOperation configuration target)
    (targetCarrier : AAT.GeneratedCarrier target)
    (hUnmapped : operation.TargetCarrierUnmapped targetCarrier) :
    system.Primitive targetCarrier.val :=
  operation.unmapped_target_atom_primitive targetCarrier hUnmapped

/--
Generated repair from a pre-molecule problem induces the existing AAT
repair-clearing package at the generated target object.
-/
def generatedRepairFromProblem_toRepairClearingPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {configuration : AAT.GeneratedRepairProblemConfiguration presentation}
    {target : AAT.GeneratedArchitectureObject presentation}
    (repair : AAT.GeneratedRepairFromProblem configuration target)
    (targetModel : AAT.GeneratedArchitectureLawModel target) :
    AAT.RepairClearingPackage
      targetModel.generatedAATCore
      (Sum
        (AAT.GeneratedRepairProblemConfiguration presentation)
        (AAT.GeneratedArchitectureObject presentation))
      Unit
      (Sum.inl configuration)
      (Sum.inr target) :=
  repair.toRepairClearingPackage targetModel

/-- Generated synthesis candidates satisfy generated bounded flatness. -/
theorem generatedSynthesisCandidate_flatWithin
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (candidate : AAT.GeneratedSynthesisCandidate object) :
    ArchitectureFlatWithin object.generatedFlatnessModel
      object.generatedComponentUniverse := by
  exact candidate.candidate_flatWithin

/--
Generated synthesis candidates induce the existing AAT synthesis soundness
package over the generated AAT core.
-/
def generatedSynthesisCandidate_toSynthesisSoundnessPackage
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (candidate : AAT.GeneratedSynthesisCandidate object) :
    AAT.SynthesisSoundnessPackage
      candidate.lawModel.generatedAATCore
      (AAT.GeneratedSynthesisCandidate object) :=
  candidate.toSynthesisSoundnessPackage

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
       "LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation",
       "Chapter7TheoremPackages.generatedSplitFeatureExtension_flatWithin",
       "Chapter7TheoremPackages.generatedSplitFeatureExtension_recordsNonConclusions"]
  | nonSplitExtensionWitness =>
      ["NonSplitExtensionWitnessPackage",
       "Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage",
       "NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness",
       "Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness",
       "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension",
       "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension",
       "Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists"]
  | repairAsResplitting =>
      ["SelectedObstructionUniverse",
       "AdmissibleRepairRule",
       "repairStepDecreases_of_admissible",
       "extensionObstructionMeasure_decreases_of_admissible",
       "Chapter7TheoremPackages.generatedRepair_target_shapeLevel",
       "Chapter7TheoremPackages.generatedRepair_clears_selected_target",
       "Chapter7TheoremPackages.generatedRepair_toRepairClearingPackage",
       "Chapter7TheoremPackages.generatedRepairProblemOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount",
       "Chapter7TheoremPackages.generatedRepairProblemOperation_unmapped_target_atom_primitive",
       "Chapter7TheoremPackages.generatedRepairFromProblem_shapeLevel",
       "Chapter7TheoremPackages.generatedRepairFromProblem_clears_selected_problem",
       "Chapter7TheoremPackages.generatedRepairFromProblem_toRepairClearingPackage"]
  | complexityTransfer =>
      ["BoundedComplexityTransferPackage",
       "BoundedComplexityTransferPackage.complexityTransfer_selectedAlternative",
       "BoundedComplexityTransferPackage.no_free_elimination_bounded",
       "complexityTransferExtensionObstructionWitness",
       "complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
       "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
       "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_multilabel_classified"]
  | noSolutionCertificate =>
      ["NoSolutionCertificate",
       "ValidNoSolutionCertificate",
       "NoSolutionCertificate.sound_of_valid",
       "Chapter7TheoremPackages.generatedSynthesisCandidate_flatWithin",
       "Chapter7TheoremPackages.generatedSynthesisCandidate_toSynthesisSoundnessPackage"]
  | architectureEvolution =>
      ["ArchitectureTransition",
       "ArchitectureEvolution",
       "ArchitectureTransition.flatness_of_transitionPreservesFlatness",
       "ArchitectureTransition.reportedObstruction_of_drift",
       "eventuallyFlat_of_targetFlat",
       "evolutionPathPreservesFlatness",
       "Chapter7TheoremPackages.generatedOperation_atomShape_transformed",
       "Chapter7TheoremPackages.generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount",
       "Chapter7TheoremPackages.generatedOperation_unmapped_target_atom_primitive",
       "Chapter7TheoremPackages.generatedOperation_toOperationTransportPackage"]

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
           "LawfulExtensionPreservesFlatness",
           "Chapter7TheoremPackages.generatedSplitFeatureExtension_flatWithin",
           "Chapter7TheoremPackages.generatedSplitFeatureExtension_recordsNonConclusions"],
         reading :=
          "bounded architecture flatness relative to coverage and measured semantic diagrams, including generated identity feature extensions",
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
           "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension",
           "Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists",
           "Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness"],
         reading :=
          "coverage and exactness assumptions required for the bounded completeness direction, specialized through generated diagram filling-failure witnesses",
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
         status := "defined only / proved" },
       { schematic := "Generated repair clears shape-level target",
         leanDeclarations :=
          ["Chapter7TheoremPackages.generatedRepair_target_shapeLevel",
           "Chapter7TheoremPackages.generatedRepair_clears_selected_target",
           "Chapter7TheoremPackages.generatedRepair_toRepairClearingPackage",
           "Chapter7TheoremPackages.generatedRepairProblemOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount",
           "Chapter7TheoremPackages.generatedRepairProblemOperation_unmapped_target_atom_primitive",
           "Chapter7TheoremPackages.generatedRepairFromProblem_shapeLevel",
           "Chapter7TheoremPackages.generatedRepairFromProblem_clears_selected_problem",
           "Chapter7TheoremPackages.generatedRepairFromProblem_toRepairClearingPackage"],
         reading :=
          "generated repair targets are port / slot / valence-level targets, repair problem operations expose AtomShape distance and unmapped target primitive evidence, and the repair induces the existing AAT repair-clearing package at a generated target object",
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
           "BoundedComplexityTransferPackage.no_free_elimination_bounded",
           "ComplexityTransferWitnessPayload",
           "complexityTransferExtensionObstructionWitness",
           "complexityTransferExtensionObstructionWitness_classified",
           "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_classified",
           "complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
           "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
           "complexityTransferExtensionObstructionWitness_multilabel_classified",
           "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_multilabel_classified"],
         reading :=
          "bounded alternative plus bridge into the generated identity Architecture Extension Formula complexity-transfer classification",
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
         status := "defined only / proved" },
       { schematic := "Generated synthesis candidate soundness",
         leanDeclarations :=
          ["Chapter7TheoremPackages.generatedSynthesisCandidate_flatWithin",
           "Chapter7TheoremPackages.generatedSynthesisCandidate_toSynthesisSoundnessPackage"],
         reading :=
          "generated synthesis candidate soundness is read from a generated target law model; this is positive candidate soundness, not a no-solution certificate",
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
           "evolutionPathPreservesFlatness",
           "Chapter7TheoremPackages.generatedOperation_atomShape_transformed",
           "Chapter7TheoremPackages.generatedOperation_mappedCarrierShapeDistance_eq_coordinate_mismatchCount",
           "Chapter7TheoremPackages.generatedOperation_unmapped_target_atom_primitive",
           "Chapter7TheoremPackages.generatedOperation_toOperationTransportPackage"],
         reading :=
          "bounded eventual flatness for a selected migration path or preserving path, with generated operations exposed as AtomShape transport, mapped shape distance, unmapped target primitive evidence, and generated AATCore transport",
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
