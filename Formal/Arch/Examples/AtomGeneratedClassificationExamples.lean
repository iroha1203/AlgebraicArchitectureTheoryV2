import Formal.Arch.AAT.TheoremClassification

namespace Formal.Arch.AtomGeneratedClassificationExamples

open Formal.Arch.AATReconstructionClassification

/--
Acceptance: every row in the reconstruction classification registry carries
the evidence required by its A/B/C class and an allowed migration action.
-/
theorem theorem_package_registry_rows_are_classified
    {row : TheoremPackageClassification}
    (hRow : row ∈ allClassifications) :
    row.Passes ∧ row.HasAllowedAction := by
  exact
    ⟨registry_rows_have_classification_evidence hRow,
      registry_rows_have_allowed_actions hRow⟩

/--
Acceptance: the theorem-package registry has no remaining bridge-assumed rows
or rewrite targets.
-/
theorem theorem_package_registry_has_no_temporary_or_rewrite_rows :
    TheoremPackageClass.bridgeAssumed ∉ allClassificationClasses ∧
      ReconstructionAction.rewriteTarget ∉ allClassificationActions := by
  exact
    ⟨theorem_package_registry_has_no_bridge_assumed_rows,
      theorem_package_registry_has_no_rewrite_targets⟩

/--
Acceptance: the generic Signature bridge remains visible as a legacy bridge
surface with an explicit generated replacement, but it no longer counts as a
theorem-package registry row.
-/
theorem generic_signature_bridge_is_legacy_replaced_surface_acceptance :
    genericSignatureBridgeLegacySurface.IsBridgeAssumptionSurface ∧
      genericSignatureBridgeLegacySurface.HasGeneratedReplacement ∧
      "aat.genericSignatureBridge" ∉ allPackageIds := by
  exact
    ⟨generic_signature_bridge_is_legacy_replaced_surface.1,
      generic_signature_bridge_is_legacy_replaced_surface.2,
      generic_signature_bridge_is_not_theorem_package_registry_row⟩

/--
Acceptance: the generated Signature bridge is the Atom-generated replacement
entrypoint for the generic bridge.
-/
theorem generated_signature_bridge_is_source_of_truth :
    (classifyAATCandidate .generatedSignatureBridge).classification =
        .atomGenerated ∧
      (classifyAATCandidate .generatedSignatureBridge).action =
        .aatSourceOfTruth := by
  exact generated_signature_bridge_is_atom_generated

/--
Acceptance: the representation-level static Signature anchor remains a
downstream library rather than being mistaken for the generated AAT source.
-/
theorem static_signature_anchor_is_downstream_library :
    (classifyAATCandidate .finiteStaticStructuralCore).classification =
        .representationLevel ∧
      (classifyAATCandidate .finiteStaticStructuralCore).action =
        .downstreamLibrary := by
  exact finite_static_core_is_downstream_representation_library

/--
Acceptance: the non-identity generated transport handoff is classified as an
Atom-generated boundary, both in the AAT smoke surface and the ArchSig/SFT
handoff surface.
-/
theorem nonidentity_transport_handoff_classified_atom_generated :
    (classifyAATCandidate .crossPackageSmoke).classification =
        .atomGenerated ∧
      (classifySFT .archSigReportBoundary).classification =
        .atomGenerated := by
  exact nonidentity_transport_handoff_is_atom_generated

/--
Acceptance: generated diagram filling failure now supplies the source-of-truth
entrypoint for the non-split / filling-failure theorem packages rather than
leaving them as representation-level rewrite targets.
-/
theorem generated_filling_failure_bridge_classified_atom_generated :
    (classifyChapter7 .nonSplitExtensionWitness).classification =
        .atomGenerated ∧
      (classifyChapter9 .fillingFailureBridge).classification =
        .atomGenerated ∧
      (classifyChapter10 .nonSplitWitnessPackage).classification =
        .atomGenerated ∧
      (classifyChapter10 .fillingFailureBridge).classification =
        .atomGenerated := by
  exact generated_filling_failure_bridge_is_atom_generated

/--
Acceptance: generated self-view feature extension supplies the source-of-truth
entrypoint for split-extension lifting and lifting-failure classification.
-/
theorem generated_split_lifting_bridge_classified_atom_generated :
    (classifyChapter9 .splitExtensionLifting).classification =
        .atomGenerated ∧
      (classifyChapter10 .liftingFailureBridge).classification =
        .atomGenerated := by
  exact generated_split_lifting_bridge_is_atom_generated

/--
Acceptance: SFT consequence envelopes now have an Atom-generated entrypoint
from generated SFT input and generated ArchSig transition evidence.
-/
theorem generated_consequence_envelope_classified_atom_generated :
    (classifySFT .consequenceEnvelope).classification =
        .atomGenerated := by
  exact generated_consequence_envelope_is_atom_generated

/--
Acceptance: Chapter 11 obstruction valuation and analytic extension formula now
have generated law-model entrypoints rather than remaining only downstream
representation packages.
-/
theorem generated_analytic_extension_formula_classified_atom_generated :
    (classifyChapter11 .obstructionValuation).classification =
        .atomGenerated ∧
      (classifyChapter11 .analyticExtensionFormula).classification =
        .atomGenerated := by
  exact generated_analytic_extension_formula_is_atom_generated

/--
Acceptance: Chapter 8 path calculus, selected observation invariance, diagram
filling, and non-fillability all have generated path/diagram entrypoints.
-/
theorem generated_chapter8_path_diagram_classified_atom_generated :
    (classifyChapter8 .architecturePaths).classification =
        .atomGenerated ∧
      (classifyChapter8 .selectedObservationInvariance).classification =
        .atomGenerated ∧
      (classifyChapter8 .diagramFiller).classification =
        .atomGenerated ∧
      (classifyChapter8 .obstructionAsNonFillability).classification =
        .atomGenerated := by
  exact generated_chapter8_path_diagram_is_atom_generated

/--
Acceptance: complexity transfer and residual coverage diagnostics now have
generated identity feature-extension entrypoints in the classification registry.
-/
theorem generated_complexity_residual_bridge_classified_atom_generated :
    (classifyChapter7 .complexityTransfer).classification =
        .atomGenerated ∧
      (classifyChapter10 .complexityTransferBridge).classification =
        .atomGenerated ∧
      (classifyChapter10 .residualCoverageGapBridge).classification =
        .atomGenerated := by
  exact generated_complexity_residual_bridge_is_atom_generated

/--
Acceptance: the Chapter 10 extension-obstruction witness universe has generated
identity feature-extension witness carriers.
-/
theorem generated_extension_obstruction_universe_classified_atom_generated :
    (classifyChapter10 .obstructionUniverse).classification =
        .atomGenerated := by
  exact generated_extension_obstruction_universe_is_atom_generated

end Formal.Arch.AtomGeneratedClassificationExamples
