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

end Formal.Arch.AtomGeneratedClassificationExamples
