import Formal.Arch.AAT.GeneratedFeatureExtension
import Formal.Arch.Evolution.Chapter9DiagramFilling
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

universe u v w q r z

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
       "Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage",
       "NonSplitExtensionWitnessPackage.not_selectedSplitExtension_of_selectedExtensionObstructionWitness",
       "Chapter9DiagramFilling.generatedFillingFailureBridge_not_selectedSplitExtension_of_generatedWitness",
       "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_of_not_selectedSplitExtension",
       "NonSplitExtensionWitnessPackage.selectedExtensionObstructionWitnessExists_iff_not_selectedSplitExtension",
       "Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists"]
  | singleLabelClassification =>
      ["ClassifiedAsInheritedCore",
       "ClassifiedAsFeatureLocal",
       "ClassifiedAsInteraction",
       "ClassifiedAsLiftingFailure",
       "ClassifiedAsFillingFailure",
       "ClassifiedAsComplexityTransfer",
       "ClassifiedAsResidualCoverageGap",
       "Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural",
       "ArchitectureExtensionFormula_structural"]
  | multiLabelClassification =>
      ["MultiLabelClassifiedAsInheritedCore",
       "MultiLabelClassifiedAsFeatureLocal",
       "MultiLabelClassifiedAsInteraction",
       "MultiLabelClassifiedAsLiftingFailure",
       "MultiLabelClassifiedAsFillingFailure",
       "MultiLabelClassifiedAsComplexityTransfer",
       "MultiLabelClassifiedAsResidualCoverageGap",
       "Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_multilabel_structural",
       "ArchitectureExtensionFormula_multilabel_structural"]
  | fillingFailureBridge =>
      ["FillingFailureWitnessPayload",
       "Chapter9DiagramFilling.generatedFillingFailureWitnessPayload",
       "fillingFailureExtensionObstructionWitness",
       "Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness",
       "fillingFailureExtensionObstructionWitness_classified",
       "Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness_classified",
       "FillingFailureRefutesSplit",
       "not_selectedSplitExtension_of_fillingFailurePayload",
       "FillingFailureBridgePackage.toNonSplitExtensionWitnessPackage",
       "Chapter9DiagramFilling.generatedFillingFailureBridge_toNonSplitExtensionWitnessPackage",
       "Chapter9DiagramFilling.generatedFillingFailureBridge_selectedExtensionObstructionWitnessExists_of_generatedWitnessExists",
       "fillingFailureExtensionObstructionWitness_multilabel_classified",
       "Chapter10ArchitectureExtensionFormula.generatedFillingFailureExtensionObstructionWitness_multilabel_classified"]
  | liftingFailureBridge =>
      ["LiftingFailureWitnessPayload",
       "Chapter9DiagramFilling.generatedSelfFeatureExtension",
       "Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData",
       "liftingFailureExtensionObstructionWitness",
       "Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitness_classified",
       "liftingFailureExtensionObstructionWitness_classified",
       "not_compatibleWithInterface_of_liftingFailurePayload",
       "liftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage",
       "Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage",
       "liftingFailureExtensionObstructionWitness_multilabel_classified",
       "Chapter10ArchitectureExtensionFormula.generatedSelfLiftingFailureExtensionObstructionWitness_multilabel_classified"]
  | complexityTransferBridge =>
      ["ComplexityTransferWitnessPayload",
       "complexityTransferExtensionObstructionWitness",
       "complexityTransferExtensionObstructionWitness_classified",
       "complexityTransferExtensionObstructionWitnessExists_of_transferredTo",
       "complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
       "complexityTransferExtensionObstructionWitness_multilabel_classified",
       "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_classified",
       "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_transferredTo",
       "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
       "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_multilabel_classified"]
  | residualCoverageGapBridge =>
      ["ResidualCoverageGapWitnessPayload",
       "residualCoverageGapExtensionObstructionWitness",
       "residualCoverageGapExtensionObstructionWitness_classified",
       "not_extensionCoverage_of_residualCoverageGapPayload",
       "residualCoverageGapExtensionObstructionWitnessExists_of_extensionCoverageWitnessExists",
       "residualCoverageGapExtensionObstructionWitnessExists_of_not_extensionCoverage",
       "residualCoverageGapExtensionObstructionWitness_multilabel_classified",
       "Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_classified",
       "Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_multilabel_classified",
       "Chapter10ArchitectureExtensionFormula.generatedIdentityExtension_noResidualCoverageGapPayload"]

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
          ["ArchitectureExtensionFormula_structural",
           "Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_structural"],
         reading :=
          "every selected single-label witness is covered by at least one of the seven classification predicates, including generated identity feature extensions",
         status := "proved" }]
  | multiLabelClassification =>
      [{ schematic := "ArchitectureExtensionFormula_multilabel_structural",
         leanDeclarations :=
          ["ArchitectureExtensionFormula_multilabel_structural",
           "Chapter10ArchitectureExtensionFormula.generatedIdentityArchitectureExtensionFormula_multilabel_structural"],
         reading :=
          "every selected multi-label witness is covered by at least one of the seven multi-label predicates, including generated identity feature extensions",
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
           "Chapter9DiagramFilling.generatedSelfFeatureExtension",
           "Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData",
           "liftingFailureExtensionObstructionWitness",
           "liftingFailureExtensionObstructionWitness_classified",
           "liftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage",
           "Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitness_classified",
           "Chapter9DiagramFilling.generatedSelfLiftingFailureExtensionObstructionWitnessExists_of_not_liftingPreservationPackage",
           "liftingFailureExtensionObstructionWitness_multilabel_classified",
           "Chapter10ArchitectureExtensionFormula.generatedSelfLiftingFailureExtensionObstructionWitness_multilabel_classified"],
         reading :=
          "absence of a selected generated self-view lifting preservation package embedded into the lifting-failure classification layer",
         status := "defined only / proved" }]
  | complexityTransferBridge =>
      [{ schematic := "complexity transfer classified as extension obstruction",
         leanDeclarations :=
          ["ComplexityTransferWitnessPayload",
           "complexityTransferExtensionObstructionWitness",
           "complexityTransferExtensionObstructionWitness_classified",
           "complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
           "complexityTransferExtensionObstructionWitness_multilabel_classified",
           "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_classified",
           "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination",
           "Chapter10ArchitectureExtensionFormula.generatedComplexityTransferExtensionObstructionWitness_multilabel_classified"],
         reading :=
          "selected runtime / semantic / policy transfer witness embedded into the generated identity feature-extension complexity-transfer classification layer",
         status := "defined only / proved" }]
  | residualCoverageGapBridge =>
      [{ schematic := "residual coverage gap classified as extension obstruction",
         leanDeclarations :=
          ["ResidualCoverageGapWitnessPayload",
           "residualCoverageGapExtensionObstructionWitness",
           "residualCoverageGapExtensionObstructionWitness_classified",
           "residualCoverageGapExtensionObstructionWitnessExists_of_not_extensionCoverage",
           "residualCoverageGapExtensionObstructionWitness_multilabel_classified",
           "Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_classified",
           "Chapter10ArchitectureExtensionFormula.generatedResidualCoverageGapExtensionObstructionWitness_multilabel_classified",
           "Chapter10ArchitectureExtensionFormula.generatedIdentityExtension_noResidualCoverageGapPayload"],
         reading :=
          "selected extension-coverage diagnostic embedded into the generated identity feature-extension residual-coverage classification layer; generated identity coverage rules out such payloads",
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

/--
Atom-generated specialization of the single-label structural architecture
extension formula.

The feature extension and coverage premise are generated from the same
`GeneratedArchitectureObject`; callers do not supply a hand-authored
`FeatureExtension`.
-/
theorem generatedIdentityArchitectureExtensionFormula_structural
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation)
    {Witness : Type z}
    (witness :
      ExtensionObstructionWitness
        object.generatedIdentityFeatureExtension Witness) :
    ClassifiedAsInheritedCore
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsFeatureLocal
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsInteraction
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsLiftingFailure
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsFillingFailure
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsComplexityTransfer
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      ClassifiedAsResidualCoverageGap
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness := by
  exact
    ArchitectureExtensionFormula_structural
      object.generatedIdentityFeatureExtension
      object.generatedIdentityExtensionComponentUniverse
      object.generatedIdentityExtensionCoverageComplete
      witness

/--
Atom-generated specialization of the multi-label structural architecture
extension formula.
-/
theorem generatedIdentityArchitectureExtensionFormula_multilabel_structural
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation)
    {Witness : Type z}
    (witness :
      MultiLabelExtensionObstructionWitness
        object.generatedIdentityFeatureExtension Witness) :
    MultiLabelClassifiedAsInheritedCore
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      MultiLabelClassifiedAsFeatureLocal
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      MultiLabelClassifiedAsInteraction
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      MultiLabelClassifiedAsLiftingFailure
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      MultiLabelClassifiedAsFillingFailure
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      MultiLabelClassifiedAsComplexityTransfer
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness ∨
      MultiLabelClassifiedAsResidualCoverageGap
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        witness := by
  exact
    ArchitectureExtensionFormula_multilabel_structural
      object.generatedIdentityFeatureExtension
      object.generatedIdentityExtensionComponentUniverse
      object.generatedIdentityExtensionCoverageComplete
      witness

/--
Atom-generated specialization of the filling-failure multi-label bridge.

The obstruction witness is built over the generated identity feature extension
of the same generated object, so callers do not supply a hand-authored
`FeatureExtension`.
-/
theorem generatedFillingFailureExtensionObstructionWitness_multilabel_classified
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    {IndependentSquare :
      (W X Y Z : AAT.GeneratedCarrier object) ->
        AAT.GeneratedArchitectureStep object W X ->
        AAT.GeneratedArchitectureStep object X Z ->
        AAT.GeneratedArchitectureStep object W Y ->
        AAT.GeneratedArchitectureStep object Y Z -> Prop}
    {SameExternalContract :
      (X Y : AAT.GeneratedCarrier object) ->
        AAT.GeneratedArchitectureStep object X Y ->
        AAT.GeneratedArchitectureStep object X Y -> Prop}
    {RepairFill :
      (X Y : AAT.GeneratedCarrier object) ->
        AAT.GeneratedArchitecturePath object X Y ->
        AAT.GeneratedArchitecturePath object X Y -> Prop}
    {source target : AAT.GeneratedCarrier object}
    {diagram : AAT.GeneratedArchitectureDiagram object
      (source := source) (target := target)}
    {DiagramWitness : Type z}
    (payload :
      FillingFailureWitnessPayload
        IndependentSquare SameExternalContract RepairFill diagram DiagramWitness) :
    MultiLabelClassifiedAsFillingFailure object.generatedIdentityFeatureExtension
      object.generatedIdentityExtensionComponentUniverse
      (Formal.Arch.Chapter9DiagramFilling.generatedFillingFailureExtensionObstructionWitness
        payload).toMultiLabel :=
  rfl

/--
Atom-generated specialization of the lifting-failure multi-label bridge over
the generated self-view feature extension.
-/
theorem generatedSelfLiftingFailureExtensionObstructionWitness_multilabel_classified
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    {featureInvariant : AAT.GeneratedCarrier object -> Prop}
    {coreInvariant : AAT.GeneratedCarrier object -> Prop}
    {featureStep : SelectedFeatureStep (AAT.GeneratedCarrier object)}
    (payload :
      LiftingFailureWitnessPayload
        (Formal.Arch.Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData object)
        featureInvariant coreInvariant featureStep) :
    MultiLabelClassifiedAsLiftingFailure
      (Formal.Arch.Chapter9DiagramFilling.generatedSelfFeatureExtension object)
      object.generatedIdentityExtensionComponentUniverse
      (liftingFailureExtensionObstructionWitness
        (Formal.Arch.Chapter9DiagramFilling.generatedSelfSplitExtensionLiftingData object)
        payload).toMultiLabel :=
  rfl

/--
Atom-generated specialization of the complexity-transfer classification bridge
over the generated identity feature extension.
-/
theorem generatedComplexityTransferExtensionObstructionWitness_classified
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    {Transform : Type q} {Witness : Type z}
    {S : ComplexityTransferSchema Transform Witness}
    {target : ComplexityTransferTarget} {t : Transform}
    (payload : ComplexityTransferWitnessPayload S target t) :
    ClassifiedAsComplexityTransfer
      object.generatedIdentityFeatureExtension
      object.generatedIdentityExtensionComponentUniverse
      (complexityTransferExtensionObstructionWitness
        object.generatedIdentityFeatureExtension payload) :=
  complexityTransferExtensionObstructionWitness_classified
    object.generatedIdentityFeatureExtension
    object.generatedIdentityExtensionComponentUniverse
    payload

/--
Atom-generated specialization of the target-specific complexity-transfer
existence bridge.
-/
theorem generatedComplexityTransferExtensionObstructionWitnessExists_of_transferredTo
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation)
    {Transform : Type q} {Witness : Type z}
    {S : ComplexityTransferSchema Transform Witness}
    {target : ComplexityTransferTarget} {t : Transform}
    (hTransfer : ComplexityTransferredTo S target t) :
    ∃ payload : ComplexityTransferWitnessPayload S target t,
      ClassifiedAsComplexityTransfer
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        (complexityTransferExtensionObstructionWitness
          object.generatedIdentityFeatureExtension payload) :=
  complexityTransferExtensionObstructionWitnessExists_of_transferredTo
    object.generatedIdentityFeatureExtension
    object.generatedIdentityExtensionComponentUniverse
    hTransfer

/--
Atom-generated specialization of the bounded no-free-elimination complexity
transfer bridge.
-/
theorem generatedComplexityTransferExtensionObstructionWitnessExists_of_no_free_elimination
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation)
    {State : Type w} {Transform : Type q} {Requirement : Type r}
    {Witness : Type z}
    {T : ArchitectureTransform State Transform}
    {staticMeasure : SelectedComplexityMeasure State}
    {requirements : RequirementSchema State Requirement}
    {S : ComplexityTransferSchema Transform Witness}
    (pkg : BoundedComplexityTransferPackage T staticMeasure requirements S)
    (t : Transform)
    (hReduces : ReducesStaticComplexity T staticMeasure t)
    (hPreserves :
      PreservesRequirements requirements (T.source t) (T.target t))
    (hNotEliminated : ¬ ComplexityEliminatedByProof S t) :
    ∃ target : ComplexityTransferTarget,
      ∃ payload : ComplexityTransferWitnessPayload S target t,
        ClassifiedAsComplexityTransfer
          object.generatedIdentityFeatureExtension
          object.generatedIdentityExtensionComponentUniverse
          (complexityTransferExtensionObstructionWitness
            object.generatedIdentityFeatureExtension payload) :=
  complexityTransferExtensionObstructionWitnessExists_of_no_free_elimination
    object.generatedIdentityFeatureExtension
    object.generatedIdentityExtensionComponentUniverse
    pkg t hReduces hPreserves hNotEliminated

/--
Atom-generated specialization of the complexity-transfer multi-label bridge.
-/
theorem generatedComplexityTransferExtensionObstructionWitness_multilabel_classified
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    {Transform : Type q} {Witness : Type z}
    {S : ComplexityTransferSchema Transform Witness}
    {target : ComplexityTransferTarget} {t : Transform}
    (payload : ComplexityTransferWitnessPayload S target t) :
    MultiLabelClassifiedAsComplexityTransfer
      object.generatedIdentityFeatureExtension
      object.generatedIdentityExtensionComponentUniverse
      (complexityTransferExtensionObstructionWitness
        object.generatedIdentityFeatureExtension payload).toMultiLabel :=
  complexityTransferExtensionObstructionWitness_multilabel_classified
    object.generatedIdentityFeatureExtension
    object.generatedIdentityExtensionComponentUniverse
    payload

/--
Atom-generated specialization of the residual-coverage-gap classification
bridge over the generated identity feature extension.
-/
theorem generatedResidualCoverageGapExtensionObstructionWitness_classified
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (payload :
      ResidualCoverageGapWitnessPayload
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse) :
    ClassifiedAsResidualCoverageGap
      object.generatedIdentityFeatureExtension
      object.generatedIdentityExtensionComponentUniverse
      (residualCoverageGapExtensionObstructionWitness
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        payload) :=
  residualCoverageGapExtensionObstructionWitness_classified
    object.generatedIdentityFeatureExtension
    object.generatedIdentityExtensionComponentUniverse
    payload

/--
Atom-generated specialization of the residual-coverage-gap multi-label bridge.
-/
theorem generatedResidualCoverageGapExtensionObstructionWitness_multilabel_classified
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : AAT.GeneratedArchitectureObject presentation}
    (payload :
      ResidualCoverageGapWitnessPayload
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse) :
    MultiLabelClassifiedAsResidualCoverageGap
      object.generatedIdentityFeatureExtension
      object.generatedIdentityExtensionComponentUniverse
      (residualCoverageGapExtensionObstructionWitness
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse
        payload).toMultiLabel :=
  residualCoverageGapExtensionObstructionWitness_multilabel_classified
    object.generatedIdentityFeatureExtension
    object.generatedIdentityExtensionComponentUniverse
    payload

/--
Generated identity feature extensions have complete generated coverage, so a
residual coverage-gap payload cannot be constructed for that generated surface.
-/
theorem generatedIdentityExtension_noResidualCoverageGapPayload
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : AAT.GeneratedArchitectureObject presentation) :
    ¬ Nonempty
      (ResidualCoverageGapWitnessPayload
        object.generatedIdentityFeatureExtension
        object.generatedIdentityExtensionComponentUniverse) := by
  intro hPayload
  rcases hPayload with ⟨payload⟩
  exact
    not_extensionCoverage_of_residualCoverageGapPayload payload
      object.generatedIdentityExtensionCoverageComplete

end Chapter10ArchitectureExtensionFormula

end Formal.Arch
