import Formal.Arch.Signature.AnalyticRepresentation
import Formal.Arch.Extension.ArchitectureExtensionFormula
import Formal.Arch.Extension.FeatureExtensionExamples
import Formal.Arch.Evolution.DiagramFiller
import Formal.Arch.Extension.CertifiedArchitecture
import Formal.Arch.Signature.Signature
import Formal.Arch.Signature.SignatureLawfulness
import Formal.Arch.Examples.StaticSemanticCounterexample

/-!
Documentation-facing entrypoint for the mathematical design Chapter 11
Analytic Representation and Canonical Example package.

This module is intentionally thin. Importing it exposes the representation and
valuation schemas, the coupon static and semantic examples, and the measurement
boundary APIs that tooling reports must respect. It does not add global
flatness, universe-wide witness completeness, empirical cost, or extractor
completeness claims.
-/

namespace Formal.Arch

namespace Chapter11AnalyticRepresentation

/--
A stable documentation-facing mapping from schematic names in Chapter 11 to the
Lean declarations that currently carry the corresponding bounded API.
-/
structure SchematicCorrespondence where
  schematic : String
  leanDeclarations : List String
  reading : String
  status : String
  deriving Repr

/--
Report-side classification used by AIR / Feature Extension Report metadata.

This mirrors the tooling vocabulary without turning a measured witness into a
formal theorem claim.
-/
inductive ClaimClassification where
  | proved
  | measured
  | assumed
  | empirical
  | unmeasured
  | outOfScope
  deriving DecidableEq, Repr

namespace ClaimClassification

/-- The claim has a discharged formal theorem package. -/
def IsProved (classification : ClaimClassification) : Prop :=
  classification = ClaimClassification.proved

/-- The claim is supported by tooling-side measurement. -/
def IsMeasured (classification : ClaimClassification) : Prop :=
  classification = ClaimClassification.measured

/-- The claim is explicitly unmeasured. -/
def IsUnmeasured (classification : ClaimClassification) : Prop :=
  classification = ClaimClassification.unmeasured

theorem measured_not_proved :
    ¬ IsProved ClaimClassification.measured := by
  intro h
  cases h

theorem unmeasured_not_proved :
    ¬ IsProved ClaimClassification.unmeasured := by
  intro h
  cases h

end ClaimClassification

/--
Minimal theorem-registry metadata that a tooling report must carry before it
can cite a Lean theorem package.

`missingPreconditions` is a positive predicate recording that the checker still
found missing premises. A formal proved claim is allowed only when the package
reference, required assumptions, and absence of missing preconditions are all
explicit.
-/
structure ToolingTheoremPackageMetadata where
  theoremReferences : List String
  claimLevel : ClaimLevel
  claimClassification : ClaimClassification
  measurementBoundary : MeasurementBoundary
  requiredAssumptions : Prop
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  missingPreconditions : Prop
  nonConclusions : Prop
  deriving Repr

namespace ToolingTheoremPackageMetadata

/-- The metadata records a report-side non-conclusion clause. -/
def RecordsNonConclusions (metadata : ToolingTheoremPackageMetadata) : Prop :=
  metadata.nonConclusions

/-- A measured witness remains tooling-level evidence. -/
def IsMeasuredWitness (metadata : ToolingTheoremPackageMetadata) : Prop :=
  metadata.claimLevel = ClaimLevel.tooling ∧
    metadata.claimClassification = ClaimClassification.measured ∧
    metadata.measurementBoundary = MeasurementBoundary.measuredNonzero

/-- A formal proved claim needs a theorem reference and discharged preconditions. -/
def IsFormalProvedClaim (metadata : ToolingTheoremPackageMetadata) : Prop :=
  metadata.claimLevel = ClaimLevel.formal ∧
    metadata.claimClassification = ClaimClassification.proved ∧
    metadata.theoremReferences ≠ [] ∧
    metadata.requiredAssumptions ∧
    metadata.coverageAssumptions ∧
    metadata.exactnessAssumptions ∧
    ¬ metadata.missingPreconditions

/-- A measured tooling witness is not classified as a formal proved claim. -/
theorem measuredWitness_not_formalProvedClaim
    (metadata : ToolingTheoremPackageMetadata)
    (hMeasured : metadata.IsMeasuredWitness) :
    ¬ metadata.IsFormalProvedClaim := by
  intro hFormal
  cases hMeasured.1.symm.trans hFormal.1

/-- Missing preconditions block formal proved report claims. -/
theorem not_formalProvedClaim_of_missingPreconditions
    (metadata : ToolingTheoremPackageMetadata)
    (hMissing : metadata.missingPreconditions) :
    ¬ metadata.IsFormalProvedClaim := by
  intro hFormal
  exact hFormal.2.2.2.2.2.2 hMissing

/-- The recorded non-conclusion predicate is exactly the schema field. -/
theorem records_nonConclusions_iff
    (metadata : ToolingTheoremPackageMetadata) :
    metadata.RecordsNonConclusions ↔ metadata.nonConclusions := by
  rfl

end ToolingTheoremPackageMetadata

/--
Chapter 11 wrapper for reading one optional analytic axis value through the
tooling report measurement boundary.

The `value` field keeps the Lean-side `Option Nat` metric. The
`measurementBoundary` field keeps the report-side classification. The coverage
fields are explicit because a measured zero value alone is not a zero-reflecting
architecture theorem.
-/
structure AnalyticAxisBoundary where
  value : Option Nat
  measurementBoundary : MeasurementBoundary
  coverageAssumptions : Prop
  witnessCompleteness : Prop
  semanticContractCoverage : Prop
  nonConclusions : Prop

namespace AnalyticAxisBoundary

/-- `some (n + 1)` records a measured nonzero selected axis value. -/
def MeasuredNonzeroValue (value : Option Nat) : Prop :=
  ∃ n, value = some (n + 1)

/-- `none` records an unmeasured axis, not a zero measurement. -/
def UnmeasuredValue (value : Option Nat) : Prop :=
  value = none

/-- Canonical report boundary for a Lean-side optional natural metric. -/
def boundaryOfOption : Option Nat -> MeasurementBoundary
  | none => MeasurementBoundary.unmeasured
  | some 0 => MeasurementBoundary.measuredZero
  | some (_n + 1) => MeasurementBoundary.measuredNonzero

/-- Build a Chapter 11 axis boundary wrapper from an optional metric. -/
def ofOption (value : Option Nat)
    (coverageAssumptions witnessCompleteness semanticContractCoverage
      nonConclusions : Prop) :
    AnalyticAxisBoundary where
  value := value
  measurementBoundary := boundaryOfOption value
  coverageAssumptions := coverageAssumptions
  witnessCompleteness := witnessCompleteness
  semanticContractCoverage := semanticContractCoverage
  nonConclusions := nonConclusions

/-- Read a concrete Signature v1 axis as a Chapter 11 analytic axis boundary. -/
def ofSignatureAxis
    (sig : ArchitectureSignature.ArchitectureSignatureV1)
    (axis : ArchitectureSignature.ArchitectureSignatureV1Axis)
    (coverageAssumptions witnessCompleteness semanticContractCoverage
      nonConclusions : Prop) :
    AnalyticAxisBoundary :=
  ofOption (ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis)
    coverageAssumptions witnessCompleteness semanticContractCoverage
    nonConclusions

/-- The wrapper records an explicit measured-zero report boundary. -/
def IsMeasuredZero (axis : AnalyticAxisBoundary) : Prop :=
  axis.measurementBoundary = MeasurementBoundary.measuredZero ∧
    AvailableAndZero axis.value

/-- The wrapper records an explicit measured-nonzero report boundary. -/
def IsMeasuredNonzero (axis : AnalyticAxisBoundary) : Prop :=
  axis.measurementBoundary = MeasurementBoundary.measuredNonzero ∧
    MeasuredNonzeroValue axis.value

/-- The wrapper records an unmeasured report boundary. -/
def IsUnmeasured (axis : AnalyticAxisBoundary) : Prop :=
  axis.measurementBoundary = MeasurementBoundary.unmeasured ∧
    UnmeasuredValue axis.value

/-- A selected analytic obstruction is supported by a measured nonzero axis. -/
def SupportsSelectedAnalyticObstruction
    (axis : AnalyticAxisBoundary) : Prop :=
  MeasuredNonzeroValue axis.value

/--
Preconditions needed before a zero-valued analytic axis can be used as a
zero-reflecting theorem claim.
-/
def CanDischargeZeroReflectingClaim
    (axis : AnalyticAxisBoundary) : Prop :=
  AvailableAndZero axis.value ∧
    axis.coverageAssumptions ∧
    axis.witnessCompleteness ∧
    axis.semanticContractCoverage

theorem boundaryOfOption_none :
    boundaryOfOption none = MeasurementBoundary.unmeasured := by
  rfl

theorem boundaryOfOption_some_zero :
    boundaryOfOption (some 0) = MeasurementBoundary.measuredZero := by
  rfl

theorem boundaryOfOption_some_succ (n : Nat) :
    boundaryOfOption (some (n + 1)) =
      MeasurementBoundary.measuredNonzero := by
  rfl

/-- `some 0` and `none` are distinct report inputs. -/
theorem some_zero_ne_unmeasured : (some 0 : Option Nat) ≠ none := by
  intro h
  cases h

/-- `none` and `some 0` are distinct report inputs. -/
theorem unmeasured_ne_some_zero : none ≠ (some 0 : Option Nat) := by
  intro h
  cases h

/--
An unmeasured optional value is not available-and-zero. This is the Chapter 11
wrapper around the stronger `AvailableAndZero` boundary.
-/
theorem unmeasured_not_availableAndZero {value : Option Nat}
    (hUnmeasured : UnmeasuredValue value) :
    ¬ AvailableAndZero value := by
  rw [hUnmeasured]
  exact not_availableAndZero_none

/-- A measured nonzero value is not weakly measured-zero. -/
theorem measuredNonzero_not_measuredZero {value : Option Nat}
    (hNonzero : MeasuredNonzeroValue value) :
    ¬ MeasuredZero value := by
  rcases hNonzero with ⟨n, hValue⟩
  intro hZero
  rw [hValue] at hZero
  have hSuccZero : n + 1 = 0 := hZero (n + 1) rfl
  cases hSuccZero

/-- A measured nonzero report axis supports the selected obstruction reading. -/
theorem supportsSelectedAnalyticObstruction_of_measuredNonzero
    {axis : AnalyticAxisBoundary}
    (hMeasured : axis.IsMeasuredNonzero) :
    axis.SupportsSelectedAnalyticObstruction :=
  hMeasured.2

/--
An unmeasured axis cannot discharge the zero-reflecting claim package, even
though `none` satisfies the weaker `MeasuredZero` predicate.
-/
theorem not_canDischargeZeroReflectingClaim_of_unmeasured
    {axis : AnalyticAxisBoundary}
    (hUnmeasured : axis.IsUnmeasured) :
    ¬ axis.CanDischargeZeroReflectingClaim := by
  intro hClaim
  exact unmeasured_not_availableAndZero hUnmeasured.2 hClaim.1

/--
An absent Signature v1 axis value remains weakly measured-zero only in the
non-certifying sense.
-/
theorem signatureAxisMeasuredZero_of_unmeasured
    {sig : ArchitectureSignature.ArchitectureSignatureV1}
    {axis : ArchitectureSignature.ArchitectureSignatureV1Axis}
    (hNone :
      ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis =
        none) :
    ArchitectureSignature.ArchitectureSignatureV1.axisMeasuredZero sig axis :=
  ArchitectureSignature.ArchitectureSignatureV1.axisMeasuredZero_of_axisValue_none
    hNone

/--
An absent Signature v1 axis value is not available-and-zero, so it cannot be
used as a covered zero-law witness.
-/
theorem not_signatureAxisAvailableAndZero_of_unmeasured
    {sig : ArchitectureSignature.ArchitectureSignatureV1}
    {axis : ArchitectureSignature.ArchitectureSignatureV1Axis}
    (hNone :
      ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis =
        none) :
    ¬ ArchitectureSignature.ArchitectureSignatureV1.axisAvailableAndZero
        sig axis :=
  ArchitectureSignature.ArchitectureSignatureV1.not_axisAvailableAndZero_of_axisValue_none
    hNone

/-- Signature v1 axes with `none` become unmeasured Chapter 11 axis wrappers. -/
theorem ofSignatureAxis_isUnmeasured_of_axisValue_none
    {sig : ArchitectureSignature.ArchitectureSignatureV1}
    {axis : ArchitectureSignature.ArchitectureSignatureV1Axis}
    {coverageAssumptions witnessCompleteness semanticContractCoverage
      nonConclusions : Prop}
    (hNone :
      ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis =
        none) :
    (ofSignatureAxis sig axis coverageAssumptions witnessCompleteness
      semanticContractCoverage nonConclusions).IsUnmeasured := by
  unfold ofSignatureAxis ofOption IsUnmeasured UnmeasuredValue
  simp [hNone, boundaryOfOption]

end AnalyticAxisBoundary

/--
Aggregate witness used by the concrete Signature v1 representation.

The witness is intentionally coarse: it records failure of the selected
required-law theorem package as a whole. Per-axis optional metrics remain
diagnostic boundaries unless they are selected required axes with available
zero evidence.
-/
inductive ArchitectureSignatureAggregateWitness where
  | selectedRequiredLawFailure
  deriving DecidableEq, Repr

/--
Non-conclusion boundary for reading Signature v1 as an analytic
representation.

An optional axis value of `none` is not an available zero certificate. In
particular, unselected optional axes do not become required analytic zero axes
merely by being absent from the report.
-/
def ArchitectureSignatureAnalyticNonConclusions : Prop :=
  ∀ sig axis,
    ArchitectureSignature.ArchitectureSignatureV1.axisValue sig axis = none ->
      ¬ ArchitectureSignature.ArchitectureSignatureV1.axisAvailableAndZero
        sig axis

/--
Concrete analytic representation sending an `ArchitectureLawModel` to its
Signature v1 output.

The analytic zero predicate is exactly selected required Signature axes being
available and zero. Reflecting directions remain fields of the representation
schema and are discharged only through the existing concrete coverage and
axis-exactness theorem package.
-/
noncomputable def architectureSignatureAnalyticRepresentation
    (C : Type u) (A : Type v) (Obs : Type w)
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs] :
    AnalyticRepresentation
      (ArchitectureSignature.ArchitectureLawModel C A Obs)
      ArchitectureSignature.ArchitectureSignatureV1
      ArchitectureSignatureAggregateWitness where
  represent := fun X =>
    haveI := Classical.decRel X.G.edge
    haveI := Classical.decRel X.GA.edge
    haveI := Classical.decRel X.boundaryAllowed
    haveI := Classical.decRel X.abstractionAllowed
    ArchitectureSignature.ArchitectureLawModel.signatureOf X
  structuralZero := fun X => ArchitectureSignature.ArchitectureLawful X
  analyticZero := fun sig =>
    ArchitectureSignature.RequiredSignatureAxesZero sig
  structuralObstruction := fun X _ =>
    ¬ ArchitectureSignature.ArchitectureLawful X
  analyticObstruction := fun sig _ =>
    ¬ ArchitectureSignature.RequiredSignatureAxesZero sig
  coverageAssumptions :=
    CompleteWitnessCoverage
      (ArchitectureSignature.architectureLawFamily C A Obs)
  witnessCompleteness :=
    RequiredWitnessCoveredByAxis
      (ArchitectureSignature.architectureLawFamily C A Obs)
      ArchitectureSignature.architectureWitnessForAxis
  semanticContractCoverage := True
  nonConclusions := ArchitectureSignatureAnalyticNonConclusions

theorem architectureSignatureAnalyticRepresentation_nonConclusions
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs] :
    (architectureSignatureAnalyticRepresentation C A Obs).nonConclusions := by
  intro sig axis hNone
  exact
    ArchitectureSignature.ArchitectureSignatureV1.not_axisAvailableAndZero_of_axisValue_none
      hNone

theorem architectureSignatureAnalyticRepresentation_zeroPreserving
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs] :
    AnalyticRepresentation.ZeroPreserving
      (architectureSignatureAnalyticRepresentation C A Obs) := by
  classical
  intro X hLawful
  dsimp [architectureSignatureAnalyticRepresentation]
  exact
    (ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero X).mp
      hLawful

theorem architectureSignatureAnalyticRepresentation_zeroReflecting
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs] :
    AnalyticRepresentation.ZeroReflecting
      (architectureSignatureAnalyticRepresentation C A Obs) := by
  classical
  intro _hCoverage _hWitness _hSemantic X hZero
  dsimp [architectureSignatureAnalyticRepresentation] at hZero
  exact
    (ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero X).mpr
      hZero

theorem architectureSignatureAnalyticRepresentation_obstructionPreserving
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs] :
    AnalyticRepresentation.ObstructionPreserving
      (architectureSignatureAnalyticRepresentation C A Obs) := by
  classical
  intro X witness hObstruction
  cases witness
  dsimp [architectureSignatureAnalyticRepresentation] at hObstruction ⊢
  intro hZero
  exact hObstruction
    ((ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero X).mpr
      hZero)

theorem architectureSignatureAnalyticRepresentation_obstructionReflecting
    [DecidableEq C] [DecidableEq A] [DecidableEq Obs] :
    AnalyticRepresentation.ObstructionReflecting
      (architectureSignatureAnalyticRepresentation C A Obs) := by
  classical
  intro _hCoverage _hWitness _hSemantic X witness hObstruction
  cases witness
  dsimp [architectureSignatureAnalyticRepresentation] at hObstruction ⊢
  intro hLawful
  exact hObstruction
    ((ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero X).mp
      hLawful)

/--
Analytic extension formula package for Chapter 11.

The formula is represented as an explicit field:

`after + repair = before + feature + interaction + transfer + residual`.

This avoids treating the analytic formula as a global conservation law. The
package is relative to its representation map, selected valuation structure,
feature payload, decomposition certificate, and coverage assumptions.
-/
structure AnalyticExtensionFormulaPackage
    (State : Type u) (Analytic : Type v) (Feature : Type w)
    (Witness : Type q) where
  representation : AnalyticRepresentation State Analytic Witness
  obstructionValuation : ObstructionValuation State Witness
  before : State
  after : State
  feature : Feature
  signatureValue : Analytic -> Nat
  featureContribution : Feature -> Nat
  interactionTerm : State -> Feature -> State -> Nat
  transferTerm : State -> Feature -> State -> Nat
  repairTerm : State -> Feature -> State -> Nat
  obstructionResidual : State -> Feature -> State -> Nat
  representationMapAssumptions : Prop
  valuationStructureAssumptions : Prop
  decompositionCertificate : Prop
  coverageAssumptions : Prop
  complexityTransferBoundary : Prop
  formulaHolds :
    signatureValue (representation.represent after) +
        repairTerm before feature after =
      signatureValue (representation.represent before) +
        featureContribution feature +
        interactionTerm before feature after +
        transferTerm before feature after +
        obstructionResidual before feature after
  nonConclusions : Prop

namespace AnalyticExtensionFormulaPackage

variable {State : Type u} {Analytic : Type v} {Feature : Type w}
variable {Witness : Type q}

/-- The package explicitly records the analytic formula equation it carries. -/
def FormulaEquation
    (pkg : AnalyticExtensionFormulaPackage State Analytic Feature Witness) :
    Prop :=
  pkg.signatureValue (pkg.representation.represent pkg.after) +
      pkg.repairTerm pkg.before pkg.feature pkg.after =
    pkg.signatureValue (pkg.representation.represent pkg.before) +
      pkg.featureContribution pkg.feature +
      pkg.interactionTerm pkg.before pkg.feature pkg.after +
      pkg.transferTerm pkg.before pkg.feature pkg.after +
      pkg.obstructionResidual pkg.before pkg.feature pkg.after

/-- The package explicitly records its non-conclusion clause. -/
def RecordsNonConclusions
    (pkg : AnalyticExtensionFormulaPackage State Analytic Feature Witness) :
    Prop :=
  pkg.nonConclusions

/-- Required assumptions for reading the analytic formula as a theorem package. -/
def RequiredAssumptions
    (pkg : AnalyticExtensionFormulaPackage State Analytic Feature Witness) :
    Prop :=
  pkg.representationMapAssumptions ∧
    pkg.valuationStructureAssumptions ∧
    pkg.decompositionCertificate ∧
    pkg.coverageAssumptions ∧
    pkg.complexityTransferBoundary

theorem formula_holds
    (pkg : AnalyticExtensionFormulaPackage State Analytic Feature Witness) :
    pkg.FormulaEquation :=
  pkg.formulaHolds

theorem records_nonConclusions_iff
    (pkg : AnalyticExtensionFormulaPackage State Analytic Feature Witness) :
    pkg.RecordsNonConclusions ↔ pkg.nonConclusions := by
  rfl

theorem requiredAssumptions_of_fields
    (pkg : AnalyticExtensionFormulaPackage State Analytic Feature Witness)
    (hRepresentation : pkg.representationMapAssumptions)
    (hValuation : pkg.valuationStructureAssumptions)
    (hDecomposition : pkg.decompositionCertificate)
    (hCoverage : pkg.coverageAssumptions)
    (hTransfer : pkg.complexityTransferBoundary) :
    pkg.RequiredAssumptions :=
  ⟨hRepresentation, hValuation, hDecomposition, hCoverage, hTransfer⟩

end AnalyticExtensionFormulaPackage

/--
Report-facing analytic snapshot for the Chapter 11 coupon canonical example.

The three axes mirror the design-note fields
`static_hidden_interaction`, `runtime_exposure`, and `semantic_curvature`.
Each axis keeps its measurement boundary, so `none` remains unmeasured rather
than being read as a zero certificate.
-/
structure CouponAnalyticSnapshot where
  staticHiddenInteraction : AnalyticAxisBoundary
  runtimeExposure : AnalyticAxisBoundary
  semanticCurvature : AnalyticAxisBoundary
  nonConclusions : Prop

namespace CouponAnalyticSnapshot

/-- Bad coupon extension: the selected static hidden-interaction axis is seen. -/
def badStaticHiddenInteractionAxis : AnalyticAxisBoundary :=
  AnalyticAxisBoundary.ofOption (some 1) True True True True

/-- Repaired coupon extension: the selected static hidden-interaction axis is measured zero. -/
def repairedStaticHiddenInteractionAxis : AnalyticAxisBoundary :=
  AnalyticAxisBoundary.ofOption (some 0) True True True True

/-- Runtime exposure is intentionally left unmeasured in the canonical snapshot. -/
def runtimeExposureUnmeasuredAxis : AnalyticAxisBoundary :=
  AnalyticAxisBoundary.ofOption none True True True True

/-- Semantic curvature can also be left unmeasured without being treated as zero. -/
def semanticCurvatureUnmeasuredAxis : AnalyticAxisBoundary :=
  AnalyticAxisBoundary.ofOption none True True True True

/--
Measured semantic curvature for the selected coupon / discount rounding-order
diagram. The concrete canonical residual is one selected obstruction.
-/
def semanticCurvatureMeasuredAxis : AnalyticAxisBoundary :=
  AnalyticAxisBoundary.ofOption (some 1) True True True True

/-- Canonical bad coupon snapshot with static hidden interaction and unmeasured runtime / semantic axes. -/
def bad : CouponAnalyticSnapshot where
  staticHiddenInteraction := badStaticHiddenInteractionAxis
  runtimeExposure := runtimeExposureUnmeasuredAxis
  semanticCurvature := semanticCurvatureUnmeasuredAxis
  nonConclusions := True

/-- Canonical repaired coupon snapshot with measured-zero selected static hidden interaction. -/
def repaired : CouponAnalyticSnapshot where
  staticHiddenInteraction := repairedStaticHiddenInteractionAxis
  runtimeExposure := runtimeExposureUnmeasuredAxis
  semanticCurvature := semanticCurvatureUnmeasuredAxis
  nonConclusions := True

/--
Canonical repaired-static snapshot where the selected semantic rounding-order
residual is measured as a positive axis.
-/
def repairedWithMeasuredSemanticCurvature : CouponAnalyticSnapshot where
  staticHiddenInteraction := repairedStaticHiddenInteractionAxis
  runtimeExposure := runtimeExposureUnmeasuredAxis
  semanticCurvature := semanticCurvatureMeasuredAxis
  nonConclusions := True

theorem bad_staticHiddenInteraction_value :
    bad.staticHiddenInteraction.value = some 1 := by
  rfl

theorem bad_staticHiddenInteraction_measuredNonzero :
    bad.staticHiddenInteraction.IsMeasuredNonzero := by
  constructor
  · rfl
  · exact ⟨0, rfl⟩

theorem bad_staticHiddenInteraction_supportsSelectedObstruction :
    bad.staticHiddenInteraction.SupportsSelectedAnalyticObstruction :=
  AnalyticAxisBoundary.supportsSelectedAnalyticObstruction_of_measuredNonzero
    bad_staticHiddenInteraction_measuredNonzero

theorem bad_staticHiddenInteraction_hiddenDependencyWitnessExists :
    StaticExtensionWitnessExists
      CouponStaticDependencyExample.badExtension
      CouponStaticDependencyExample.declaredInterface
      CouponStaticDependencyExample.coreAllowedStaticEdge
      CouponStaticDependencyExample.extendedAllowedStaticEdge :=
  CouponStaticDependencyExample.hiddenDependencyWitnessExists

theorem bad_staticHiddenInteraction_bridge :
    bad.staticHiddenInteraction.SupportsSelectedAnalyticObstruction ∧
      StaticExtensionWitnessExists
        CouponStaticDependencyExample.badExtension
        CouponStaticDependencyExample.declaredInterface
        CouponStaticDependencyExample.coreAllowedStaticEdge
        CouponStaticDependencyExample.extendedAllowedStaticEdge :=
  ⟨bad_staticHiddenInteraction_supportsSelectedObstruction,
    bad_staticHiddenInteraction_hiddenDependencyWitnessExists⟩

theorem bad_selectedStaticSplitFailure :
    ¬ SelectedStaticSplitExtension
      CouponStaticDependencyExample.badExtension
      CouponStaticDependencyExample.declaredInterface
      CouponStaticDependencyExample.coreAllowedStaticEdge
      CouponStaticDependencyExample.extendedAllowedStaticEdge :=
  CouponStaticDependencyExample.bad_not_selectedStaticSplitFeatureExtension

theorem repaired_staticHiddenInteraction_value :
    repaired.staticHiddenInteraction.value = some 0 := by
  rfl

theorem repaired_staticHiddenInteraction_measuredZero :
    repaired.staticHiddenInteraction.IsMeasuredZero := by
  constructor
  · rfl
  · rfl

theorem repaired_selectedStaticSplit :
    SelectedStaticSplitExtension
      CouponStaticDependencyExample.repairedExtension
      CouponStaticDependencyExample.declaredInterface
      CouponStaticDependencyExample.coreAllowedStaticEdge
      CouponStaticDependencyExample.extendedAllowedStaticEdge :=
  CouponStaticDependencyExample.repaired_selectedStaticSplitFeatureExtension

theorem repaired_staticWitnessAbsent :
    ¬ StaticExtensionWitnessExists
      CouponStaticDependencyExample.repairedExtension
      CouponStaticDependencyExample.declaredInterface
      CouponStaticDependencyExample.coreAllowedStaticEdge
      CouponStaticDependencyExample.extendedAllowedStaticEdge := by
  intro hWitness
  exact
    not_selectedStaticSplitExtension_of_staticExtensionWitnessExists hWitness
      repaired_selectedStaticSplit

theorem repaired_staticHiddenInteraction_bridge :
    repaired.staticHiddenInteraction.IsMeasuredZero ∧
      ¬ StaticExtensionWitnessExists
        CouponStaticDependencyExample.repairedExtension
        CouponStaticDependencyExample.declaredInterface
        CouponStaticDependencyExample.coreAllowedStaticEdge
        CouponStaticDependencyExample.extendedAllowedStaticEdge :=
  ⟨repaired_staticHiddenInteraction_measuredZero, repaired_staticWitnessAbsent⟩

theorem runtimeExposure_unmeasured :
    bad.runtimeExposure.IsUnmeasured := by
  constructor
  · rfl
  · rfl

theorem runtimeExposure_not_zeroReflectingClaim :
    ¬ bad.runtimeExposure.CanDischargeZeroReflectingClaim :=
  AnalyticAxisBoundary.not_canDischargeZeroReflectingClaim_of_unmeasured
    runtimeExposure_unmeasured

theorem semanticCurvature_unmeasured :
    bad.semanticCurvature.IsUnmeasured := by
  constructor
  · rfl
  · rfl

theorem semanticCurvature_unmeasured_not_zeroReflectingClaim :
    ¬ bad.semanticCurvature.CanDischargeZeroReflectingClaim :=
  AnalyticAxisBoundary.not_canDischargeZeroReflectingClaim_of_unmeasured
    semanticCurvature_unmeasured

theorem repairedWithMeasuredSemanticCurvature_value :
    repairedWithMeasuredSemanticCurvature.semanticCurvature.value = some 1 := by
  rfl

theorem repairedWithMeasuredSemanticCurvature_measuredNonzero :
    repairedWithMeasuredSemanticCurvature.semanticCurvature.IsMeasuredNonzero := by
  constructor
  · rfl
  · exact ⟨0, rfl⟩

theorem repairedWithMeasuredSemanticCurvature_supportsSelectedObstruction :
    repairedWithMeasuredSemanticCurvature.semanticCurvature.SupportsSelectedAnalyticObstruction :=
  AnalyticAxisBoundary.supportsSelectedAnalyticObstruction_of_measuredNonzero
    repairedWithMeasuredSemanticCurvature_measuredNonzero

theorem repairedWithMeasuredSemanticCurvature_roundingOrderValuation_positive :
    0 < CouponDiscountExample.roundingOrderValuation.value
      CouponDiscountExample.couponDiscountDiagram
      CouponDiscountExample.CouponDiscountWitness.roundingOrder :=
  CouponDiscountExample.roundingOrderValuation_positive

theorem recordsNonConclusions (snapshot : CouponAnalyticSnapshot) :
    snapshot.nonConclusions -> snapshot.nonConclusions :=
  id

end CouponAnalyticSnapshot

namespace CouponHiddenInteractionLiftingBridge

open CouponStaticDependencyExample

/--
Selected operation endpoints used only to read the bad coupon hidden
interaction as a local lifting failure. This operation view does not assert
feature ownership for the core cache in the static split model.
-/
inductive HiddenInteractionEndpoint where
  | couponCalculation
  | paymentCacheRead
  deriving DecidableEq, Repr

inductive HiddenInteractionFeatureEdge :
    HiddenInteractionEndpoint -> HiddenInteractionEndpoint -> Prop where
  | couponCalculationToPaymentCacheRead :
      HiddenInteractionFeatureEdge .couponCalculation .paymentCacheRead

def operationFeatureGraph : ArchGraph HiddenInteractionEndpoint where
  edge := HiddenInteractionFeatureEdge

def operationFeatureEmbedding :
    HiddenInteractionEndpoint -> ExtendedComponent
  | .couponCalculation => .couponService
  | .paymentCacheRead => .internalCache

def operationFeatureObservation :
    Observation HiddenInteractionEndpoint Unit where
  observe := fun _ => ()

def operationFeatureView :
    Observation ExtendedComponent Unit where
  observe := fun _ => ()

/--
The operation endpoint view shares the bad coupon extended graph. It is a
selected lifting view for one interaction, not a replacement for the static
ownership model used by `CouponStaticDependencyExample.badExtension`.
-/
def operationExtension :
    FeatureExtension CoreComponent HiddenInteractionEndpoint ExtendedComponent
      Unit where
  core := coreGraph
  feature := operationFeatureGraph
  extended := badGraph
  coreEmbedding := coreEmbedding
  featureEmbedding := operationFeatureEmbedding
  featureView := operationFeatureView
  preservesRequiredInvariants := True
  interactionFactorsThroughDeclaredInterfaces := True
  coverageAssumptions := True
  proofObligations := True

def operationCoreObservation : Observation CoreComponent Unit where
  observe := fun _ => ()

def operationCoreRetraction : ExtendedComponent -> CoreComponent
  | .paymentApi => .paymentApi
  | .paymentAdapter => .paymentAdapter
  | .internalCache => .internalCache
  | .couponService => .paymentApi
  | .declaredPaymentPort => .paymentApi

def liftingData :
    SplitExtensionLiftingData CoreComponent HiddenInteractionEndpoint
      ExtendedComponent Unit Unit where
  extension := operationExtension
  featureObservation := operationFeatureObservation
  coreObservation := operationCoreObservation
  featureSection := operationFeatureEmbedding
  coreRetraction := operationCoreRetraction
  featureSectionLaw := by
    intro f
    cases f <;> rfl
  observationalCoreRetraction := by
    intro c
    cases c <;> rfl
  interfaceFactorization := trivial
  preservesRequiredInvariants := trivial

def selectedFeatureStep : SelectedFeatureStep HiddenInteractionEndpoint where
  source := .couponCalculation
  target := .paymentCacheRead

def featureInvariant (_endpoint : HiddenInteractionEndpoint) : Prop :=
  True

/--
The selected core invariant excludes direct interaction with the internal cache.
This makes the hidden cache read a local lifting-preservation failure without
claiming a global semantic or runtime theorem.
-/
def coreInvariant (c : CoreComponent) : Prop :=
  c ≠ .internalCache

theorem lawfulSelectedFeatureStep :
    LawfulFeatureStep featureInvariant selectedFeatureStep := by
  intro _h
  trivial

theorem selectedFeatureStep_liftedEdge_is_hiddenDependency :
    operationExtension.extended.edge
      (liftingData.featureSection selectedFeatureStep.source)
      (liftingData.featureSection selectedFeatureStep.target) :=
  BadStaticEdge.hiddenCouponToInternalCache

theorem selectedFeatureStep_not_declaredInterfaceFactor :
    ¬ EdgeFactorsThroughDeclaredInterface operationExtension.extended
      declaredInterface
      (liftingData.featureSection selectedFeatureStep.source)
      (liftingData.featureSection selectedFeatureStep.target) :=
  hidden_dependency_not_declared_factor

theorem sourceCoreInvariant :
    coreInvariant
      (liftingData.coreRetraction
        (liftingData.featureSection selectedFeatureStep.source)) := by
  intro hEq
  cases hEq

theorem targetCoreInvariant_false :
    ¬ coreInvariant
      (liftingData.coreRetraction
        (liftingData.featureSection selectedFeatureStep.target)) := by
  intro hTarget
  exact hTarget rfl

theorem not_compatibleWithInterface :
    ¬ CompatibleWithInterface liftingData coreInvariant selectedFeatureStep := by
  intro hCompatible
  exact targetCoreInvariant_false
    (hCompatible.coreInvariantPreserved sourceCoreInvariant)

theorem noPreservationPackage :
    ¬ ∃ liftedStep : LiftedExtensionStep ExtendedComponent,
      SplitExtensionLiftingPreservationPackage
        liftingData featureInvariant coreInvariant selectedFeatureStep
        liftedStep := by
  intro hExists
  rcases hExists with ⟨liftedStep, hPackage⟩
  have hSource :
      coreInvariant (liftingData.coreRetraction liftedStep.source) := by
    rw [hPackage.liftsFeatureStep.1]
    exact sourceCoreInvariant
  have hTarget :
      coreInvariant (liftingData.coreRetraction liftedStep.target) :=
    hPackage.preservesCoreInvariants hSource
  have hCanonicalTarget :
      coreInvariant
        (liftingData.coreRetraction
          (liftingData.featureSection selectedFeatureStep.target)) := by
    rw [hPackage.liftsFeatureStep.2.1] at hTarget
    exact hTarget
  exact targetCoreInvariant_false hCanonicalTarget

def liftingFailurePayload :
    LiftingFailureWitnessPayload
      liftingData featureInvariant coreInvariant selectedFeatureStep where
  lawfulFeatureStep := lawfulSelectedFeatureStep
  notPreservationPackage := noPreservationPackage

def liftingFailureWitness :
    ExtensionObstructionWitness operationExtension
      (LiftingFailureWitnessPayload
        liftingData featureInvariant coreInvariant selectedFeatureStep) :=
  liftingFailureExtensionObstructionWitness liftingData liftingFailurePayload

def allExtendedComponents : List ExtendedComponent :=
  [ .paymentApi
  , .paymentAdapter
  , .internalCache
  , .couponService
  , .declaredPaymentPort
  ]

theorem allExtendedComponents_nodup : allExtendedComponents.Nodup := by
  decide

theorem mem_allExtendedComponents (c : ExtendedComponent) :
    c ∈ allExtendedComponents := by
  cases c <;> simp [allExtendedComponents]

def canonicalUniverse : ComponentUniverse operationExtension.extended :=
  ComponentUniverse.full operationExtension.extended allExtendedComponents
    allExtendedComponents_nodup mem_allExtendedComponents

theorem liftingFailureWitness_classified :
    ClassifiedAsLiftingFailure operationExtension canonicalUniverse
      liftingFailureWitness :=
  liftingFailureExtensionObstructionWitness_classified
    liftingData canonicalUniverse liftingFailurePayload

theorem liftingFailurePayload_refutesCompatibility :
    ¬ CompatibleWithInterface liftingData coreInvariant selectedFeatureStep :=
  not_compatibleWithInterface

theorem hiddenDependency_liftingFailure_bridge :
    StaticExtensionWitnessExists
      badExtension declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge ∧
    ∃ payload :
      LiftingFailureWitnessPayload
        liftingData featureInvariant coreInvariant selectedFeatureStep,
      ClassifiedAsLiftingFailure operationExtension canonicalUniverse
        (liftingFailureExtensionObstructionWitness liftingData payload) :=
  ⟨hiddenDependencyWitnessExists,
    ⟨liftingFailurePayload, liftingFailureWitness_classified⟩⟩

end CouponHiddenInteractionLiftingBridge

/-- The main Chapter 11 API groups exposed through this entrypoint. -/
inductive Candidate where
  | analyticRepresentation
  | toolingReportMetadata
  | architectureSignatureRepresentation
  | obstructionValuation
  | analyticExtensionFormula
  | couponAnalyticSnapshot
  | couponHiddenInteractionLiftingBridge
  | couponStaticExample
  | couponSemanticValuation
  | staticSemanticCounterexample
  | measurementBoundary
  deriving DecidableEq, Repr

namespace Candidate

/-- Human-readable section number in `docs/aat_v2_mathematical_design.md`. -/
def designSection : Candidate -> String
  | analyticRepresentation => "11"
  | toolingReportMetadata => "11.1 / tooling report metadata"
  | architectureSignatureRepresentation => "11.1 / 11.2"
  | obstructionValuation => "11"
  | analyticExtensionFormula => "11.1 / analytic extension formula"
  | couponAnalyticSnapshot => "11.3"
  | couponHiddenInteractionLiftingBridge => "11.3 / coupon lifting bridge"
  | couponStaticExample => "11 / coupon static axis"
  | couponSemanticValuation => "11 / coupon semantic axis"
  | staticSemanticCounterexample => "11 / canonical counterexample"
  | measurementBoundary => "11 / tooling boundary"

/-- Stable schematic name used by documentation and theorem-index tables. -/
def schematicName : Candidate -> String
  | analyticRepresentation => "Analytic Representation"
  | toolingReportMetadata =>
      "AIR / Feature Extension Report theorem metadata"
  | architectureSignatureRepresentation =>
      "ArchitectureSignatureV1 concrete analytic representation"
  | obstructionValuation => "Obstruction Valuation"
  | analyticExtensionFormula => "Analytic Extension Formula theorem package"
  | couponAnalyticSnapshot => "Coupon canonical analytic snapshot"
  | couponHiddenInteractionLiftingBridge =>
      "Coupon hidden interaction as lifting failure"
  | couponStaticExample => "Coupon static hidden dependency example"
  | couponSemanticValuation => "Coupon semantic rounding-order valuation"
  | staticSemanticCounterexample => "Static-flat semantic-obstruction example"
  | measurementBoundary => "Measurement boundary for unmeasured axes"

/-- Representative Lean declarations that serve as public entrypoints. -/
def representativeDeclarations : Candidate -> List String
  | analyticRepresentation =>
      ["AnalyticRepresentation",
       "AnalyticRepresentation.ZeroPreserving",
       "AnalyticRepresentation.ZeroReflecting",
       "AnalyticRepresentation.ObstructionPreserving",
       "AnalyticRepresentation.ObstructionReflecting",
       "AnalyticRepresentation.RecordsNonConclusions",
       "AnalyticRepresentation.analyticZero_of_structuralZero",
       "AnalyticRepresentation.structuralZero_of_analyticZero",
       "AnalyticRepresentation.analyticObstruction_of_structuralObstruction",
       "AnalyticRepresentation.structuralObstruction_of_analyticObstruction"]
  | toolingReportMetadata =>
      ["ClaimClassification",
       "ClaimClassification.IsProved",
       "ClaimClassification.IsMeasured",
       "ClaimClassification.measured_not_proved",
       "ToolingTheoremPackageMetadata",
       "ToolingTheoremPackageMetadata.IsMeasuredWitness",
       "ToolingTheoremPackageMetadata.IsFormalProvedClaim",
       "ToolingTheoremPackageMetadata.measuredWitness_not_formalProvedClaim",
       "ToolingTheoremPackageMetadata.not_formalProvedClaim_of_missingPreconditions",
       "ToolingTheoremPackageMetadata.RecordsNonConclusions"]
  | architectureSignatureRepresentation =>
      ["ArchitectureSignatureAggregateWitness",
       "ArchitectureSignatureAnalyticNonConclusions",
       "architectureSignatureAnalyticRepresentation",
       "architectureSignatureAnalyticRepresentation_nonConclusions",
       "architectureSignatureAnalyticRepresentation_zeroPreserving",
       "architectureSignatureAnalyticRepresentation_zeroReflecting",
       "architectureSignatureAnalyticRepresentation_obstructionPreserving",
       "architectureSignatureAnalyticRepresentation_obstructionReflecting",
       "ArchitectureSignature.ArchitectureLawModel.signatureOf",
       "ArchitectureSignature.RequiredSignatureAxesZero",
       "ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero"]
  | obstructionValuation =>
      ["ObstructionValuation",
       "ObstructionValuation.NoSelectedObstruction",
       "ObstructionValuation.ZeroReflectingSum",
       "ObstructionValuation.no_obstruction_of_value_zero",
       "ObstructionValuation.noSelectedObstruction_of_zeroReflectingSum",
       "ObstructionValuation.RecordsNonConclusions"]
  | analyticExtensionFormula =>
      ["AnalyticExtensionFormulaPackage",
       "AnalyticExtensionFormulaPackage.FormulaEquation",
       "AnalyticExtensionFormulaPackage.RequiredAssumptions",
       "AnalyticExtensionFormulaPackage.RecordsNonConclusions",
       "AnalyticExtensionFormulaPackage.formula_holds",
       "AnalyticExtensionFormulaPackage.requiredAssumptions_of_fields",
       "AnalyticExtensionFormulaPackage.records_nonConclusions_iff",
       "ObstructionValuation",
       "BoundedComplexityTransferPackage.no_free_elimination_bounded"]
  | couponAnalyticSnapshot =>
      ["CouponAnalyticSnapshot",
       "CouponAnalyticSnapshot.bad",
       "CouponAnalyticSnapshot.repaired",
       "CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature",
       "CouponAnalyticSnapshot.bad_staticHiddenInteraction_bridge",
       "CouponAnalyticSnapshot.repaired_staticHiddenInteraction_bridge",
       "CouponAnalyticSnapshot.runtimeExposure_not_zeroReflectingClaim",
       "CouponAnalyticSnapshot.semanticCurvature_unmeasured_not_zeroReflectingClaim",
       "CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature_roundingOrderValuation_positive",
       "CouponAnalyticSnapshot.recordsNonConclusions"]
  | couponHiddenInteractionLiftingBridge =>
      ["CouponHiddenInteractionLiftingBridge.selectedFeatureStep",
       "CouponHiddenInteractionLiftingBridge.selectedFeatureStep_liftedEdge_is_hiddenDependency",
       "CouponHiddenInteractionLiftingBridge.selectedFeatureStep_not_declaredInterfaceFactor",
       "CouponHiddenInteractionLiftingBridge.not_compatibleWithInterface",
       "CouponHiddenInteractionLiftingBridge.liftingFailurePayload",
       "CouponHiddenInteractionLiftingBridge.liftingFailureWitness",
       "CouponHiddenInteractionLiftingBridge.liftingFailureWitness_classified",
       "CouponHiddenInteractionLiftingBridge.liftingFailurePayload_refutesCompatibility",
       "CouponHiddenInteractionLiftingBridge.hiddenDependency_liftingFailure_bridge"]
  | couponStaticExample =>
      ["CouponStaticDependencyExample.goodStaticSplitFeatureExtension",
       "CouponStaticDependencyExample.hiddenDependencyWitness",
       "CouponStaticDependencyExample.hiddenDependencyWitnessExists",
       "CouponStaticDependencyExample.bad_not_selectedStaticSplitFeatureExtension",
       "CouponStaticDependencyExample.repairedStaticSplitFeatureExtension",
       "CouponStaticDependencyExample.repaired_selectedStaticSplitFeatureExtension"]
  | couponSemanticValuation =>
      ["CouponDiscountExample.couponDiscountDiagram",
       "CouponDiscountExample.roundingOrderResidual",
       "CouponDiscountExample.roundingOrderValuation",
       "CouponDiscountExample.couponDiscount_roundingOrderResidual_positive",
       "CouponDiscountExample.roundingOrderValuation_obstruction",
       "CouponDiscountExample.roundingOrderValuation_positive",
       "CouponDiscountExample.roundingOrderValuation_recordsNonConclusions"]
  | staticSemanticCounterexample =>
      ["StaticSemanticCounterexample.canonical_staticFlatWithin",
       "StaticSemanticCounterexample.canonical_not_semanticFlatWithin",
       "StaticSemanticCounterexample.canonical_not_architectureFlat",
       "StaticSemanticCounterexample.staticFlat_with_semanticObstruction",
       "StaticSemanticCounterexample.staticFlat_not_architectureFlat"]
  | measurementBoundary =>
      ["MeasurementBoundary",
       "MeasurementBoundary.measuredZero",
       "MeasurementBoundary.measuredNonzero",
       "MeasurementBoundary.unmeasured",
       "MeasurementBoundary.outOfScope",
       "AnalyticAxisBoundary",
       "AnalyticAxisBoundary.boundaryOfOption",
       "AnalyticAxisBoundary.ofOption",
       "AnalyticAxisBoundary.ofSignatureAxis",
       "AnalyticAxisBoundary.IsMeasuredZero",
       "AnalyticAxisBoundary.IsMeasuredNonzero",
       "AnalyticAxisBoundary.IsUnmeasured",
       "AnalyticAxisBoundary.SupportsSelectedAnalyticObstruction",
       "AnalyticAxisBoundary.CanDischargeZeroReflectingClaim",
       "AnalyticAxisBoundary.some_zero_ne_unmeasured",
       "AnalyticAxisBoundary.unmeasured_not_availableAndZero",
       "AnalyticAxisBoundary.supportsSelectedAnalyticObstruction_of_measuredNonzero",
       "AnalyticAxisBoundary.not_canDischargeZeroReflectingClaim_of_unmeasured",
       "AnalyticAxisBoundary.signatureAxisMeasuredZero_of_unmeasured",
       "AnalyticAxisBoundary.not_signatureAxisAvailableAndZero_of_unmeasured",
       "MeasurementBoundary.unmeasured_not_measuredZero",
       "ArchitectureClaim.unmeasured_not_measuredZero",
       "ArchitectureSignature.v1Schema_unitNoEdge_unmeasured"]

/--
Schematic-name to Lean-API correspondences for Chapter 11.

These rows are metadata only. They stabilize how the design-note schematic names
and tooling report fields are read against existing bounded Lean APIs without
adding new global flatness, completeness, or extractor claims.
-/
def schematicCorrespondences : Candidate -> List SchematicCorrespondence
  | analyticRepresentation =>
      [{ schematic := "AnalyticRepresentation State Analytic Witness",
         leanDeclarations :=
          ["AnalyticRepresentation",
           "AnalyticRepresentation.ZeroPreserving",
           "AnalyticRepresentation.ZeroReflecting",
           "AnalyticRepresentation.ObstructionPreserving",
           "AnalyticRepresentation.ObstructionReflecting"],
         reading :=
          "representation map with preserving directions and reflecting directions relative to coverage and completeness assumptions",
         status := "defined only / proved" },
       { schematic := "coverage / witness completeness / semantic contract coverage",
         leanDeclarations :=
          ["AnalyticRepresentation.coverageAssumptions",
           "AnalyticRepresentation.witnessCompleteness",
           "AnalyticRepresentation.semanticContractCoverage",
           "AnalyticRepresentation.RecordsNonConclusions"],
         reading :=
          "explicit assumptions required before analytic zero or analytic obstruction facts are reflected back to structural facts",
         status := "defined only" }]
  | toolingReportMetadata =>
      [{ schematic :=
          "claim_level / claim_classification / measurement_boundary",
         leanDeclarations :=
          ["ClaimLevel",
           "ClaimClassification",
           "MeasurementBoundary",
           "ToolingTheoremPackageMetadata"],
         reading :=
          "report metadata separates formal theorem claims from tooling, empirical, hypothesis, measured, unmeasured, and out-of-scope evidence",
         status := "defined only" },
       { schematic := "MEASURED witness is not a PROVED claim",
         leanDeclarations :=
          ["ToolingTheoremPackageMetadata.IsMeasuredWitness",
           "ToolingTheoremPackageMetadata.IsFormalProvedClaim",
           "ToolingTheoremPackageMetadata.measuredWitness_not_formalProvedClaim",
           "ClaimClassification.measured_not_proved"],
         reading :=
          "tooling-side measured witnesses support obstruction reports but do not become formal proved claims without theorem-package discharge",
         status := "proved" },
       { schematic :=
          "required assumptions / missing preconditions / non-conclusions",
         leanDeclarations :=
          ["ToolingTheoremPackageMetadata.requiredAssumptions",
           "ToolingTheoremPackageMetadata.coverageAssumptions",
           "ToolingTheoremPackageMetadata.exactnessAssumptions",
           "ToolingTheoremPackageMetadata.missingPreconditions",
           "ToolingTheoremPackageMetadata.not_formalProvedClaim_of_missingPreconditions",
           "ToolingTheoremPackageMetadata.RecordsNonConclusions"],
         reading :=
          "the theorem precondition checker must expose required assumptions, missing premises, coverage, exactness, and non-conclusions before a formal claim is displayed",
         status := "defined only / proved" }]
  | architectureSignatureRepresentation =>
      [{ schematic :=
          "ArchitectureLawModel -> ArchitectureSignatureV1",
         leanDeclarations :=
          ["architectureSignatureAnalyticRepresentation",
           "ArchitectureSignature.ArchitectureLawModel.signatureOf"],
         reading :=
          "concrete representation map from a law model to the Signature v1 analytic domain",
         status := "defined only" },
       { schematic := "selected required axes zero",
         leanDeclarations :=
          ["ArchitectureSignature.RequiredSignatureAxesZero",
           "architectureSignatureAnalyticRepresentation_zeroPreserving",
           "architectureSignatureAnalyticRepresentation_zeroReflecting",
           "ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero"],
         reading :=
          "structural zero and analytic zero are connected through the existing selected required-axis theorem package",
         status := "proved" },
       { schematic := "selected required-law obstruction package",
         leanDeclarations :=
          ["ArchitectureSignatureAggregateWitness",
           "architectureSignatureAnalyticRepresentation_obstructionPreserving",
           "architectureSignatureAnalyticRepresentation_obstructionReflecting"],
         reading :=
          "aggregate failure of the selected required-law theorem package is preserved and reflected relative to the representation assumptions",
         status := "proved" },
       { schematic := "optional axis none is not analytic zero evidence",
         leanDeclarations :=
          ["ArchitectureSignatureAnalyticNonConclusions",
           "architectureSignatureAnalyticRepresentation_nonConclusions",
           "ArchitectureSignature.ArchitectureSignatureV1.not_axisAvailableAndZero_of_axisValue_none"],
         reading :=
          "`none` is an unavailable optional metric, not an available selected required-axis zero certificate",
         status := "proved" }]
  | obstructionValuation =>
      [{ schematic := "ObstructionValuation State Witness",
         leanDeclarations :=
          ["ObstructionValuation",
           "ObstructionValuation.NoSelectedObstruction",
           "ObstructionValuation.ZeroReflectingSum",
           "ObstructionValuation.no_obstruction_of_value_zero",
           "ObstructionValuation.noSelectedObstruction_of_zeroReflectingSum"],
         reading :=
          "selected witness valuation; zero values rule out selected witnesses, not global flatness",
         status := "defined only / proved" }]
  | analyticExtensionFormula =>
      [{ schematic := "AnalyticExtensionFormulaPackage",
         leanDeclarations :=
          ["AnalyticExtensionFormulaPackage",
           "AnalyticExtensionFormulaPackage.FormulaEquation",
           "AnalyticExtensionFormulaPackage.formula_holds"],
         reading :=
          "the Chapter 11 analytic formula is a package field relative to representation, before/after state, feature contribution, interaction, transfer, repair, and obstruction residual terms",
         status := "defined only / proved" },
       { schematic :=
          "representation / valuation / decomposition / coverage assumptions",
         leanDeclarations :=
          ["AnalyticExtensionFormulaPackage.RequiredAssumptions",
           "AnalyticExtensionFormulaPackage.requiredAssumptions_of_fields",
           "AnalyticExtensionFormulaPackage.RecordsNonConclusions",
           "ObstructionValuation",
           "BoundedComplexityTransferPackage.no_free_elimination_bounded"],
         reading :=
          "formula use is relative to explicit representation-map, valuation-structure, decomposition, coverage, and complexity-transfer boundary assumptions",
         status := "defined only / proved" }]
  | couponAnalyticSnapshot =>
      [{ schematic := "coupon canonical analytic snapshot",
         leanDeclarations :=
          ["CouponAnalyticSnapshot",
           "CouponAnalyticSnapshot.bad",
           "CouponAnalyticSnapshot.repaired",
           "CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature"],
         reading :=
          "report-facing static_hidden_interaction / runtime_exposure / semantic_curvature axes with explicit measurement boundaries",
         status := "defined only" },
       { schematic := "static_hidden_interaction = some 1",
         leanDeclarations :=
          ["CouponAnalyticSnapshot.bad_staticHiddenInteraction_bridge",
           "CouponStaticDependencyExample.hiddenDependencyWitnessExists",
           "CouponStaticDependencyExample.bad_not_selectedStaticSplitFeatureExtension"],
         reading :=
          "bad coupon extension has a selected static hidden dependency witness and a measured nonzero static axis",
         status := "proved" },
       { schematic := "repaired static_hidden_interaction = some 0",
         leanDeclarations :=
          ["CouponAnalyticSnapshot.repaired_staticHiddenInteraction_bridge",
           "CouponStaticDependencyExample.repaired_selectedStaticSplitFeatureExtension"],
         reading :=
          "repaired coupon extension has a measured-zero selected static axis and no selected static witness",
         status := "proved" },
       { schematic := "runtime_exposure = none / semantic_curvature = none or measured delta",
         leanDeclarations :=
          ["CouponAnalyticSnapshot.runtimeExposure_not_zeroReflectingClaim",
           "CouponAnalyticSnapshot.semanticCurvature_unmeasured_not_zeroReflectingClaim",
           "CouponAnalyticSnapshot.repairedWithMeasuredSemanticCurvature_roundingOrderValuation_positive"],
         reading :=
          "unmeasured runtime or semantic axes do not discharge zero-reflecting claims; the selected semantic residual can be recorded as measured nonzero",
         status := "proved" }]
  | couponHiddenInteractionLiftingBridge =>
      [{ schematic := "coupon hidden interaction as selected lifting failure",
         leanDeclarations :=
          ["CouponHiddenInteractionLiftingBridge.selectedFeatureStep_liftedEdge_is_hiddenDependency",
           "CouponHiddenInteractionLiftingBridge.selectedFeatureStep_not_declaredInterfaceFactor",
           "CouponHiddenInteractionLiftingBridge.not_compatibleWithInterface",
           "CouponHiddenInteractionLiftingBridge.liftingFailurePayload",
           "CouponHiddenInteractionLiftingBridge.liftingFailureWitness_classified",
           "CouponHiddenInteractionLiftingBridge.hiddenDependency_liftingFailure_bridge"],
         reading :=
          "the selected CouponService -> PaymentAdapter.internalCache interaction is the bad hidden edge and is also packaged as a local `.liftingFailure` obstruction witness",
         status := "defined only / proved" }]
  | couponStaticExample =>
      [{ schematic := "coupon static_hidden_interaction = some 1",
         leanDeclarations :=
          ["CouponStaticDependencyExample.hiddenDependencyWitness",
           "CouponStaticDependencyExample.hiddenDependencyWitnessExists",
           "CouponStaticDependencyExample.bad_not_selectedStaticSplitFeatureExtension"],
         reading :=
          "selected static hidden dependency witness for the bad coupon extension",
         status := "defined only / proved" },
       { schematic := "coupon repaired static split",
         leanDeclarations :=
          ["CouponStaticDependencyExample.repairedStaticSplitFeatureExtension",
           "CouponStaticDependencyExample.repaired_selectedStaticSplitFeatureExtension"],
         reading :=
          "positive selected static split package for the repaired coupon extension",
         status := "defined only / proved" }]
  | couponSemanticValuation =>
      [{ schematic := "coupon semantic_curvature = measured nonzero delta",
         leanDeclarations :=
          ["CouponDiscountExample.roundingOrderResidual",
           "CouponDiscountExample.roundingOrderValuation",
           "CouponDiscountExample.couponDiscount_roundingOrderResidual_positive",
           "CouponDiscountExample.roundingOrderValuation_positive"],
         reading :=
          "selected coupon / discount rounding-order residual is positive for the canonical diagram",
         status := "defined only / proved" },
       { schematic := "coupon semantic axis non-conclusions",
         leanDeclarations :=
          ["CouponDiscountExample.roundingOrderValuation_recordsNonConclusions"],
         reading :=
          "valuation is restricted to the selected rounding-order residual and does not close unmeasured semantic axes",
         status := "proved" }]
  | staticSemanticCounterexample =>
      [{ schematic := "static flatness does not imply semantic flatness",
         leanDeclarations :=
          ["StaticSemanticCounterexample.canonical_staticFlatWithin",
           "StaticSemanticCounterexample.canonical_not_semanticFlatWithin",
           "StaticSemanticCounterexample.canonical_not_architectureFlat",
           "StaticSemanticCounterexample.staticFlat_with_semanticObstruction",
           "StaticSemanticCounterexample.staticFlat_not_architectureFlat"],
         reading :=
          "repaired static skeleton can be selected-static-flat while the selected semantic coupon / discount diagram still obstructs architecture flatness",
         status := "proved" }]
  | measurementBoundary =>
      [{ schematic := "measuredZero / measuredNonzero / unmeasured / outOfScope",
         leanDeclarations :=
          ["MeasurementBoundary",
           "AnalyticAxisBoundary",
           "AnalyticAxisBoundary.boundaryOfOption",
           "MeasurementBoundary.unmeasured_not_measuredZero",
           "ArchitectureClaim.unmeasured_not_measuredZero"],
         reading :=
          "tooling report axis boundary distinguishes an unmeasured axis from measured zero evidence",
         status := "defined only / proved" },
       { schematic := "Option Nat axis: some 0 versus none",
         leanDeclarations :=
          ["AnalyticAxisBoundary.IsMeasuredZero",
           "AnalyticAxisBoundary.IsUnmeasured",
           "AnalyticAxisBoundary.some_zero_ne_unmeasured",
           "AnalyticAxisBoundary.unmeasured_not_availableAndZero",
           "AnalyticAxisBoundary.not_canDischargeZeroReflectingClaim_of_unmeasured"],
         reading :=
          "`some 0` is an available measured zero; `none` is unmeasured and cannot discharge zero-reflecting theorem preconditions",
         status := "defined only / proved" },
       { schematic := "measuredNonzero selected analytic obstruction support",
         leanDeclarations :=
          ["AnalyticAxisBoundary.IsMeasuredNonzero",
           "AnalyticAxisBoundary.SupportsSelectedAnalyticObstruction",
           "AnalyticAxisBoundary.supportsSelectedAnalyticObstruction_of_measuredNonzero"],
         reading :=
          "a measured nonzero axis is report evidence for a selected analytic obstruction support, not a global flatness theorem",
         status := "defined only / proved" },
       { schematic := "runtime_exposure = none",
         leanDeclarations :=
          ["AnalyticAxisBoundary.ofSignatureAxis",
           "AnalyticAxisBoundary.ofSignatureAxis_isUnmeasured_of_axisValue_none",
           "AnalyticAxisBoundary.signatureAxisMeasuredZero_of_unmeasured",
           "AnalyticAxisBoundary.not_signatureAxisAvailableAndZero_of_unmeasured",
           "ArchitectureSignature.v1Schema_unitNoEdge_unmeasured"],
         reading :=
          "absent v1 extension-axis values remain `none` rather than being encoded as zero",
         status := "proved" }]

/-- Boundary reminder for reading each candidate as a bounded Chapter 11 API. -/
def nonConclusionBoundary : Candidate -> String
  | analyticRepresentation =>
      "reflecting directions require coverage, witness completeness, and semantic contract coverage; analytic values alone do not prove flatness"
  | toolingReportMetadata =>
      "MEASURED tooling witnesses, missing preconditions, unmeasured axes, and out-of-scope evidence are not PROVED formal theorem claims"
  | architectureSignatureRepresentation =>
      "concrete bridge is restricted to selected required Signature axes; optional none values, runtime axes, empirical cost, and extractor completeness are not zero certificates"
  | obstructionValuation =>
      "valuation is selected-witness-relative; zero selected valuation does not imply global ArchitectureFlat"
  | analyticExtensionFormula =>
      "formulaHolds is a package field under explicit assumptions, not a global conservation law or empirical cost theorem"
  | couponAnalyticSnapshot =>
      "snapshot axes are report-facing and selected-example-relative; unmeasured runtime / semantic axes are not zero certificates"
  | couponHiddenInteractionLiftingBridge =>
      "bridge is local to one selected coupon interaction; no strict section equality, all-step lifting failure, runtime flatness, or semantic flatness is concluded"
  | couponStaticExample =>
      "selected static hidden dependency witness only; no runtime flatness, semantic flatness, or extractor completeness"
  | couponSemanticValuation =>
      "selected rounding-order semantic residual only; no unmeasured-axis zero claim or global semantic completeness"
  | staticSemanticCounterexample =>
      "counterexample is selected static / semantic scope only; no empirical frequency or extractor claim"
  | measurementBoundary =>
      "unmeasured and out-of-scope report axes are not measured-zero evidence and cannot discharge Lean theorem preconditions"

end Candidate

end Chapter11AnalyticRepresentation

end Formal.Arch
