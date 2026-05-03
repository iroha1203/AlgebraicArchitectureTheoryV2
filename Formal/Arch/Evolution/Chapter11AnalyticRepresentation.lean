import Formal.Arch.Signature.AnalyticRepresentation
import Formal.Arch.Extension.FeatureExtensionExamples
import Formal.Arch.Evolution.DiagramFiller
import Formal.Arch.Extension.CertifiedArchitecture
import Formal.Arch.Signature.Signature
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

/-- The main Chapter 11 API groups exposed through this entrypoint. -/
inductive Candidate where
  | analyticRepresentation
  | obstructionValuation
  | couponStaticExample
  | couponSemanticValuation
  | staticSemanticCounterexample
  | measurementBoundary
  deriving DecidableEq, Repr

namespace Candidate

/-- Human-readable section number in `docs/aat_v2_mathematical_design.md`. -/
def designSection : Candidate -> String
  | analyticRepresentation => "11"
  | obstructionValuation => "11"
  | couponStaticExample => "11 / coupon static axis"
  | couponSemanticValuation => "11 / coupon semantic axis"
  | staticSemanticCounterexample => "11 / canonical counterexample"
  | measurementBoundary => "11 / tooling boundary"

/-- Stable schematic name used by documentation and theorem-index tables. -/
def schematicName : Candidate -> String
  | analyticRepresentation => "Analytic Representation"
  | obstructionValuation => "Obstruction Valuation"
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
  | obstructionValuation =>
      ["ObstructionValuation",
       "ObstructionValuation.NoSelectedObstruction",
       "ObstructionValuation.ZeroReflectingSum",
       "ObstructionValuation.no_obstruction_of_value_zero",
       "ObstructionValuation.noSelectedObstruction_of_zeroReflectingSum",
       "ObstructionValuation.RecordsNonConclusions"]
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
           "MeasurementBoundary.unmeasured_not_measuredZero",
           "ArchitectureClaim.unmeasured_not_measuredZero"],
         reading :=
          "tooling report axis boundary distinguishes an unmeasured axis from measured zero evidence",
         status := "defined only / proved" },
       { schematic := "runtime_exposure = none",
         leanDeclarations :=
          ["ArchitectureSignature.v1Schema_unitNoEdge_unmeasured"],
         reading :=
          "absent v1 extension-axis values remain `none` rather than being encoded as zero",
         status := "proved" }]

/-- Boundary reminder for reading each candidate as a bounded Chapter 11 API. -/
def nonConclusionBoundary : Candidate -> String
  | analyticRepresentation =>
      "reflecting directions require coverage, witness completeness, and semantic contract coverage; analytic values alone do not prove flatness"
  | obstructionValuation =>
      "valuation is selected-witness-relative; zero selected valuation does not imply global ArchitectureFlat"
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
