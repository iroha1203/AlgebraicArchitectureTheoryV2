import Formal.Arch.Evolution.ArchitecturePath
import Formal.Arch.Evolution.DiagramFiller

/-!
Documentation-facing entrypoint for the mathematical design Chapter 8 homotopy
skeleton.

This module is intentionally thin. Importing it exposes the finite path
calculus, generated path homotopy, selected observation-invariance theorem, and
diagram-filler obstruction API used by Chapter 8 without adding global semantic
completeness, higher-category, or extractor-completeness claims.
-/

namespace Formal.Arch

namespace Chapter8HomotopySkeleton

/--
A stable documentation-facing mapping from schematic names in Chapter 8 to the
Lean declarations that currently carry the corresponding bounded API.
-/
structure SchematicCorrespondence where
  schematic : String
  leanDeclarations : List String
  reading : String
  status : String
  deriving Repr

/-- The main Chapter 8 API groups exposed through this entrypoint. -/
inductive Candidate where
  | architecturePaths
  | generatedPathHomotopy
  | selectedObservationInvariance
  | diagramFiller
  | obstructionAsNonFillability
  deriving DecidableEq, Repr

namespace Candidate

/-- Human-readable section number in `docs/aat_v2_mathematical_design.md`. -/
def designSection : Candidate -> String
  | architecturePaths => "8.1"
  | generatedPathHomotopy => "8.1"
  | selectedObservationInvariance => "8"
  | diagramFiller => "8"
  | obstructionAsNonFillability => "8"

/-- Stable schematic name used by documentation and theorem-index tables. -/
def schematicName : Candidate -> String
  | architecturePaths => "Architecture paths"
  | generatedPathHomotopy => "Generated path homotopy"
  | selectedObservationInvariance => "Selected observation invariance"
  | diagramFiller => "Diagram filler"
  | obstructionAsNonFillability => "Obstruction as non-fillability"

/-- Representative Lean declarations that serve as public entrypoints. -/
def representativeDeclarations : Candidate -> List String
  | architecturePaths =>
      ["ArchitecturePath",
       "ArchitecturePath.append",
       "ArchitecturePath.append_assoc",
       "ArchitecturePath.length_append",
       "ArchitecturePath.everyStepPreserves_append",
       "ArchitecturePath.pathPreservesInvariant"]
  | generatedPathHomotopy =>
      ["ArchitecturePath.PathHomotopy",
       "ArchitecturePath.PathHomotopy.cons_congr",
       "ArchitecturePath.PathHomotopy.append_left",
       "ArchitecturePath.PathHomotopy.append_right",
       "ArchitecturePath.HomotopyInvariant",
       "ArchitecturePath.architectureHomotopyInvariance"]
  | selectedObservationInvariance =>
      ["ArchitecturePath.PathHomotopy.observation_eq_append",
       "ArchitecturePath.PathHomotopy.observation_eq",
       "CouponDiscountExample.pathHomotopy_preserves_roundingTrace_append",
       "CouponDiscountExample.pathHomotopy_preserves_roundingTrace"]
  | diagramFiller =>
      ["ArchitectureDiagram",
       "DiagramFiller",
       "diagramFiller_observation_eq",
       "observationDifference_refutesDiagramFiller",
       "CouponDiscountExample.couponDiscountDiagram",
       "CouponDiscountExample.roundingOrder_refutes_selectedDiagramFiller"]
  | obstructionAsNonFillability =>
      ["NonFillabilityWitness",
       "NonFillabilityWitnessFor",
       "obstructionAsNonFillability_sound",
       "observationDifference_nonFillabilityWitnessFor",
       "WitnessUniverseComplete",
       "obstructionAsNonFillability_complete_bounded",
       "CouponDiscountExample.roundingOrder_nonFillabilityWitnessFor",
       "CouponDiscountExample.roundingOrderValuation_positive"]

/--
Schematic-name to Lean-API correspondences for Chapter 8.

These rows are metadata only. They stabilize how the design-note schematic names
are read against the existing bounded Lean API without adding new theorems or
global completeness claims.
-/
def schematicCorrespondences : Candidate -> List SchematicCorrespondence
  | architecturePaths =>
      [{ schematic := "ArchitecturePath Step X Y",
         leanDeclarations :=
          ["ArchitecturePath",
           "ArchitecturePath.append",
           "ArchitecturePath.length",
           "ArchitecturePath.length_append"],
         reading :=
          "finite endpoint-indexed path calculus over an explicit primitive step family",
         status := "defined only / proved" }]
  | generatedPathHomotopy =>
      [{ schematic := "PathHomotopy p q",
         leanDeclarations :=
          ["ArchitecturePath.PathHomotopy",
           "ArchitecturePath.PathHomotopy.cons_congr",
           "ArchitecturePath.PathHomotopy.append_left",
           "ArchitecturePath.PathHomotopy.append_right"],
         reading :=
          "generated relation closed under selected finite path contexts",
         status := "defined only / proved" }]
  | selectedObservationInvariance =>
      [{ schematic := "Obs p = Obs q for homotopic paths",
         leanDeclarations :=
          ["ArchitecturePath.PathHomotopy.observation_eq_append",
           "ArchitecturePath.PathHomotopy.observation_eq"],
         reading :=
          "selected observation preservation under explicit generator-preservation and context-congruence assumptions",
         status := "proved" },
       { schematic := "coupon / discount selected observation preservation",
         leanDeclarations :=
          ["CouponDiscountExample.pathHomotopy_preserves_roundingTrace_append",
           "CouponDiscountExample.pathHomotopy_preserves_roundingTrace"],
         reading :=
          "coupon / discount specialization of the general selected observation theorem",
         status := "proved" }]
  | diagramFiller =>
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
          "selected observation difference refutes fillability when the supplied filler generators preserve that observation",
         status := "proved" }]
  | obstructionAsNonFillability =>
      [{ schematic := "NonFillabilityWitness D w",
         leanDeclarations :=
          ["NonFillabilityWitness",
           "NonFillabilityWitnessFor",
           "obstructionAsNonFillability_sound",
           "observationDifference_nonFillabilityWitnessFor"],
         reading :=
          "sound non-fillability witness for one selected diagram and witness value",
         status := "defined only / proved" },
       { schematic := "bounded completeness for non-fillability witnesses",
         leanDeclarations :=
          ["WitnessUniverseComplete",
           "obstructionAsNonFillability_complete_bounded"],
         reading :=
          "converse direction only under an explicit finite witness-universe completeness premise",
         status := "defined only / proved" }]

/-- Boundary reminder for reading each candidate as a bounded Chapter 8 API. -/
def nonConclusionBoundary : Candidate -> String
  | architecturePaths =>
      "finite endpoint-indexed paths only; no path-count or walk-length metric semantics beyond the listed API"
  | generatedPathHomotopy =>
      "generated relation over supplied contracts only; no HoTT or higher-category completeness claim"
  | selectedObservationInvariance =>
      "selected observations only under explicit generator assumptions; no all-observation preservation"
  | diagramFiller =>
      "diagram fillability in the finite path calculus only; no global semantic completeness"
  | obstructionAsNonFillability =>
      "soundness plus bounded completeness under WitnessUniverseComplete only; no extractor completeness or full witness coverage"

end Candidate

end Chapter8HomotopySkeleton

end Formal.Arch
