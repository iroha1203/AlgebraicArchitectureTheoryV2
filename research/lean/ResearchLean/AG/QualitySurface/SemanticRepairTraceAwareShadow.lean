import ResearchLean.AG.QualitySurface.SemanticRepairFiniteShadowSeparation

/-!
Cycle 14 evidence for `G-aat-quality-surface-04`.

This file adds a one-coordinate trace-aware enrichment of the current
four-bit `FiniteTowerLayerShadow`.  It is a support node responding to the
Cycle 13 trace-loss blocker: the selected source-trace observation factors
through the enriched shadow, and the Cycle 13 pair that the four-bit shadow
identifies is separated by the trace-aware shadow.

The enrichment is deliberately local.  It does not replace the four-bit
shadow, assert full representation adequacy, prove arbitrary semantic
observation factorization, or claim ArchSig / ArchMap extraction correctness.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairTraceAwareShadow

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairFiniteShadowSeparation

universe u v w x y

/-! ## One-coordinate trace-aware shadow -/

/--
A trace-aware enrichment of the current four-bit finite shadow.

The `sourceTrace` field is one supplied Boolean coordinate of the tower's
`sourceTraceToken`.  It is input geometry, not a correctness theorem about any
runtime extractor.
-/
structure TraceAwareFiniteTowerLayerShadow where
  layer : FiniteTowerLayerShadow
  sourceTrace : Bool

/-- Read the trace coordinate from a trace-aware shadow. -/
def traceAwareSourceTraceFactor
    (shadow : TraceAwareFiniteTowerLayerShadow) : Bool :=
  shadow.sourceTrace

/--
The canonical trace-aware shadow for a chosen Boolean source-trace coordinate.
-/
def canonicalTraceAwareTowerLayerShadow
    {Atom : Type u}
    (traceCoordinate : (Atom -> Bool) -> Bool)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    TraceAwareFiniteTowerLayerShadow where
  layer := canonicalTowerLayerShadow T
  sourceTrace := traceCoordinate T.sourceTraceToken

/-- The trace-aware shadow projects back to the current four-bit shadow. -/
theorem traceAwareShadow_projects_to_currentShadow
    {Atom : Type u}
    (traceCoordinate : (Atom -> Bool) -> Bool)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (canonicalTraceAwareTowerLayerShadow traceCoordinate T).layer =
      canonicalTowerLayerShadow T := by
  rfl

/--
The chosen source-trace coordinate factors through the trace-aware shadow.
-/
theorem traceCoordinateObservation_factors_through_traceAwareShadow
    {Atom : Type u}
    (traceCoordinate : (Atom -> Bool) -> Bool) :
    ∃ factor : TraceAwareFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        traceCoordinate T.sourceTraceToken =
          factor (canonicalTraceAwareTowerLayerShadow traceCoordinate T) := by
  exact ⟨traceAwareSourceTraceFactor, by intro T; rfl⟩

/-! ## Cycle 13 source-trace witness revisited -/

/-- The concrete `PUnit` source-trace coordinate used by Cycle 13. -/
def punitSourceTraceCoordinate
    (traceToken : PUnit.{u + 1} -> Bool) : Bool :=
  traceToken PUnit.unit

/--
The Cycle 13 source-trace observation factors through the trace-aware shadow.
-/
theorem sourceTraceObservation_factors_through_traceAwareShadow :
    ∃ factor : TraceAwareFiniteTowerLayerShadow -> Bool,
      ∀ T :
        FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0} PUnit.{u + 1},
        sourceTraceObservation T =
          factor
            (canonicalTraceAwareTowerLayerShadow
              punitSourceTraceCoordinate T) := by
  exact
    traceCoordinateObservation_factors_through_traceAwareShadow
      punitSourceTraceCoordinate

/--
The Cycle 13 pair that the current four-bit shadow identifies is separated by
the trace-aware shadow's source-trace coordinate.
-/
theorem selected_traceTrue_traceAwareShadow_sourceTrace_ne :
    (canonicalTraceAwareTowerLayerShadow punitSourceTraceCoordinate
        (selectedFiniteSemanticRepairObstructionTower :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1})).sourceTrace ≠
      (canonicalTraceAwareTowerLayerShadow punitSourceTraceCoordinate
        selectedFiniteSemanticRepairObstructionTower_traceTrue).sourceTrace := by
  decide

/--
The enriched shadow still remembers the current four-bit shadow agreement from
Cycle 13, while adding the separating trace coordinate.
-/
theorem selected_traceTrue_traceAwareShadow_layer_agrees :
    (canonicalTraceAwareTowerLayerShadow punitSourceTraceCoordinate
        (selectedFiniteSemanticRepairObstructionTower :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1})).layer =
      (canonicalTraceAwareTowerLayerShadow punitSourceTraceCoordinate
        selectedFiniteSemanticRepairObstructionTower_traceTrue).layer := by
  exact selected_traceTrue_same_canonicalShadow.{u}

end SemanticRepairTraceAwareShadow
end QualitySurface
end ResearchLean.AG
