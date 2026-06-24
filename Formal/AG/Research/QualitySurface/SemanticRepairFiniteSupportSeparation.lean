import Formal.AG.Research.QualitySurface.SemanticRepairFiniteTraceSupport

/-!
Cycle 17 evidence for `G-aat-quality-surface-04`.

This file records a finite boundary for the Cycle 16 support-trace shadow:
reading a finite support list does not make the shadow complete for trace
coordinates outside that support.  The result is an obstruction/refinement,
not a full trace incompleteness theorem.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteSupportSeparation

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport

universe u v w x y z

/-! ## Generic support-shadow separation -/

/--
If an observation separates two towers with the same finite-support trace
shadow, then it cannot factor through that support shadow.

This is a formal obstruction to over-reading a finite support as a complete
source trace.  It does not assert that every omitted coordinate is semantically
relevant.
-/
theorem no_supportTraceShadowFactor_of_sameShadow_observation_ne
    {Atom : Type u}
    {Obs : Type z}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs}
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalSupportTraceProbeTowerLayerShadow support left =
        canonicalSupportTraceProbeTowerLayerShadow support right)
    (hobs : observe left ≠ observe right) :
    ¬ ∃ factor : TraceProbeFiniteTowerLayerShadow -> Obs,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T =
          factor (canonicalSupportTraceProbeTowerLayerShadow support T) := by
  intro hfactor
  rcases hfactor with ⟨factor, hfactor⟩
  exact hobs <|
    calc
      observe left =
          factor (canonicalSupportTraceProbeTowerLayerShadow support left) :=
        hfactor left
      _ = factor (canonicalSupportTraceProbeTowerLayerShadow support right) := by
        rw [hshadow]
      _ = observe right := (hfactor right).symm

/-! ## A missed support coordinate witness -/

/-- The finite support that reads only the `false` atom of `Bool`. -/
def boolFalseOnlyTraceSupport : List Bool :=
  [false]

/-- A two-atom calibration tower with all obstruction-layer tokens zero. -/
def boolTraceBaseTower :
    FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool :=
  representativeTowerOfShadow zeroFiniteTowerLayerShadow

/--
The same calibration tower with only the missed `true` trace coordinate set.
The support `[false]` still reads the same trace vector.
-/
def boolTraceMissedTrueTower :
    FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool :=
  { boolTraceBaseTower with
    sourceTraceToken := fun atom => atom }

/-- Observe the trace coordinate omitted by `boolFalseOnlyTraceSupport`. -/
def boolMissedTraceObservation
    (T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool) :
    Bool :=
  T.sourceTraceToken true

/--
Changing only the omitted `true` coordinate leaves the finite-support trace
shadow for `[false]` unchanged.
-/
theorem bool_missedTrue_same_supportTraceShadow :
    canonicalSupportTraceProbeTowerLayerShadow
        boolFalseOnlyTraceSupport boolTraceBaseTower =
      canonicalSupportTraceProbeTowerLayerShadow
        boolFalseOnlyTraceSupport boolTraceMissedTrueTower := by
  rfl

/-- The omitted `true` trace coordinate separates the two towers. -/
theorem boolMissedTraceObservation_separates_pair :
    boolMissedTraceObservation boolTraceBaseTower ≠
      boolMissedTraceObservation boolTraceMissedTrueTower := by
  decide

/--
The omitted-coordinate observation cannot factor through the `[false]`
finite-support trace shadow.
-/
theorem boolMissedTraceObservation_no_supportTraceShadowFactor :
    ¬ ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        boolMissedTraceObservation T =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              boolFalseOnlyTraceSupport T) := by
  exact
    no_supportTraceShadowFactor_of_sameShadow_observation_ne
      bool_missedTrue_same_supportTraceShadow
      boolMissedTraceObservation_separates_pair

/--
The pair still agrees after forgetting the finite-support trace readings back
to the current four-bit shadow.
-/
theorem bool_missedTrue_same_currentShadow :
    canonicalTowerLayerShadow boolTraceBaseTower =
      canonicalTowerLayerShadow boolTraceMissedTrueTower := by
  rfl

end SemanticRepairFiniteSupportSeparation
end QualitySurface
end Formal.AG.Research
