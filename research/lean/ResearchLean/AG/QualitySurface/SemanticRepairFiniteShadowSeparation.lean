import ResearchLean.AG.QualitySurface.SemanticRepairTargetFactorization

/-!
Cycle 13 evidence for `G-aat-quality-surface-04`.

This file records a finite separation for the current four-bit
`FiniteTowerLayerShadow`.  The shadow reads only the selected `H1`, torsor,
higher, and stack tokens.  It does not read the supplied `sourceTraceToken`.

The result is a target obstruction, not a completion theorem: a
source-trace-sensitive observation cannot factor through the current four-bit
shadow unless the shadow is enriched or the admissible observation class is
restricted to shadow-extensional observations.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteShadowSeparation

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTargetFactorization

universe u v w x y z

/-! ## Generic finite-shadow separation -/

/--
If an observation separates two towers with the same canonical finite shadow,
then it cannot factor through the current `FiniteTowerLayerShadow`.

This is a purely formal obstruction to unrestricted shadow factorization.  It
does not assume or imply global coherence, tower vanishing, effective descent,
ArchMap correctness, or extraction completeness.
-/
theorem no_finiteShadowFactor_of_sameShadow_observation_ne
    {Atom : Type u}
    {Obs : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs}
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalTowerLayerShadow left = canonicalTowerLayerShadow right)
    (hobs : observe left ≠ observe right) :
    ¬ ∃ factor : FiniteTowerLayerShadow -> Obs,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T) := by
  intro hfactor
  rcases hfactor with ⟨factor, hfactor⟩
  have hextensional :
      ShadowExtensionalTowerObservation observe :=
    shadowExtensional_of_factorization factor hfactor
  exact hobs (hextensional left right hshadow)

/-! ## Source-trace-sensitive witness -/

/--
The selected calibration tower with only the supplied source trace changed.
The four obstruction-layer tokens are unchanged.
-/
def selectedFiniteSemanticRepairObstructionTower_traceTrue :
    FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0} PUnit.{u + 1} :=
  { (selectedFiniteSemanticRepairObstructionTower :
      FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0} PUnit.{u + 1}) with
    sourceTraceToken := fun _ => true }

/-- Read the supplied source trace at the concrete `PUnit` atom. -/
def sourceTraceObservation
    (T :
      FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0} PUnit.{u + 1}) :
    Bool :=
  T.sourceTraceToken PUnit.unit

/--
Changing only `sourceTraceToken` leaves the current four-bit canonical shadow
unchanged.
-/
theorem selected_traceTrue_same_canonicalShadow :
    canonicalTowerLayerShadow
        (selectedFiniteSemanticRepairObstructionTower :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1}) =
      canonicalTowerLayerShadow
        selectedFiniteSemanticRepairObstructionTower_traceTrue := by
  rfl

/-- The concrete source-trace observation separates the two towers. -/
theorem sourceTraceObservation_separates_selected_trace_pair :
    sourceTraceObservation
        (selectedFiniteSemanticRepairObstructionTower :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1}) ≠
      sourceTraceObservation
        selectedFiniteSemanticRepairObstructionTower_traceTrue := by
  decide

/--
The source-trace observation is not extensional for the current four-bit
finite shadow.
-/
theorem sourceTraceObservation_not_shadowExtensional :
    ¬ ShadowExtensionalTowerObservation
        (sourceTraceObservation :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1} -> Bool) := by
  intro hextensional
  exact sourceTraceObservation_separates_selected_trace_pair
    (hextensional
      (selectedFiniteSemanticRepairObstructionTower :
        FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
          PUnit.{u + 1})
      selectedFiniteSemanticRepairObstructionTower_traceTrue
      selected_traceTrue_same_canonicalShadow)

/--
The source-trace observation cannot factor through the current four-bit
finite shadow.
-/
theorem sourceTraceObservation_no_finiteShadowFactor :
    ¬ ∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T :
        FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0} PUnit.{u + 1},
        sourceTraceObservation T =
          factor (canonicalTowerLayerShadow T) := by
  exact
    no_finiteShadowFactor_of_sameShadow_observation_ne
      selected_traceTrue_same_canonicalShadow
      sourceTraceObservation_separates_selected_trace_pair

end SemanticRepairFiniteShadowSeparation
end QualitySurface
end ResearchLean.AG
