import Formal.AG.Research.QualitySurface.SemanticRepairFiniteSupportMembership

/-!
Cycle 19 evidence for `G-aat-quality-surface-04`.

This file makes the support-completeness certificate explicit.  A complete
finite support, in the narrow sense that every atom is listed in the support,
gives pointwise source-trace coordinate factorization through the finite-support
trace shadow.  This is not an arbitrary-observation or runtime-extraction
completeness theorem.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteSupportCompleteness

open SemanticRepairObstructionTower
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportMembership

universe u v w x y

/-! ## Explicit support-completeness certificate -/

/--
A finite support is complete for this local theorem when every atom is explicitly
listed in the support.  This is a visible premise, not a field hidden inside the
shadow.
-/
def FiniteSupportComplete
    {Atom : Type u}
    (support : List Atom) : Prop :=
  ∀ atom : Atom, atom ∈ support

/--
Under an explicit finite-support completeness certificate, every source-trace
coordinate factors through the finite-support trace shadow.
-/
theorem sourceTraceCoordinate_factors_through_completeSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    (hcomplete : FiniteSupportComplete support)
    (atom : Atom) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        T.sourceTraceToken atom =
          factor (canonicalSupportTraceProbeTowerLayerShadow support T) := by
  exact
    sourceTraceCoordinate_factors_through_supportTraceProbeShadow
      support (hcomplete atom)

/--
The complete support shadow is pointwise extensional for source-trace tokens.
The conclusion is pointwise rather than function equality, so the theorem does
not require a hidden `funext` step.
-/
theorem sourceTraceCoordinates_same_of_same_completeSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    (hcomplete : FiniteSupportComplete support)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalSupportTraceProbeTowerLayerShadow support left =
        canonicalSupportTraceProbeTowerLayerShadow support right)
    (atom : Atom) :
    left.sourceTraceToken atom = right.sourceTraceToken atom := by
  exact
    sourceTraceCoordinate_same_of_same_supportTraceProbeShadow
      (hcomplete atom) hshadow

/-! ## Concrete Bool support witness -/

/-- A complete finite support for the two-atom `Bool` type. -/
def boolCompleteTraceSupport : List Bool :=
  [false, true]

/-- The support `[false, true]` contains every `Bool` atom. -/
theorem boolCompleteTraceSupport_complete :
    FiniteSupportComplete boolCompleteTraceSupport := by
  intro atom
  cases atom
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

/-- The `true` coordinate factors through the complete Bool support shadow. -/
theorem boolTrueTraceObservation_factors_through_completeBoolSupport :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        sourceTraceCoordinateObservation true T =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              boolCompleteTraceSupport T) := by
  exact
    sourceTraceCoordinateObservation_factors_through_supportTraceShadow_of_mem
      boolCompleteTraceSupport (boolCompleteTraceSupport_complete true)

/--
The Cycle 17 missed-coordinate pair is separated by the complete Bool support
shadow readings.  This shows the explicit complete support fixes that concrete
omitted-coordinate failure; it does not prove arbitrary observation adequacy.
-/
theorem bool_missedTrue_completeSupportShadow_readings_ne :
    (canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport
        SemanticRepairFiniteSupportSeparation.boolTraceBaseTower).sourceTraceReadings ≠
      (canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport
        SemanticRepairFiniteSupportSeparation.boolTraceMissedTrueTower).sourceTraceReadings := by
  decide

/--
For any two Bool towers with the same complete Bool support shadow, the `true`
source-trace coordinate agrees.
-/
theorem boolTrueTrace_same_of_same_completeBoolSupportShadow
    {left right :
      FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool}
    (hshadow :
      canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport left =
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport right) :
    left.sourceTraceToken true = right.sourceTraceToken true := by
  exact
    sourceTraceCoordinates_same_of_same_completeSupportTraceShadow
      boolCompleteTraceSupport_complete hshadow true

end SemanticRepairFiniteSupportCompleteness
end QualitySurface
end Formal.AG.Research
