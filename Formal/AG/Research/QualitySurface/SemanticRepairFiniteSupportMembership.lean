import Formal.AG.Research.QualitySurface.SemanticRepairFiniteSupportSeparation

/-!
Cycle 18 evidence for `G-aat-quality-surface-04`.

This file records the positive side of the finite-support boundary: a source
trace coordinate that is explicitly listed in the finite support factors
through the finite-support trace shadow.  It is a membership-local theorem, not
a completeness theorem for unlisted coordinates or arbitrary observations.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteSupportMembership

open SemanticRepairObstructionTower
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport

universe u v w x y

/-! ## Membership-local coordinate factorization -/

/-- A source-trace coordinate observation. -/
def sourceTraceCoordinateObservation
    {Atom : Type u}
    (atom : Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    Bool :=
  T.sourceTraceToken atom

/--
Forget the head finite-support reading while preserving the four-bit layer.
This is the shadow-level map used to recurse through a support list.
-/
def supportTraceShadowTail
    (shadow : TraceProbeFiniteTowerLayerShadow) :
    TraceProbeFiniteTowerLayerShadow where
  layer := shadow.layer
  sourceTraceReadings := shadow.sourceTraceReadings.tail

/--
The tail of a cons support shadow is the shadow for the tail support.
-/
theorem supportTraceShadowTail_cons
    {Atom : Type u}
    (head : Atom)
    (rest : List Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    supportTraceShadowTail
        (canonicalSupportTraceProbeTowerLayerShadow (head :: rest) T) =
      canonicalSupportTraceProbeTowerLayerShadow rest T := by
  rfl

/--
If a coordinate is explicitly listed in the finite support, then that coordinate
observation factors through the finite-support trace shadow.

This theorem is intentionally local to a membership proof.  It does not say
that the support is complete, minimal, duplicate-free, permutation-invariant, or
runtime-extracted.
-/
theorem sourceTraceCoordinate_factors_through_supportTraceProbeShadow
    {Atom : Type u} :
    (support : List Atom) ->
    {atom : Atom} ->
    atom ∈ support ->
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        T.sourceTraceToken atom =
          factor (canonicalSupportTraceProbeTowerLayerShadow support T)
  | [], _, hmem => by
      cases hmem
  | head :: rest, atom, hmem => by
      cases hmem with
      | head =>
        exact
          ⟨fun shadow => shadow.sourceTraceReadings.headD false,
            by
              intro T
              rfl⟩
      | tail _ htail =>
        rcases
          sourceTraceCoordinate_factors_through_supportTraceProbeShadow
            rest htail with
          ⟨factorRest, hfactorRest⟩
        exact
          ⟨fun shadow => factorRest (supportTraceShadowTail shadow),
            by
              intro T
              simpa [supportTraceShadowTail_cons] using hfactorRest T⟩

/--
Observation-wrapper version of the membership-local coordinate factorization.
-/
theorem sourceTraceCoordinateObservation_factors_through_supportTraceShadow_of_mem
    {Atom : Type u}
    (support : List Atom)
    {atom : Atom}
    (hmem : atom ∈ support) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        sourceTraceCoordinateObservation atom T =
          factor (canonicalSupportTraceProbeTowerLayerShadow support T) := by
  exact sourceTraceCoordinate_factors_through_supportTraceProbeShadow support hmem

/--
If a listed coordinate has the same finite-support trace shadow on two towers,
then its source-trace value is the same on those towers.
-/
theorem sourceTraceCoordinate_same_of_same_supportTraceProbeShadow
    {Atom : Type u}
    {support : List Atom}
    {atom : Atom}
    (hmem : atom ∈ support)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalSupportTraceProbeTowerLayerShadow support left =
        canonicalSupportTraceProbeTowerLayerShadow support right) :
    left.sourceTraceToken atom = right.sourceTraceToken atom := by
  rcases
    (sourceTraceCoordinate_factors_through_supportTraceProbeShadow
      (Atom := Atom) support hmem :
      ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          T.sourceTraceToken atom =
            factor (canonicalSupportTraceProbeTowerLayerShadow support T)) with
    ⟨factor, hfactor⟩
  calc
    left.sourceTraceToken atom =
        factor (canonicalSupportTraceProbeTowerLayerShadow support left) :=
      hfactor left
    _ = factor (canonicalSupportTraceProbeTowerLayerShadow support right) := by
      rw [hshadow]
    _ = right.sourceTraceToken atom := (hfactor right).symm

/-! ## Concrete support membership witnesses -/

/-- The `false` coordinate is explicitly present in the Cycle 17 support. -/
theorem false_mem_boolFalseOnlyTraceSupport :
    false ∈ SemanticRepairFiniteSupportSeparation.boolFalseOnlyTraceSupport := by
  exact List.Mem.head _

/--
The `false` coordinate observation factors through the Cycle 17 finite support
shadow.
-/
theorem boolFalseTraceObservation_factors_through_boolFalseOnlySupport :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        sourceTraceCoordinateObservation false T =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              SemanticRepairFiniteSupportSeparation.boolFalseOnlyTraceSupport T) := by
  exact
    sourceTraceCoordinateObservation_factors_through_supportTraceShadow_of_mem
      SemanticRepairFiniteSupportSeparation.boolFalseOnlyTraceSupport
      false_mem_boolFalseOnlyTraceSupport

/--
For the Cycle 17 missed-coordinate pair, the listed `false` coordinate agrees
through the finite support shadow even while the omitted `true` coordinate
separates the pair.
-/
theorem boolFalseTraceObservation_same_on_missedTrue_pair :
    sourceTraceCoordinateObservation false
        SemanticRepairFiniteSupportSeparation.boolTraceBaseTower =
      sourceTraceCoordinateObservation false
        SemanticRepairFiniteSupportSeparation.boolTraceMissedTrueTower := by
  rfl

end SemanticRepairFiniteSupportMembership
end QualitySurface
end Formal.AG.Research
