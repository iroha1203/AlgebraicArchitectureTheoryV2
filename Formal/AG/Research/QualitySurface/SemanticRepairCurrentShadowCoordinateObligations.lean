import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryCanonicalBridge

/-!
Cycle 25 evidence for `G-aat-quality-surface-04`.

This file decomposes the Cycle 24 current-shadow determinacy premise into
pointwise coordinate obligations.  A finite support trace shadow is determined
by the current canonical shadow exactly when every listed source-trace
coordinate is itself current-shadow extensional.

The file also records that the Bool `true` source-trace coordinate is not
current-shadow extensional for the existing missed-coordinate pair.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairCurrentShadowCoordinateObligations

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportSeparation
open SemanticRepairFiniteSupportMembership
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryCanonicalBridge

universe u v w x y

/-! ## Coordinate obligations for current-shadow determinacy -/

/--
A source-trace coordinate is extensional for the current canonical all-layer
shadow.

This is a pointwise obligation.  It is not automatic for trace-sensitive
coordinates.
-/
def SourceTraceCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (atom : Atom) : Prop :=
  ShadowExtensionalTowerObservation
    (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
      sourceTraceCoordinateObservation atom T)

/--
Every listed coordinate in a finite support is current-shadow extensional.
-/
def SupportTraceCoordinatesCurrentShadowExtensional
    {Atom : Type u}
    (support : List Atom) : Prop :=
  ∀ atom : Atom,
    atom ∈ support ->
      SourceTraceCoordinateCurrentShadowExtensional.{u, v, w, x, y} atom

/--
Pointwise coordinate extensionality makes the finite support trace vector
current-shadow determined.
-/
theorem supportTraceVector_eq_of_coordinateCurrentShadowExtensional
    {Atom : Type u} :
    (support : List Atom) ->
    SupportTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y} support ->
    ∀ left right : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      canonicalTowerLayerShadow left = canonicalTowerLayerShadow right ->
        supportTraceVector support left.sourceTraceToken =
          supportTraceVector support right.sourceTraceToken
  | [], _, _, _, _ => rfl
  | head :: rest, hcoords, left, right, hshadow => by
      have hhead :
          left.sourceTraceToken head = right.sourceTraceToken head :=
        hcoords head (List.Mem.head _) left right hshadow
      have htail :
          supportTraceVector rest left.sourceTraceToken =
            supportTraceVector rest right.sourceTraceToken :=
        supportTraceVector_eq_of_coordinateCurrentShadowExtensional
          rest
          (by
            intro atom hmem
            exact hcoords atom (List.Mem.tail _ hmem))
          left right hshadow
      change
        left.sourceTraceToken head ::
            supportTraceVector rest left.sourceTraceToken =
          right.sourceTraceToken head ::
            supportTraceVector rest right.sourceTraceToken
      rw [hhead, htail]

/--
Coordinate extensionality for every listed support atom implies that the
support trace shadow is determined by the current canonical shadow.
-/
theorem currentShadowDeterminesSupportTraceShadow_of_coordinateCurrentShadowExtensional
    {Atom : Type u}
    {support : List Atom}
    (hcoords :
      SupportTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        support) :
    CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support := by
  intro left right hshadow
  exact
    (supportTraceShadow_eq_iff_currentShadow_eq_and_sourceTraceReadings_eq).2
      ⟨hshadow,
        supportTraceVector_eq_of_coordinateCurrentShadowExtensional
          support hcoords left right hshadow⟩

/--
If the whole support trace shadow is current-shadow determined, then every
listed source-trace coordinate is current-shadow extensional.
-/
theorem coordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support) :
    SupportTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      support := by
  intro atom hmem left right hshadow
  exact
    sourceTraceCoordinate_same_of_same_supportTraceProbeShadow
      hmem (hcurrent left right hshadow)

/--
The Cycle 24 support-determinacy premise is equivalent to the pointwise
coordinate-obligation family.
-/
theorem currentShadowDeterminesSupportTraceShadow_iff_coordinateCurrentShadowExtensional
    {Atom : Type u}
    (support : List Atom) :
    CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support ↔
      SupportTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        support := by
  exact
    ⟨coordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow,
      currentShadowDeterminesSupportTraceShadow_of_coordinateCurrentShadowExtensional⟩

/-! ## Concrete obstruction -/

/--
The Bool `true` source-trace coordinate is not current-shadow extensional.

The existing missed-coordinate pair has the same current four-bit shadow but
different `true` source-trace readings.
-/
theorem not_boolTrueSourceTraceCoordinateCurrentShadowExtensional :
    ¬ SourceTraceCoordinateCurrentShadowExtensional.{0, 0, 0, 0, 0}
      true := by
  intro hcoordinate
  have hsame :=
    hcoordinate
      boolTraceBaseTower
      boolTraceMissedTrueTower
      bool_missedTrue_same_currentShadow
  exact
    boolMissedTraceObservation_separates_pair
      (by
        simpa [sourceTraceCoordinateObservation, boolMissedTraceObservation]
          using hsame)

/--
The complete Bool support cannot satisfy the pointwise current-shadow
coordinate obligations.
-/
theorem not_boolCompleteSupportCoordinatesCurrentShadowExtensional :
    ¬ SupportTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
      SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport := by
  intro hcoords
  exact
    not_boolTrueSourceTraceCoordinateCurrentShadowExtensional
      (hcoords true
        (SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport_complete
          true))

end SemanticRepairCurrentShadowCoordinateObligations
end QualitySurface
end Formal.AG.Research
