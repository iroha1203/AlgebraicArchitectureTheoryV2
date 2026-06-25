import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationSupportRecovery

/-!
Cycle 42 evidence for `G-aat-quality-surface-04`.

Cycle 41 discharged realized query-reading recovery for canonical support-shadow
observations.  This file keeps the anti-weakening boundary explicit: visible
recovery does not itself give current-shadow adequacy.  Under visible recovery,
raw current-shadow factorization and canonical current-shadow reading
faithfulness are exactly the query-coordinate current-shadow criterion.

This is a support node, not target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationRecoveredFactorization

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationPostInvariant
open SemanticRepairFiniteQueryRepresentationCurrentShadowReading
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationCoordinateExtraction
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryRepresentationSupportRecovery

universe u v w x y z

/-! ## Visible recovery makes current-shadow factorization an exact criterion -/

/--
For a visibly represented finite-query observation that recovers its query
readings, raw current-shadow factorization is exactly the query-coordinate
current-shadow criterion.

The recovery premise is visible theorem data.  The coordinate criterion remains
the current-shadow adequacy boundary.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, z}
        repr.package.query observe) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        repr.package.query := by
  constructor
  · intro hfactor
    exact
      representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowFactor_of_observationRecoversQueryReadings
        (Atom := Atom) repr hfactor hrecover
  · intro hcoords
    exact
      representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) repr hcoords

/--
For a visibly represented finite-query observation that recovers its query
readings, canonical current-shadow reading faithfulness is exactly the
query-coordinate current-shadow criterion.
-/
theorem representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, z}
        repr.package.query observe) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        repr.package.query := by
  constructor
  · intro hfaithful
    exact
      representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_observationRecoversQueryReadings
        (Atom := Atom) repr hfaithful hrecover
  · intro hcoords
    exact
      representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) repr hcoords

/--
For a visibly represented finite-query observation that recovers its query
readings, semantic-reading adequacy existence is exactly the query-coordinate
current-shadow criterion.
-/
theorem representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, z}
        repr.package.query observe) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading repr.package.query repr.package.post) ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        repr.package.query := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_semanticReadingAdequacy
      (Atom := Atom) repr).symm.trans
      (representedFiniteTraceQueryObservation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
        (Atom := Atom) repr hrecover)

/-! ## Canonical support-shadow specialization -/

/--
For the canonical support-shadow representation, Cycle 41 discharges recovery,
so current-shadow factorization is exactly support-coordinate current-shadow
extensionality.
-/
theorem supportTraceShadowRepresentation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (support : List Atom) :
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T)) ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        support := by
  exact
    representedFiniteTraceQueryObservation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservationRepresentation support)
      (supportTraceShadowFiniteTraceQueryObservation_recoversQueryReadings
        (Atom := Atom) support)

/--
For the canonical support-shadow representation, current-shadow reading
faithfulness is exactly support-coordinate current-shadow extensionality.
-/
theorem supportTraceShadowRepresentation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (support : List Atom) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (supportTraceShadowFiniteTraceQueryObservation support).post ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        support := by
  exact
    representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservationRepresentation support)
      (supportTraceShadowFiniteTraceQueryObservation_recoversQueryReadings
        (Atom := Atom) support)

/--
Semantic-reading adequacy for the canonical support-shadow representation is
exactly support-coordinate current-shadow extensionality.
-/
theorem supportTraceShadowRepresentation_semanticReadingAdequacy_iff_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (support : List Atom) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post) ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        support := by
  exact
    representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservationRepresentation support)
      (supportTraceShadowFiniteTraceQueryObservation_recoversQueryReadings
        (Atom := Atom) support)

/-! ## Bool anti-weakening witness -/

/--
The complete Bool support-shadow observation recovers Bool `[true]` readings,
but it still does not factor through the current shadow.

Recovery is therefore not current-shadow representation adequacy.
-/
theorem boolCompleteSupportTraceShadow_recoversBoolTrueReadings_but_no_currentShadowFactor :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
    ¬ ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T =
          factor (canonicalTowerLayerShadow T) := by
  refine
    ⟨boolTrueCompleteSupportTraceShadowObservation_recoversQueryReadings,
      ?_⟩
  intro hfactor
  have hfaithful :
      SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
        (Atom := Bool)
        (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
        (supportTraceShadowFiniteTraceQueryObservation
          boolCompleteTraceSupport).query
        (supportTraceShadowFiniteTraceQueryObservation
          boolCompleteTraceSupport).post :=
    (representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_currentShadowFactor
      (Atom := Bool)
      (supportTraceShadowFiniteTraceQueryObservationRepresentation
        boolCompleteTraceSupport)).2
      hfactor
  exact
    not_boolCompleteSupportTraceShadowObservation_currentShadowSemanticReading_faithful
      hfaithful

end SemanticRepairFiniteQueryRepresentationRecoveredFactorization
end QualitySurface
end Formal.AG.Research
