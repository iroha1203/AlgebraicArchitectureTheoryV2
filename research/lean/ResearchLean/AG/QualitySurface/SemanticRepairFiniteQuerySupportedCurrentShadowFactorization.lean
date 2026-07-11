import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryRepresentationRecoveredFactorization

/-!
Cycle 43 evidence for `G-aat-quality-surface-04`.

Cycle 42 made current-shadow factorization an exact query-coordinate criterion
under visible query-reading recovery.  This file records the adjacent support
boundary: a visible current-shadow determinacy certificate for an ambient
support restricts to any explicitly supported finite query, and only then gives
current-shadow factorization for that query.

This is a support node, not target theorem completion.  The support-level
determinacy certificate remains visible theorem data.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQuerySupportedCurrentShadowFactorization

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairCurrentShadowCoordinateObligations
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationCoordinateExtraction
open SemanticRepairFiniteQueryRepresentationRecoverableReadings
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryRepresentationRecoveredFactorization

universe u v w x y z

/-! ## Support determinacy restricts to supported queries -/

/--
An ambient support trace shadow determined by the current shadow determines
every explicitly supported finite query coordinate.

The support determinacy premise is visible and undischarged here.
-/
theorem queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy
    {Atom : Type u}
    {support query : List Atom}
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support)
    (hquery : QuerySupportedBy support query) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      query := by
  intro atom hmem
  exact
    coordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow
      (Atom := Atom) hcurrent atom (hquery atom hmem)

/--
Support-level current-shadow determinacy restricts to query-level
current-shadow determinacy for explicitly supported queries.
-/
theorem currentShadowDeterminesTraceQuery_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy
    {Atom : Type u}
    {support query : List Atom}
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support)
    (hquery : QuerySupportedBy support query) :
    CurrentShadowDeterminesTraceQuery.{u, v, w, x, y} query := by
  exact
    currentShadowDeterminesTraceQuery_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      (queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy
        (Atom := Atom) hcurrent hquery)

/-! ## Query-reading factorization under visible support determinacy -/

/--
For the raw query-readings observation, current-shadow factorization is exactly
the query-coordinate current-shadow criterion.
-/
theorem queryTraceReadings_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (query : List Atom) :
    (∃ factor : FiniteTowerLayerShadow -> List Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        supportTraceVector query T.sourceTraceToken =
          factor (canonicalTowerLayerShadow T)) ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query := by
  exact
    representedFiniteTraceQueryObservation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
      (Atom := Atom)
      (queryTraceReadingsFiniteTraceQueryObservationRepresentation query)
      (queryTraceReadingsObservation_recoversQueryReadings
        (Atom := Atom) query)

/--
A supported query's raw readings factor through the current shadow when the
ambient support trace shadow is visibly current-shadow determined.
-/
theorem supportedQueryTraceReadings_currentShadowFactor_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support query : List Atom}
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support)
    (hquery : QuerySupportedBy support query) :
    ∃ factor : FiniteTowerLayerShadow -> List Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        supportTraceVector query T.sourceTraceToken =
          factor (canonicalTowerLayerShadow T) := by
  exact
    (queryTraceReadings_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) query).2
      (queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy
        (Atom := Atom) hcurrent hquery)

/--
Generated observations over a supported finite query factor through the current
shadow under a visible ambient support-determinacy certificate.
-/
theorem supportedQueryGeneratedObservation_currentShadowFactor_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support query : List Atom}
    {Out : Type z}
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support)
    (hquery : QuerySupportedBy support query)
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        post (canonicalTowerLayerShadow T)
            (supportTraceVector query T.sourceTraceToken) =
          factor (canonicalTowerLayerShadow T) := by
  exact
    representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      (repr :=
        { package :=
            { query := query
              query_supported := hquery
              post := post }
          represents := by
            intro T
            rfl })
      (queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy
        (Atom := Atom) hcurrent hquery)

/-! ## Represented finite-query corollaries -/

/--
Package-level corollary: a represented finite-query observation over a support
factors through the current shadow when that support trace shadow is visibly
current-shadow determined.

The `query_supported` field is only the package instance of finite query
admissibility; it is not semantic soundness or representation adequacy.
-/
theorem representedSupportedFiniteTraceQueryObservation_currentShadowFactor_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr : FiniteTraceQueryObservationRepresentation support observe)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support) :
    ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T) := by
  exact
    representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) repr
      (queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy
        (Atom := Atom) hcurrent repr.package.query_supported)

/--
Under visible recovery, the represented factorization criterion can be closed
from an ambient support-determinacy certificate for the represented package's
supported query.
-/
theorem representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr : FiniteTraceQueryObservationRepresentation support observe)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      repr.package.query := by
  exact
    queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy
      (Atom := Atom) hcurrent repr.package.query_supported

/--
For the canonical support-shadow representation, current-shadow factorization
is exactly visible support-level current-shadow determinacy.
-/
theorem supportTraceShadowRepresentation_currentShadowFactor_iff_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    (support : List Atom) :
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T)) ↔
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
        support := by
  exact
    (supportTraceShadowRepresentation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) support).trans
      (currentShadowDeterminesSupportTraceShadow_iff_coordinateCurrentShadowExtensional
        (Atom := Atom) support).symm

end SemanticRepairFiniteQuerySupportedCurrentShadowFactorization
end QualitySurface
end ResearchLean.AG
