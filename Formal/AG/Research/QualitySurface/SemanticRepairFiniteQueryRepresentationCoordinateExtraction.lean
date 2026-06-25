import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationSupportControl
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryCurrentShadowCoordinates

/-!
Cycle 38 evidence for `G-aat-quality-surface-04`.

Cycle 37 reduced canonical current-shadow reading faithfulness to query/support
determinacy.  This file composes that support-control theorem with the earlier
query-coordinate obligation boundary: a query is current-shadow determined
exactly when every source-trace coordinate it reads is current-shadow
extensional.

The result is still a support node.  Query-coordinate extensionality remains a
visible theorem argument / concrete certificate, not a semantic-soundness
discharge and not target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationCoordinateExtraction

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairCurrentShadowCoordinateObligations
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryRepresentationSupportControl

universe u v w x y z

/-! ## Query-coordinate extraction of current-shadow determinacy -/

/--
Query-coordinate current-shadow extensionality supplies the Cycle 37
query-determinacy certificate.
-/
theorem currentShadowDeterminesTraceQuery_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {query : List Atom}
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y} query) :
    CurrentShadowDeterminesTraceQuery.{u, v, w, x, y} query := by
  intro left right hshadow
  exact
    (supportTraceShadow_eq_iff_currentShadow_eq_and_sourceTraceReadings_eq).2
      ⟨hshadow,
        queryTraceVector_eq_of_coordinateCurrentShadowExtensional
          hcoords hshadow⟩

/--
For a finite query, current-shadow determinacy is equivalent to pointwise
current-shadow extensionality of all queried source-trace coordinates.
-/
theorem currentShadowDeterminesTraceQuery_iff_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (query : List Atom) :
    CurrentShadowDeterminesTraceQuery.{u, v, w, x, y} query ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query := by
  exact currentShadowDeterminesSupportTraceShadow_iff_coordinateCurrentShadowExtensional query

/-! ## Coordinate-level extraction of current-shadow reading faithfulness -/

/--
Pointwise query-coordinate extensionality makes every post-map invariant on
realized current-shadow query fibers.
-/
theorem postInvariantOnCurrentShadowFibers_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y} query) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  exact
    postInvariantOnCurrentShadowFibers_of_currentShadowDeterminesTraceQuery
      (Atom := Atom)
      (currentShadowDeterminesTraceQuery_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) hcoords)

/--
Pointwise query-coordinate extensionality makes every post-map on that query
faithful for the canonical current-shadow reading.
-/
theorem currentShadowSemanticReading_faithfulToQueryPost_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y} query) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      query post := by
  exact
    currentShadowSemanticReading_faithfulToQueryPost_of_currentShadowDeterminesTraceQuery
      (Atom := Atom)
      (currentShadowDeterminesTraceQuery_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) hcoords)

/--
Finite query package version: query-coordinate extensionality discharges
canonical current-shadow reading faithfulness for the package post-map.
-/
theorem finiteTraceQueryObservation_currentShadowSemanticReading_faithful_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        obs.query) :
    SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      obs := by
  exact
    currentShadowSemanticReading_faithfulToQueryPost_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) hcoords

/--
Represented observation version: query-coordinate extensionality discharges
canonical current-shadow reading faithfulness for the representing package.
-/
theorem representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        repr.package.query) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post := by
  exact
    currentShadowSemanticReading_faithfulToQueryPost_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) hcoords

/--
Query-coordinate extensionality gives raw current-shadow factorization for a
represented finite-query observation.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        repr.package.query) :
    ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T) := by
  exact
    representedFiniteTraceQueryObservation_currentShadowFactor_of_currentShadowDeterminesTraceQuery
      (Atom := Atom)
      repr
      (currentShadowDeterminesTraceQuery_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) hcoords)

/--
Query-coordinate extensionality rules out separated post-fibers for a
represented finite-query observation.
-/
theorem no_queryPostFiberSeparation_of_representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        repr.package.query) :
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) repr.package.query repr.package.post := by
  exact
    no_queryPostFiberSeparation_of_representedFiniteTraceQueryObservation_currentShadowDeterminesTraceQuery
      (Atom := Atom)
      repr
      (currentShadowDeterminesTraceQuery_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) hcoords)

/-! ## Exact support-shadow faithfulness boundary at query level -/

/--
The support-shadow observation for a query is faithful for the canonical
current-shadow reading exactly when all queried coordinates are current-shadow
extensional.
-/
theorem queryCoordinateCurrentShadowExtensional_iff_querySupportShadowObservation_currentShadowSemanticReading_faithful
    {Atom : Type u}
    (query : List Atom) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query ↔
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation query).query
        (supportTraceShadowFiniteTraceQueryObservation query).post := by
  exact
    (currentShadowDeterminesTraceQuery_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) query).symm.trans
      (currentShadowDeterminesSupportTraceShadow_iff_supportTraceShadowObservation_currentShadowSemanticReading_faithful
        (Atom := Atom) query)

/-! ## Empty-query positive and Bool obstruction compatibility -/

/--
Empty-query represented observations are faithful for the canonical
current-shadow reading through the coordinate-level route.
-/
theorem nilQuery_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hquery :
      repr.package.query = ([] : List Atom)) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post := by
  have hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        repr.package.query := by
    rw [hquery]
    exact nilQueryTraceCoordinatesCurrentShadowExtensional
  exact
    representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      repr
      hcoords

/--
The Bool `[true]` query support-shadow observation is not faithful for the
canonical current-shadow reading.
-/
theorem not_boolTrueTraceQuerySupportShadowObservation_currentShadowSemanticReading_faithful :
    ¬ SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      (supportTraceShadowFiniteTraceQueryObservation
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).query
      (supportTraceShadowFiniteTraceQueryObservation
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).post := by
  intro hfaithful
  have hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery :=
    (queryCoordinateCurrentShadowExtensional_iff_querySupportShadowObservation_currentShadowSemanticReading_faithful
      (Atom := Bool)
      SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).2
      hfaithful
  exact not_boolTrueTraceQueryCoordinatesCurrentShadowExtensional hcoords

end SemanticRepairFiniteQueryRepresentationCoordinateExtraction
end QualitySurface
end Formal.AG.Research
