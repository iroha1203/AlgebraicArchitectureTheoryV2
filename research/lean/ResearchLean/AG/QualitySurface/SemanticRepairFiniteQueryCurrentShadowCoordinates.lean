import ResearchLean.AG.QualitySurface.SemanticRepairCurrentShadowCoordinateObligations

/-!
Cycle 26 evidence for `G-aat-quality-surface-04`.

This file moves the Cycle 25 coordinate-obligation boundary from ambient
support lists to finite queries themselves.  The query trace vector is
current-shadow extensional exactly when the queried source-trace coordinates
are current-shadow extensional.  Query-generated observations then factor
through the current canonical shadow under that visible query-coordinate
obligation.

The result is still a visible obligation.  It does not derive coordinate
extensionality from semantic soundness, and the Bool `[true]` query records a
concrete obstruction.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryCurrentShadowCoordinates

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportSeparation
open SemanticRepairFiniteSupportMembership
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairCurrentShadowCoordinateObligations

universe u v w x y z

/-! ## Query-local current-shadow coordinate obligations -/

/--
Every coordinate queried by a finite trace query is current-shadow extensional.

This is query-local: it does not require a larger support trace shadow to be
determined by the current canonical shadow.
-/
def QueryTraceCoordinatesCurrentShadowExtensional
    {Atom : Type u}
    (query : List Atom) : Prop :=
  ∀ atom : Atom,
    atom ∈ query ->
      SourceTraceCoordinateCurrentShadowExtensional.{u, v, w, x, y} atom

/--
Query-coordinate extensionality makes the finite query trace vector
current-shadow determined.
-/
theorem queryTraceVector_eq_of_coordinateCurrentShadowExtensional
    {Atom : Type u}
    {query : List Atom}
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y} query)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalTowerLayerShadow left = canonicalTowerLayerShadow right) :
    supportTraceVector query left.sourceTraceToken =
      supportTraceVector query right.sourceTraceToken := by
  exact
    supportTraceVector_eq_of_coordinateCurrentShadowExtensional
      query hcoords left right hshadow

/--
The finite query trace vector itself is current-shadow extensional under the
query-coordinate obligation.
-/
theorem queryTraceVector_shadowExtensional_of_coordinateCurrentShadowExtensional
    {Atom : Type u}
    {query : List Atom}
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y} query) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        supportTraceVector query T.sourceTraceToken) := by
  intro left right hshadow
  exact queryTraceVector_eq_of_coordinateCurrentShadowExtensional hcoords hshadow

/--
If the finite query trace vector is current-shadow extensional, then each
listed coordinate in the query is current-shadow extensional.
-/
theorem coordinateCurrentShadowExtensional_of_queryTraceVector_shadowExtensional
    {Atom : Type u}
    {query : List Atom}
    (hvector :
      ShadowExtensionalTowerObservation
        (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          supportTraceVector query T.sourceTraceToken)) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      query := by
  intro atom hmem left right hshadow
  have hreadings :
      supportTraceVector query left.sourceTraceToken =
        supportTraceVector query right.sourceTraceToken :=
    hvector left right hshadow
  have hsupport :
      canonicalSupportTraceProbeTowerLayerShadow query left =
        canonicalSupportTraceProbeTowerLayerShadow query right := by
    exact
      (supportTraceShadow_eq_iff_currentShadow_eq_and_sourceTraceReadings_eq).2
        ⟨hshadow, hreadings⟩
  exact sourceTraceCoordinate_same_of_same_supportTraceProbeShadow hmem hsupport

/--
The finite query trace vector is current-shadow extensional exactly when all
queried source-trace coordinates are current-shadow extensional.
-/
theorem queryTraceVector_shadowExtensional_iff_coordinateCurrentShadowExtensional
    {Atom : Type u}
    (query : List Atom) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        supportTraceVector query T.sourceTraceToken) ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query := by
  exact
    ⟨coordinateCurrentShadowExtensional_of_queryTraceVector_shadowExtensional,
      queryTraceVector_shadowExtensional_of_coordinateCurrentShadowExtensional⟩

/-! ## Query-generated observations -/

/--
Observations generated from the current layer and a query vector are
current-shadow extensional when the query coordinates are current-shadow
extensional.
-/
theorem queryTraceGeneratedObservation_shadowExtensional_of_coordinateCurrentShadowExtensional
    {Atom : Type u}
    {Out : Type z}
    {query : List Atom}
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y} query)
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) := by
  intro left right hshadow
  have hreadings :
      supportTraceVector query left.sourceTraceToken =
        supportTraceVector query right.sourceTraceToken :=
    queryTraceVector_eq_of_coordinateCurrentShadowExtensional hcoords hshadow
  change
    post (canonicalTowerLayerShadow left)
        (supportTraceVector query left.sourceTraceToken) =
      post (canonicalTowerLayerShadow right)
        (supportTraceVector query right.sourceTraceToken)
  rw [hshadow, hreadings]

/--
A finite query-generated observation is current-shadow extensional when its
own query coordinates are current-shadow extensional.
-/
theorem finiteTraceQueryObservation_shadowExtensional_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        obs.query) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        obs.observe T) := by
  exact
    queryTraceGeneratedObservation_shadowExtensional_of_coordinateCurrentShadowExtensional
      hcoords obs.post

/--
The query-coordinate obligation gives canonical-shadow factorization for a
finite query-generated observation.
-/
theorem finiteTraceQueryObservation_eq_canonicalShadowFactor_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        obs.query)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    obs.observe T =
      canonicalShadowFactor
        (fun U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          obs.observe U)
        (canonicalTowerLayerShadow T) := by
  exact
    shadowExtensionalObservation_factors
      (finiteTraceQueryObservation_shadowExtensional_of_queryCoordinateCurrentShadowExtensional
        obs hcoords)
      T

/-- The empty finite query has no coordinate obligations. -/
theorem nilQueryTraceCoordinatesCurrentShadowExtensional
    {Atom : Type u} :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      (Atom := Atom) [] := by
  intro atom hmem
  cases hmem

/--
Generated observations with an empty query are current-shadow extensional
without any source-trace coordinate premise.
-/
theorem nilQueryTraceGeneratedObservation_shadowExtensional
    {Atom : Type u}
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector ([] : List Atom) T.sourceTraceToken)) := by
  exact
    queryTraceGeneratedObservation_shadowExtensional_of_coordinateCurrentShadowExtensional
      nilQueryTraceCoordinatesCurrentShadowExtensional post

/-! ## Concrete Bool obstruction -/

/-- Post-map reading the first query result as a Boolean observation. -/
def boolFirstQueryReadingPost :
    FiniteTowerLayerShadow -> List Bool -> Bool :=
  fun _ readings => readings.headD false

/--
The concrete Bool `[true]` query asks for a non-current-shadow-extensional
coordinate.
-/
theorem not_boolTrueTraceQueryCoordinatesCurrentShadowExtensional :
    ¬ QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
      SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery := by
  intro hcoords
  exact
    not_boolTrueSourceTraceCoordinateCurrentShadowExtensional
      (hcoords true (List.Mem.head _))

/--
The Bool `[true]` query observation with the first-reading post-map is exactly
the missed `true` source-trace coordinate.
-/
theorem boolTrueFiniteTraceQueryObservation_firstReading_eq_missedTraceObservation
    (T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool) :
    (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).observe T =
      boolMissedTraceObservation T := by
  rfl

/--
The Bool `[true]` query observation that returns its first query reading is
not current-shadow extensional.
-/
theorem not_boolTrueFiniteTraceQueryObservation_shadowExtensional :
    ¬ ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).observe T) := by
  intro hobs
  have hsame :=
    hobs
      boolTraceBaseTower
      boolTraceMissedTrueTower
      bool_missedTrue_same_currentShadow
  have hmissed :
      boolMissedTraceObservation boolTraceBaseTower =
        boolMissedTraceObservation boolTraceMissedTrueTower := by
    rw [← boolTrueFiniteTraceQueryObservation_firstReading_eq_missedTraceObservation
          boolTraceBaseTower,
        ← boolTrueFiniteTraceQueryObservation_firstReading_eq_missedTraceObservation
          boolTraceMissedTrueTower]
    exact hsame
  exact
    boolMissedTraceObservation_separates_pair
      hmissed

end SemanticRepairFiniteQueryCurrentShadowCoordinates
end QualitySurface
end ResearchLean.AG
