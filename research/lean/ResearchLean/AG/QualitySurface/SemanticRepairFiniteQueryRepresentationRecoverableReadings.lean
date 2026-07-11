import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryRepresentationCoordinateExtraction

/-!
Cycle 39 evidence for `G-aat-quality-surface-04`.

Cycle 38 identified query-coordinate current-shadow extensionality as the
visible certificate that discharges current-shadow reading faithfulness.  This
file records one non-circular extraction route into that certificate: if the
post-map visibly recovers the query readings, then faithfulness for the
canonical current-shadow reading forces those query readings to be
current-shadow extensional.

The reading recovery map is an explicit theorem argument.  It is not hidden in
the representation package, a typeclass, or an opaque adequacy field, and it is
still not target theorem completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationRecoverableReadings

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
open SemanticRepairFiniteQueryRepresentationNoSeparation
open SemanticRepairFiniteQueryRepresentationCurrentShadowReading
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationCoordinateExtraction

universe u v w x y z

/-! ## Visible recovery of query readings from a post-map -/

/--
A post-map visibly recovers the query readings when it admits a public decoder
from its output back to the `List Bool` readout.

This is a theorem-level premise, not a field in `FiniteTraceQueryObservation`
or `FiniteTraceQueryObservationRepresentation`.
-/
def QueryReadingsRecoveringPost
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) : Prop :=
  ∃ decode : Out -> List Bool,
    ∀ shadow readings, decode (post shadow readings) = readings

/-- The raw query-readings post-map forgets the current layer and returns readings. -/
def queryTraceReadingsPost :
    FiniteTowerLayerShadow -> List Bool -> List Bool :=
  fun _ readings => readings

/-- The raw query-readings post-map visibly recovers its readings. -/
theorem queryTraceReadingsPost_recovers :
    QueryReadingsRecoveringPost queryTraceReadingsPost := by
  exact ⟨id, by intro _shadow _readings; rfl⟩

/-- The finite-query package that observes exactly the query trace readings. -/
def queryTraceReadingsFiniteTraceQueryObservation
    {Atom : Type u}
    (query : List Atom) :
    FiniteTraceQueryObservation query (List Bool) where
  query := query
  query_supported := supportSelfQuerySupportedBy query
  post := queryTraceReadingsPost

/-- The raw query-readings package observes the query trace vector. -/
theorem queryTraceReadingsFiniteTraceQueryObservation_observe_eq
    {Atom : Type u}
    (query : List Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (queryTraceReadingsFiniteTraceQueryObservation query).observe T =
      supportTraceVector query T.sourceTraceToken := by
  rfl

/--
A visible representation certificate for the raw query-readings observation.
-/
def queryTraceReadingsFiniteTraceQueryObservationRepresentation
    {Atom : Type u}
    (query : List Atom) :
    FiniteTraceQueryObservationRepresentation query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        supportTraceVector query T.sourceTraceToken) where
  package := queryTraceReadingsFiniteTraceQueryObservation query
  represents := by
    intro T
    rfl

/-! ## Recoverable post-maps extract coordinate extensionality -/

/--
If a post-map recovers query readings, then current-shadow reading faithfulness
forces the query trace vector itself to be current-shadow extensional.
-/
theorem queryTraceVector_shadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        query post)
    (hrecover : QueryReadingsRecoveringPost post) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        supportTraceVector query T.sourceTraceToken) := by
  rcases hrecover with ⟨decode, hdecode⟩
  intro left right hshadow
  have hpost :
      post (canonicalTowerLayerShadow left)
          (supportTraceVector query left.sourceTraceToken) =
        post (canonicalTowerLayerShadow right)
          (supportTraceVector query right.sourceTraceToken) :=
    hfaithful left right hshadow
  have hdecoded := congrArg decode hpost
  calc
    supportTraceVector query left.sourceTraceToken =
        decode
          (post (canonicalTowerLayerShadow left)
            (supportTraceVector query left.sourceTraceToken)) := by
      rw [hdecode]
    _ =
        decode
          (post (canonicalTowerLayerShadow right)
            (supportTraceVector query right.sourceTraceToken)) :=
      hdecoded
    _ = supportTraceVector query right.sourceTraceToken := by
      rw [hdecode]

/--
Recoverable post-map faithfulness is a non-circular route from semantic reading
faithfulness to the Cycle 38 query-coordinate certificate.
-/
theorem queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        query post)
    (hrecover : QueryReadingsRecoveringPost post) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      query := by
  exact
    coordinateCurrentShadowExtensional_of_queryTraceVector_shadowExtensional
      (queryTraceVector_shadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
        (Atom := Atom) hfaithful hrecover)

/--
Finite query package version: if the package post-map visibly recovers query
readings, faithfulness of the current-shadow reading forces query-coordinate
extensionality.
-/
theorem finiteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hfaithful :
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        obs)
    (hrecover : QueryReadingsRecoveringPost obs.post) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      obs.query := by
  exact
    queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
      (Atom := Atom) hfaithful hrecover

/--
Represented observation version.  The representation certificate supplies the
package; the recovery of query readings is still a separate visible premise.
-/
theorem representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        repr.package.query repr.package.post)
    (hrecover : QueryReadingsRecoveringPost repr.package.post) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      repr.package.query := by
  exact
    queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
      (Atom := Atom) hfaithful hrecover

/-! ## Raw query-readings observation is the exact coordinate boundary -/

/--
For the raw query-readings observation, current-shadow reading faithfulness is
exactly query-coordinate current-shadow extensionality.
-/
theorem queryTraceReadingsObservation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (query : List Atom) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      (queryTraceReadingsFiniteTraceQueryObservation query).query
      (queryTraceReadingsFiniteTraceQueryObservation query).post ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query := by
  constructor
  · intro hfaithful
    exact
      queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPost
        (Atom := Atom) hfaithful queryTraceReadingsPost_recovers
  · intro hcoords
    exact
      currentShadowSemanticReading_faithfulToQueryPost_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom) hcoords

/--
The raw query-readings represented observation has the same exact faithfulness
criterion.
-/
theorem queryTraceReadingsRepresentation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    (query : List Atom) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      (queryTraceReadingsFiniteTraceQueryObservationRepresentation query).package.query
      (queryTraceReadingsFiniteTraceQueryObservationRepresentation query).package.post ↔
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query := by
  exact
    queryTraceReadingsObservation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) query

/-! ## Support-shadow semantic adequacy exposes the exact coordinate boundary -/

/--
For the query support-shadow observation, existence of a semantic-reading
adequacy package is exactly query-coordinate current-shadow extensionality.

This is not an arbitrary semantic-soundness extraction theorem: the observation
being tested is the query trace shadow itself, fixed by `query`.
-/
theorem queryCoordinateCurrentShadowExtensional_iff_querySupportShadowObservation_exists_semanticReadingAdequacy
    {Atom : Type u}
    (query : List Atom) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query ↔
      ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading
          (supportTraceShadowFiniteTraceQueryObservation query).query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
          (Atom := Atom) reading
          (supportTraceShadowFiniteTraceQueryObservation query).query
          (supportTraceShadowFiniteTraceQueryObservation query).post := by
  exact
    (queryCoordinateCurrentShadowExtensional_iff_querySupportShadowObservation_currentShadowSemanticReading_faithful
      (Atom := Atom) query).trans
      ((currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom)
        (supportTraceShadowFiniteTraceQueryObservation query).query
        (supportTraceShadowFiniteTraceQueryObservation query).post).trans
        (exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
          (Atom := Atom)
          (supportTraceShadowFiniteTraceQueryObservation query).query
          (supportTraceShadowFiniteTraceQueryObservation query).post).symm)

/--
If the query support-shadow observation factors through the current shadow,
then the queried coordinates must already be current-shadow extensional.
-/
theorem queryCoordinateCurrentShadowExtensional_of_querySupportShadow_currentShadowFactor
    {Atom : Type u}
    (query : List Atom)
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          (supportTraceShadowFiniteTraceQueryObservation query).observe T =
            factor (canonicalTowerLayerShadow T)) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      query := by
  have hfactor' :
      ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          canonicalSupportTraceProbeTowerLayerShadow query T =
            factor (canonicalTowerLayerShadow T) := by
    rcases hfactor with ⟨factor, hfactor⟩
    exact
      ⟨factor, by
        intro T
        simpa [supportTraceShadowFiniteTraceQueryObservation_observe_eq]
          using hfactor T⟩
  have hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        (supportTraceShadowFiniteTraceQueryObservation query).query
        (supportTraceShadowFiniteTraceQueryObservation query).post :=
    (representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_currentShadowFactor
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservationRepresentation query)).2
      hfactor'
  exact
    (queryCoordinateCurrentShadowExtensional_iff_querySupportShadowObservation_currentShadowSemanticReading_faithful
      (Atom := Atom) query).2
      hfaithful

/--
The Bool `[true]` query support-shadow observation has no current-shadow
factor.  Support-shadow representation alone therefore does not supply
current-shadow adequacy.
-/
theorem no_boolTrueQuerySupportShadow_currentShadowFactor :
    ¬ ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (supportTraceShadowFiniteTraceQueryObservation
          SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).observe T =
          factor (canonicalTowerLayerShadow T) := by
  intro hfactor
  have hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery :=
    queryCoordinateCurrentShadowExtensional_of_querySupportShadow_currentShadowFactor
      SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery hfactor
  exact not_boolTrueTraceQueryCoordinatesCurrentShadowExtensional hcoords

/-! ## Arbitrary faithfulness is not coordinate extraction -/

/--
A constant Bool post-map is faithful for the current-shadow reading even on the
non-extensional Bool `[true]` query.
-/
theorem boolTrueConstantFiniteTraceQueryObservation_currentShadowFaithful_not_queryCoordinateCurrentShadowExtensional :
    SemanticReadingFaithfulToFiniteTraceQueryObservation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      (boolTrueFiniteTraceQueryObservation
        (fun _shadow _readings => false)) ∧
    ¬ QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
      (boolTrueFiniteTraceQueryObservation
        (fun _shadow _readings => false)).query := by
  constructor
  · exact
      (finiteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_postInvariant
        (Atom := Bool)
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false))).2
        (by
          intro _shadow _leftReadings _rightReadings _hleft _hright
          rfl)
  · change
      ¬ QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery
    exact not_boolTrueTraceQueryCoordinatesCurrentShadowExtensional

/--
The Bool first-reading observation factors through complete support trace
shadow, but not through the current shadow.
-/
theorem boolFirstQueryRepresentation_supportFactor_but_no_currentShadowFactor :
    (∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).observe T =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              boolCompleteTraceSupport T)) ∧
    ¬ ∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).observe T =
          factor (canonicalTowerLayerShadow T) := by
  exact
    ⟨boolTrueRepresentedFiniteTraceQueryObservation_factors
      boolFirstQueryReadingPost,
      boolFirstRepresentedFiniteTraceQueryObservation_no_currentShadowFactor⟩

/--
The represented Bool first-reading observation has no semantic-reading adequacy
package.
-/
theorem no_boolFirstRepresentedFiniteTraceQueryObservation_semanticReadingAdequacy :
    ¬ ∃ reading : TowerSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{0, 0, 0, 0, 0}
        (Atom := Bool) reading
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).query ∧
      SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
        (Atom := Bool) reading
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).query
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).post := by
  exact
    no_representedFiniteTraceQueryObservation_semanticReadingAdequacy_of_queryPostFiberSeparation
      (Atom := Bool)
      (boolTrueFiniteTraceQueryObservationRepresentation boolFirstQueryReadingPost)
      boolFirstRepresentedFiniteTraceQueryObservation_queryPostFiberSeparation

/-! ## Support-shadow adequacy obstruction boundary -/

/--
The Bool `[true]` support-shadow observation has no semantic-reading adequacy
package.  The exact coordinate boundary therefore cannot be bypassed by an
arbitrary semantic reading.
-/
theorem not_boolTrueTraceQuerySupportShadowObservation_exists_semanticReadingAdequacy :
    ¬ ∃ reading : TowerSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{0, 0, 0, 0, 0}
        (Atom := Bool) reading
        (supportTraceShadowFiniteTraceQueryObservation
          SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).query ∧
      SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
        (Atom := Bool) reading
        (supportTraceShadowFiniteTraceQueryObservation
          SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).query
        (supportTraceShadowFiniteTraceQueryObservation
          SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).post := by
  intro hadequacy
  have hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery :=
    (queryCoordinateCurrentShadowExtensional_iff_querySupportShadowObservation_exists_semanticReadingAdequacy
      (Atom := Bool)
      SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).2
      hadequacy
  exact not_boolTrueTraceQueryCoordinatesCurrentShadowExtensional hcoords

/-! ## Raw-query readings positive and obstruction boundaries -/

/-- Empty raw-query readings are faithful for the current-shadow reading. -/
theorem nilQuery_queryTraceReadingsObservation_currentShadowSemanticReading_faithful
    {Atom : Type u} :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      (queryTraceReadingsFiniteTraceQueryObservation ([] : List Atom)).query
      (queryTraceReadingsFiniteTraceQueryObservation ([] : List Atom)).post := by
  exact
    (queryTraceReadingsObservation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) ([] : List Atom)).2
      nilQueryTraceCoordinatesCurrentShadowExtensional

/--
The Bool `[true]` raw query-readings observation is not faithful for the
current-shadow reading.
-/
theorem not_boolTrueQueryTraceReadingsObservation_currentShadowSemanticReading_faithful :
    ¬ SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      (queryTraceReadingsFiniteTraceQueryObservation
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).query
      (queryTraceReadingsFiniteTraceQueryObservation
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).post := by
  intro hfaithful
  have hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery :=
    (queryTraceReadingsObservation_currentShadowSemanticReading_faithful_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Bool)
      SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery).1
      hfaithful
  exact not_boolTrueTraceQueryCoordinatesCurrentShadowExtensional hcoords

end SemanticRepairFiniteQueryRepresentationRecoverableReadings
end QualitySurface
end ResearchLean.AG
