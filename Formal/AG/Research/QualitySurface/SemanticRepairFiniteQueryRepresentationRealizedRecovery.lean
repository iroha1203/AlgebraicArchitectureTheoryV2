import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationRecoverableReadings

/-!
Cycle 40 evidence for `G-aat-quality-surface-04`.

Cycle 39 used a strong uniform decoder premise on all `shadow/readings`
arguments of a post-map.  This file weakens that premise to the actually
realized towers: it is enough that the post-map output recovers the query
readings on towers that exist.  A visible representation certificate can then
transport an observation-level decoder to the representing post-map on realized
towers.

The recovery premise remains explicit theorem data.  This is not a claim that
arbitrary semantic soundness or representation adequacy automatically supplies
such a decoder, and it is not target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationRealizedRecovery

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteSupportSeparation
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationCurrentShadowReading
open SemanticRepairFiniteQueryRepresentationCoordinateExtraction
open SemanticRepairFiniteQueryRepresentationRecoverableReadings

universe u v w x y z

/-! ## Realized-tower recovery premises -/

/--
A post-map recovers query readings on realized towers when its output can be
decoded back to the actual readings of each tower.

This is weaker than `QueryReadingsRecoveringPost`: it does not claim recovery
for arbitrary unattested `shadow/readings` pairs.
-/
def QueryReadingsRecoveringPostOnRealizedTowers
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) : Prop :=
  ∃ decode : Out -> List Bool,
    ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      decode
        (post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) =
        supportTraceVector query T.sourceTraceToken

/--
An arbitrary observation recovers query readings on realized towers when its
output can be decoded back to the query trace vector of each tower.
-/
def ObservationRecoversQueryReadings
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out) :
    Prop :=
  ∃ decode : Out -> List Bool,
    ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      decode (observe T) = supportTraceVector query T.sourceTraceToken

/--
The stronger Cycle 39 post-map recovery premise restricts to realized towers.
-/
theorem queryReadingsRecoveringPostOnRealizedTowers_of_queryReadingsRecoveringPost
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hrecover : QueryReadingsRecoveringPost post) :
    QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, z}
      (Atom := Atom) query post := by
  rcases hrecover with ⟨decode, hdecode⟩
  exact
    ⟨decode, by
      intro T
      exact hdecode
        (canonicalTowerLayerShadow T)
        (supportTraceVector query T.sourceTraceToken)⟩

/-! ## Realized recovery extracts the coordinate boundary -/

/--
Faithfulness for the canonical current-shadow reading plus realized-tower
recovery makes the query trace vector current-shadow extensional.
-/
theorem queryTraceVector_shadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        query post)
    (hrecover :
      QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
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
      rw [hdecode left]
    _ =
        decode
          (post (canonicalTowerLayerShadow right)
            (supportTraceVector query right.sourceTraceToken)) :=
      hdecoded
    _ = supportTraceVector query right.sourceTraceToken := by
      rw [hdecode right]

/--
Realized-tower recovery is enough to extract the Cycle 38 query-coordinate
certificate.
-/
theorem queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        query post)
    (hrecover :
      QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      query := by
  exact
    coordinateCurrentShadowExtensional_of_queryTraceVector_shadowExtensional
      (queryTraceVector_shadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
        (Atom := Atom) hfaithful hrecover)

/-- Finite query package version of realized recovery extraction. -/
theorem finiteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hfaithful :
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        obs)
    (hrecover :
      QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, z}
        (Atom := Atom) obs.query obs.post) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      obs.query := by
  exact
    queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
      (Atom := Atom) hfaithful hrecover

/-! ## Representation transports observation-level recovery -/

/--
A visible finite-query representation transports observation-level recovery to
the representing post-map, on realized towers.
-/
theorem queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings
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
    QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, z}
      (Atom := Atom) repr.package.query repr.package.post := by
  rcases hrecover with ⟨decode, hdecode⟩
  exact
    ⟨decode, by
      intro T
      change decode (repr.package.observe T) =
        supportTraceVector repr.package.query T.sourceTraceToken
      rw [← repr.represents T]
      exact hdecode T⟩

/--
Represented-observation version: current-shadow reading faithfulness plus a
visible observation-level decoder extracts query-coordinate extensionality.
-/
theorem representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_observationRecoversQueryReadings
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
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, z}
        repr.package.query observe) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      repr.package.query := by
  exact
    queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_queryReadingsRecoveringPostOnRealizedTowers
      (Atom := Atom)
      hfaithful
      (queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings
        (Atom := Atom) repr hrecover)

/--
If a represented observation is already current-shadow extensional and visibly
recovers its query readings, then the query coordinates are current-shadow
extensional.
-/
theorem representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_shadowExtensional_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hext :
      ShadowExtensionalTowerObservation observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, z}
        repr.package.query observe) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      repr.package.query := by
  exact
    representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_observationRecoversQueryReadings
      (Atom := Atom)
      repr
      (representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_shadowExtensional
        (Atom := Atom) repr hext)
      hrecover

/--
If a represented observation factors through the current shadow and visibly
recovers its query readings, then the query coordinates are current-shadow
extensional.
-/
theorem representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowFactor_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> Out,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe T = factor (canonicalTowerLayerShadow T))
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, z}
        repr.package.query observe) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      repr.package.query := by
  exact
    representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowSemanticReading_faithful_of_observationRecoversQueryReadings
      (Atom := Atom)
      repr
      ((representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_currentShadowFactor
        (Atom := Atom) repr).2 hfactor)
      hrecover

/-! ## Raw query-readings observations satisfy realized recovery -/

/-- The raw query-readings observation visibly recovers its query readings. -/
theorem queryTraceReadingsObservation_recoversQueryReadings
    {Atom : Type u}
    (query : List Atom) :
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (queryTraceReadingsFiniteTraceQueryObservation query).observe T) := by
  exact
    ⟨id, by
      intro T
      rfl⟩

/--
The raw query-readings representation therefore recovers readings on realized
towers.
-/
theorem queryTraceReadingsRepresentation_recoversQueryReadingsOnRealizedTowers
    {Atom : Type u}
    (query : List Atom) :
    QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, 0}
      (Atom := Atom)
      (queryTraceReadingsFiniteTraceQueryObservationRepresentation
        query).package.query
      (queryTraceReadingsFiniteTraceQueryObservationRepresentation
        query).package.post := by
  exact
    queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings
      (Atom := Atom)
      (queryTraceReadingsFiniteTraceQueryObservationRepresentation query)
      (queryTraceReadingsObservation_recoversQueryReadings
        (Atom := Atom) query)

/-! ## Realized recovery obstruction boundary -/

/--
The constant Bool post-map used in Cycle 39 is faithful for the current-shadow
reading, but it does not recover Bool `[true]` query readings on realized
towers.
-/
theorem not_boolTrueConstantPost_queryReadingsRecoveringPostOnRealizedTowers :
    ¬ QueryReadingsRecoveringPostOnRealizedTowers.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false) := by
  intro hrecover
  rcases hrecover with ⟨decode, hdecode⟩
  have hbase := hdecode boolTraceBaseTower
  have hmissed := hdecode boolTraceMissedTrueTower
  change decode false = [false] at hbase
  change decode false = [true] at hmissed
  have hcontr : ([false] : List Bool) = [true] := hbase.symm.trans hmissed
  nomatch hcontr

/--
The constant Bool post-map is faithful for the current-shadow reading, but it
does not recover realized Bool `[true]` query readings.
-/
theorem boolTrueConstantPost_currentShadowFaithful_but_not_queryReadingsRecoveringPostOnRealizedTowers :
    SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      boolTrueTraceQuery
      (fun _shadow _readings => false) ∧
    ¬ QueryReadingsRecoveringPostOnRealizedTowers.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false) := by
  exact
    ⟨(currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
        (Atom := Bool)
        boolTrueTraceQuery
        (fun _shadow _readings => false)).2
        (by
          intro _shadow _leftReadings _rightReadings _hleft _hright
          rfl),
      not_boolTrueConstantPost_queryReadingsRecoveringPostOnRealizedTowers⟩

/--
The Bool first-reading observation factors through support shadow and recovers
the represented query readings, but it still has no current-shadow factor.
-/
theorem boolFirstQueryRepresentation_supportFactor_no_currentFactor_but_recoversReadings :
    (∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).observe T =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              boolCompleteTraceSupport T)) ∧
    (¬ ∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation boolFirstQueryReadingPost).observe T) := by
  refine
    ⟨boolFirstQueryRepresentation_supportFactor_but_no_currentShadowFactor.1,
      boolFirstQueryRepresentation_supportFactor_but_no_currentShadowFactor.2,
      ?_⟩
  exact
    ⟨fun reading => [reading], by
      intro T
      rfl⟩

end SemanticRepairFiniteQueryRepresentationRealizedRecovery
end QualitySurface
end Formal.AG.Research
