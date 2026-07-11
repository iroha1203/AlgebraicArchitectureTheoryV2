import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryExplicitCurrentShadowCertificates

/-!
Cycle 45 evidence for `G-aat-quality-surface-04`.

Cycle 44 named the explicit per-coordinate current-shadow certificate surface.
This file records a non-circular extraction route into that surface: a semantic
reading that collapses current-shadow query fibers, a post-map faithful to that
reading, and a realized-tower decoder for query readings together force the
explicit coordinate certificate.

This is a support node, not target theorem completion.  The semantic-reading
collapse, post faithfulness, and recovery premises remain visible theorem data;
they are not full semantic soundness, representation adequacy, finite shadow
adequacy, or target completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQuerySemanticReadingCertificateExtraction

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQuerySupportedCurrentShadowFactorization
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates

universe u v w x y z

/-! ## Semantic-reading and recovery extraction -/

/--
Semantic-reading collapse, post faithfulness, and realized-tower recovery make
the raw query-reading vector current-shadow extensional.

All three premises are visible: this is not an automatic extraction from
semantic soundness or representation adequacy.
-/
theorem queryTraceVector_shadowExtensional_of_semanticReadingAdequacy_of_queryReadingsRecoveringPostOnRealizedTowers
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post)
    (hrecover :
      QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        supportTraceVector query T.sourceTraceToken) := by
  rcases hrecover with ⟨decode, hdecode⟩
  intro left right hshadow
  have hequiv : reading.Equivalent left right :=
    hcollapse
      (shadow := canonicalTowerLayerShadow left)
      (leftReadings := supportTraceVector query left.sourceTraceToken)
      (rightReadings := supportTraceVector query right.sourceTraceToken)
      (left := left)
      (right := right)
      rfl
      rfl
      hshadow.symm
      rfl
  have hpost : SameQueryPostValue query post left right :=
    hfaithful left right hequiv
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
The semantic-reading / recovery route extracts the explicit Cycle 44 query
coordinate certificate.
-/
theorem queryCurrentShadowCoordinateCertificate_of_semanticReadingAdequacy_of_queryReadingsRecoveringPostOnRealizedTowers
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post)
    (hrecover :
      QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y} query := by
  exact
    certificate_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      (coordinateCurrentShadowExtensional_of_queryTraceVector_shadowExtensional
        (queryTraceVector_shadowExtensional_of_semanticReadingAdequacy_of_queryReadingsRecoveringPostOnRealizedTowers
          (Atom := Atom) hcollapse hfaithful hrecover))

/-- Finite query package version of semantic-reading / recovery extraction. -/
theorem finiteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_semanticReadingAdequacy_of_queryReadingsRecoveringPostOnRealizedTowers
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs)
    (hfaithful :
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs)
    (hrecover :
      QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, z}
        (Atom := Atom) obs.query obs.post) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      obs.query := by
  exact
    queryCurrentShadowCoordinateCertificate_of_semanticReadingAdequacy_of_queryReadingsRecoveringPostOnRealizedTowers
      (Atom := Atom) hcollapse hfaithful hrecover

/--
A visible representation transports observation-level recovery, so
semantic-reading collapse and post faithfulness extract the represented query's
coordinate certificate.
-/
theorem representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, z}
        repr.package.query observe) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      repr.package.query := by
  exact
    queryCurrentShadowCoordinateCertificate_of_semanticReadingAdequacy_of_queryReadingsRecoveringPostOnRealizedTowers
      (Atom := Atom)
      hcollapse
      hfaithful
      (queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings
        (Atom := Atom) repr hrecover)

/--
If a represented observation visibly factors through the current shadow and
recovers its query readings, then the represented query carries the explicit
coordinate certificate.

The factorization and recovery premises remain visible.
-/
theorem representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_currentShadowFactor_of_observationRecoversQueryReadings
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
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      repr.package.query := by
  exact
    certificate_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      (representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_currentShadowFactor_of_observationRecoversQueryReadings
        (Atom := Atom) repr hfactor hrecover)

/-! ## Generated-observation exact boundary -/

/--
All finite query-generated observations factor through the current shadow
exactly when the query carries the explicit coordinate certificate.

The quantification ranges only over query-generated observations, not arbitrary
semantic observations.
-/
theorem queryGeneratedObservations_currentShadowFactor_forall_listPost_iff_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    (query : List Atom) :
    (∀ (post : FiniteTowerLayerShadow -> List Bool -> List Bool),
      ∃ factor : FiniteTowerLayerShadow -> List Bool,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          post (canonicalTowerLayerShadow T)
              (supportTraceVector query T.sourceTraceToken) =
            factor (canonicalTowerLayerShadow T)) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        query := by
  constructor
  · intro hall
    have hreadings :
        ∃ factor : FiniteTowerLayerShadow -> List Bool,
          ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
            supportTraceVector query T.sourceTraceToken =
              factor (canonicalTowerLayerShadow T) := by
      simpa using
        hall (fun _shadow readings => readings)
    exact
      certificate_of_queryCoordinateCurrentShadowExtensional
        (Atom := Atom)
        ((queryTraceReadings_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
          (Atom := Atom) query).1 hreadings)
  · intro cert post
    rcases queryTraceReadings_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) query cert with
      ⟨readingsFactor, hreadings⟩
    exact
      ⟨fun shadow => post shadow (readingsFactor shadow), by
        intro T
        rw [hreadings T]⟩

/--
For supported finite queries, support membership plus all generated-observation
factorizations is exactly the supported explicit certificate package.

This keeps `QuerySupportedBy` as admissibility data and the coordinate
certificate as the current-shadow adequacy data.
-/
theorem supportedQueryGeneratedObservations_currentShadowFactor_forall_listPost_iff_supportedCurrentShadowCertificate
    {Atom : Type u}
    (support query : List Atom) :
    (QuerySupportedBy support query ∧
      ∀ (post : FiniteTowerLayerShadow -> List Bool -> List Bool),
        ∃ factor : FiniteTowerLayerShadow -> List Bool,
          ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
            post (canonicalTowerLayerShadow T)
                (supportTraceVector query T.sourceTraceToken) =
              factor (canonicalTowerLayerShadow T)) ↔
      SupportedFiniteQueryCurrentShadowCertificate.{u, v, w, x, y}
        support query := by
  constructor
  · intro h
    exact
      { query_supported := h.1
        coordinates :=
          (queryGeneratedObservations_currentShadowFactor_forall_listPost_iff_queryCurrentShadowCoordinateCertificate
            (Atom := Atom) query).1 h.2 }
  · intro cert
    exact
      ⟨cert.query_supported,
        (queryGeneratedObservations_currentShadowFactor_forall_listPost_iff_queryCurrentShadowCoordinateCertificate
          (Atom := Atom) query).2 cert.coordinates⟩

end SemanticRepairFiniteQuerySemanticReadingCertificateExtraction
end QualitySurface
end ResearchLean.AG
