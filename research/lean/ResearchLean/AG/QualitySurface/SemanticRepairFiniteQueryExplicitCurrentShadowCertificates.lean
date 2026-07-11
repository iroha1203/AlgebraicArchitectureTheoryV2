import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQuerySupportedCurrentShadowFactorization

/-!
Cycle 44 evidence for `G-aat-quality-surface-04`.

Cycle 43 kept support-level current-shadow determinacy visible.  This file
turns the corresponding coordinate obligation into an explicit finite
certificate surface: current-shadow factorization of each queried source-trace
coordinate is exactly the certificate needed for query-level determinacy.

This is a support / obstruction node.  The certificate is theorem data, not
semantic soundness, representation adequacy, or target theorem completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryExplicitCurrentShadowCertificates

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportMembership
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteSupportSeparation
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairCurrentShadowCoordinateObligations
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryRepresentationCoordinateExtraction
open SemanticRepairFiniteQueryRepresentationRecoveredFactorization
open SemanticRepairFiniteQuerySupportedCurrentShadowFactorization

universe u v w x y z

/-! ## Coordinate factor certificates -/

/--
A source-trace coordinate has a current-shadow factor when its Bool reading is
computed by a factor on the current canonical shadow.

This is a visible per-coordinate certificate, not an automatic consequence of
support membership or query recovery.
-/
def SourceTraceCoordinateCurrentShadowFactor
    {Atom : Type u}
    (atom : Atom) : Prop :=
  ∃ factor : FiniteTowerLayerShadow -> Bool,
    ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      sourceTraceCoordinateObservation atom T =
        factor (canonicalTowerLayerShadow T)

/--
Current-shadow extensionality of a source-trace coordinate gives its canonical
current-shadow factor.
-/
theorem sourceTraceCoordinateCurrentShadowFactor_of_currentShadowExtensional
    {Atom : Type u}
    {atom : Atom}
    (hcoord :
      SourceTraceCoordinateCurrentShadowExtensional.{u, v, w, x, y} atom) :
    SourceTraceCoordinateCurrentShadowFactor.{u, v, w, x, y} atom := by
  exact
    ⟨canonicalShadowFactor
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        sourceTraceCoordinateObservation atom T),
      shadowExtensionalObservation_factors hcoord⟩

/--
A current-shadow factor for a source-trace coordinate is exactly the
extensionality condition for that coordinate.
-/
theorem sourceTraceCoordinateCurrentShadowExtensional_of_currentShadowFactor
    {Atom : Type u}
    {atom : Atom}
    (hfactor :
      SourceTraceCoordinateCurrentShadowFactor.{u, v, w, x, y} atom) :
    SourceTraceCoordinateCurrentShadowExtensional.{u, v, w, x, y} atom := by
  rcases hfactor with ⟨factor, hfactor⟩
  intro left right hshadow
  calc
    sourceTraceCoordinateObservation atom left =
        factor (canonicalTowerLayerShadow left) := hfactor left
    _ = factor (canonicalTowerLayerShadow right) := by rw [hshadow]
    _ = sourceTraceCoordinateObservation atom right := (hfactor right).symm

/--
Per-coordinate current-shadow factorization is equivalent to per-coordinate
current-shadow extensionality.
-/
theorem sourceTraceCoordinateCurrentShadowFactor_iff_currentShadowExtensional
    {Atom : Type u}
    (atom : Atom) :
    SourceTraceCoordinateCurrentShadowFactor.{u, v, w, x, y} atom ↔
      SourceTraceCoordinateCurrentShadowExtensional.{u, v, w, x, y}
        atom := by
  exact
    ⟨sourceTraceCoordinateCurrentShadowExtensional_of_currentShadowFactor,
      sourceTraceCoordinateCurrentShadowFactor_of_currentShadowExtensional⟩

/-! ## Finite query certificate surface -/

/--
An explicit finite certificate that every coordinate queried by a finite query
has a current-shadow factor.
-/
def QueryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    (query : List Atom) : Prop :=
  ∀ atom : Atom,
    atom ∈ query ->
      SourceTraceCoordinateCurrentShadowFactor.{u, v, w, x, y} atom

/--
A supported finite query certificate packages ordinary query support with the
explicit per-coordinate current-shadow factor certificate.
-/
structure SupportedFiniteQueryCurrentShadowCertificate
    {Atom : Type u}
    (support query : List Atom) : Prop where
  query_supported : QuerySupportedBy support query
  coordinates :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y} query

/-- A query coordinate certificate gives the existing query-coordinate premise. -/
theorem queryCoordinateCurrentShadowExtensional_of_certificate
    {Atom : Type u}
    {query : List Atom}
    (cert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y} query) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      query := by
  intro atom hmem
  exact
    sourceTraceCoordinateCurrentShadowExtensional_of_currentShadowFactor
      (Atom := Atom) (cert atom hmem)

/-- The existing query-coordinate premise gives the explicit factor certificate. -/
theorem certificate_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {query : List Atom}
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y} query := by
  intro atom hmem
  exact
    sourceTraceCoordinateCurrentShadowFactor_of_currentShadowExtensional
      (Atom := Atom) (hcoords atom hmem)

/--
The explicit finite certificate is exactly the existing query-coordinate
current-shadow obligation.
-/
theorem queryCoordinateCurrentShadowExtensional_iff_certificate
    {Atom : Type u}
    (query : List Atom) :
    QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        query ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        query := by
  exact
    ⟨certificate_of_queryCoordinateCurrentShadowExtensional,
      queryCoordinateCurrentShadowExtensional_of_certificate⟩

/--
Cycle 43's support-determinacy premise induces the explicit supported-query
certificate, but does not discharge that premise.
-/
theorem supportedFiniteQueryCurrentShadowCertificate_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support query : List Atom}
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support)
    (hquery : QuerySupportedBy support query) :
    SupportedFiniteQueryCurrentShadowCertificate.{u, v, w, x, y}
      support query where
  query_supported := hquery
  coordinates :=
    certificate_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      (queryCoordinateCurrentShadowExtensional_of_currentShadowDeterminesSupportTraceShadow_of_querySupportedBy
        (Atom := Atom) hcurrent hquery)

/-! ## Certificate-driven current-shadow factorization -/

/-- The explicit query certificate gives query-level current-shadow determinacy. -/
theorem currentShadowDeterminesTraceQuery_of_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    {query : List Atom}
    (cert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y} query) :
    CurrentShadowDeterminesTraceQuery.{u, v, w, x, y} query := by
  exact
    currentShadowDeterminesTraceQuery_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom)
      (queryCoordinateCurrentShadowExtensional_of_certificate
        (Atom := Atom) cert)

/-- Raw query readings factor through the current shadow under the certificate. -/
theorem queryTraceReadings_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    (query : List Atom)
    (cert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y} query) :
    ∃ factor : FiniteTowerLayerShadow -> List Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        supportTraceVector query T.sourceTraceToken =
          factor (canonicalTowerLayerShadow T) := by
  exact
    (queryTraceReadings_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) query).2
      (queryCoordinateCurrentShadowExtensional_of_certificate
        (Atom := Atom) cert)

/--
Generated observations over a supported finite query factor through the current
shadow when the explicit supported-query certificate is supplied.
-/
theorem supportedQueryGeneratedObservation_currentShadowFactor_of_supportedCurrentShadowCertificate
    {Atom : Type u}
    {support query : List Atom}
    {Out : Type z}
    (cert :
      SupportedFiniteQueryCurrentShadowCertificate.{u, v, w, x, y}
        support query)
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        post (canonicalTowerLayerShadow T)
            (supportTraceVector query T.sourceTraceToken) =
          factor (canonicalTowerLayerShadow T) := by
  exact
    supportedQueryGeneratedObservation_currentShadowFactor_of_currentShadowDeterminesSupportTraceShadow
      (Atom := Atom)
      (hcurrent :=
        currentShadowDeterminesSupportTraceShadow_of_coordinateCurrentShadowExtensional
          (Atom := Atom)
          (support := query)
          (queryCoordinateCurrentShadowExtensional_of_certificate
            (Atom := Atom) cert.coordinates))
      (hquery := fun atom hmem => hmem)
      post

/--
Represented finite-query observations factor through the current shadow when
their represented query carries the explicit coordinate certificate.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr : FiniteTraceQueryObservationRepresentation support observe)
    (cert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) :
    ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T) := by
  exact
    representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) repr
      (queryCoordinateCurrentShadowExtensional_of_certificate
        (Atom := Atom) cert)

/-! ## Support-level exact boundary and Bool obstruction -/

/--
Support-level current-shadow determinacy is exactly the family of explicit
current-shadow coordinate factors for the listed support.
-/
theorem currentShadowDeterminesSupportTraceShadow_iff_supportCoordinateCurrentShadowFactors
    {Atom : Type u}
    (support : List Atom) :
    CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
        support ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support := by
  exact
    (currentShadowDeterminesSupportTraceShadow_iff_coordinateCurrentShadowExtensional
      (Atom := Atom) support).trans
      (queryCoordinateCurrentShadowExtensional_iff_certificate
        (Atom := Atom) support)

/--
Singleton query-reading current-shadow factorization gives the corresponding
source-trace coordinate current-shadow factor.
-/
theorem sourceTraceCoordinateCurrentShadowFactor_of_singletonQueryReadings_currentShadowFactor
    {Atom : Type u}
    (atom : Atom)
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> List Bool,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          supportTraceVector [atom] T.sourceTraceToken =
            factor (canonicalTowerLayerShadow T)) :
    SourceTraceCoordinateCurrentShadowFactor.{u, v, w, x, y} atom := by
  have hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        (Atom := Atom) [atom] :=
    (queryTraceReadings_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional
      (Atom := Atom) [atom]).1 hfactor
  exact
    sourceTraceCoordinateCurrentShadowFactor_of_currentShadowExtensional
      (Atom := Atom) (hcoords atom (List.Mem.head _))

/--
A finite family of singleton query-reading factor certificates yields
support-level current-shadow determinacy.
-/
theorem currentShadowDeterminesSupportTraceShadow_of_singletonQueryReadings_currentShadowFactors
    {Atom : Type u}
    {support : List Atom}
    (hfactor :
      ∀ atom : Atom, atom ∈ support ->
        ∃ factor : FiniteTowerLayerShadow -> List Bool,
          ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
            supportTraceVector [atom] T.sourceTraceToken =
              factor (canonicalTowerLayerShadow T)) :
    CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y}
      support := by
  exact
    (currentShadowDeterminesSupportTraceShadow_iff_supportCoordinateCurrentShadowFactors
      (Atom := Atom) support).2
      (by
        intro atom hmem
        exact
          sourceTraceCoordinateCurrentShadowFactor_of_singletonQueryReadings_currentShadowFactor
            (Atom := Atom) atom (hfactor atom hmem))

/--
The Bool `true` coordinate factors through the complete support shadow but has
no current-shadow factor.
-/
theorem boolTrueSourceTraceCoordinate_supportFactor_but_no_currentShadowFactor :
    (∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        sourceTraceCoordinateObservation true T =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              boolCompleteTraceSupport T)) ∧
    ¬ SourceTraceCoordinateCurrentShadowFactor.{0, 0, 0, 0, 0}
      (Atom := Bool) true := by
  exact
    ⟨boolTrueTraceObservation_factors_through_completeBoolSupport,
      fun hfactor =>
        not_boolTrueSourceTraceCoordinateCurrentShadowExtensional
          (sourceTraceCoordinateCurrentShadowExtensional_of_currentShadowFactor
            (Atom := Bool) hfactor)⟩

end SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
end QualitySurface
end ResearchLean.AG
