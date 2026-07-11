import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceRepresentationAdequacyBoundary
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorSemanticIndependence

/-!
Cycle 78 evidence for `G-aat-quality-surface-04`.

Cycles 75--77 fixed the representation witness, the failed recovery route, and
the exact raw-factorization boundary.  This file records the next guardrail:
any non-circular target-level current-shadow adequacy data that constructs
`CurrentShadowTraceReadingRepresentation` must supply the source-trace
coordinates as current-shadow extensional data.

The point is negative as much as positive.  Semantic-reading adequacy, raw
current-shadow factorization of an unrelated observation, no post-fiber
separation, or target-surface factorization do not by themselves satisfy the
coordinate obligation for the represented query.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceRepresentationAdequacyNecessaryConditions

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportMembership
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryTargetSurfaceCoordinateIndependence
open SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorSemanticIndependence
open SemanticRepairCurrentShadowCoordinateObligations
open SemanticRepairFiniteQueryTargetSurfaceRepresentationBridge
open SemanticRepairFiniteQueryTargetSurfaceRepresentationConstructionBlocker
open SemanticRepairFiniteQueryTargetSurfaceRepresentationAdequacyBoundary

universe u v w x y

/-! ## Representation adequacy necessary coordinate conditions -/

/--
Current-shadow trace-reading representability is exactly the support-coordinate
current-shadow extensionality obligation.

This is the necessary-condition gate for future target-level adequacy data:
constructing representation is not weaker than proving that every listed
source-trace coordinate is extensional for the current canonical shadow.
-/
theorem currentShadowTraceReadingRepresentable_iff_supportTraceCoordinatesCurrentShadowExtensional
    {Atom : Type u}
    (support : List Atom) :
    CurrentShadowTraceReadingRepresentable.{u, v, w, x, y}
        (Atom := Atom) support ↔
      SupportTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
        (Atom := Atom) support := by
  constructor
  · intro hrepr
    have hcert :
        QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
          support :=
      (currentShadowTraceReadingRepresentable_iff_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support).1 hrepr
    exact
      (queryCoordinateCurrentShadowExtensional_iff_certificate
        (Atom := Atom) support).2 hcert
  · intro hcoords
    have hcert :
        QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
          support :=
      (queryCoordinateCurrentShadowExtensional_iff_certificate
        (Atom := Atom) support).1 hcoords
    exact
      (currentShadowTraceReadingRepresentable_iff_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support).2 hcert

/--
A concrete current-shadow trace-reading representation supplies the
support-coordinate current-shadow extensionality obligation.
-/
theorem supportTraceCoordinatesCurrentShadowExtensional_of_currentShadowTraceReadingRepresentation
    {Atom : Type u}
    {support : List Atom}
    (repr :
      CurrentShadowTraceReadingRepresentation.{u, v, w, x, y}
        (Atom := Atom) support) :
    SupportTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
      (Atom := Atom) support := by
  exact
    (currentShadowTraceReadingRepresentable_iff_supportTraceCoordinatesCurrentShadowExtensional
      (Atom := Atom) support).1
      (fun atom hmem =>
        ⟨fun shadow => repr.read shadow atom, repr.realizes atom hmem⟩)

/--
For complete Bool support, the necessary coordinate condition fails.
-/
theorem not_boolCompleteTraceSupport_representationAdequacyNecessaryCoordinates :
    ¬ SupportTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
      (Atom := Bool) boolCompleteTraceSupport := by
  exact not_boolCompleteSupportCoordinatesCurrentShadowExtensional

/--
Complete finite support, support-shadow coordinate factorization, and
support-shadow self-recovery coexist with failure of the coordinate condition
needed by current-shadow representation adequacy.
-/
theorem boolCompleteSupportTraceShadow_complete_selfRecovery_noRepresentationAdequacyNecessaryCoordinates :
    FiniteSupportComplete boolCompleteTraceSupport ∧
    (∀ atom : Bool, atom ∈ boolCompleteTraceSupport ->
      ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
        ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
          sourceTraceCoordinateObservation atom T =
            factor (canonicalSupportTraceProbeTowerLayerShadow
              boolCompleteTraceSupport T)) ∧
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (supportTraceShadowFiniteTraceQueryObservation boolCompleteTraceSupport).query
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) ∧
    ¬ SupportTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
      (Atom := Bool) boolCompleteTraceSupport ∧
    ¬ CurrentShadowTraceReadingRepresentable.{0, 0, 0, 0, 0}
      (Atom := Bool) boolCompleteTraceSupport := by
  exact
    ⟨boolCompleteTraceSupport_complete,
      boolCompleteTraceSupport_supportShadowCoordinateFactors,
      boolCompleteSupportTraceShadow_complete_selfRecovery_noCurrentShadowRepresentation.2.2.1,
      not_boolCompleteTraceSupport_representationAdequacyNecessaryCoordinates,
      not_boolCompleteTraceSupport_currentShadowTraceReadingRepresentable⟩

/-! ## Semantic/factorization routes do not discharge the coordinate condition -/

/--
The Bool constant post-map has raw current-shadow factorization, semantic
adequacy, and no post-fiber separation, but its represented Bool `[true]`
query still fails the source-trace/current-shadow coordinate condition.
-/
theorem boolTrueConstantPost_factor_semanticAdequacy_noSeparation_but_not_representationAdequacyNecessaryCoordinates :
    (∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation
          (fun _shadow _readings => false)).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    (∃ reading : TowerSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{0, 0, 0, 0, 0}
        (Atom := Bool) reading boolTrueTraceQuery ∧
      SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
        (Atom := Bool) reading boolTrueTraceQuery
        (fun _shadow _readings => false)) ∧
    (¬ QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun _shadow _readings => false)) ∧
    ¬ QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
      (Atom := Bool) boolTrueTraceQuery ∧
    ¬ CurrentShadowTraceReadingRepresentable.{0, 0, 0, 0, 0}
      (Atom := Bool) boolTrueTraceQuery := by
  have hcombo :=
    boolTrueConstantPost_currentShadowFactor_semanticAdequacy_noSeparation_but_not_recovery_or_coordinateCertificate
  have hnotCoords :
      ¬ QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
        (Atom := Bool) boolTrueTraceQuery := by
    intro hcoords
    exact
      not_boolTrueTraceQueryCurrentShadowCoordinateCertificate
        ((queryCoordinateCurrentShadowExtensional_iff_certificate
          (Atom := Bool) boolTrueTraceQuery).1 hcoords)
  have hnotRepr :
      ¬ CurrentShadowTraceReadingRepresentable.{0, 0, 0, 0, 0}
        (Atom := Bool) boolTrueTraceQuery := by
    intro hrepr
    exact
      hnotCoords
        ((currentShadowTraceReadingRepresentable_iff_supportTraceCoordinatesCurrentShadowExtensional
          (Atom := Bool) boolTrueTraceQuery).1 hrepr)
  exact
    ⟨hcombo.1,
      hcombo.2.1,
      hcombo.2.2.1,
      hnotCoords,
      hnotRepr⟩

end SemanticRepairFiniteQueryTargetSurfaceRepresentationAdequacyNecessaryConditions
end QualitySurface
end ResearchLean.AG
