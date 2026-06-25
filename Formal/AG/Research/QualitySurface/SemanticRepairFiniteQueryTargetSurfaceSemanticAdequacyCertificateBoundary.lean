import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceCoordinateCertificateBoundary
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQuerySemanticReadingCertificateExtraction

/-!
Cycle 54 evidence for `G-aat-quality-surface-04`.

Cycle 53 recorded that semantic-reading adequacy alone is not recovery or
coordinate certification.  This file records the positive exact boundary:
once a represented finite-query observation visibly recovers its query
readings, semantic-reading adequacy existence is exactly the explicit
query-coordinate current-shadow certificate.  The reverse direction, from a
certificate to semantic-reading adequacy, remains recovery-free.

The theorem package keeps the recovery premise visible.  It does not promote
semantic-reading adequacy or coordinate certificates to target-level semantic
soundness, arbitrary representation adequacy, global coherence, obstruction
vanishing, or target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSemanticAdequacyCertificateBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQuerySemanticReadingCertificateExtraction
open SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
open SemanticRepairFiniteQueryTargetSurfaceCoordinateCertificateBoundary
open SemanticRepairTargetFactorization

universe u v w x y s

/-! ## Semantic-reading adequacy and coordinate certificates -/

/--
An explicit query-coordinate certificate is enough to produce semantic-reading
adequacy for a represented finite-query observation.  This direction does not
use recovery.
-/
theorem representedFiniteTraceQueryObservation_exists_semanticReadingAdequacy_of_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (cert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) :
    ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post := by
  have hentry :
      ∃ assignment :
        ShadowExtensionalObstructionAssignment
          (Atom := Atom) Out,
        assignment.observe = observe :=
    ⟨representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) repr cert,
      rfl⟩
  exact
    (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_exists_semanticReadingAdequacy
      (Atom := Atom) repr).1 hentry

/--
Under visible observation-level recovery, semantic-reading adequacy existence
is exactly the explicit query-coordinate current-shadow certificate.
-/
theorem representedFiniteTraceQueryObservation_exists_semanticReadingAdequacy_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query := by
  constructor
  · rintro ⟨reading, hcollapse, hfaithful⟩
    exact
      representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
        (Atom := Atom) repr hcollapse hfaithful hrecover
  · intro cert
    exact
      representedFiniteTraceQueryObservation_exists_semanticReadingAdequacy_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) repr cert

/--
With visible recovery, missing the explicit coordinate certificate blocks
semantic-reading adequacy existence.
-/
theorem no_representedFiniteTraceQueryObservation_exists_semanticReadingAdequacy_of_not_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe)
    (hnotcert :
      ¬ QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) :
    ¬ ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post := by
  intro hadequacy
  exact
    hnotcert
      ((representedFiniteTraceQueryObservation_exists_semanticReadingAdequacy_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
        (Atom := Atom) repr hrecover).1 hadequacy)

/--
With visible recovery, assignment entry, semantic-reading adequacy existence,
and the explicit coordinate certificate form the same represented finite-query
boundary.
-/
theorem representedFiniteTraceQueryObservation_entry_semanticAdequacy_coordinateCertificate_exact_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    ((∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading repr.package.query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
          (Atom := Atom) reading repr.package.query repr.package.post)) ∧
    ((∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) := by
  exact
    ⟨representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_exists_semanticReadingAdequacy
      (Atom := Atom) repr,
      representedFiniteTraceQueryObservation_exists_semanticReadingAdequacy_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
        (Atom := Atom) repr hrecover⟩

end SemanticRepairFiniteQueryTargetSurfaceSemanticAdequacyCertificateBoundary
end QualitySurface
end Formal.AG.Research
