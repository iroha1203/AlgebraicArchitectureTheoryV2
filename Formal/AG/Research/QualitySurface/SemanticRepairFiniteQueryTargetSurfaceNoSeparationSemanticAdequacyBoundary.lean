import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSemanticAdequacyCertificateBoundary
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSeparationCertificateBoundary

/-!
Cycle 55 evidence for `G-aat-quality-surface-04`.

Cycles 49 and 54 isolate the visible recovery boundary around
no-separation, semantic-reading adequacy, and explicit query-coordinate
certificates.  This file packages that relation as an exact represented
finite-query triangle: with visible recovery and decidable output equality,
semantic-reading adequacy, absence of post-fiber separation, and the coordinate
certificate are the same finite-query boundary.

It also records the recovery-free obstruction side: a separated post-fiber
blocks both semantic-reading adequacy and the coordinate certificate.  These
are finite-query support theorems, not target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceNoSeparationSemanticAdequacyBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryRepresentationNoSeparation
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceSeparationCertificateBoundary
open SemanticRepairFiniteQueryTargetSurfaceSemanticAdequacyCertificateBoundary

universe u v w x y s

/-! ## Exact no-separation / adequacy / certificate triangle -/

/--
With visible recovery, no-separation is exactly the explicit query-coordinate
current-shadow certificate.
-/
theorem representedFiniteTraceQueryObservation_no_queryPostFiberSeparation_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    (¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
      (Atom := Atom) repr.package.query repr.package.post) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query := by
  exact
    (representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_iff_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover).symm

/--
With visible recovery, semantic-reading adequacy, no-separation, and the
explicit coordinate certificate are the same represented finite-query boundary.
-/
theorem representedFiniteTraceQueryObservation_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    ((∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post) ∧
    ((¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
      (Atom := Atom) repr.package.query repr.package.post) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) ∧
    ((∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) := by
  have hsemanticNoSep :
      (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading repr.package.query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
          (Atom := Atom) reading repr.package.query repr.package.post) ↔
        ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
          (Atom := Atom) repr.package.query repr.package.post :=
    representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_no_queryPostFiberSeparation
      (Atom := Atom) repr
  have hnoSepCert :
      (¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post) ↔
        QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
          repr.package.query :=
    representedFiniteTraceQueryObservation_no_queryPostFiberSeparation_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover
  exact
    ⟨hsemanticNoSep, hnoSepCert, hsemanticNoSep.trans hnoSepCert⟩

/--
A separated post-fiber blocks both semantic-reading adequacy and the explicit
query-coordinate certificate.  This obstruction direction is recovery-free.
-/
theorem no_representedFiniteTraceQueryObservation_semanticAdequacy_and_queryCurrentShadowCoordinateCertificate_of_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hsep :
      QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post) :
    (¬ ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      repr.package.query := by
  exact
    ⟨no_representedFiniteTraceQueryObservation_semanticReadingAdequacy_of_queryPostFiberSeparation
      (Atom := Atom) repr hsep,
      no_representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_queryPostFiberSeparation
        (Atom := Atom) repr hsep⟩

end SemanticRepairFiniteQueryTargetSurfaceNoSeparationSemanticAdequacyBoundary
end QualitySurface
end Formal.AG.Research
