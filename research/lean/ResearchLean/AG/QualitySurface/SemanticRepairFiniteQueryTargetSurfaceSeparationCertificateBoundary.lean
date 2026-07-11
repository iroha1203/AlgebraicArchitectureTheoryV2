import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceCoordinateCertificateBoundary

/-!
Cycle 49 evidence for `G-aat-quality-surface-04`.

Cycle 48 made explicit coordinate certificates the represented finite-query
entry boundary for target-surface factorization.  This file connects that
certificate boundary to the post-fiber obstruction side: under visible recovery
and decidable output equality, having the coordinate certificate is exactly the
absence of a separated post-fiber.

The separation blocker for shadow-extensional assignment entry itself does not
need recovery: a represented observation with a separated post-fiber cannot be
shadow-extensional.  The certificate necessity statement still keeps recovery
visible, because assignment entry alone does not force query-coordinate
certificates without a recovery premise.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceSeparationCertificateBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryRepresentationNoSeparation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
open SemanticRepairFiniteQueryTargetSurfaceCoordinateCertificateBoundary
open SemanticRepairTargetFactorization

universe u v w x y s

/-! ## Coordinate certificates and no separated post-fibers -/

/--
An explicit coordinate certificate already excludes a separated post-fiber in
the representing package.

This direction is recovery-free; the certificate gives assignment entry, and
the resulting current-shadow factorization is incompatible with a separated
post-fiber.
-/
theorem representedFiniteTraceQueryObservation_no_queryPostFiberSeparation_of_queryCurrentShadowCoordinateCertificate
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
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
      (Atom := Atom) repr.package.query repr.package.post := by
  intro hsep
  exact
    no_representedFiniteTraceQueryObservation_currentShadowFactor_of_queryPostFiberSeparation
      (Atom := Atom) repr hsep
      (representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) repr cert)

/--
With visible recovery, the explicit coordinate certificate is exactly the
absence of a separated post-fiber in the representing package.
-/
theorem representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_iff_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
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
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post := by
  exact
    (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover).symm.trans
      (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_no_queryPostFiberSeparation
        (Atom := Atom) repr)

/--
Separated post-fibers block explicit coordinate certificates.

This obstruction is recovery-free: the certificate would give current-shadow
factorization, and separation blocks that factorization.
-/
theorem no_representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_queryPostFiberSeparation
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
    ¬ QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      repr.package.query := by
  intro cert
  exact
    (representedFiniteTraceQueryObservation_no_queryPostFiberSeparation_of_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) repr cert) hsep

/-! ## Separation blocks assignment entry -/

/--
A separated post-fiber blocks shadow-extensional assignment entry for the
represented observation.

This obstruction does not need recovery; it follows from the represented
no-separation boundary.
-/
theorem no_representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_queryPostFiberSeparation
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
    ¬ ∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe := by
  intro hentry
  have hext : ShadowExtensionalTowerObservation observe :=
    (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
      (Atom := Atom) repr).1 hentry
  exact
    not_representedFiniteTraceQueryObservation_shadowExtensional_of_queryPostFiberSeparation
      (Atom := Atom) repr hsep hext

end SemanticRepairFiniteQueryTargetSurfaceSeparationCertificateBoundary
end QualitySurface
end ResearchLean.AG
