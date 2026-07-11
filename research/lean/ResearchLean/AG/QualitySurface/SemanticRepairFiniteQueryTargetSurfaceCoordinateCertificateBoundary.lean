import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryExplicitCurrentShadowCertificates

/-!
Cycle 48 evidence for `G-aat-quality-surface-04`.

Cycle 47 isolated the recovery-free target-surface admissibility boundary:
represented finite-query observations factor through the target-surface finite
shadow once they visibly enter the `ShadowExtensionalTowerObservation` fence.
This file connects that fence to the explicit coordinate-certificate surface.

The positive direction needs only a visible
`QueryCurrentShadowCoordinateCertificate`.  The reverse direction is stated
only under visible `ObservationRecoversQueryReadings`: recovery makes assignment
entry force the queried coordinates to be current-shadow certified.  Recovery is
therefore not hidden representation adequacy; it is a visible theorem argument
for certificate necessity.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceCoordinateCertificateBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryRepresentationRecoveredFactorization
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r s

/-! ## Coordinate certificates as target-surface entry data -/

/--
An explicit query-coordinate current-shadow certificate makes a represented
finite-query observation shadow-extensional.

The certificate is visible theorem data.  It is not target-level semantic
soundness, representation adequacy, or target theorem completion.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensional_of_queryCurrentShadowCoordinateCertificate
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
    ShadowExtensionalTowerObservation observe := by
  rcases
    representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) repr cert with
    ⟨factor, hfactor⟩
  exact shadowExtensional_of_factorization factor hfactor

/--
An explicit query-coordinate current-shadow certificate packages a represented
finite-query observation as a shadow-extensional obstruction assignment.
-/
def representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_queryCurrentShadowCoordinateCertificate
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
    ShadowExtensionalObstructionAssignment
      (Atom := Atom) Out where
  observe := observe
  shadow_extensional :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) repr cert

/--
The explicit coordinate certificate is sufficient for target-surface
finite-shadow factorization.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (cert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates) := by
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_shadowExtensional
      (Atom := Atom) repr
      (representedFiniteTraceQueryObservation_shadowExtensional_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) repr cert)
      A certificates

/--
The explicit coordinate certificate gives the full target-surface
factorization and uniqueness package.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (cert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    (observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe U = factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor observe
            (targetSurfaceLayerShadow A certificates)) := by
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_shadowExtensional
      (Atom := Atom) repr
      (representedFiniteTraceQueryObservation_shadowExtensional_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) repr cert)
      A certificates

/-! ## Recovery makes coordinate certificates necessary for assignment entry -/

/--
Under visible query-reading recovery, raw current-shadow factorization is
exactly the explicit coordinate certificate.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
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
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_queryCoordinateCurrentShadowExtensional_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover).trans
      (queryCoordinateCurrentShadowExtensional_iff_certificate
        (Atom := Atom) repr.package.query)

/--
Under visible query-reading recovery, assignment entry is exactly the explicit
query-coordinate current-shadow certificate.

The recovery premise is visible theorem data; it is not packaged as target
semantic soundness or representation adequacy.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
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
    (∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query := by
  constructor
  · intro hentry
    have hext : ShadowExtensionalTowerObservation observe :=
      (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
        (Atom := Atom) repr).1 hentry
    have hcoords :
        QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y}
          repr.package.query :=
      representedFiniteTraceQueryObservation_queryCoordinateCurrentShadowExtensional_of_shadowExtensional_of_observationRecoversQueryReadings
        (Atom := Atom) repr hext hrecover
    exact
      (queryCoordinateCurrentShadowExtensional_iff_certificate
        (Atom := Atom) repr.package.query).1 hcoords
  · intro cert
    exact
      (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
        (Atom := Atom) repr).2
        (representedFiniteTraceQueryObservation_shadowExtensional_of_queryCurrentShadowCoordinateCertificate
          (Atom := Atom) repr cert)

/--
With visible recovery, lack of the explicit coordinate certificate blocks
shadow-extensional assignment entry.
-/
theorem no_representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_not_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
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
    ¬ ∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe := by
  intro hentry
  exact
    hnotcert
      ((representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
        (Atom := Atom) repr hrecover).1 hentry)

end SemanticRepairFiniteQueryTargetSurfaceCoordinateCertificateBoundary
end QualitySurface
end ResearchLean.AG
