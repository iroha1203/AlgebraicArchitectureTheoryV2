import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQuerySemanticReadingCertificateExtraction
import ResearchLean.AG.QualitySurface.SemanticRepairTargetFactorization

/-!
Cycle 46 evidence for `G-aat-quality-surface-04`.

Cycle 45 extracted explicit current-shadow coordinate certificates from visible
semantic-reading and recovery data.  This file connects that finite-query route
to the target-surface finite-shadow factorization API: once a represented finite
query observation becomes current-shadow extensional, it is a
`ShadowExtensionalObstructionAssignment` and therefore reads `Obs(A)` through
the canonical target-surface shadow.

This is still a support node.  The no-separation, semantic-reading adequacy, and
recovery premises remain visible finite-query data; they are not arbitrary
semantic observation factorization, target-level representation adequacy,
global coherence, obstruction vanishing, or target theorem completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceFactorization

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQuerySemanticReadingCertificateExtraction
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r s

/-! ## No-separation route to explicit current-shadow certificates -/

/--
Finite no-separation plus realized query-reading recovery extracts the explicit
current-shadow coordinate certificate.

No-separation is visible finite-query data.  It discharges current-shadow
reading faithfulness, but it is not arbitrary representation adequacy.
-/
theorem queryCurrentShadowCoordinateCertificate_of_no_queryPostFiberSeparation_of_queryReadingsRecoveringPostOnRealizedTowers
    {Atom : Type u}
    {query : List Atom}
    {Out : Type s}
    [DecidableEq Out]
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) query post)
    (hrecover :
      QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, s}
        (Atom := Atom) query post) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      query := by
  have hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) query post :=
    (not_queryPostFiberSeparation_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) query post).1 hno
  exact
    queryCurrentShadowCoordinateCertificate_of_semanticReadingAdequacy_of_queryReadingsRecoveringPostOnRealizedTowers
      (Atom := Atom)
      (reading := currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      (currentShadowSemanticReading_collapsesCurrentShadowQueryFibers
        (Atom := Atom) query)
      ((currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) query post).2 hinvariant)
      hrecover

/--
Represented finite-query observations inherit the no-separation / recovery
route to explicit coordinate certificates.
-/
theorem representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      repr.package.query := by
  exact
    queryCurrentShadowCoordinateCertificate_of_no_queryPostFiberSeparation_of_queryReadingsRecoveringPostOnRealizedTowers
      (Atom := Atom)
      hno
      (queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings
        (Atom := Atom) repr hrecover)

/-! ## Represented finite-query observations as shadow-extensional assignments -/

/--
Semantic-reading adequacy plus represented recovery makes the represented
observation shadow-extensional for the canonical target shadow.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensional_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    ShadowExtensionalTowerObservation observe := by
  have hcert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query :=
    representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
      (Atom := Atom) repr hcollapse hfaithful hrecover
  rcases
    representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) repr hcert with
    ⟨factor, hfactor⟩
  exact shadowExtensional_of_factorization factor hfactor

/--
Finite no-separation plus represented recovery makes the represented
observation shadow-extensional.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    ShadowExtensionalTowerObservation observe := by
  have hcert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query :=
    representedFiniteTraceQueryObservation_queryCurrentShadowCoordinateCertificate_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
      (Atom := Atom) repr hno hrecover
  rcases
    representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) repr hcert with
    ⟨factor, hfactor⟩
  exact shadowExtensional_of_factorization factor hfactor

/--
Package a semantically adequate represented finite-query observation as a
shadow-extensional obstruction assignment.
-/
def representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    ShadowExtensionalObstructionAssignment
      (Atom := Atom) Out where
  observe := observe
  shadow_extensional :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
      (Atom := Atom) repr hcollapse hfaithful hrecover

/--
Package a no-separated represented finite-query observation as a
shadow-extensional obstruction assignment.
-/
def representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe) :
    ShadowExtensionalObstructionAssignment
      (Atom := Atom) Out where
  observe := observe
  shadow_extensional :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
      (Atom := Atom) repr hno hrecover

/-! ## Target-surface finite-shadow factorization -/

/--
Semantic-reading adequacy plus represented recovery makes the target-surface
reading factor through the finite shadow of `Obs(A)`.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
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
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe)
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
  have hext : ShadowExtensionalTowerObservation observe :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
      (Atom := Atom) repr hcollapse hfaithful hrecover
  exact
    (targetSurfaceShadowExtensionalObservation_universalFactorization
      (A := A) certificates observe hext).1

/--
No-separation plus represented recovery makes the target-surface reading factor
through the finite shadow of `Obs(A)`.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    [DecidableEq Out]
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe)
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
  have hext : ShadowExtensionalTowerObservation observe :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
      (Atom := Atom) repr hno hrecover
  exact
    (targetSurfaceShadowExtensionalObservation_universalFactorization
      (A := A) certificates observe hext).1

/--
Semantic-reading adequacy plus represented recovery gives the full
target-surface finite-shadow factorization and uniqueness package.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
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
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe)
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
  have hext : ShadowExtensionalTowerObservation observe :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_semanticReadingAdequacy_of_observationRecoversQueryReadings
      (Atom := Atom) repr hcollapse hfaithful hrecover
  exact
    targetSurfaceShadowExtensionalObservation_universalFactorization
      (A := A) certificates observe hext

/--
No-separation plus represented recovery gives the full target-surface
finite-shadow factorization and uniqueness package.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    [DecidableEq Out]
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)
    (hrecover :
      ObservationRecoversQueryReadings.{u, v, w, x, y, s}
        repr.package.query observe)
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
  have hext : ShadowExtensionalTowerObservation observe :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
      (Atom := Atom) repr hno hrecover
  exact
    targetSurfaceShadowExtensionalObservation_universalFactorization
      (A := A) certificates observe hext

end SemanticRepairFiniteQueryTargetSurfaceFactorization
end QualitySurface
end ResearchLean.AG
