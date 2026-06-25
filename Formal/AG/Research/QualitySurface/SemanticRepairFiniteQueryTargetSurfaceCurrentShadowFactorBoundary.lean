import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceEntryExactnessBoundary

/-!
Cycle 58 evidence for `G-aat-quality-surface-04`.

Cycle 56 made represented assignment entry exact with semantic-reading
adequacy, no-separation, and explicit coordinate certificates under visible
recovery.  This file adds the raw current-shadow factorization face.

The factorization-to-entry equivalence is recovery-free: both sides are exactly
the represented post-invariance boundary.  The full exact package keeps
`ObservationRecoversQueryReadings` and `[DecidableEq Out]` visible when it
exchanges raw factorization with coordinate certificates and no-separation.
None of these finite-query boundaries is target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryRepresentationPostInvariant
open SemanticRepairFiniteQueryRepresentationNoSeparation
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
open SemanticRepairFiniteQueryTargetSurfaceCoordinateCertificateBoundary
open SemanticRepairFiniteQueryTargetSurfaceNoSeparationSemanticAdequacyBoundary
open SemanticRepairFiniteQueryTargetSurfaceEntryExactnessBoundary
open SemanticRepairTargetFactorization

universe u v w x y s

/-! ## Raw current-shadow factorization and assignment entry -/

/--
For represented finite-query observations, raw current-shadow factorization is
exactly assignment entry.  This equivalence is recovery-free: both sides are
the represented post-invariance boundary.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_iff_entry
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      ∃ assignment :
        ShadowExtensionalObstructionAssignment
          (Atom := Atom) Out,
        assignment.observe = observe := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_postInvariant
      (Atom := Atom) repr).trans
      (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_postInvariant
        (Atom := Atom) repr).symm

/--
With visible recovery and decidable output equality, raw current-shadow
factorization, assignment entry, semantic-reading adequacy, no-separation, and
the explicit coordinate certificate form one exact represented finite-query
boundary.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_entry_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
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
    ((∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      (∃ assignment :
        ShadowExtensionalObstructionAssignment
          (Atom := Atom) Out,
        assignment.observe = observe)) ∧
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
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post) ∧
    ((¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
      (Atom := Atom) repr.package.query repr.package.post) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) ∧
    ((∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) ∧
    ((∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post) := by
  have hfactorEntry :=
    representedFiniteTraceQueryObservation_currentShadowFactor_iff_entry
      (Atom := Atom) repr
  have hentrySemantic :=
    (representedFiniteTraceQueryObservation_entry_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover).1
  have hsemanticNoSep :=
    (representedFiniteTraceQueryObservation_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover).1
  have hnoSepCert :=
    (representedFiniteTraceQueryObservation_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover).2.1
  have hentryCert :=
    representedFiniteTraceQueryObservation_entry_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover
  have hentryNoSep :=
    representedFiniteTraceQueryObservation_entry_iff_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover
  exact
    ⟨hfactorEntry,
      hentrySemantic,
      hsemanticNoSep,
      hnoSepCert,
      hfactorEntry.trans hentryCert,
      hfactorEntry.trans hentryNoSep⟩

/--
A separated post-fiber blocks raw current-shadow factorization, assignment
entry, semantic-reading adequacy, and the coordinate certificate.  This
obstruction direction is recovery-free.
-/
theorem no_representedFiniteTraceQueryObservation_currentShadowFactor_entry_semanticAdequacy_coordinateCertificate_of_queryPostFiberSeparation
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
    (¬ ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ∧
    (¬ ∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ∧
    (¬ ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
        (Atom := Atom) reading repr.package.query repr.package.post) ∧
    ¬ QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      repr.package.query := by
  have hentryBoundary :=
    no_representedFiniteTraceQueryObservation_entry_semanticAdequacy_coordinateCertificate_of_queryPostFiberSeparation
      (Atom := Atom) repr hsep
  exact
    ⟨no_representedFiniteTraceQueryObservation_currentShadowFactor_of_queryPostFiberSeparation
      (Atom := Atom) repr hsep,
      hentryBoundary.1,
      hentryBoundary.2.1,
      hentryBoundary.2.2⟩

end SemanticRepairFiniteQueryTargetSurfaceCurrentShadowFactorBoundary
end QualitySurface
end Formal.AG.Research
