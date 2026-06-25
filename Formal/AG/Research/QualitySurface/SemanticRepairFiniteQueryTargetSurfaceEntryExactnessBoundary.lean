import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceNoSeparationSemanticAdequacyBoundary

/-!
Cycle 56 evidence for `G-aat-quality-surface-04`.

Cycle 55 made semantic-reading adequacy, no post-fiber separation, and explicit
query-coordinate certificates exact under visible recovery.  This file adds the
remaining represented target-surface entry face: with visible recovery and
decidable output equality, assignment entry, semantic-reading adequacy,
no-separation, and the coordinate certificate are the same finite-query
boundary.

The separated-post-fiber obstruction remains recovery-free.  The positive
exactness theorem keeps `ObservationRecoversQueryReadings` and `[DecidableEq
Out]` visible; it does not promote represented finite-query exactness to
target-level semantic soundness, arbitrary representation adequacy, global
coherence, obstruction vanishing, or target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceEntryExactnessBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceSeparationCertificateBoundary
open SemanticRepairFiniteQueryTargetSurfaceSemanticAdequacyCertificateBoundary
open SemanticRepairFiniteQueryTargetSurfaceNoSeparationSemanticAdequacyBoundary
open SemanticRepairTargetFactorization

universe u v w x y s

/-! ## Entry exactness for the represented finite-query boundary -/

/--
Under visible recovery, represented target-surface assignment entry is exactly
the explicit query-coordinate current-shadow certificate.
-/
theorem representedFiniteTraceQueryObservation_entry_iff_queryCurrentShadowCoordinateCertificate_of_observationRecoversQueryReadings
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
  have hpackage :=
    representedFiniteTraceQueryObservation_entry_semanticAdequacy_coordinateCertificate_exact_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover
  exact hpackage.1.trans hpackage.2

/--
With visible recovery and decidable output equality, represented target-surface
assignment entry is exactly absence of post-fiber separation.
-/
theorem representedFiniteTraceQueryObservation_entry_iff_no_queryPostFiberSeparation_of_observationRecoversQueryReadings
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
    (∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post := by
  have hentrySemantic :=
    (representedFiniteTraceQueryObservation_entry_semanticAdequacy_coordinateCertificate_exact_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover).1
  have hsemanticNoSep :=
    (representedFiniteTraceQueryObservation_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
      (Atom := Atom) repr hrecover).1
  exact hentrySemantic.trans hsemanticNoSep

/--
With visible recovery and decidable output equality, assignment entry,
semantic-reading adequacy, no-separation, and the explicit coordinate
certificate form one exact represented finite-query boundary.
-/
theorem representedFiniteTraceQueryObservation_entry_semanticAdequacy_noSeparation_coordinateCertificate_exact_of_observationRecoversQueryReadings
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
    ((∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        repr.package.query) ∧
    ((∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post) := by
  have hentrySemantic :=
    (representedFiniteTraceQueryObservation_entry_semanticAdequacy_coordinateCertificate_exact_of_observationRecoversQueryReadings
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
  exact ⟨hentrySemantic, hsemanticNoSep, hnoSepCert, hentryCert, hentryNoSep⟩

/--
A separated post-fiber blocks assignment entry, semantic-reading adequacy, and
the coordinate certificate.  This obstruction direction is recovery-free.
-/
theorem no_representedFiniteTraceQueryObservation_entry_semanticAdequacy_coordinateCertificate_of_queryPostFiberSeparation
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
  have hblocked :=
    no_representedFiniteTraceQueryObservation_semanticAdequacy_and_queryCurrentShadowCoordinateCertificate_of_queryPostFiberSeparation
      (Atom := Atom) repr hsep
  exact
    ⟨no_representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_queryPostFiberSeparation
      (Atom := Atom) repr hsep,
      hblocked.1,
      hblocked.2⟩

end SemanticRepairFiniteQueryTargetSurfaceEntryExactnessBoundary
end QualitySurface
end Formal.AG.Research
