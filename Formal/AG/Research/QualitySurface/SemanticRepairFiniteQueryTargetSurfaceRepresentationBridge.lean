import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportBoundaryCertificateGap

/-!
Cycle 75 evidence for `G-aat-quality-surface-04`.

Cycle 74 showed that support-shadow self-recovery does not construct the
current-shadow boundary faces.  This file adds the positive representation
bridge with the boundary kept exact: a current-shadow trace-reading
representation is explicit reader data for support trace coordinates, and it
is equivalent to the existing coordinate-certificate surface.  Thus the
target-surface route can be entered from a non-recovery representation witness,
but the witness is not weaker than the coordinate boundary.

This is a finite support-shadow bridge.  It does not claim arbitrary semantic
observation adequacy, global target-level representation adequacy, full sheaf
universality, tower vanishing, or target theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceRepresentationBridge

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportMembership
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryTargetSurfaceSupportFaithfulnessCertificateRoute
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r

/-! ## Representation witness for current-shadow trace readings -/

/--
A support-level representation witness that reads each listed source-trace
coordinate from the current finite tower shadow.

The field is concrete reader data plus a realization law for listed support
coordinates.  It is intentionally not bundled into `FiniteTraceQueryObservation`
or target-surface data, so the remaining current-shadow boundary is visible.
-/
structure CurrentShadowTraceReadingRepresentation
    {Atom : Type u}
    (support : List Atom) where
  read : FiniteTowerLayerShadow -> Atom -> Bool
  realizes :
    ∀ atom : Atom, atom ∈ support ->
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        sourceTraceCoordinateObservation atom T =
          read (canonicalTowerLayerShadow T) atom

/--
The proposition-level representation boundary: every listed support
coordinate has some current-shadow reader that realizes its source-trace
coordinate.
-/
def CurrentShadowTraceReadingRepresentable
    {Atom : Type u}
    (support : List Atom) : Prop :=
  ∀ atom : Atom, atom ∈ support ->
    ∃ read : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        sourceTraceCoordinateObservation atom T =
          read (canonicalTowerLayerShadow T)

/--
A support-level current-shadow trace-reading representation restricts to any
explicitly supported query and constructs the visible coordinate certificate.
-/
theorem queryCurrentShadowCoordinateCertificate_of_currentShadowTraceReadingRepresentation_of_querySupportedBy
    {Atom : Type u}
    {support query : List Atom}
    (repr :
      CurrentShadowTraceReadingRepresentation.{u, v, w, x, y}
        support)
    (hquery : QuerySupportedBy support query) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      query := by
  intro atom hmem
  exact ⟨fun shadow => repr.read shadow atom, repr.realizes atom (hquery atom hmem)⟩

/--
Specialized to the support itself, the representation witness constructs the
explicit support-coordinate current-shadow certificate.
-/
theorem queryCurrentShadowCoordinateCertificate_of_currentShadowTraceReadingRepresentation
    {Atom : Type u}
    {support : List Atom}
    (repr :
      CurrentShadowTraceReadingRepresentation.{u, v, w, x, y}
        support) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      support := by
  exact
    queryCurrentShadowCoordinateCertificate_of_currentShadowTraceReadingRepresentation_of_querySupportedBy
      (Atom := Atom)
      (support := support)
      (query := support)
      repr
      (fun atom hmem => hmem)

/--
The proposition-level current-shadow trace-reading representation is exactly
the existing support-coordinate certificate surface.  This records the
anti-weakening boundary without choosing representation data from a Prop.
-/
theorem currentShadowTraceReadingRepresentable_iff_queryCurrentShadowCoordinateCertificate
    {Atom : Type u}
    (support : List Atom) :
    CurrentShadowTraceReadingRepresentable.{u, v, w, x, y}
        (Atom := Atom) support ↔
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support := by
  constructor
  · intro hrepr atom hmem
    exact hrepr atom hmem
  · intro hcert atom hmem
    exact hcert atom hmem

/-! ## Representation bridge into the target-surface route -/

/--
The representation witness exposes the coordinate certificate and then enters
the certificate-visible support-shadow target-surface route.
-/
theorem supportTraceShadowRepresentation_currentShadowFaithfulness_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_currentShadowTraceReadingRepresentation
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (support : List Atom)
    (repr :
      CurrentShadowTraceReadingRepresentation.{u, v, w, x, y}
        support)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support ∧
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (supportTraceShadowFiniteTraceQueryObservation support).post ∧
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T) ∧
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, 0}
        (Atom := Atom) reading
        (supportTraceShadowFiniteTraceQueryObservation support).query
        (supportTraceShadowFiniteTraceQueryObservation support).post) ∧
    (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        (supportTraceShadowFiniteTraceQueryObservation support).observe T =
          factor (canonicalTowerLayerShadow T)) ∧
    (((fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor
        (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          (supportTraceShadowFiniteTraceQueryObservation support).observe T)
        (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          (supportTraceShadowFiniteTraceQueryObservation support).observe U =
            factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor
            (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
              (supportTraceShadowFiniteTraceQueryObservation support).observe T)
            (targetSurfaceLayerShadow A certificates))) := by
  have hcert :
      QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
        support :=
    queryCurrentShadowCoordinateCertificate_of_currentShadowTraceReadingRepresentation
      (Atom := Atom) repr
  exact
    ⟨hcert,
      supportTraceShadowRepresentation_currentShadowFaithfulness_recovery_semanticAdequacy_currentShadowFactor_targetSurfaceRoute_of_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support hcert A certificates⟩

end SemanticRepairFiniteQueryTargetSurfaceRepresentationBridge
end QualitySurface
end Formal.AG.Research
