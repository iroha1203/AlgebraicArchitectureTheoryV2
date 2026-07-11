import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceRepresentationConstructionBlocker
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryTargetSurfaceSupportBoundarySquare

/-!
Cycle 77 evidence for `G-aat-quality-surface-04`.

Cycle 75 introduced `CurrentShadowTraceReadingRepresentation`; Cycle 76 showed
that finite support/probe completeness and support-shadow self-recovery do not
construct it.  This file fixes the exact adjacent boundary: a concrete
current-shadow trace-reading representation can be constructed from raw
current-shadow factorization of the canonical support-shadow observation, but
that raw factorization is exactly the same support boundary as proposition-level
representability.

Thus raw factorization is a valid construction route, not a weaker adequacy
premise.  It remains visible boundary data and does not discharge target-level
representation adequacy by itself.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceRepresentationAdequacyBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportMembership
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRealizedRecovery
open SemanticRepairFiniteQueryExplicitCurrentShadowCertificates
open SemanticRepairFiniteQueryTargetSurfaceSupportBoundarySquare
open SemanticRepairFiniteQueryTargetSurfaceRepresentationBridge
open SemanticRepairFiniteQueryTargetSurfaceRepresentationConstructionBlocker

universe u v w x y

/-! ## Exact boundary between representation and raw current-shadow factorization -/

/--
Proposition-level current-shadow trace-reading representability is exactly raw
current-shadow factorization of the canonical support-shadow observation.

This is the anti-weakening boundary for any target-level representation
adequacy bridge: assuming the raw factorization face is not weaker than
assuming representability.
-/
theorem currentShadowTraceReadingRepresentable_iff_supportTraceShadowCurrentFactor
    {Atom : Type u}
    (support : List Atom) :
    CurrentShadowTraceReadingRepresentable.{u, v, w, x, y}
        (Atom := Atom) support ↔
      (∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          canonicalSupportTraceProbeTowerLayerShadow support T =
            factor (canonicalTowerLayerShadow T)) := by
  exact
    (currentShadowTraceReadingRepresentable_iff_queryCurrentShadowCoordinateCertificate
      (Atom := Atom) support).trans
      ((supportTraceShadowRepresentation_currentShadowFactor_iff_queryCurrentShadowCoordinateCertificate
        (Atom := Atom) support).symm)

/--
Raw current-shadow factorization gives proposition-level current-shadow
trace-reading representability.
-/
theorem currentShadowTraceReadingRepresentable_of_supportTraceShadowCurrentFactor
    {Atom : Type u}
    {support : List Atom}
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          canonicalSupportTraceProbeTowerLayerShadow support T =
            factor (canonicalTowerLayerShadow T)) :
    CurrentShadowTraceReadingRepresentable.{u, v, w, x, y}
      (Atom := Atom) support := by
  exact
    (currentShadowTraceReadingRepresentable_iff_supportTraceShadowCurrentFactor
      (Atom := Atom) support).2 hfactor

/--
Conversely, proposition-level representability forces raw current-shadow
factorization of the canonical support-shadow observation.
-/
theorem supportTraceShadowCurrentFactor_of_currentShadowTraceReadingRepresentable
    {Atom : Type u}
    {support : List Atom}
    (hrepr :
      CurrentShadowTraceReadingRepresentable.{u, v, w, x, y}
        (Atom := Atom) support) :
    ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T) := by
  exact
    (currentShadowTraceReadingRepresentable_iff_supportTraceShadowCurrentFactor
      (Atom := Atom) support).1 hrepr

/-! ## Concrete construction from the visible raw-factorization face -/

/--
Read one atom's coordinate from a support vector.

For duplicate support entries this returns the first matching coordinate, which
is definitionally the same source-trace value for the same atom.
-/
def readSupportTraceCoordinate
    {Atom : Type u}
    [DecidableEq Atom] :
    List Atom -> List Bool -> Atom -> Bool
  | [], _, _ => false
  | head :: rest, [], atom =>
      if atom = head then false else readSupportTraceCoordinate rest [] atom
  | head :: rest, reading :: readings, atom =>
      if atom = head then reading
      else readSupportTraceCoordinate rest readings atom

/--
Reading a listed atom from the support vector recovers that atom's source-trace
coordinate.
-/
theorem readSupportTraceCoordinate_supportTraceVector_of_mem
    {Atom : Type u}
    [DecidableEq Atom]
    {atom : Atom}
    {traceToken : Atom -> Bool} :
    (support : List Atom) ->
      atom ∈ support ->
        readSupportTraceCoordinate support
            (supportTraceVector support traceToken) atom =
          traceToken atom
  | [], hmem => by
      cases hmem
  | head :: rest, hmem => by
      cases hmem with
      | head =>
          simp [readSupportTraceCoordinate, supportTraceVector]
      | tail _ htail =>
        by_cases heq : atom = head
        · subst heq
          simp [readSupportTraceCoordinate, supportTraceVector]
        · simp [readSupportTraceCoordinate, supportTraceVector, heq,
            readSupportTraceCoordinate_supportTraceVector_of_mem rest htail]

/--
Raw current-shadow factorization of the canonical support-shadow observation
constructs a concrete current-shadow trace-reading representation.

The premise is kept as the raw factorization face.  It is not hidden in a
coordinate-certificate field; the reader is obtained by projecting the factored
support vector.
-/
def currentShadowTraceReadingRepresentation_of_supportTraceShadowCurrentFactor
    {Atom : Type u}
    [DecidableEq Atom]
    {support : List Atom}
    (factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow)
    (hfactor :
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T)) :
    CurrentShadowTraceReadingRepresentation.{u, v, w, x, y}
      (Atom := Atom) support where
  read shadow atom :=
    readSupportTraceCoordinate support
      (factor shadow).sourceTraceReadings atom
  realizes := by
    intro atom hmem T
    have hreadings :
        (factor (canonicalTowerLayerShadow T)).sourceTraceReadings =
          supportTraceVector support T.sourceTraceToken := by
      have h :=
        congrArg TraceProbeFiniteTowerLayerShadow.sourceTraceReadings
          (hfactor T)
      simpa [canonicalSupportTraceProbeTowerLayerShadow] using h.symm
    change
      T.sourceTraceToken atom =
        readSupportTraceCoordinate support
          (factor (canonicalTowerLayerShadow T)).sourceTraceReadings atom
    rw [hreadings]
    exact
      (readSupportTraceCoordinate_supportTraceVector_of_mem
        (Atom := Atom) (atom := atom)
        (traceToken := T.sourceTraceToken) support hmem).symm

/--
An existential raw factorization gives existence of a concrete representation.
Because the conclusion is a proposition, the factor witness can be unpacked
without adding choice to the theorem.
-/
theorem nonempty_currentShadowTraceReadingRepresentation_of_supportTraceShadowCurrentFactor
    {Atom : Type u}
    [DecidableEq Atom]
    {support : List Atom}
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          canonicalSupportTraceProbeTowerLayerShadow support T =
            factor (canonicalTowerLayerShadow T)) :
    Nonempty
      (CurrentShadowTraceReadingRepresentation.{u, v, w, x, y}
        (Atom := Atom) support) := by
  rcases hfactor with ⟨factor, hfactor⟩
  exact
    ⟨currentShadowTraceReadingRepresentation_of_supportTraceShadowCurrentFactor
      (Atom := Atom) factor hfactor⟩

/--
The concrete raw-factorization construction realizes the same certificate
surface used by Cycle 75.
-/
theorem queryCurrentShadowCoordinateCertificate_of_supportTraceShadowCurrentFactor
    {Atom : Type u}
    [DecidableEq Atom]
    {support : List Atom}
    (factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow)
    (hfactor :
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        canonicalSupportTraceProbeTowerLayerShadow support T =
          factor (canonicalTowerLayerShadow T)) :
    QueryCurrentShadowCoordinateCertificate.{u, v, w, x, y}
      support := by
  exact
    queryCurrentShadowCoordinateCertificate_of_currentShadowTraceReadingRepresentation
      (Atom := Atom)
      (currentShadowTraceReadingRepresentation_of_supportTraceShadowCurrentFactor
        (Atom := Atom) factor hfactor)

/-! ## Complete Bool support remains outside the boundary -/

/--
The complete Bool support has no raw current-shadow factorization of its
canonical support-shadow observation.
-/
theorem not_boolCompleteTraceSupport_supportTraceShadowCurrentFactor :
    ¬ ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T =
          factor (canonicalTowerLayerShadow T) := by
  intro hfactor
  exact
    not_boolCompleteTraceSupport_currentShadowTraceReadingRepresentable
      (currentShadowTraceReadingRepresentable_of_supportTraceShadowCurrentFactor
        (Atom := Bool) hfactor)

/--
Complete finite support, support-shadow coordinate factors, and support-shadow
self-recovery coexist with both failures: no raw current-shadow factorization
and no concrete current-shadow trace-reading representation.
-/
theorem boolCompleteSupportTraceShadow_complete_selfRecovery_noCurrentShadowFactor_noRepresentation :
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
    (¬ ∃ factor : FiniteTowerLayerShadow -> TraceProbeFiniteTowerLayerShadow,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T =
          factor (canonicalTowerLayerShadow T)) ∧
    ¬ Nonempty
      (CurrentShadowTraceReadingRepresentation.{0, 0, 0, 0, 0}
        (Atom := Bool) boolCompleteTraceSupport) := by
  exact
    ⟨boolCompleteTraceSupport_complete,
      boolCompleteTraceSupport_supportShadowCoordinateFactors,
      boolCompleteSupportTraceShadow_complete_selfRecovery_noCurrentShadowRepresentation.2.2.1,
      not_boolCompleteTraceSupport_supportTraceShadowCurrentFactor,
      not_nonempty_boolCompleteTraceSupport_currentShadowTraceReadingRepresentation⟩

end SemanticRepairFiniteQueryTargetSurfaceRepresentationAdequacyBoundary
end QualitySurface
end ResearchLean.AG
