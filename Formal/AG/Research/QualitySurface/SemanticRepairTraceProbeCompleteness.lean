import Formal.AG.Research.QualitySurface.SemanticRepairFiniteSupportCompleteness

/-!
Cycle 100 evidence for `G-aat-quality-surface-04`.

This file makes finite trace-probe completeness explicit for the generic
`SourceTraceProbe` family introduced by the trace-probe shadow.  Completeness
means only that every source-trace coordinate has a supplied probe in the
finite probe family.  It is not runtime extraction correctness, arbitrary
observation completeness, semantic faithfulness, global coherence, obstruction
vanishing, or descent effectiveness.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairTraceProbeCompleteness

open SemanticRepairObstructionTower
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportMembership
open SemanticRepairFiniteSupportCompleteness

universe u v w x y

/-! ## Explicit trace-probe completeness certificate -/

/--
A supplied finite probe family is coordinate-complete when each source-trace
coordinate is read by some listed probe.

This is a visible certificate over the supplied probes.  It does not say that
the probes were runtime-extracted, complete for arbitrary semantic observations,
or faithful to global repair coherence.
-/
def TraceProbeFamilyComplete
    {Atom : Type u}
    (probes : List (SourceTraceProbe Atom)) : Prop :=
  ∀ atom : Atom,
    ∃ probe : SourceTraceProbe Atom,
      probe ∈ probes ∧
        ∀ traceToken : Atom -> Bool, probe traceToken = traceToken atom

/--
Forget the head trace-probe reading while preserving the four-bit layer.
-/
theorem traceProbeShadowTail_cons
    {Atom : Type u}
    (head : SourceTraceProbe Atom)
    (rest : List (SourceTraceProbe Atom))
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    supportTraceShadowTail
        (canonicalTraceProbeTowerLayerShadow (head :: rest) T) =
      canonicalTraceProbeTowerLayerShadow rest T := by
  rfl

/--
If a probe is listed in the supplied probe family, then that probe reading
factors through the trace-probe shadow.
-/
theorem traceProbeReading_factors_through_traceProbeShadow_of_mem
    {Atom : Type u} :
    (probes : List (SourceTraceProbe Atom)) ->
    {probe : SourceTraceProbe Atom} ->
    probe ∈ probes ->
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        probe T.sourceTraceToken =
          factor (canonicalTraceProbeTowerLayerShadow probes T)
  | [], _, hmem => by
      cases hmem
  | head :: rest, probe, hmem => by
      cases hmem with
      | head =>
          exact
            ⟨fun shadow => shadow.sourceTraceReadings.headD false,
              by
                intro T
                rfl⟩
      | tail _ htail =>
          rcases
            traceProbeReading_factors_through_traceProbeShadow_of_mem
              rest htail with
          ⟨factorRest, hfactorRest⟩
          exact
            ⟨fun shadow => factorRest (supportTraceShadowTail shadow),
              by
                intro T
                simpa [traceProbeShadowTail_cons] using hfactorRest T⟩

/--
Under an explicit probe-family completeness certificate, every source-trace
coordinate factors through the complete trace-probe shadow.
-/
theorem sourceTraceCoordinate_factors_through_completeTraceProbeShadow
    {Atom : Type u}
    {probes : List (SourceTraceProbe Atom)}
    (hcomplete : TraceProbeFamilyComplete probes)
    (atom : Atom) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        T.sourceTraceToken atom =
          factor (canonicalTraceProbeTowerLayerShadow probes T) := by
  rcases hcomplete atom with ⟨probe, hmem, hprobe⟩
  rcases
    (traceProbeReading_factors_through_traceProbeShadow_of_mem
      (Atom := Atom) probes hmem :
      ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          probe T.sourceTraceToken =
            factor (canonicalTraceProbeTowerLayerShadow probes T)) with
  ⟨factor, hfactor⟩
  exact
    ⟨factor,
      by
        intro T
        calc
          T.sourceTraceToken atom = probe T.sourceTraceToken :=
            (hprobe T.sourceTraceToken).symm
          _ = factor (canonicalTraceProbeTowerLayerShadow probes T) :=
            hfactor T⟩

/--
The complete trace-probe shadow is pointwise extensional for source-trace
coordinates.
-/
theorem sourceTraceCoordinates_same_of_same_completeTraceProbeShadow
    {Atom : Type u}
    {probes : List (SourceTraceProbe Atom)}
    (hcomplete : TraceProbeFamilyComplete probes)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalTraceProbeTowerLayerShadow probes left =
        canonicalTraceProbeTowerLayerShadow probes right)
    (atom : Atom) :
    left.sourceTraceToken atom = right.sourceTraceToken atom := by
  rcases
    (sourceTraceCoordinate_factors_through_completeTraceProbeShadow
      (Atom := Atom) hcomplete atom :
      ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          T.sourceTraceToken atom =
            factor (canonicalTraceProbeTowerLayerShadow probes T)) with
  ⟨factor, hfactor⟩
  calc
    left.sourceTraceToken atom =
        factor (canonicalTraceProbeTowerLayerShadow probes left) :=
      hfactor left
    _ = factor (canonicalTraceProbeTowerLayerShadow probes right) := by
      rw [hshadow]
    _ = right.sourceTraceToken atom := (hfactor right).symm

/-! ## Support-completeness compatibility -/

/-- The canonical coordinate probe for a listed support atom is listed. -/
theorem sourceTraceCoordinateProbe_mem_supportTraceProbes
    {Atom : Type u}
    {atom : Atom} :
    (support : List Atom) ->
      atom ∈ support ->
        (fun traceToken : Atom -> Bool => traceToken atom) ∈
          supportTraceProbes support
  | [], hmem => by
      cases hmem
  | head :: rest, hmem => by
      cases hmem with
      | head =>
          exact List.Mem.head _
      | tail _ htail =>
          exact
            List.Mem.tail _
              (sourceTraceCoordinateProbe_mem_supportTraceProbes rest htail)

/--
An explicit complete finite support induces a complete canonical probe family.
-/
theorem traceProbeFamilyComplete_of_finiteSupportComplete_supportTraceProbes
    {Atom : Type u}
    {support : List Atom}
    (hcomplete : FiniteSupportComplete support) :
    TraceProbeFamilyComplete (supportTraceProbes support) := by
  intro atom
  exact
    ⟨fun traceToken : Atom -> Bool => traceToken atom,
      sourceTraceCoordinateProbe_mem_supportTraceProbes support
        (hcomplete atom),
      by intro traceToken; rfl⟩

/-! ## Concrete Bool complete probe family -/

/-- The complete Bool support induces a complete finite probe family. -/
theorem boolCompleteTraceProbeFamily_complete :
    TraceProbeFamilyComplete
      (supportTraceProbes boolCompleteTraceSupport) := by
  exact
    traceProbeFamilyComplete_of_finiteSupportComplete_supportTraceProbes
      boolCompleteTraceSupport_complete

/-! ## Complete trace-probe artifact boundary -/

/--
Under an explicit probe-family completeness certificate, every source-trace
coordinate factors through the bounded trace-probe artifact surface.

This only composes the complete trace-probe shadow factorization with the
Cycle 99 artifact projection.  It is not an ArchSig runtime extraction
correctness theorem or arbitrary observation completeness.
-/
theorem sourceTraceCoordinate_factors_through_completeTraceProbeArtifact
    {Atom : Type u}
    {probes : List (SourceTraceProbe Atom)}
    (hcomplete : TraceProbeFamilyComplete probes)
    (atom : Atom) :
    ∃ factor : TraceProbeArchSigStyleFiniteShadowArtifact -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        T.sourceTraceToken atom =
          factor (traceProbeArchSigStyleArtifactOfTower probes T) := by
  rcases
    (sourceTraceCoordinate_factors_through_completeTraceProbeShadow
      (Atom := Atom) hcomplete atom :
      ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          T.sourceTraceToken atom =
            factor (canonicalTraceProbeTowerLayerShadow probes T)) with
  ⟨shadowFactor, hshadowFactor⟩
  exact
    ⟨fun artifact =>
        shadowFactor (traceProbeArchSigStyleArtifactShadow artifact),
      by
        intro T
        calc
          T.sourceTraceToken atom =
              shadowFactor (canonicalTraceProbeTowerLayerShadow probes T) :=
            hshadowFactor T
          _ =
              shadowFactor
                (traceProbeArchSigStyleArtifactShadow
                  (traceProbeArchSigStyleArtifactOfTower probes T)) := by
            rw [traceProbeArchSigStyleArtifactOfTower_factors_through_traceProbeShadow]⟩

/--
Equality of complete trace-probe artifacts implies pointwise equality of
source-trace coordinates under the visible probe-family completeness
certificate.
-/
theorem sourceTraceCoordinates_same_of_same_completeTraceProbeArtifact
    {Atom : Type u}
    {probes : List (SourceTraceProbe Atom)}
    (hcomplete : TraceProbeFamilyComplete probes)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hartifact :
      traceProbeArchSigStyleArtifactOfTower probes left =
        traceProbeArchSigStyleArtifactOfTower probes right)
    (atom : Atom) :
    left.sourceTraceToken atom = right.sourceTraceToken atom := by
  apply
    sourceTraceCoordinates_same_of_same_completeTraceProbeShadow
      (Atom := Atom) hcomplete
  calc
    canonicalTraceProbeTowerLayerShadow probes left =
        traceProbeArchSigStyleArtifactShadow
          (traceProbeArchSigStyleArtifactOfTower probes left) := by
      rw [traceProbeArchSigStyleArtifactOfTower_factors_through_traceProbeShadow]
    _ =
        traceProbeArchSigStyleArtifactShadow
          (traceProbeArchSigStyleArtifactOfTower probes right) := by
      rw [hartifact]
    _ = canonicalTraceProbeTowerLayerShadow probes right := by
      rw [traceProbeArchSigStyleArtifactOfTower_factors_through_traceProbeShadow]

/--
Under the visible finite probe-family completeness certificate, equality of the
bounded trace-probe artifacts determines the whole source-trace token.

This is still only source-trace extensionality for a supplied complete probe
family.  It is not arbitrary semantic observation adequacy, semantic
faithfulness, or runtime extraction correctness.
-/
theorem sourceTraceToken_same_of_same_completeTraceProbeArtifact
    {Atom : Type u}
    {probes : List (SourceTraceProbe Atom)}
    (hcomplete : TraceProbeFamilyComplete probes)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hartifact :
      traceProbeArchSigStyleArtifactOfTower probes left =
        traceProbeArchSigStyleArtifactOfTower probes right) :
    left.sourceTraceToken = right.sourceTraceToken := by
  funext atom
  exact
    sourceTraceCoordinates_same_of_same_completeTraceProbeArtifact
      (Atom := Atom) hcomplete hartifact atom

end SemanticRepairTraceProbeCompleteness
end QualitySurface
end Formal.AG.Research
