import Formal.AG.Research.QualitySurface.SemanticRepairTraceProbeShadow

/-!
Cycle 16 evidence for `G-aat-quality-surface-04`.

This file specializes the finite trace-probe shadow to a supplied finite atom
support.  The canonical probes read the source-trace token on exactly the
listed atoms.  This is a finite-support bridge, not a full trace-completeness
or runtime extraction theorem.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteTraceSupport

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairFiniteShadowSeparation
open SemanticRepairTraceAwareShadow
open SemanticRepairTraceProbeShadow

universe u v w x y z

/-! ## Finite-support trace probes -/

/-- Canonical probes reading a source-trace token on a supplied finite support. -/
def supportTraceProbes
    {Atom : Type u}
    (support : List Atom) : List (SourceTraceProbe Atom) :=
  match support with
  | [] => []
  | atom :: rest =>
      (fun traceToken => traceToken atom) :: supportTraceProbes rest

/-- The source-trace vector restricted to a supplied finite support. -/
def supportTraceVector
    {Atom : Type u}
    (support : List Atom)
    (traceToken : Atom -> Bool) : List Bool :=
  match support with
  | [] => []
  | atom :: rest =>
      traceToken atom :: supportTraceVector rest traceToken

/-- Canonical support probes read exactly the finite support trace vector. -/
theorem traceProbeReadings_supportTraceProbes
    {Atom : Type u} :
    (support : List Atom) ->
    ∀ traceToken : Atom -> Bool,
      traceProbeReadings (supportTraceProbes support) traceToken =
        supportTraceVector support traceToken
  | [], _ => rfl
  | atom :: rest, traceToken =>
      congrArg (List.cons (traceToken atom))
        (traceProbeReadings_supportTraceProbes rest traceToken)

/-- The trace-probe shadow induced by a finite support. -/
def canonicalSupportTraceProbeTowerLayerShadow
    {Atom : Type u}
    (support : List Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    TraceProbeFiniteTowerLayerShadow where
  layer := canonicalTowerLayerShadow T
  sourceTraceReadings := supportTraceVector support T.sourceTraceToken

/-- The direct support shadow agrees with the Cycle 15 generic trace-probe shadow. -/
theorem canonicalSupportTraceProbeTowerLayerShadow_eq_traceProbeShadow
    {Atom : Type u}
    (support : List Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    canonicalSupportTraceProbeTowerLayerShadow support T =
      canonicalTraceProbeTowerLayerShadow (supportTraceProbes support) T := by
  change
    ({ layer := canonicalTowerLayerShadow T
       sourceTraceReadings := supportTraceVector support T.sourceTraceToken } :
        TraceProbeFiniteTowerLayerShadow) =
      { layer := canonicalTowerLayerShadow T
        sourceTraceReadings :=
          traceProbeReadings (supportTraceProbes support) T.sourceTraceToken }
  rw [traceProbeReadings_supportTraceProbes support T.sourceTraceToken]

/-- The finite-support trace shadow projects to the current four-bit shadow. -/
theorem supportTraceProbeShadow_projects_to_currentShadow
    {Atom : Type u}
    (support : List Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (canonicalSupportTraceProbeTowerLayerShadow support T).layer =
      canonicalTowerLayerShadow T := by
  rfl

/-- The finite-support trace shadow stores exactly the support trace vector. -/
theorem supportTraceProbeShadow_sourceTraceReadings_eq
    {Atom : Type u}
    (support : List Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    (canonicalSupportTraceProbeTowerLayerShadow support T).sourceTraceReadings =
      supportTraceVector support T.sourceTraceToken := by
  rfl

/-- The finite support trace vector factors through the support trace shadow. -/
theorem supportTraceVector_factors_through_supportTraceProbeShadow
    {Atom : Type u}
    (support : List Atom) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> List Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        supportTraceVector support T.sourceTraceToken =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow support T) := by
  exact
    ⟨traceProbeVectorFactor,
      by intro T; rfl⟩

/--
Every observation generated from the four-bit layer and the finite support
trace vector factors through the support trace shadow.
-/
theorem supportTraceGeneratedObservation_factors_through_supportTraceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    (support : List Atom)
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        post (canonicalTowerLayerShadow T)
            (supportTraceVector support T.sourceTraceToken) =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow support T) := by
  exact
    ⟨traceProbeGeneratedFactor post,
      by
        intro T
        rfl⟩

/--
Generated observations are extensional for equality of finite-support trace
shadows.
-/
theorem supportTraceGeneratedObservation_same_of_same_supportTraceProbeShadow
    {Atom : Type u}
    {Out : Type z}
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    {support : List Atom}
    (post : FiniteTowerLayerShadow -> List Bool -> Out)
    (hshadow :
      canonicalSupportTraceProbeTowerLayerShadow support left =
        canonicalSupportTraceProbeTowerLayerShadow support right) :
    post (canonicalTowerLayerShadow left)
        (supportTraceVector support left.sourceTraceToken) =
      post (canonicalTowerLayerShadow right)
        (supportTraceVector support right.sourceTraceToken) := by
  simpa [canonicalSupportTraceProbeTowerLayerShadow,
    traceProbeGeneratedFactor] using
    congrArg (traceProbeGeneratedFactor post) hshadow

/--
Support-trace extensionality for the canonical finite-support shadow.
-/
def SupportTraceShadowExtensional
    {Atom : Type u}
    (support : List Atom)
    {Out : Type z}
    (observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out) :
    Prop :=
  ∀ left right : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
    canonicalSupportTraceProbeTowerLayerShadow support left =
      canonicalSupportTraceProbeTowerLayerShadow support right ->
    observe left = observe right

/-- Factorization through the finite-support trace shadow implies extensionality. -/
theorem supportTraceShadowExtensional_of_factorization
    {Atom : Type u}
    {Out : Type z}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (factor : TraceProbeFiniteTowerLayerShadow -> Out)
    (hfactor :
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T =
          factor (canonicalSupportTraceProbeTowerLayerShadow support T)) :
    SupportTraceShadowExtensional support observe := by
  intro left right hshadow
  calc
    observe left = factor (canonicalSupportTraceProbeTowerLayerShadow support left) :=
      hfactor left
    _ = factor (canonicalSupportTraceProbeTowerLayerShadow support right) := by
      rw [hshadow]
    _ = observe right := (hfactor right).symm

/-! ## Cycle 13 witness as a finite support reading -/

/-- The finite support containing the Cycle 13 `PUnit` atom. -/
def selectedSourceTraceSupport : List PUnit.{u + 1} :=
  [PUnit.unit]

/-- The singleton support probes recover the Cycle 15 selected probe family. -/
theorem selectedSourceTraceSupport_probes_eq :
    supportTraceProbes selectedSourceTraceSupport =
      selectedSourceTraceProbeFamily.{u} := by
  rfl

/-- The Cycle 13 source-trace observation factors through singleton support. -/
theorem sourceTraceObservation_factors_through_supportTraceProbeShadow :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
      ∀ T :
        FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0} PUnit.{u + 1},
        sourceTraceObservation T =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              selectedSourceTraceSupport T) := by
  exact
    ⟨fun shadow => shadow.sourceTraceReadings.headD false,
      by intro T; rfl⟩

/--
The Cycle 13 pair is separated by the singleton finite-support trace vector.
-/
theorem selected_traceTrue_supportTraceShadow_readings_ne :
    (canonicalSupportTraceProbeTowerLayerShadow selectedSourceTraceSupport
        (selectedFiniteSemanticRepairObstructionTower :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1})).sourceTraceReadings ≠
      (canonicalSupportTraceProbeTowerLayerShadow selectedSourceTraceSupport
        selectedFiniteSemanticRepairObstructionTower_traceTrue).sourceTraceReadings := by
  decide

/--
The same pair still agrees after forgetting finite-support trace readings back
to the current four-bit shadow.
-/
theorem selected_traceTrue_supportTraceShadow_layer_agrees :
    (canonicalSupportTraceProbeTowerLayerShadow selectedSourceTraceSupport
        (selectedFiniteSemanticRepairObstructionTower :
          FiniteSemanticRepairObstructionTower.{u, 0, 0, 0, 0}
            PUnit.{u + 1})).layer =
      (canonicalSupportTraceProbeTowerLayerShadow selectedSourceTraceSupport
        selectedFiniteSemanticRepairObstructionTower_traceTrue).layer := by
  exact selected_traceTrue_same_canonicalShadow.{u}

end SemanticRepairFiniteTraceSupport
end QualitySurface
end Formal.AG.Research
