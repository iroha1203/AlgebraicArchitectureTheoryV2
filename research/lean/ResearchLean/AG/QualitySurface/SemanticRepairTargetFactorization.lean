import ResearchLean.AG.QualitySurface.SemanticRepairTargetSurface

/-!
Cycle 12 evidence for `G-aat-quality-surface-04`.

This file specializes finite-shadow factorization to the explicit
`S_A/R_A/T_A/St_A` target surface.  The crucial boundary is
`ShadowExtensionalTowerObservation`: arbitrary codomain observations factor
through `Obs(A)` only when they are extensional for the canonical finite
all-layer shadow.

The file also records the necessary condition in the reverse direction:
anything that factors through the canonical finite shadow is necessarily
shadow-extensional.  Thus Cycle 12 narrows the remaining target blocker to the
future task "semantic soundness implies shadow-extensionality / representation
adequacy"; it does not claim unrestricted universality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairTargetFactorization

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTargetSurface

universe u v w x y z r s

/-! ## Shadow-extensional assignments -/

/--
An arbitrary-output obstruction assignment that is extensional for the
canonical finite all-layer shadow.

The extensionality field is a visible material boundary.  It is not global
coherence, tower vanishing, effective descent, or target equivalence.
-/
structure ShadowExtensionalObstructionAssignment
    {Atom : Type u}
    (Out : Type s) where
  observe :
    FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out
  shadow_extensional :
    ShadowExtensionalTowerObservation observe

/-- The canonical finite all-layer shadow of `Obs(A)` from finite certificates. -/
def targetSurfaceLayerShadow
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    FiniteTowerLayerShadow :=
  canonicalTowerLayerShadow (Obs_A_ofFiniteCertificates A certificates)

/-- The factor induced by a shadow-extensional assignment. -/
def shadowExtensionalAssignmentFactor
    {Atom : Type u}
    {Out : Type s}
    (assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out) :
    FiniteTowerLayerShadow -> Out :=
  canonicalShadowFactor assignment.observe

/-- A shadow-extensional assignment factors through the canonical tower shadow. -/
theorem shadowExtensionalAssignment_factors
    {Atom : Type u}
    {Out : Type s}
    (assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    assignment.observe T =
      shadowExtensionalAssignmentFactor assignment
        (canonicalTowerLayerShadow T) := by
  exact
    shadowExtensionalObservation_factors
      assignment.shadow_extensional T

/-- Read the target surface `A` through a shadow-extensional assignment. -/
def targetSurfaceAssignmentReads
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    (assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) : Out :=
  assignment.observe (Obs_A_ofFiniteCertificates A certificates)

/-- Target-surface readings factor through the finite shadow of `Obs(A)`. -/
theorem targetSurfaceAssignment_factors_through_ObsA_shadow
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    (assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    targetSurfaceAssignmentReads assignment A certificates =
      shadowExtensionalAssignmentFactor assignment
        (targetSurfaceLayerShadow A certificates) := by
  exact
    shadowExtensionalAssignment_factors assignment
      (Obs_A_ofFiniteCertificates A certificates)

/-! ## Necessity of shadow-extensionality -/

/--
Any observation that factors through the canonical finite shadow is necessarily
shadow-extensional.

This records the remaining blocker: to prove unrestricted assignment
factorization, one must show semantic soundness implies this extensionality or
enrich the tower so that the assignment becomes extensional.
-/
theorem shadowExtensional_of_factorization
    {Atom : Type u}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (factor : FiniteTowerLayerShadow -> Out)
    (hfactor :
      forall T :
        FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) :
    ShadowExtensionalTowerObservation observe := by
  intro left right hshadow
  calc
    observe left = factor (canonicalTowerLayerShadow left) := hfactor left
    _ = factor (canonicalTowerLayerShadow right) := by rw [hshadow]
    _ = observe right := (hfactor right).symm

/-! ## Target-surface universal factorization package -/

/--
Target-surface specialization of the universal factorization theorem for
shadow-extensional observations.
-/
theorem targetSurfaceShadowExtensionalObservation_universalFactorization
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A)
    (observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out)
    (extensional : ShadowExtensionalTowerObservation observe) :
    (observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates)) /\
      (forall factor : FiniteTowerLayerShadow -> Out,
        (forall T :
          FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
            observe T = factor (canonicalTowerLayerShadow T)) ->
          factor (targetSurfaceLayerShadow A certificates) =
            canonicalShadowFactor observe
              (targetSurfaceLayerShadow A certificates)) := by
  have hfactor :=
    shadowExtensionalObservation_universalFactorization observe extensional
  exact
    ⟨by
        simpa [targetSurfaceLayerShadow] using
          hfactor.1 (Obs_A_ofFiniteCertificates A certificates),
      fun factor hfactor' =>
        hfactor.2 factor hfactor'
          (targetSurfaceLayerShadow A certificates)⟩

/-- The assignment form of target-surface finite-shadow factorization. -/
theorem targetSurfaceShadowExtensionalAssignment_package
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A)
    (assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out) :
    targetSurfaceAssignmentReads assignment A certificates =
      shadowExtensionalAssignmentFactor assignment
        (targetSurfaceLayerShadow A certificates) := by
  exact
    targetSurfaceAssignment_factors_through_ObsA_shadow
      assignment A certificates

end SemanticRepairTargetFactorization
end QualitySurface
end ResearchLean.AG
