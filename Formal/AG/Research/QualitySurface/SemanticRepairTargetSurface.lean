import Formal.AG.Research.QualitySurface.SemanticRepairTargetCompletion

/-!
Cycle 11 evidence for `G-aat-quality-surface-04`.

This file makes the target-level objects in the GOAL card explicit.  A
`UniversalSemanticRepairTargetSurface` carries the semantic repair site `S_A`,
the residual coefficient sheaf `R_A`, the nonabelian repair-choice torsor
`T_A`, and the stack-valued repair descent object `St_A`.  The surface is only
input geometry; it does not store global coherence, obstruction vanishing, or
effective descent.

The finite certificate package is also kept outside the surface.  It supplies
finite boundary semantic closure and finite layer decision completeness, then
reuses the integrated sheaf / torsor / stack theorem package from Cycle 10.
This is a target-strength surface checkpoint, not a final completion verdict.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairTargetSurface

open SemanticRepairObstructionTower
open SemanticRepairAdequacyDischarge
open SemanticRepairUniversalShadow
open SemanticRepairSheafH1
open SemanticRepairNonabelianTorsor
open SemanticRepairStackyH2
open SemanticRepairTargetCompletion

universe u v w x y z r s

/-! ## Explicit target-level objects -/

/--
Explicit target surface for the universal semantic repair obstruction tower.

The fields are the objects named in the GOAL card: `S_A`, `R_A`, `T_A`, and
`St_A`.  No field asserts global coherence, obstruction vanishing, effective
descent, tower universality, or a selected obstruction value.
-/
structure UniversalSemanticRepairTargetSurface
    (Atom : Type u)
    (Choice : Type z)
    (TorsorRepair : Type r)
    (Coherence : Type z)
    (StackRepair : Type r) where
  sheaf : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom
  torsor : FinitePointedRepairTorsor Choice TorsorRepair
  stack : FiniteStackyRepairH2Envelope Coherence StackRepair

/-- The semantic repair site `S_A` of a target surface. -/
def S_A
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair) :
    SemanticRepairSite.{u, v} Atom :=
  A.sheaf.site

/-- The residual coefficient sheaf `R_A` of a target surface. -/
def R_A
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair) :
    SemanticResidualCoefficientSheaf.{u, v, w, x, y} (S_A A) :=
  A.sheaf.coefficient

/-- The nonabelian repair-choice torsor object `T_A`. -/
def T_A
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair) :
    FinitePointedRepairTorsor Choice TorsorRepair :=
  A.torsor

/-- The stack-valued repair descent object `St_A`. -/
def St_A
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair) :
    FiniteStackyRepairH2Envelope Coherence StackRepair :=
  A.stack

theorem targetSurface_objects_are_explicit
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair) :
    S_A A = A.sheaf.site /\
      R_A A = A.sheaf.coefficient /\
      T_A A = A.torsor /\
      St_A A = A.stack := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Target obstruction tower and finite certificates -/

/-- The obstruction tower `Obs(A)` induced by the explicit target surface. -/
def Obs_A
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [Decidable (EffectiveNonabelianRepairDescent A.torsor)]
    [Decidable (StackyRepairH2Zero A.stack)]
    [Decidable (EffectiveStackyRepairDescent A.stack)] :
    FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom :=
  toIntegratedSheafTorsorStackTower A.sheaf A.torsor A.stack

/--
Concrete finite certificates for a target surface.

These certificates carry finite boundary semantic closure and finite list
completeness for the torsor / stack layers.  They do not contain global
coherence, tower vanishing, sheaf `H1` zero, nonabelian descent, or stacky
descent as fields.
-/
structure UniversalSemanticRepairTargetCertificates
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair) where
  boundary :
    FiniteBoundarySemanticClosureCertificate (toFiniteTower A.sheaf)
  torsor :
    FiniteNonabelianRepairDecisionCertificate A.torsor
  stack :
    FiniteStackyRepairDecisionCertificate A.stack

/--
Target-surface semantic faithfulness discharge from the visible finite
boundary certificate.

This is only the sheaf-side exactness discharge: it does not use or store
global coherence, obstruction vanishing, effective descent, torsor triviality,
stack effectiveness, or finite-shadow completeness.
-/
def targetSurface_semanticFaithfulnessDischarge_of_finiteCertificates
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    SemanticRepairSheafH1ExactnessDischarge A.sheaf :=
  sheafH1ExactnessDischarge_of_finiteBoundaryCertificate
    certificates.boundary

/--
Every target-surface primitive whose boundary is the selected residual is
semantically closed, provided by the finite boundary certificate.
-/
theorem targetSurface_boundaryPrimitiveSemanticallyClosed_of_finiteCertificates
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    (certificates : UniversalSemanticRepairTargetCertificates A)
    (primitive : A.sheaf.coefficient.C0)
    (hboundary :
      A.sheaf.coefficient.delta0 primitive =
        A.sheaf.coefficient.residual) :
    A.sheaf.primitiveSemanticallyClosed primitive := by
  exact
    (targetSurface_semanticFaithfulnessDischarge_of_finiteCertificates
      A certificates).semanticFaithful_of_boundary primitive hboundary

/-- The finite-certificate version of `Obs(A)`. -/
def Obs_A_ofFiniteCertificates
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
    FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom :=
  toIntegratedSheafTorsorStackTowerOfFiniteCertificates
    A.sheaf certificates.boundary
    A.torsor certificates.torsor
    A.stack certificates.stack

/-! ## Target-surface theorem package -/

/--
Universal semantic repair obstruction tower package over explicit
`S_A/R_A/T_A/St_A` objects and concrete finite certificates.

The theorem exposes well-definedness of the sheaf, torsor, and stacky selected
obstruction components, the all-layer vanish / global coherence equivalence,
and the canonical finite-shadow factorization.  Remaining target-completion
work is the fully general universality / functoriality audit and T6 review.
-/
theorem universalSemanticRepairTargetSurface_package_of_finiteCertificates
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
    CechZ1 A.sheaf A.sheaf.coefficient.residual /\
      NonabelianCechZ1 A.torsor A.torsor.selectedTransition /\
      StackyCechZ2 A.stack A.stack.selected2Cocycle /\
      (ObstructionTowerVanishes (Obs_A_ofFiniteCertificates A certificates) <->
        SemanticRepairH1Zero A.sheaf /\
          EffectiveNonabelianRepairDescent A.torsor /\
          StackyRepairH2Zero A.stack /\
          EffectiveStackyRepairDescent A.stack) /\
      (GlobalSemanticRepairCoherent
          (Obs_A_ofFiniteCertificates A certificates) <->
        SemanticRepairH1Zero A.sheaf /\
          EffectiveNonabelianRepairDescent A.torsor /\
          StackyRepairH2Zero A.stack /\
          EffectiveStackyRepairDescent A.stack) /\
      (forall assignment : SoundAllLayerObstructionAssignment,
        assignmentLayerShadow assignment
            (Obs_A_ofFiniteCertificates A certificates) =
          assignmentReadsShadow assignment
            (canonicalTowerLayerShadow
              (Obs_A_ofFiniteCertificates A certificates))) /\
      (forall (Obs : Type s)
          (observe :
            FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Obs),
        ShadowExtensionalTowerObservation observe ->
          (forall U,
            observe U =
              canonicalShadowFactor observe (canonicalTowerLayerShadow U)) /\
          (forall factor : FiniteTowerLayerShadow -> Obs,
            (forall U :
              FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
                observe U = factor (canonicalTowerLayerShadow U)) ->
              forall shadow,
                factor shadow =
                  canonicalShadowFactor observe shadow)) := by
  letI : Decidable (EffectiveNonabelianRepairDescent A.torsor) :=
    effectiveNonabelianRepairDescentDecisionOfCertificate
      A.torsor certificates.torsor
  letI : Decidable (StackyRepairH2Zero A.stack) :=
    stackyRepairH2ZeroDecisionOfCertificate
      A.stack certificates.stack
  letI : Decidable (EffectiveStackyRepairDescent A.stack) :=
    effectiveStackyRepairDescentDecisionOfCertificate
      A.stack certificates.stack
  refine
    ⟨semanticRepairSheafH1_wellDefined A.sheaf,
      nonabelianRepairTorsor_wellDefined A.torsor,
      stackyRepairH2_wellDefined A.stack,
      ?_,
      ?_,
      ?_,
      ?_⟩
  · simpa [Obs_A_ofFiniteCertificates,
      toIntegratedSheafTorsorStackTowerOfFiniteCertificates] using
      integratedTower_vanishes_iff_layers A.sheaf A.torsor A.stack
  · simpa [Obs_A_ofFiniteCertificates,
      toIntegratedSheafTorsorStackTowerOfFiniteCertificates] using
      integratedTower_globalCoherent_iff_layers
        A.sheaf
        (sheafH1ExactnessDischarge_of_finiteBoundaryCertificate
          certificates.boundary)
        A.torsor A.stack
  · intro assignment
    simpa [Obs_A_ofFiniteCertificates,
      toIntegratedSheafTorsorStackTowerOfFiniteCertificates] using
      soundAllLayerAssignment_factors_through_tower assignment
        (toIntegratedSheafTorsorStackTower A.sheaf A.torsor A.stack)
  · intro Obs observe extensional
    exact
      shadowExtensionalObservation_universalFactorization
        (Obs := Obs) observe extensional

end SemanticRepairTargetSurface
end QualitySurface
end Formal.AG.Research
