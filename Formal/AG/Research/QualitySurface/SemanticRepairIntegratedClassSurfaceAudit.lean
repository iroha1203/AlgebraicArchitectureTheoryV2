import Formal.AG.Research.QualitySurface.SemanticRepairTargetCompletion
import Formal.AG.Research.QualitySurface.SemanticRepairSheafH1Universality
import Formal.AG.Research.QualitySurface.SemanticRepairNonabelianH1Universality
import Formal.AG.Research.QualitySurface.SemanticRepairStackyH2Universality

/-!
Cycle 84 evidence for `G-aat-quality-surface-04`.

Cycles 81--83 added object-level quotient surfaces for sheaf `H1`,
nonabelian repair `H1`, and stacky `H2`.  This file records the target-level
integration audit connecting those quotient surfaces to the comparison-free
integrated finite tower from `SemanticRepairTargetCompletion`.

The bridge is intentionally one-way: integrated layer vanishing data gives
equality of the selected quotient classes with the visible zero/neutral
classes.  The file does not reflect quotient equality back to tower vanishing,
effective descent, stack effectiveness, representation adequacy, or target
theorem completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairIntegratedClassSurfaceAudit

open SemanticRepairObstructionTower
open SemanticRepairSheafH1
open SemanticRepairSheafH1Universality
open SemanticRepairNonabelianTorsor
open SemanticRepairNonabelianH1Universality
open SemanticRepairStackyH2
open SemanticRepairStackyH2Universality
open SemanticRepairTargetCompletion

universe u v w x y z r

/-! ## Visible class-surface equality target -/

/-- The zero sheaf `H1` class used by the integrated class-surface audit. -/
def integratedSheafH1ZeroClass
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom) :
    SemanticRepairH1Class E :=
  semanticRepairH1Class_mk E E.coefficient.zero1
    (semanticRepairSheafH1_zero_is_cocycle E)

/--
The class equalities supplied by the integrated target tower.

This predicate deliberately records only class equalities.  It does not claim
that class equality reflects effective descent or tower vanishing.
-/
def IntegratedLayerClassSurfaceEqualities
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    {torsor : FinitePointedRepairTorsor Choice TorsorRepair}
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence StackRepair}
    (stackRelation : StackyRepairH2ClassRelation stack) : Prop :=
  semanticRepairH1_selectedResidualClass E =
      integratedSheafH1ZeroClass E /\
    nonabelianRepairH1_selectedTransitionClass torsorRelation =
      nonabelianRepairH1_neutralClass torsorRelation /\
    stackyRepairH2_selected2Class stackRelation =
      stackyRepairH2_neutralClass stackRelation

/-! ## Layer predicates give quotient-class equalities -/

/-- Sheaf `H1` zero identifies the selected residual class with the zero class. -/
theorem sheafH1Zero_selectedClass_eq_zeroClass
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    (hzero : SemanticRepairH1Zero E) :
    semanticRepairH1_selectedResidualClass E =
      integratedSheafH1ZeroClass E := by
  exact
    semanticRepairH1Class_eq_of_sameClass
      E
      E.coefficient.residual_cocycle
      (semanticRepairSheafH1_zero_is_cocycle E)
      hzero.2

/--
Visible layer predicates induce the three quotient-class equalities.

The nonabelian and stacky directions use only the safe one-way effectivity
comparisons from Cycles 82 and 83.
-/
theorem integratedLayerClassSurfaceEqualities_of_layerPredicates
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    {torsor : FinitePointedRepairTorsor Choice TorsorRepair}
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence StackRepair}
    (stackRelation : StackyRepairH2ClassRelation stack)
    (hsheaf : SemanticRepairH1Zero E)
    (hnonabelian : EffectiveNonabelianRepairDescent torsor)
    (hstacky : EffectiveStackyRepairDescent stack) :
    IntegratedLayerClassSurfaceEqualities
      E torsorRelation stackRelation := by
  exact
    ⟨sheafH1Zero_selectedClass_eq_zeroClass E hsheaf,
      nonabelianRepairH1_selectedClass_eq_neutral_of_effectiveDescent
        torsorRelation hnonabelian,
      stackyRepairH2_selectedClass_eq_neutral_of_effectiveDescent
        stackRelation hstacky⟩

/-! ## Integrated tower audit bridge -/

/--
The comparison-free integrated finite tower supplies class-surface equalities.

This theorem is one-way from the integrated tower's visible vanishing predicate
to the quotient-class equalities.  It does not use class equality to prove
vanishing and does not close the G-04 target theorem.
-/
theorem integratedTowerVanishes_to_classSurfaceEqualities
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackRelation : StackyRepairH2ClassRelation stack)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) ->
      IntegratedLayerClassSurfaceEqualities
        E torsorRelation stackRelation := by
  intro hvanishes
  have hlayers :
      SemanticRepairH1Zero E /\
        EffectiveNonabelianRepairDescent torsor /\
        StackyRepairH2Zero stack /\
        EffectiveStackyRepairDescent stack :=
    (integratedTower_vanishes_iff_layers E torsor stack).1 hvanishes
  exact
    integratedLayerClassSurfaceEqualities_of_layerPredicates
      E torsorRelation stackRelation
      hlayers.1 hlayers.2.1 hlayers.2.2.2

/--
Cycle 84 checkpoint package.

It bundles the transparent integrated tower equivalence with the safe one-way
class-surface bridge.  The package intentionally has no converse from class
equalities to tower vanishing and is not a target-theorem completion result.
-/
theorem integratedClassSurfaceAudit_checkpoint_package
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackRelation : StackyRepairH2ClassRelation stack)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    (ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) <->
      SemanticRepairH1Zero E /\
        EffectiveNonabelianRepairDescent torsor /\
        StackyRepairH2Zero stack /\
        EffectiveStackyRepairDescent stack) /\
      (ObstructionTowerVanishes
          (toIntegratedSheafTorsorStackTower E torsor stack) ->
        IntegratedLayerClassSurfaceEqualities
          E torsorRelation stackRelation) := by
  exact
    ⟨integratedTower_vanishes_iff_layers E torsor stack,
      integratedTowerVanishes_to_classSurfaceEqualities
        E torsor torsorRelation stack stackRelation⟩

/-! ## Final premise audit for reflection -/

/--
Visible certificate required to use quotient-class equalities in the reverse
direction.

The fields are intentionally strong and explicit.  They are the material
reflection data needed to turn class equalities back into layer predicates.
Without such data, Cycle 84's one-way bridge must not be read as target
completion.
-/
structure IntegratedClassSurfaceReflectionCertificate
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    {torsor : FinitePointedRepairTorsor Choice TorsorRepair}
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence StackRepair}
    (stackRelation : StackyRepairH2ClassRelation stack) where
  sheaf_zero_of_selectedClass_eq_zero :
    semanticRepairH1_selectedResidualClass E =
        integratedSheafH1ZeroClass E ->
      SemanticRepairH1Zero E
  nonabelian_effective_of_selectedClass_eq_neutral :
    nonabelianRepairH1_selectedTransitionClass torsorRelation =
        nonabelianRepairH1_neutralClass torsorRelation ->
      EffectiveNonabelianRepairDescent torsor
  stack_h2Zero_of_selectedClass_eq_neutral :
    stackyRepairH2_selected2Class stackRelation =
        stackyRepairH2_neutralClass stackRelation ->
      StackyRepairH2Zero stack
  stack_effective_of_selectedClass_eq_neutral :
    stackyRepairH2_selected2Class stackRelation =
        stackyRepairH2_neutralClass stackRelation ->
      EffectiveStackyRepairDescent stack

/--
Construct the reflection certificate from visible quotient relations and
explicit descent discharge data.

The certificate is not supplied as an assumption.  Its sheaf field follows
from quotient reflection for the sheaf `H1` setoid.  The nonabelian and stacky
fields first reflect quotient equality to the visible same-class relation, then
use the relation's selected/neutral comparison and the explicit descent
discharge data.
-/
theorem integratedClassSurfaceReflectionCertificate_of_visibleDischarges
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    {torsor : FinitePointedRepairTorsor Choice TorsorRepair}
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    (torsorDischarge :
      NonabelianRepairTorsorDescentDischarge torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence StackRepair}
    (stackRelation : StackyRepairH2ClassRelation stack)
    (stackDischarge : StackyRepairDescentDischarge stack) :
    IntegratedClassSurfaceReflectionCertificate
      E torsorRelation stackRelation where
  sheaf_zero_of_selectedClass_eq_zero := by
    intro heq
    refine ⟨E.coefficient.residual_cocycle, ?_⟩
    exact Quotient.exact heq
  nonabelian_effective_of_selectedClass_eq_neutral := by
    intro heq
    have hsame :
        NonabelianRepairH1SameClass
          torsorRelation
          ⟨torsor.selectedTransition, torsor.selected_cocycle⟩
          ⟨torsor.neutral, torsorRelation.neutral_cocycle⟩ :=
      Quotient.exact heq
    have htrivial : PointedTorsorTrivial torsor :=
      torsorRelation.selected_neutral_iff_trivial.1 hsame
    exact
      (pointedTorsorTrivial_iff_effectiveNonabelianRepairDescent
        torsor torsorDischarge).1 htrivial
  stack_h2Zero_of_selectedClass_eq_neutral := by
    intro heq
    have hsame :
        StackyRepairH2SameClass
          stackRelation
          ⟨stack.selected2Cocycle, stack.selected2_cocycle⟩
          ⟨stack.neutral2, stackRelation.neutral2_cocycle⟩ :=
      Quotient.exact heq
    have htrivial : StackyRepairTrivial stack :=
      stackRelation.selected_neutral_iff_trivial.1 hsame
    exact (stackyH2Zero_iff_stackyRepairTrivial stack).2 htrivial
  stack_effective_of_selectedClass_eq_neutral := by
    intro heq
    have hsame :
        StackyRepairH2SameClass
          stackRelation
          ⟨stack.selected2Cocycle, stack.selected2_cocycle⟩
          ⟨stack.neutral2, stackRelation.neutral2_cocycle⟩ :=
      Quotient.exact heq
    have htrivial : StackyRepairTrivial stack :=
      stackRelation.selected_neutral_iff_trivial.1 hsame
    exact
      (stackyRepairTrivial_iff_effectiveStackyRepairDescent
        stack stackDischarge).1 htrivial

/--
With an explicit reflection certificate, quotient-class equalities recover the
layer predicates used by the integrated target tower.

This is the audited reverse direction.  The certificate is visible theorem
data and is not hidden inside the quotient relation.
-/
theorem classSurfaceEqualities_to_layerPredicates_of_reflectionCertificate
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    {torsor : FinitePointedRepairTorsor Choice TorsorRepair}
    {torsorRelation : NonabelianRepairH1ClassRelation torsor}
    {Coherence : Type z}
    {StackRepair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence StackRepair}
    {stackRelation : StackyRepairH2ClassRelation stack}
    (reflection :
      IntegratedClassSurfaceReflectionCertificate
        E torsorRelation stackRelation) :
    IntegratedLayerClassSurfaceEqualities
        E torsorRelation stackRelation ->
      SemanticRepairH1Zero E /\
        EffectiveNonabelianRepairDescent torsor /\
        StackyRepairH2Zero stack /\
        EffectiveStackyRepairDescent stack := by
  intro hequalities
  exact
    ⟨reflection.sheaf_zero_of_selectedClass_eq_zero hequalities.1,
      reflection.nonabelian_effective_of_selectedClass_eq_neutral
        hequalities.2.1,
      reflection.stack_h2Zero_of_selectedClass_eq_neutral
        hequalities.2.2,
      reflection.stack_effective_of_selectedClass_eq_neutral
        hequalities.2.2⟩

/--
Class-surface equalities imply integrated tower vanishing only after the
reflection certificate is supplied.

This theorem makes the final-premise audit explicit: quotient equality alone
is not used as a substitute for nonabelian descent adequacy, stack
effectiveness, or target completion.
-/
theorem classSurfaceEqualities_to_integratedTowerVanishes_of_reflectionCertificate
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    {torsorRelation : NonabelianRepairH1ClassRelation torsor}
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    {stackRelation : StackyRepairH2ClassRelation stack}
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)]
    (reflection :
      IntegratedClassSurfaceReflectionCertificate
        E torsorRelation stackRelation) :
    IntegratedLayerClassSurfaceEqualities
        E torsorRelation stackRelation ->
      ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) := by
  intro hequalities
  exact
    (integratedTower_vanishes_iff_layers E torsor stack).2
      (classSurfaceEqualities_to_layerPredicates_of_reflectionCertificate
        E reflection hequalities)

/--
Class-surface equalities imply integrated tower vanishing from visible descent
discharge data.

This removes the opaque reflection-certificate argument by constructing the
certificate from quotient reflection, selected/neutral relation data, and the
explicit nonabelian / stacky descent discharges.
-/
theorem classSurfaceEqualities_to_integratedTowerVanishes_of_visibleDischarges
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    (torsorDischarge :
      NonabelianRepairTorsorDescentDischarge torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackRelation : StackyRepairH2ClassRelation stack)
    (stackDischarge : StackyRepairDescentDischarge stack)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    IntegratedLayerClassSurfaceEqualities
        E torsorRelation stackRelation ->
      ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) := by
  exact
    classSurfaceEqualities_to_integratedTowerVanishes_of_reflectionCertificate
      E torsor stack
      (integratedClassSurfaceReflectionCertificate_of_visibleDischarges
        E torsorRelation torsorDischarge stackRelation stackDischarge)

/--
Construct the reflection certificate from a strengthened finite nonabelian
descent certificate and an explicit stacky descent discharge.

This removes the raw nonabelian discharge input without treating the finite
decision certificate as sufficient.  The stacky discharge remains explicit.
-/
theorem integratedClassSurfaceReflectionCertificate_of_nonabelianDescentCertificate
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    {torsor : FinitePointedRepairTorsor Choice TorsorRepair}
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    (torsorCertificate :
      FiniteNonabelianRepairDescentCertificate torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence StackRepair}
    (stackRelation : StackyRepairH2ClassRelation stack)
    (stackDischarge : StackyRepairDescentDischarge stack) :
    IntegratedClassSurfaceReflectionCertificate
      E torsorRelation stackRelation :=
  integratedClassSurfaceReflectionCertificate_of_visibleDischarges
    E torsorRelation
    (nonabelianRepairTorsorDescentDischarge_of_finiteNonabelianRepairDescentCertificate
      torsorCertificate)
    stackRelation stackDischarge

/--
Class-surface equalities imply integrated tower vanishing when the nonabelian
visible discharge is supplied by the strengthened finite descent certificate.

The stacky visible descent discharge is still an explicit premise.
-/
theorem classSurfaceEqualities_to_integratedTowerVanishes_of_nonabelianDescentCertificate
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    (torsorCertificate :
      FiniteNonabelianRepairDescentCertificate torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackRelation : StackyRepairH2ClassRelation stack)
    (stackDischarge : StackyRepairDescentDischarge stack)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    IntegratedLayerClassSurfaceEqualities
        E torsorRelation stackRelation ->
      ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) := by
  exact
    classSurfaceEqualities_to_integratedTowerVanishes_of_visibleDischarges
      E torsor torsorRelation
      (nonabelianRepairTorsorDescentDischarge_of_finiteNonabelianRepairDescentCertificate
        torsorCertificate)
      stack stackRelation stackDischarge

/--
Construct the reflection certificate from strengthened nonabelian and stacky
finite descent certificates.

Both finite decision certificates remain separate from the visible
`effective_of_trivialization` discharge fields.
-/
theorem integratedClassSurfaceReflectionCertificate_of_descentCertificates
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    {torsor : FinitePointedRepairTorsor Choice TorsorRepair}
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    (torsorCertificate :
      FiniteNonabelianRepairDescentCertificate torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    {stack : FiniteStackyRepairH2Envelope Coherence StackRepair}
    (stackRelation : StackyRepairH2ClassRelation stack)
    (stackCertificate :
      FiniteStackyRepairDescentCertificate stack) :
    IntegratedClassSurfaceReflectionCertificate
      E torsorRelation stackRelation :=
  integratedClassSurfaceReflectionCertificate_of_visibleDischarges
    E torsorRelation
    (nonabelianRepairTorsorDescentDischarge_of_finiteNonabelianRepairDescentCertificate
      torsorCertificate)
    stackRelation
    (stackyRepairDescentDischarge_of_finiteStackyRepairDescentCertificate
      stackCertificate)

/--
Class-surface equalities imply integrated tower vanishing when the nonabelian
and stacky visible discharges are both supplied by strengthened finite descent
certificates.
-/
theorem classSurfaceEqualities_to_integratedTowerVanishes_of_descentCertificates
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    (torsorCertificate :
      FiniteNonabelianRepairDescentCertificate torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackRelation : StackyRepairH2ClassRelation stack)
    (stackCertificate :
      FiniteStackyRepairDescentCertificate stack)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    IntegratedLayerClassSurfaceEqualities
        E torsorRelation stackRelation ->
      ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) := by
  exact
    classSurfaceEqualities_to_integratedTowerVanishes_of_visibleDischarges
      E torsor torsorRelation
      (nonabelianRepairTorsorDescentDischarge_of_finiteNonabelianRepairDescentCertificate
        torsorCertificate)
      stack stackRelation
      (stackyRepairDescentDischarge_of_finiteStackyRepairDescentCertificate
        stackCertificate)

/--
Fail-closed final packet checkpoint for the descent-certificate material
premises.

The first component is the strongest currently available reverse bridge:
class-surface equalities imply integrated tower vanishing when both strengthened
descent certificates are supplied.  The remaining components record that the
existing finite/triviality witnesses do not construct those certificates.
Thus a final review packet must keep both strengthened certificates explicit
unless later theorems construct them from stronger non-conclusion data.
-/
theorem finalPacket_descentCertificateMaterialPremiseAudit_checkpoint
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    (torsorCertificate :
      FiniteNonabelianRepairDescentCertificate torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackRelation : StackyRepairH2ClassRelation stack)
    (stackCertificate :
      FiniteStackyRepairDescentCertificate stack)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    (IntegratedLayerClassSurfaceEqualities
        E torsorRelation stackRelation ->
      ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack)) /\
      Not
        (FiniteNonabelianRepairDescentCertificate
          finiteDecisionButNoNonabelianDischargeTorsor) /\
      Not
        (FiniteStackyRepairDescentCertificate
          finiteDecisionButNoStackyDischargeEnvelope) := by
  exact
    ⟨classSurfaceEqualities_to_integratedTowerVanishes_of_descentCertificates
        E torsor torsorRelation torsorCertificate
        stack stackRelation stackCertificate,
      finiteDecisionButNoNonabelianDescentCertificate,
      finiteDecisionButNoStackyDescentCertificate⟩

/--
Cycle 85 final-premise audit package.

It exposes both directions side by side: the existing one-way bridge requires
no extra reflection data, while the reverse direction requires an explicit
`IntegratedClassSurfaceReflectionCertificate`.
-/
theorem integratedClassSurfaceFinalPremiseAudit_checkpoint_package
    {Atom : Type u}
    (E : SemanticRepairSheafH1Envelope.{u, v, w, x, y} Atom)
    {Choice : Type z}
    {TorsorRepair : Type r}
    (torsor : FinitePointedRepairTorsor Choice TorsorRepair)
    (torsorRelation : NonabelianRepairH1ClassRelation torsor)
    {Coherence : Type z}
    {StackRepair : Type r}
    (stack : FiniteStackyRepairH2Envelope Coherence StackRepair)
    (stackRelation : StackyRepairH2ClassRelation stack)
    [Decidable (EffectiveNonabelianRepairDescent torsor)]
    [Decidable (StackyRepairH2Zero stack)]
    [Decidable (EffectiveStackyRepairDescent stack)] :
    (ObstructionTowerVanishes
        (toIntegratedSheafTorsorStackTower E torsor stack) ->
      IntegratedLayerClassSurfaceEqualities
        E torsorRelation stackRelation) /\
      (IntegratedClassSurfaceReflectionCertificate
          E torsorRelation stackRelation ->
        IntegratedLayerClassSurfaceEqualities
          E torsorRelation stackRelation ->
          ObstructionTowerVanishes
            (toIntegratedSheafTorsorStackTower E torsor stack)) := by
  exact
    ⟨integratedTowerVanishes_to_classSurfaceEqualities
        E torsor torsorRelation stack stackRelation,
      fun reflection =>
        classSurfaceEqualities_to_integratedTowerVanishes_of_reflectionCertificate
          E torsor stack reflection⟩

end SemanticRepairIntegratedClassSurfaceAudit
end QualitySurface
end Formal.AG.Research
