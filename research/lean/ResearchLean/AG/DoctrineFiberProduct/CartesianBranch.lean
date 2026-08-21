import ResearchLean.AG.DoctrineFiberProduct.CartesianTarget

/-!
# Carrier-global cartesian branch artifact and regime producer

This module fixes the remaining branch-selection surface of the G-110
cartesian layer.  A right-branch value must use one authored structural syntax
template at universe zero and its canonical rebasing at every carrier; the
checker bridges therefore prevent carrier-by-carrier semantic target fitting.
The right theorem output also contains its own nondegenerate positive family
and finite condition-failing no-lift witness.

The actual artifact selects the already proved carrier-global left branch.
`cartesianRegimeOfDisjunction` is the sole exported producer from the global
branch choice to per-carrier `CartesianRegime` data.  The separate canonical
`FiniteModelLift` package/lift-reflection obligation is not encoded as a right-
branch field here: accepting it as a field would reintroduce the certificate
escape rejected by F0c2.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

universe u

/-- Executable Atom equality for the universe-zero finite condition template. -/
local instance finiteCartesianBranchAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## The carrier-global right theorem-output surface -/

/--
The complete theorem output of the conditional cartesian branch at one
universe level.  `template`, `base_term`, and `regime_term` force every
carrier's qualified semantic predicate to be governed by the same frozen
structural syntax through its checker bridge.  The positive family and finite
counterexample are mathematical outputs, not fields of a presentation.

No value of this structure is assumed by the selected left branch.  A genuine
right-branch construction would additionally have to use the separately named
canonical `FiniteModelLift` theorem to transport its finite obstruction; that
result is deliberately not accepted as a field here.
-/
structure RightBranch : Type (u + 1) where
  /-- Carrier-independent authored condition template at the finite base carrier. -/
  template : CartConditionSyntax FiniteModel.carrier
  /-- Qualified right regime on the finite base carrier. -/
  baseRegime : RightCartesianRegime FiniteModel.carrier
  /-- The base regime uses exactly the authored template. -/
  base_term : baseRegime.condition.term = template
  /-- Qualified right regime on every carrier at this universe level. -/
  regime : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom],
    RightCartesianRegime U
  /-- Every carrier regime uses the canonical rebase of the one authored template. -/
  regime_term : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom],
    (regime U).condition.term = rebaseCartCondition template
  /-- The same base condition fires on a nondegenerate family with actual lifts. -/
  positiveFamily : ParametricCartPositiveFamily baseRegime.condition
  /-- The same base condition excludes an explicit finite no-lift input. -/
  finiteCounterexample : CartesianLiftCounterexample baseRegime.condition

/--
The proved carrier-global left branch rules out any value of the conditional
theorem-output structure: its base counterexample contradicts the generated
universe-zero lift.  This supplies the negative instance required for the new
certificate surface without manufacturing a right-branch value.
-/
theorem rightBranch_isEmpty : IsEmpty RightBranch.{u} := by
  refine ⟨?_⟩
  intro right
  let counterexample := right.finiteCounterexample.nonexistence
  exact counterexample.no_lift
    (globalCartesianLift FiniteModel.carrier counterexample.input
      counterexample.targetPackage)

/-! ## One global branch choice and its sole per-carrier producer -/

/--
One carrier-global branch choice.  The quantifier over carriers occurs inside
each constructor payload, so this cannot degenerate to a per-carrier choice.
-/
inductive DisjunctionArtifact : Type (u + 1)
  /-- The unconditional carrier-global lift theorem was selected. -/
  | global (proof : GlobalCartesianLift.{u})
  /-- One uniform qualified conditional theorem was selected. -/
  | conditional (proof : RightBranch.{u})

/--
The required producer from one carrier-global branch artifact to every
per-carrier regime.  Later G-110 layers must consume this output rather than an
arbitrary caller-supplied `CartesianRegime`.
-/
def cartesianRegimeOfDisjunction
    (artifact : DisjunctionArtifact.{u}) :
    ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom], CartesianRegime U := by
  intro U _
  cases artifact with
  | global proof => exact .global (proof U)
  | conditional proof => exact .conditional (proof.regime U)

/-- The actual G-110 branch artifact generated from the proved global theorem. -/
def globalDisjunctionArtifact : DisjunctionArtifact.{u} :=
  .global globalCartesianLift

/-- The selected per-carrier regime, produced only from the named global artifact. -/
def selectedCartesianRegime (U : AtomCarrier.{u})
    [DecidableEq U.Atom] : CartesianRegime U :=
  cartesianRegimeOfDisjunction globalDisjunctionArtifact U

/-- The selected regime is definitionally the global branch instantiated at the carrier. -/
theorem selectedCartesianRegime_eq_global (U : AtomCarrier.{u})
    [DecidableEq U.Atom] :
    selectedCartesianRegime U = .global (globalCartesianLift U) :=
  rfl

/-- Every realized arrow belongs to the regime produced by the selected artifact. -/
theorem selectedCartesianRegime_HCart (U : AtomCarrier.{u})
    [DecidableEq U.Atom] (input : RealizableHom U) :
    (selectedCartesianRegime U).HCart input := by
  trivial

/--
The selected producer supplies an actual strong cartesian lift for every
realized arrow and endpoint package through the ordinary regime eliminator.
-/
theorem selectedCartesianRegime_hasStrongCartesianLift
    (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    HasStrongCartesianLift input.semantic targetPackage :=
  CartesianRegime.hasStrongCartesianLift (selectedCartesianRegime U) input
    (selectedCartesianRegime_HCart U input) targetPackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
