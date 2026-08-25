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
branch choice to per-carrier `CartesianRegime` data.  Before a conditional
artifact can serve as a G-110 completion output, its `RightBranch` value must be
paired with the branch-local named-package lift/reflection family specified by
the revised GOAL.
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
right-branch construction must generate this value together with its named
finite-obstruction transport in the revised `RightBranchArtifact` theorem
package.
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
The generated global branch rules out every strong-cartesian no-lift witness,
at every carrier and universe level.  This is the branch-exclusivity fact used
to mark the right-branch `FiniteModelLift` family as not applicable when the
global branch is selected.
-/
theorem cartesianLiftNonexistence_isEmpty (U : AtomCarrier.{u})
    [DecidableEq U.Atom] : IsEmpty (CartesianLiftNonexistence U) := by
  refine ⟨?_⟩
  intro counterexample
  exact counterexample.no_lift
    (globalCartesianLift U counterexample.input counterexample.targetPackage)

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

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
