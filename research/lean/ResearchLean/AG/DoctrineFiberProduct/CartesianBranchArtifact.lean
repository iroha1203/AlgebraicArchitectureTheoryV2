import ResearchLean.AG.DoctrineFiberProduct.CartesianBranch
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelRealizationULift

/-!
# Typed carrier-global cartesian branch artifact

This module fixes the revised G-110 branch output.  A conditional value carries
one `RightBranch` together with the finite-obstruction transport family indexed
by that same value.  The selected theorem remains the carrier-global left
branch, so no conditional certificate is assumed or manufactured.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

universe u

local instance finiteBranchArtifactAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/--
The endpoint and total-hom graph required of the named finite-obstruction
reflection.  The high input is the canonical rebasing of the low input; both
supplied high lifts and their reflected low lifts retain their package points
and base morphisms.
-/
structure FiniteModelLiftComponentGraph
    (lowInput : RealizableHom FiniteModel.carrier)
    (lowTarget : CoreFiber lowInput.semantic.target)
    (highInput : RealizableHom finiteModelLiftCarrier.{u})
    (highTarget : CoreFiber highInput.semantic.target)
    (reflect : StrongCartesianLift highInput.semantic highTarget →
      StrongCartesianLift lowInput.semantic lowTarget) : Prop where
  highInput_eq : highInput = finiteModelLiftRealizableHom.{u} lowInput
  lowTargetPackage_eq : lowTarget.1 = FiniteModel.corePackage
  highTargetPackage_eq : highTarget.1 = finiteModelLiftCorePackage.{u}
  lowTotalHom : ∀ (lift : StrongCartesianLift highInput.semantic highTarget),
    (packageProjection FiniteModel.carrier).IsHomLift
      lowInput.semantic.hom (reflect lift).hom
  highTotalHom : ∀ (lift : StrongCartesianLift highInput.semantic highTarget),
    (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
      highInput.semantic.hom lift.hom

/--
The right-branch-local finite obstruction family.  Its low endpoints are tied
to the counterexample selected by `right`; its high endpoints live at the
declaration universe.  A right-branch producer must obtain its no-lift proof
through the supplied reflection.
-/
structure RightFiniteModelLiftFamily (right : RightBranch.{u}) where
  finiteCounterexampleInput : RealizableHom FiniteModel.carrier
  finiteCounterexampleTargetPackage :
    CoreFiber finiteCounterexampleInput.semantic.target
  finiteCounterexampleNoLift :
    ¬ HasStrongCartesianLift finiteCounterexampleInput.semantic
      finiteCounterexampleTargetPackage
  rightFiniteCounterexampleInput_eq :
    right.finiteCounterexample.nonexistence.input =
      finiteCounterexampleInput
  rightFiniteCounterexampleTargetPackage_heq :
    HEq right.finiteCounterexample.nonexistence.targetPackage
      finiteCounterexampleTargetPackage
  rightFiniteCounterexample_eq :
    right.finiteCounterexample.nonexistence =
      { input := finiteCounterexampleInput
        targetPackage := finiteCounterexampleTargetPackage
        no_lift := finiteCounterexampleNoLift }
  finiteModelLiftCounterexampleInput :
    RealizableHom finiteModelLiftCarrier.{u}
  finiteModelLiftCounterexampleTargetPackage :
    CoreFiber finiteModelLiftCounterexampleInput.semantic.target
  reflectFiniteModelCounterexampleLift :
    StrongCartesianLift finiteModelLiftCounterexampleInput.semantic
        finiteModelLiftCounterexampleTargetPackage →
      StrongCartesianLift finiteCounterexampleInput.semantic
        finiteCounterexampleTargetPackage
  componentGraph : FiniteModelLiftComponentGraph
    finiteCounterexampleInput finiteCounterexampleTargetPackage
    finiteModelLiftCounterexampleInput
    finiteModelLiftCounterexampleTargetPackage
    reflectFiniteModelCounterexampleLift
  finiteModelLift_noLift :
    ¬ HasStrongCartesianLift
      finiteModelLiftCounterexampleInput.semantic
      finiteModelLiftCounterexampleTargetPackage

/-- The typed conditional payload generated as one branch-local package. -/
structure RightBranchArtifact where
  right : RightBranch.{u}
  finiteModelLift : RightFiniteModelLiftFamily.{u} right

/--
One carrier-global branch choice.  The conditional constructor cannot separate
the qualified right theorem from its named finite-obstruction transport.
-/
inductive DisjunctionArtifact : Type (u + 1)
  | global (proof : GlobalCartesianLift.{u})
  | conditional (proof : RightBranchArtifact.{u})

/-- The sole producer from the carrier-global branch artifact to each regime. -/
def cartesianRegimeOfDisjunction
    (artifact : DisjunctionArtifact.{u}) :
    ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom], CartesianRegime U := by
  intro U _
  cases artifact with
  | global proof => exact .global (proof U)
  | conditional proof => exact .conditional (proof.right.regime U)

/-- The actual G-110 branch artifact generated from the proved global theorem. -/
def globalDisjunctionArtifact : DisjunctionArtifact.{u} :=
  .global globalCartesianLift

/-- A typed right payload is impossible under the selected global branch. -/
theorem rightBranchArtifact_isEmpty : IsEmpty RightBranchArtifact.{u} := by
  refine ⟨?_⟩
  intro artifact
  exact rightBranch_isEmpty.false artifact.right

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

/-- The selected producer supplies the required strong cartesian lift. -/
theorem selectedCartesianRegime_hasStrongCartesianLift
    (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    HasStrongCartesianLift input.semantic targetPackage :=
  CartesianRegime.hasStrongCartesianLift (selectedCartesianRegime U) input
    (selectedCartesianRegime_HCart U input) targetPackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
