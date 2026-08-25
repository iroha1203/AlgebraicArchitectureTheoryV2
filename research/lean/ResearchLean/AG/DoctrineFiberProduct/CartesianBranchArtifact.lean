import ResearchLean.AG.DoctrineFiberProduct.CartesianBranch
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedLiftNaturality

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

/-- One semantic input and target package, bundled for dependent lift transport. -/
structure CartesianLiftEndpoint (U : AtomCarrier.{u}) where
  input : CartSemanticInput U
  targetPackage : CoreFiber input.target

namespace CartesianLiftEndpoint

/-- Strong lift type at one bundled endpoint. -/
abbrev Lift {U : AtomCarrier.{u}} (endpoint : CartesianLiftEndpoint U) :=
  StrongCartesianLift endpoint.input endpoint.targetPackage

/-- Transport a strong lift along equality of its complete dependent endpoint. -/
def transportLift {U : AtomCarrier.{u}}
    {first second : CartesianLiftEndpoint U}
    (endpoint_eq : first = second) (lift : first.Lift) : second.Lift := by
  subst second
  exact lift

end CartesianLiftEndpoint

/-- The actual low endpoint selected by a right-branch family. -/
def finiteModelLowEndpoint
    (input : RealizableHom FiniteModel.carrier)
    (targetPackage : CoreFiber input.semantic.target) :
    CartesianLiftEndpoint FiniteModel.carrier :=
  ⟨input.semantic, targetPackage⟩

/-- The actual high endpoint selected by a right-branch family. -/
def finiteModelHighEndpoint
    (input : RealizableHom finiteModelLiftCarrier.{u})
    (targetPackage : CoreFiber input.semantic.target) :
    CartesianLiftEndpoint finiteModelLiftCarrier.{u} :=
  ⟨input.semantic, targetPackage⟩

/-- The named generated low endpoint used by the exact component graph. -/
noncomputable def generatedFiniteModelLowEndpoint
    (input : FiniteGeneratedLiftInput) :
    CartesianLiftEndpoint FiniteModel.carrier :=
  ⟨input.lowInput, input.lowTarget⟩

/-- The named generated high endpoint used by the exact component graph. -/
noncomputable def generatedFiniteModelHighEndpoint
    (input : FiniteGeneratedLiftInput) :
    CartesianLiftEndpoint finiteModelLiftCarrier.{u} :=
  ⟨input.highInput, input.highTarget⟩

/--
The complete endpoint, package, and total-hom graph required of the named
finite-obstruction reflection.  Endpoint equalities transport the supplied
high lift and the reflected low lift to one generated input.  The existing
`ReflectedGeneratedComponentGraph` then retains normalization, generated
naturality, base/projection equations, Atom/object/configuration/equation/
operation/invariant/signature component equations, and domain observations.
-/
structure FiniteModelLiftComponentGraph
    (lowInput : RealizableHom FiniteModel.carrier)
    (lowTarget : CoreFiber lowInput.semantic.target)
    (highInput : RealizableHom finiteModelLiftCarrier.{u})
    (highTarget : CoreFiber highInput.semantic.target)
    (reflect : StrongCartesianLift highInput.semantic highTarget →
      StrongCartesianLift lowInput.semantic lowTarget) where
  generatedInput : FiniteGeneratedLiftInput
  lowEndpoint_eq :
    finiteModelLowEndpoint lowInput lowTarget =
      generatedFiniteModelLowEndpoint generatedInput
  highEndpoint_eq :
    finiteModelHighEndpoint highInput highTarget =
      generatedFiniteModelHighEndpoint.{u} generatedInput
  reflectedLift_eq : ∀
    (lift : StrongCartesianLift highInput.semantic highTarget),
    CartesianLiftEndpoint.transportLift lowEndpoint_eq (reflect lift) =
      generatedInput.lowGeneratedLift
  components : ∀
    (lift : StrongCartesianLift highInput.semantic highTarget),
    ReflectedGeneratedComponentGraph.{u, 0, 0, 0, 0, 0, 0, 0} generatedInput
      (CartesianLiftEndpoint.transportLift highEndpoint_eq lift)
      generatedInput.lowGeneratedLift.hom

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
