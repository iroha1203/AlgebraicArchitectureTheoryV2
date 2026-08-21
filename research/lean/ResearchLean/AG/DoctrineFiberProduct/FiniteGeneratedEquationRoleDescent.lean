import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationIndexDescent

/-!
# Generated equation-role descent

This module reflects the `role_eq` field read directly from the actual
normalized high factor.  The two generated-domain endpoint graphs compute from
the selected finite-model equation systems, whose complete index families have
the required role.  Between those endpoints, the proof uses the actual high
`EquationSystemExactTransport.role_eq` at the canonically imaged source index.

No pre-existing reflected low role theorem, whole-factor comparison equality,
caller role certificate, or reflexive equation transport is accepted or used.
The canonical low and high generated uppers are used only to prove their
endpoint image graph.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Generated endpoint role graphs -/

/--
The selected finite-model target role is unchanged by canonical index lifting.

This is the only direct computation in the endpoint comparison: both fixed
target equation systems assign the required role to their complete index
families.
-/
theorem finiteModelTargetEquationRole_lift
    (index : FiniteModel.corePackage.algebra.equationSystem.Index) :
    finiteModelLiftCorePackage.{u}.algebra.equationSystem.role
        (FiniteGeneratedLiftInput.targetEquationIndexLift.{u} index) =
      FiniteModel.corePackage.algebra.equationSystem.role index := by
  cases index
  rfl

/--
Every canonical generated-domain index image has the same role as its low
source index.

The proof maps the low index to the fixed target by the canonical low generated
upper, applies the fixed target lift bridge, and returns through the canonical
high generated upper.  These two generated upper `role_eq` fields establish
only the endpoint image graph; they do not supply the reflected role theorem.
-/
theorem finiteGeneratedDomainEquationRole_image
    (input : FiniteGeneratedLiftInput)
    (index : input.lowGeneratedLift.domain.algebra.equationSystem.Index) :
    input.highGeneratedLift.domain.algebra.equationSystem.role
        (finiteGeneratedDomainEquationIndexEquiv.{u} input index) =
      input.lowGeneratedLift.domain.algebra.equationSystem.role index := by
  calc
    input.highGeneratedLift.domain.algebra.equationSystem.role
          (finiteGeneratedDomainEquationIndexEquiv.{u} input index) =
        finiteModelLiftCorePackage.{u}.algebra.equationSystem.role
          (input.highPackageHomFromLowData.upper.equationMap
            (finiteGeneratedDomainEquationIndexEquiv.{u} input index)) :=
      (input.highPackageHomFromLowData.upper.equationTransport.role_eq
        (finiteGeneratedDomainEquationIndexEquiv.{u} input index)).symm
    _ = finiteModelLiftCorePackage.{u}.algebra.equationSystem.role
          (FiniteGeneratedLiftInput.targetEquationIndexLift.{u}
            ((inverseCorePackageForwardUpper FiniteModel.corePackage
              input.hom).equationMap index)) := by
      rw [finiteGeneratedDomainEquationIndexEquiv_apply,
        FiniteGeneratedLiftInput.generatedUpper_equationMap_graph]
    _ = FiniteModel.corePackage.algebra.equationSystem.role
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).equationMap index) :=
      finiteModelTargetEquationRole_lift.{u}
        ((inverseCorePackageForwardUpper FiniteModel.corePackage
          input.hom).equationMap index)
    _ = input.lowGeneratedLift.domain.algebra.equationSystem.role index :=
      (inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).equationTransport.role_eq index

/-! ## The actual high role field -/

/--
The role equality projected at every index directly from the actual normalized
high factor supplied by the strong-cartesian lift.

The definition of the factor is used transparently through its upper
`equationTransport.role_eq` field; no comparison with a canonical whole factor
or known low transport occurs.
-/
theorem finiteGeneratedActualHighEquationRole_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).highGeneratedLift.domain.algebra.equationSystem.Index) :
    input.highGeneratedLift.domain.algebra.equationSystem.role
        (finiteGeneratedActualHighEquationIndexEquiv input lift base index) =
      (finiteGeneratedOuterInput input base).highGeneratedLift.domain.algebra.equationSystem.role
        index := by
  exact
    (finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport.role_eq
      index

/-! ## Reflection to the generated low domains -/

/--
For every generated low source index, the reflected equation-index equivalence
preserves its role exactly.  In this selected finite-model family every role is
`required`; the theorem nevertheless covers the complete generated index type.

The proof first moves both low endpoints to their canonical high images, uses
the Cycle 21 forward index-image graph, consumes the actual normalized high
factor's `role_eq`, and returns through the source endpoint graph.  Thus the
supplied high factor field is a material proof term rather than a decorative
argument.
-/
theorem finiteGeneratedReflectedEquationRole_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index) :
    input.lowGeneratedLift.domain.algebra.equationSystem.role
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index) =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.role
        index := by
  calc
    input.lowGeneratedLift.domain.algebra.equationSystem.role
          (finiteGeneratedReflectedEquationIndexEquiv input lift base index) =
        input.highGeneratedLift.domain.algebra.equationSystem.role
          (finiteGeneratedDomainEquationIndexEquiv.{u} input
            (finiteGeneratedReflectedEquationIndexEquiv input lift base index)) :=
      (finiteGeneratedDomainEquationRole_image.{u} input
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index)).symm
    _ = input.highGeneratedLift.domain.algebra.equationSystem.role
          (finiteGeneratedActualHighEquationIndexEquiv input lift base
            (finiteGeneratedDomainEquationIndexEquiv.{u}
              (finiteGeneratedOuterInput input base) index)) :=
      congrArg input.highGeneratedLift.domain.algebra.equationSystem.role
        (finiteGeneratedReflectedEquationIndex_forward_image.{u}
          input lift base index)
    _ = (finiteGeneratedOuterInput input base).highGeneratedLift.domain.algebra.equationSystem.role
          (finiteGeneratedDomainEquationIndexEquiv.{u}
            (finiteGeneratedOuterInput input base) index) :=
      finiteGeneratedActualHighEquationRole_eq.{u} input lift base
        (finiteGeneratedDomainEquationIndexEquiv.{u}
          (finiteGeneratedOuterInput input base) index)
    _ = (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.role
          index :=
      finiteGeneratedDomainEquationRole_image.{u}
        (finiteGeneratedOuterInput input base) index

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
