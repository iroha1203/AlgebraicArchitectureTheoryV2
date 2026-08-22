import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationIndexDescent

/-!
# Generated detector-law descent

This module reflects the `detectorCode_eq` field of the actual normalized high
factor to the two generated low domains.  The proof compares the low detector
codes only through their canonical high images, consumes the actual high
`detectorCode_eq` at every generated source index, and then returns by the
injectivity of finite detector-code lifting.

No known low factor, complete upper morphism, caller image certificate, or
whole-factor comparison equality is used.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Actual high Atom and detector fields -/

/--
The actual high Atom equivalence is exactly the carrier lift of its reflected
Atom equivalence.  This is a field-level conjugation equality, not a rewrite of
the complete normalized factor.
-/
theorem finiteGeneratedActualHighAtomEquiv_eq_lift_reflected
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteModelLiftCarrierEquiv.{u}.atom.symm.trans
        ((finiteGeneratedReflectedUpperAtomEquiv input lift base).trans
          finiteModelLiftCarrierEquiv.{u}.atom) =
      (finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv := by
  apply Equiv.ext
  intro atom
  rcases atom with ⟨atom⟩
  simpa [finiteModelLiftCarrierEquiv] using
    (finiteGeneratedReflectedUpperAtomEquiv_high_graph.{u}
      input lift base atom)

/--
At every generated high source index, the target detector code is the actual
normalized high upper's transport of the source detector code.
-/
theorem finiteGeneratedActualHighDetectorCode_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).highGeneratedLift.domain.algebra.equationSystem.Index) :
    input.highGeneratedLift.domain.algebra.circuits.code
        (finiteGeneratedActualHighEquationIndexEquiv input lift base index) =
      ((finiteGeneratedOuterInput input base).highGeneratedLift.domain.algebra.circuits.code
        index).transport
          (finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv := by
  exact
    (finiteGeneratedNormalizedHighFactor input lift base).upper.detectorCode_eq
      index

/-! ## Reflected low detector law -/

/--
The equation-index equivalence and Atom equivalence reflected from the actual
normalized high factor satisfy the exact low `detectorCode_eq` law at every
generated source index.

The actual high detector field is used between the two independently generated
endpoint image graphs.  Canonical detector-code lifting is invoked only to
cross the universe boundary and is cancelled by its injectivity.
-/
theorem finiteGeneratedReflectedDetectorCode_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index) :
    input.lowGeneratedLift.domain.algebra.circuits.code
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index) =
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.circuits.code
        index).transport
          (finiteGeneratedReflectedUpperAtomEquiv input lift base) := by
  apply finiteModelLiftCircuitDetectorCode_injective.{u}
  let outer := finiteGeneratedOuterInput input base
  let actual := finiteGeneratedNormalizedHighFactor input lift base
  let reflectedIndex :=
    finiteGeneratedReflectedEquationIndexEquiv input lift base index
  let sourceHighIndex :=
    finiteGeneratedDomainEquationIndexEquiv.{u} outer index
  have htarget := input.inverseGeneratedDomain_detectorCode_graph reflectedIndex
  have hindex := finiteGeneratedReflectedEquationIndex_forward_image.{u}
    input lift base index
  have hactual := actual.upper.detectorCode_eq sourceHighIndex
  have hsource := outer.inverseGeneratedDomain_detectorCode_graph index
  have hatom := finiteGeneratedActualHighAtomEquiv_eq_lift_reflected.{u}
    input lift base
  calc
    finiteModelLiftCircuitDetectorCode.{u}
          (input.lowGeneratedLift.domain.algebra.circuits.code reflectedIndex) =
        input.highGeneratedLift.domain.algebra.circuits.code
          (finiteGeneratedDomainEquationIndexEquiv.{u} input reflectedIndex) :=
      htarget.symm
    _ = input.highGeneratedLift.domain.algebra.circuits.code
          (finiteGeneratedActualHighEquationIndexEquiv input lift base
            sourceHighIndex) :=
      congrArg input.highGeneratedLift.domain.algebra.circuits.code hindex
    _ = (outer.highGeneratedLift.domain.algebra.circuits.code
          sourceHighIndex).transport actual.upper.atomEquiv := hactual
    _ = (finiteModelLiftCircuitDetectorCode.{u}
          (outer.lowGeneratedLift.domain.algebra.circuits.code index)).transport
            actual.upper.atomEquiv :=
      congrArg (fun code => code.transport actual.upper.atomEquiv) hsource
    _ = (finiteModelLiftCircuitDetectorCode.{u}
          (outer.lowGeneratedLift.domain.algebra.circuits.code index)).transport
            (finiteModelLiftCarrierEquiv.{u}.atom.symm.trans
              ((finiteGeneratedReflectedUpperAtomEquiv input lift base).trans
                finiteModelLiftCarrierEquiv.{u}.atom)) := by
      rw [hatom]
    _ = finiteModelLiftCircuitDetectorCode.{u}
          ((outer.lowGeneratedLift.domain.algebra.circuits.code index).transport
            (finiteGeneratedReflectedUpperAtomEquiv input lift base)) :=
      (finiteModelLiftCircuitDetectorCode_transport.{u}
        (finiteGeneratedReflectedUpperAtomEquiv input lift base)
        (outer.lowGeneratedLift.domain.algebra.circuits.code index)).symm

/-! ## All-index high observable graph -/

/--
For every low source index and every lifted finite circuit datum, evaluating
the actual high target detector at the actual mapped index agrees with
evaluating the reflected low target detector on the reflected datum.

This exposes observable proof-use of both the actual equation-index field and
the complete recursively transported detector syntax.
-/
theorem finiteGeneratedReflectedDetectorCode_eval_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index)
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{u}) :
    (input.highGeneratedLift.domain.algebra.circuits.code
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport.equationEquiv
        (finiteGeneratedDomainEquationIndexEquiv.{u}
          (finiteGeneratedOuterInput input base) index))).eval datum =
      (input.lowGeneratedLift.domain.algebra.circuits.code
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index)).eval
          (finiteModelReflectFiniteCircuitDatum.{u} datum) := by
  have hindex := finiteGeneratedReflectedEquationIndex_forward_image.{u}
    input lift base index
  have htarget := input.inverseGeneratedDomain_detectorCode_graph
    (finiteGeneratedReflectedEquationIndexEquiv input lift base index)
  calc
    (input.highGeneratedLift.domain.algebra.circuits.code
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport.equationEquiv
        (finiteGeneratedDomainEquationIndexEquiv.{u}
          (finiteGeneratedOuterInput input base) index))).eval datum =
        (input.highGeneratedLift.domain.algebra.circuits.code
          (finiteGeneratedDomainEquationIndexEquiv.{u} input
            (finiteGeneratedReflectedEquationIndexEquiv input lift base index))).eval
              datum := by
      rw [hindex]
      rfl
    _ = (finiteModelLiftCircuitDetectorCode.{u}
          (input.lowGeneratedLift.domain.algebra.circuits.code
            (finiteGeneratedReflectedEquationIndexEquiv input lift base index))).eval
              datum := congrArg (fun code => code.eval datum) htarget
    _ = (input.lowGeneratedLift.domain.algebra.circuits.code
          (finiteGeneratedReflectedEquationIndexEquiv input lift base index)).eval
            (finiteModelReflectFiniteCircuitDatum.{u} datum) :=
      finiteModelLiftCircuitDetectorCode_eval_reflect.{u} _ datum

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
