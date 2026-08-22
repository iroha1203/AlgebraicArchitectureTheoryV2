import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperCompositionEquationDescent

/-!
# Generated equation-transport composition descent

This module isolates the equation-system component of the reflected generated
upper composition.  The equation-index equivalence descends completely from
the actual normalized high-factor triangle.  The context component is retained
at its strongest currently generated form: every composed reflected forward
context has exactly the outer high forward image.

The actual high observable composition is also projected without changing its
dependent type.  A complete low `EquationSystemExactTransport` equality still
requires compatibility of the inner high observable equivalence with the
context cast from the reflected forward-object landing theorem.  No low factor,
known-low factorization law, canonical-factor equality, or caller certificate
is used here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Extensionality and actual-high projections -/

/--
Two exact equation transports with equal computational equivalences are equal.
The role, naturality, violation, and residual fields are propositions and are
therefore removed by proof irrelevance after the three data fields are aligned.
-/
private theorem equationSystemExactTransport_ext
    {U : AtomCarrier.{u}}
    {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {first second :
      EquationSystemExactTransport E F atomEquiv objectMap}
    (hContext : first.contextEquivalence = second.contextEquivalence)
    (hEquation : first.equationEquiv = second.equationEquiv)
    (hObservable : HEq first.observableEquiv second.observableEquiv) :
    first = second := by
  cases first
  cases second
  cases hContext
  cases hEquation
  cases hObservable
  rfl

/-- Equality of whole exact uppers gives heterogeneous equality of their observable families. -/
private theorem equationObservableEquiv_heq_of_upper_eq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : SignedExactCoreReadingHom P Q}
    (equality : first = second) :
    HEq first.equationTransport.observableEquiv
      second.equationTransport.observableEquiv := by
  cases equality
  rfl

/--
The context-equivalence component of the actual high factor triangle composes
to the outer generated high context equivalence.
-/
theorem finiteGeneratedNormalizedHighFactor_upper_fac_contextEquivalence
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    ((finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport.comp
        input.highGeneratedLift.hom.upper.equationTransport).contextEquivalence =
      (finiteGeneratedOuterInput input base).highGeneratedLift.hom.upper.equationTransport.contextEquivalence := by
  exact congrArg
    (fun upper => upper.equationTransport.contextEquivalence)
    (finiteGeneratedNormalizedHighFactor_upper_fac input lift base)

/--
The observable-equivalence family of the actual high factor triangle is the
outer generated high family.  `HEq` retains the dependency on the composed
context equivalence.
-/
theorem finiteGeneratedNormalizedHighFactor_upper_fac_observableEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    HEq
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport.comp
        input.highGeneratedLift.hom.upper.equationTransport).observableEquiv
      (finiteGeneratedOuterInput input base).highGeneratedLift.hom.upper.equationTransport.observableEquiv := by
  exact equationObservableEquiv_heq_of_upper_eq
    (finiteGeneratedNormalizedHighFactor_upper_fac input lift base)

/-! ## Reflected context and index composition -/

/--
Every reflected forward context, followed through the inner generated high
arrow, lands on the outer generated high forward context.  This is the exact
context-object consequence of the actual high triangle available before a low
whole-equivalence equality is proved.
-/
theorem finiteGeneratedReflectedUpper_comp_contextForward_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    input.highGeneratedLift.hom.upper.equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u} input).obj
          ((finiteGeneratedReflectedSignedExactCoreReadingHom
            input lift base).equationTransport.contextForward W)) =
      (finiteGeneratedOuterInput input base).highGeneratedLift.hom.upper.equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u}
          (finiteGeneratedOuterInput input base)).obj W) := by
  let outer := finiteGeneratedOuterInput input base
  change
    input.highGeneratedLift.hom.upper.equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u} input).obj
          (finiteGeneratedReflectedForwardObject input lift base W)) =
      outer.highGeneratedLift.hom.upper.equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u} outer).obj W)
  rw [finiteGeneratedReflectedForwardObject_image_eq]
  have equality := congrArg
    (fun equivalence => equivalence.functor.obj
      ((finiteGeneratedContextImageFunctor.{u} outer).obj W))
    (finiteGeneratedNormalizedHighFactor_upper_fac_contextEquivalence
      input lift base)
  change
    input.highGeneratedLift.hom.upper.equationTransport.contextForward
        ((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
          ((finiteGeneratedContextImageFunctor.{u} outer).obj W)) =
      outer.highGeneratedLift.hom.upper.equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u} outer).obj W) at equality
  exact equality

/--
The equation-index equivalence of the reflected upper followed by the inner
generated upper is exactly the outer generated equation-index equivalence.
The proof maps both values into the selected lifted target and uses only the
actual high upper triangle and the generated source/target index images.
-/
theorem finiteGeneratedReflectedUpper_comp_equationEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
        input.lowGeneratedLift.hom.upper).equationTransport.equationEquiv =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.equationTransport.equationEquiv := by
  apply Equiv.ext
  intro index
  let outer := finiteGeneratedOuterInput input base
  let reflectedIndex :=
    finiteGeneratedReflectedEquationIndexEquiv input lift base index
  change input.lowGeneratedLift.hom.upper.equationMap reflectedIndex =
    outer.lowGeneratedLift.hom.upper.equationMap index
  apply finiteModelTargetEquationIndexEquiv.{u}.injective
  have reflectedIndexImage :
      finiteGeneratedDomainEquationIndexEquiv.{u} input reflectedIndex =
        finiteGeneratedActualHighEquationIndexEquiv input lift base
          (finiteGeneratedDomainEquationIndexEquiv.{u} outer index) := by
    simpa only [reflectedIndex] using
      finiteGeneratedReflectedEquationIndex_forward_image
        input lift base index
  have actualTriangle := congrArg
    (fun upper => upper.equationMap
      (finiteGeneratedDomainEquationIndexEquiv.{u} outer index))
    (finiteGeneratedNormalizedHighFactor_upper_fac input lift base)
  change
    input.highGeneratedLift.hom.upper.equationMap
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.equationMap
          (finiteGeneratedDomainEquationIndexEquiv.{u} outer index)) =
      outer.highGeneratedLift.hom.upper.equationMap
        (finiteGeneratedDomainEquationIndexEquiv.{u} outer index) at actualTriangle
  calc
    finiteModelTargetEquationIndexEquiv.{u}
        (input.lowGeneratedLift.hom.upper.equationMap reflectedIndex) =
      input.highGeneratedLift.hom.upper.equationMap
        (finiteGeneratedDomainEquationIndexEquiv.{u} input reflectedIndex) := by
          simpa only [finiteGeneratedDomainEquationIndexEquiv_apply,
            finiteModelTargetEquationIndexEquiv_apply] using
              (input.generatedUpper_equationMap_graph reflectedIndex).symm
    _ = input.highGeneratedLift.hom.upper.equationMap
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.equationMap
          (finiteGeneratedDomainEquationIndexEquiv.{u} outer index)) := by
      simpa only [finiteGeneratedActualHighEquationIndexEquiv] using
        congrArg input.highGeneratedLift.hom.upper.equationMap
          reflectedIndexImage
    _ = outer.highGeneratedLift.hom.upper.equationMap
        (finiteGeneratedDomainEquationIndexEquiv.{u} outer index) := actualTriangle
    _ = finiteModelTargetEquationIndexEquiv.{u}
        (outer.lowGeneratedLift.hom.upper.equationMap index) :=
      by
        simpa only [finiteGeneratedDomainEquationIndexEquiv_apply,
          finiteModelTargetEquationIndexEquiv_apply] using
            outer.generatedUpper_equationMap_graph index

/-!
## Exact remaining composition type

The first missing low component is the following context-equivalence equality:

```lean
((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
    input.lowGeneratedLift.hom.upper).equationTransport.contextEquivalence =
  (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper
    .equationTransport.contextEquivalence
```

The theorem `finiteGeneratedReflectedUpper_comp_contextForward_high_image`
proves its forward-object equation after applying the generated high image and
the inner high context functor.  The current API has no object-level equality
reflection from that landing to the selected low target context category.
Consequently the dependent low `observableEquiv` families cannot yet be
compared: doing so additionally requires a theorem commuting the inner high
observable equivalence with the landing context cast.  Those are the first
unproved inputs to `equationSystemExactTransport_ext`; the exact low index
equality above is already discharged.
-/

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
