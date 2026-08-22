import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperCompositionEquationDescent

/-!
# Generated upper composition: operations and signatures

This module descends the operation, invariant-index, signature-axis, and
dependent coordinate components of the actual normalized high factorization
to the corresponding composite of generated low uppers.  Every theorem reads
`finiteGeneratedNormalizedHighFactor_fac` and the generated high-image APIs;
no low factor or caller-supplied comparison is used.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

private theorem configurationHom_heq_of_endpoint_eq
    {C C' D D' : AtomConfiguration FiniteModel.carrier}
    (first : ConfigurationHom C D) (second : ConfigurationHom C' D')
    (hsource : C = C') (htarget : D = D')
    (hatom : first.atomMap = second.atomMap) :
    HEq first second := by
  cases hsource
  cases htarget
  exact heq_of_eq (ConfigurationHom.ext hatom)

private theorem operationMap_heq_of_atomEquiv_objectMap_eq
    {P : AATCorePackage FiniteModel.carrier}
    (first second : SignedExactCoreReadingHom P FiniteModel.corePackage)
    (hatom : first.atomEquiv = second.atomEquiv)
    (hobject : first.objectMap = second.objectMap) :
    HEq
      (@SignedExactCoreReadingHom.operationMap FiniteModel.carrier P
        FiniteModel.corePackage first)
      (@SignedExactCoreReadingHom.operationMap FiniteModel.carrier P
        FiniteModel.corePackage second) := by
  apply Function.hfunext rfl
  intro source source' hsource
  cases hsource
  apply Function.hfunext rfl
  intro target target' htarget
  cases htarget
  apply Function.hfunext rfl
  intro operation operation' hoperation
  cases hoperation
  apply configurationHom_heq_of_endpoint_eq
  · exact congrArg ArchitectureObject.configuration (congrFun hobject source)
  · exact congrArg ArchitectureObject.configuration (congrFun hobject target)
  · change
      (FiniteModel.corePackage.reading.operationReading.configurationMap
        (first.operationMap operation)).atomMap =
      (FiniteModel.corePackage.reading.operationReading.configurationMap
        (second.operationMap operation)).atomMap
    exact operationConfigurationMap_atomMap_eq_of_atomEquiv_eq
      first second hatom operation

/--
The operation map of the reflected composite agrees heterogeneously with the
outer generated operation map.  The actual high triangle first supplies the
Atom and complete-object equalities; exact operation naturality then determines
the resulting finite-model configuration homomorphism.
-/
theorem finiteGeneratedReflectedUpper_comp_operationMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    HEq
      (@SignedExactCoreReadingHom.operationMap FiniteModel.carrier
        (finiteGeneratedOuterInput input base).lowGeneratedLift.domain
        FiniteModel.corePackage
        ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
          input.lowGeneratedLift.hom.upper))
      (@SignedExactCoreReadingHom.operationMap FiniteModel.carrier
        (finiteGeneratedOuterInput input base).lowGeneratedLift.domain
        FiniteModel.corePackage
        (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper) := by
  let composite :=
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
      input.lowGeneratedLift.hom.upper
  let outerUpper :=
    (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper
  have hatom : composite.atomEquiv = outerUpper.atomEquiv :=
    finiteGeneratedReflectedUpper_comp_atomEquiv input lift base
  have hobject : composite.objectMap = outerUpper.objectMap :=
    finiteGeneratedReflectedUpper_comp_objectMap input lift base
  exact operationMap_heq_of_atomEquiv_objectMap_eq
    composite outerUpper hatom hobject

/--
The invariant-index map of the reflected composite is the outer generated
invariant-index map.  Injectivity of the target `ULift` image reduces the
claim to the invariant projection of the actual high factorization.
-/
theorem finiteGeneratedReflectedUpper_comp_invariantMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
      input.lowGeneratedLift.hom.upper).invariantMap =
        (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.invariantMap := by
  funext index
  apply ULift.up.inj
  let outer := finiteGeneratedOuterInput input base
  let actual := finiteGeneratedNormalizedHighFactor input lift base
  have hhigh := finiteGeneratedNormalizedHighFactor_upper_fac input lift base
  have hhighInvariant := congrArg SignedExactCoreReadingHom.invariantMap hhigh
  change
    ULift.up
        (input.lowGeneratedLift.hom.upper.invariantMap
          (finiteGeneratedReflectedInvariantMap input lift base index)) =
      ULift.up (outer.lowGeneratedLift.hom.upper.invariantMap index)
  calc
    ULift.up
        (input.lowGeneratedLift.hom.upper.invariantMap
          (finiteGeneratedReflectedInvariantMap input lift base index)) =
        input.highGeneratedLift.hom.upper.invariantMap
          (finiteGeneratedInvariantIndexEquiv.{u} input
            (finiteGeneratedReflectedInvariantMap input lift base index)) := by
          exact (input.generatedUpper_invariantMap_graph
            (finiteGeneratedReflectedInvariantMap input lift base index)).symm
    _ = input.highGeneratedLift.hom.upper.invariantMap
          (actual.upper.invariantMap
            (finiteGeneratedInvariantIndexEquiv.{u} outer index)) := by
          rw [finiteGeneratedReflectedInvariantMap_high_image]
    _ = outer.highGeneratedLift.hom.upper.invariantMap
          (finiteGeneratedInvariantIndexEquiv.{u} outer index) := by
          exact congrFun hhighInvariant
            (finiteGeneratedInvariantIndexEquiv.{u} outer index)
    _ = ULift.up (outer.lowGeneratedLift.hom.upper.invariantMap index) := by
          exact outer.generatedUpper_invariantMap_graph index

/--
The signature-axis map of the reflected composite is the outer generated
axis map.  The proof is the axis projection of the actual high triangle after
the two canonical generated-domain images.
-/
theorem finiteGeneratedReflectedUpper_comp_axisMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
      input.lowGeneratedLift.hom.upper).axisMap =
        (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.axisMap := by
  funext axis
  apply ULift.up.inj
  let outer := finiteGeneratedOuterInput input base
  let actual := finiteGeneratedNormalizedHighFactor input lift base
  have hhigh := finiteGeneratedNormalizedHighFactor_upper_fac input lift base
  have hhighAxis := congrArg SignedExactCoreReadingHom.axisMap hhigh
  change
    ULift.up
        (input.lowGeneratedLift.hom.upper.axisMap
          (finiteGeneratedReflectedAxisMap input lift base axis)) =
      ULift.up (outer.lowGeneratedLift.hom.upper.axisMap axis)
  calc
    ULift.up
        (input.lowGeneratedLift.hom.upper.axisMap
          (finiteGeneratedReflectedAxisMap input lift base axis)) =
        input.highGeneratedLift.hom.upper.axisMap
          (finiteGeneratedSignatureAxisEquiv.{u} input
            (finiteGeneratedReflectedAxisMap input lift base axis)) := by
          exact (input.generatedUpper_axisMap_graph
            (finiteGeneratedReflectedAxisMap input lift base axis)).symm
    _ = input.highGeneratedLift.hom.upper.axisMap
          (actual.upper.axisMap
            (finiteGeneratedSignatureAxisEquiv.{u} outer axis)) := by
          rw [finiteGeneratedReflectedAxisMap_high_image]
    _ = outer.highGeneratedLift.hom.upper.axisMap
          (finiteGeneratedSignatureAxisEquiv.{u} outer axis) := by
          exact congrFun hhighAxis
            (finiteGeneratedSignatureAxisEquiv.{u} outer axis)
    _ = ULift.up (outer.lowGeneratedLift.hom.upper.axisMap axis) := by
          exact outer.generatedUpper_axisMap_graph axis

/--
The dependent coordinate equivalence of the reflected composite is the outer
generated coordinate equivalence.  The preceding axis equality aligns the
low codomains; the actual axis image then removes the high landing cast before
the coordinate projection of the actual high triangle is used.
-/
theorem finiteGeneratedReflectedUpper_comp_coordinateEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    HEq
      ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
        input.lowGeneratedLift.hom.upper).coordinateEquiv
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.coordinateEquiv := by
  let outer := finiteGeneratedOuterInput input base
  let actual := finiteGeneratedNormalizedHighFactor input lift base
  have haxis := finiteGeneratedReflectedUpper_comp_axisMap input lift base
  cases haxis
  apply heq_of_eq
  funext axis
  apply Equiv.ext
  intro coordinate
  apply ULift.up.inj
  have haxisImage := finiteGeneratedReflectedAxisMap_high_image.{u}
    input lift base axis
  cases haxisImage
  have hhigh := finiteGeneratedNormalizedHighFactor_upper_fac input lift base
  change
    ULift.up
        (input.lowGeneratedLift.hom.upper.coordinateEquiv
          (finiteGeneratedReflectedAxisMap input lift base axis)
          (finiteGeneratedReflectedCoordinateEquiv input lift base axis coordinate)) =
      ULift.up
        (outer.lowGeneratedLift.hom.upper.coordinateEquiv axis coordinate)
  calc
    ULift.up
        (input.lowGeneratedLift.hom.upper.coordinateEquiv
          (finiteGeneratedReflectedAxisMap input lift base axis)
          (finiteGeneratedReflectedCoordinateEquiv input lift base axis coordinate)) =
        input.highGeneratedLift.hom.upper.coordinateEquiv
          (finiteGeneratedSignatureAxisEquiv.{u} input
            (finiteGeneratedReflectedAxisMap input lift base axis))
          (finiteGeneratedSignatureCoordinateEquiv.{u} input
            (finiteGeneratedReflectedAxisMap input lift base axis)
            (finiteGeneratedReflectedCoordinateEquiv input lift base axis coordinate)) := by
          exact (input.generatedUpper_coordinateEquiv_graph
            (finiteGeneratedReflectedAxisMap input lift base axis)
            (finiteGeneratedReflectedCoordinateEquiv input lift base axis coordinate)).symm
    _ = input.highGeneratedLift.hom.upper.coordinateEquiv
          (actual.upper.axisMap
            (finiteGeneratedSignatureAxisEquiv.{u} outer axis))
          (actual.upper.coordinateEquiv
            (finiteGeneratedSignatureAxisEquiv.{u} outer axis)
            (finiteGeneratedSignatureCoordinateEquiv.{u} outer axis coordinate)) := by
          rw [finiteGeneratedReflectedCoordinateEquiv_apply_high_image]
          rfl
    _ = outer.highGeneratedLift.hom.upper.coordinateEquiv
          (finiteGeneratedSignatureAxisEquiv.{u} outer axis)
          (finiteGeneratedSignatureCoordinateEquiv.{u} outer axis coordinate) := by
          change
            (actual.upper.comp input.highGeneratedLift.hom.upper).coordinateEquiv
                (finiteGeneratedSignatureAxisEquiv.{u} outer axis)
                (finiteGeneratedSignatureCoordinateEquiv.{u} outer axis coordinate) = _
          rw [hhigh]
          rfl
    _ = ULift.up
          (outer.lowGeneratedLift.hom.upper.coordinateEquiv axis coordinate) := by
          exact outer.generatedUpper_coordinateEquiv_graph axis coordinate

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
