import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableEquivalenceDescent

/-!
# Generated equation-observable naturality descent

This module reflects observable restriction naturality from the actual
normalized high equation transport.  Canonical generated-domain observable
images handle the two endpoints, while the reflected context map and its
Cycle 20 high-image theorem supply the arrow.  The central equality is the
actual high `observable_naturality` field.

No observable naturality, context equality, low reflected transport, or value
is supplied by the caller.  This module does not claim violation-coordinate
or equation-residual descent.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Canonical generated-image restriction graph -/

/--
The selected finite-model observable lift commutes with restriction along any
low target arrow and any lifted target arrow.  Both selected target equation
systems use their concrete identity restriction maps; no transport
naturality is accepted as an argument.
-/
theorem finiteModelTargetEquationObservableEquiv_restrict
    {W V : Site.ContextCategoryObject
      FiniteModel.corePackage.algebra.contextPreorder}
    {W' V' : Site.ContextCategoryObject
      finiteModelLiftCorePackage.{u}.algebra.contextPreorder}
    (lowMap : W ⟶ V) (highMap : W' ⟶ V')
    (value : FiniteModel.corePackage.algebra.equationSystem.Observable V) :
    finiteModelTargetEquationObservableEquiv.{u} W W'
        (FiniteModel.corePackage.algebra.equationSystem.restrict lowMap value) =
      finiteModelLiftCorePackage.{u}.algebra.equationSystem.restrict highMap
        (finiteModelTargetEquationObservableEquiv.{u} V V' value) :=
  rfl

/--
The canonical equation-observable image of every generated low restriction is
the corresponding generated high restriction.  The proof follows the two
generated forward equation transports around the concrete `Int`/`ULift Int`
target square; it is not a naturality statement for a reflected low factor.
-/
theorem finiteGeneratedEquationObservableEquiv_restrict
    (input : FiniteGeneratedLiftInput)
    {W V : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder}
    (map : W ⟶ V)
    (value : input.lowGeneratedLift.domain.algebra.equationSystem.Observable V) :
    finiteGeneratedEquationObservableEquiv.{u} input W
        (input.lowGeneratedLift.domain.algebra.equationSystem.restrict map value) =
      input.highGeneratedLift.domain.algebra.equationSystem.restrict
        ((finiteGeneratedContextImageFunctor.{u} input).map map)
        (finiteGeneratedEquationObservableEquiv.{u} input V value) := by
  let lowTransport :=
    (inverseCorePackageForwardUpper FiniteModel.corePackage input.hom).equationTransport
  let highTransport :=
    input.highPackageHomFromLowData.upper.equationTransport
  let image := finiteGeneratedContextImageFunctor.{u} input
  let lowW := lowTransport.observableEquiv W
  let lowV := lowTransport.observableEquiv V
  let highW := highTransport.observableEquiv (image.obj W)
  let highV := highTransport.observableEquiv (image.obj V)
  let targetW := finiteModelTargetEquationObservableEquiv.{u}
    (lowTransport.contextForward W) (highTransport.contextForward (image.obj W))
  let targetV := finiteModelTargetEquationObservableEquiv.{u}
    (lowTransport.contextForward V) (highTransport.contextForward (image.obj V))
  have hLow :
      lowW (input.lowGeneratedLift.domain.algebra.equationSystem.restrict map value) =
        FiniteModel.corePackage.algebra.equationSystem.restrict
          (lowTransport.contextForward_map map) (lowV value) :=
    lowTransport.observable_naturality map value
  change highW.symm (targetW (lowW
      (input.lowGeneratedLift.domain.algebra.equationSystem.restrict map value))) =
    input.highGeneratedLift.domain.algebra.equationSystem.restrict (image.map map)
      (highV.symm (targetV (lowV value)))
  calc
    highW.symm (targetW (lowW
        (input.lowGeneratedLift.domain.algebra.equationSystem.restrict map value))) =
      highW.symm (targetW
        (FiniteModel.corePackage.algebra.equationSystem.restrict
          (lowTransport.contextForward_map map) (lowV value))) := by
            exact congrArg (fun result => highW.symm (targetW result)) hLow
    _ = highW.symm
        (finiteModelLiftCorePackage.{u}.algebra.equationSystem.restrict
          (highTransport.contextForward_map (image.map map))
          (targetV (lowV value))) := by
            rw [finiteModelTargetEquationObservableEquiv_restrict]
    _ = input.highGeneratedLift.domain.algebra.equationSystem.restrict
        (image.map map) (highV.symm (targetV (lowV value))) := by
      have actualHigh := highTransport.observable_naturality
        (image.map map) (highV.symm (targetV (lowV value)))
      rw [highV.apply_symm_apply] at actualHigh
      rw [← actualHigh]
      exact highW.symm_apply_apply _

/-! ## Endpoint casts and actual reflected naturality -/

/--
Restriction commutes with rewriting both context endpoints.  This local
dependent cast lemma only aligns the actual high target arrow with the
Cycle 20 reflected-image arrow.
-/
private theorem equationObservableCast_restrict
    {U : AtomCarrier.{u}}
    {object : ArchitectureObject U}
    {context : Site.ContextPreorderCategory object}
    (equations : ArchitecturalEquationSystem context)
    {W V W' V' : Site.ContextCategoryObject context}
    (hW : W' = W) (hV : V' = V)
    (map : W ⟶ V) (rewrittenMap : W' ⟶ V')
    (value : equations.Observable V) :
    RingEquiv.cast
        (R := fun X : Site.ContextCategoryObject context => equations.Observable X)
        hW.symm (equations.restrict map value) =
      equations.restrict rewrittenMap
        (RingEquiv.cast
          (R := fun X : Site.ContextCategoryObject context => equations.Observable X)
          hV.symm value) := by
  cases hW
  cases hV
  have map_eq : rewrittenMap = map := Subsingleton.elim _ _
  cases map_eq
  rfl

/--
The observable equivalence reflected from the actual normalized high factor
is natural for every generated low context arrow and every observable value.
The proof uses the actual high `observable_naturality` between the two Cycle 21
observable high-image graphs and then descends through the Cycle 20 map image.
-/
theorem finiteGeneratedReflectedEquationObservableEquiv_naturality
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {W V : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)}
    (map : W ⟶ V)
    (value : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Observable V) :
    finiteGeneratedReflectedEquationObservableEquiv input lift base W
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.restrict
          map value) =
      input.lowGeneratedLift.domain.algebra.equationSystem.restrict
        (finiteGeneratedReflectedForwardMap input lift base map)
        (finiteGeneratedReflectedEquationObservableEquiv input lift base V value) := by
  let outer := finiteGeneratedOuterInput input base
  let sourceImage := finiteGeneratedContextImageFunctor.{u} outer
  let targetImage := finiteGeneratedContextImageFunctor.{u} input
  let actualContext := finiteGeneratedActualHighContextEquivalence input lift base
  let actualTransport :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport
  let sourceLiftW := finiteGeneratedEquationObservableEquiv.{u} outer W
  let sourceLiftV := finiteGeneratedEquationObservableEquiv.{u} outer V
  let targetLiftW := finiteGeneratedEquationObservableEquiv.{u} input
    (finiteGeneratedReflectedForwardObject input lift base W)
  let targetLiftV := finiteGeneratedEquationObservableEquiv.{u} input
    (finiteGeneratedReflectedForwardObject input lift base V)
  let actualW := finiteGeneratedActualHighEquationObservableEquiv input lift base
    (sourceImage.obj W)
  let actualV := finiteGeneratedActualHighEquationObservableEquiv input lift base
    (sourceImage.obj V)
  let targetCastW := finiteGeneratedReflectedEquationObservableTargetCast
    input lift base W
  let targetCastV := finiteGeneratedReflectedEquationObservableTargetCast
    input lift base V
  have hActual :
      actualW
          (outer.highGeneratedLift.domain.algebra.equationSystem.restrict
            (sourceImage.map map) (sourceLiftV value)) =
        input.highGeneratedLift.domain.algebra.equationSystem.restrict
          (actualContext.functor.map (sourceImage.map map))
          (actualV (sourceLiftV value)) :=
    actualTransport.observable_naturality
      (sourceImage.map map) (sourceLiftV value)
  apply targetLiftW.injective
  calc
    targetLiftW
        (finiteGeneratedReflectedEquationObservableEquiv input lift base W
          (outer.lowGeneratedLift.domain.algebra.equationSystem.restrict map value)) =
      targetCastW (actualW (sourceLiftW
        (outer.lowGeneratedLift.domain.algebra.equationSystem.restrict map value))) :=
          finiteGeneratedReflectedEquationObservableEquiv_apply_high_image
            input lift base W _
    _ = targetCastW (actualW
        (outer.highGeneratedLift.domain.algebra.equationSystem.restrict
          (sourceImage.map map) (sourceLiftV value))) := by
      rw [finiteGeneratedEquationObservableEquiv_restrict]
    _ = targetCastW
        (input.highGeneratedLift.domain.algebra.equationSystem.restrict
          (actualContext.functor.map (sourceImage.map map))
          (actualV (sourceLiftV value))) := by
      exact congrArg (fun result => targetCastW result) hActual
    _ = input.highGeneratedLift.domain.algebra.equationSystem.restrict
        (finiteGeneratedReflectedForwardHighMap input lift base map)
        (targetCastV (actualV (sourceLiftV value))) := by
      exact equationObservableCast_restrict
        input.highGeneratedLift.domain.algebra.equationSystem
        (finiteGeneratedReflectedForwardObject_image_eq input lift base W)
        (finiteGeneratedReflectedForwardObject_image_eq input lift base V)
        (actualContext.functor.map (sourceImage.map map))
        (finiteGeneratedReflectedForwardHighMap input lift base map)
        (actualV (sourceLiftV value))
    _ = input.highGeneratedLift.domain.algebra.equationSystem.restrict
        (targetImage.map (finiteGeneratedReflectedForwardMap input lift base map))
        (targetLiftV
          (finiteGeneratedReflectedEquationObservableEquiv input lift base V value)) := by
      rw [finiteGeneratedReflectedForwardMap_image]
      rw [finiteGeneratedReflectedEquationObservableEquiv_apply_high_image]
    _ = targetLiftW
        (input.lowGeneratedLift.domain.algebra.equationSystem.restrict
          (finiteGeneratedReflectedForwardMap input lift base map)
          (finiteGeneratedReflectedEquationObservableEquiv input lift base V value)) := by
      rw [finiteGeneratedEquationObservableEquiv_restrict]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
