import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedInvariantSignatureMapDescent

/-!
# Generated invariant and signature law descent

This module reflects the invariant-transport, selected-axis, and coordinate
laws of the actual normalized high prefix factor.  Each proof first consumes
the corresponding high upper law on a generated high image and only then
returns through the accepted invariant, axis, coordinate, and complete-object
images.

No low upper law, canonical whole-factor equality, caller certificate, or
completed signed-reading hom is used or asserted here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/--
An equality of dependent indices turns a heterogeneous value equality into the
exact `Equiv.cast` equality used by the generated coordinate landing map.
-/
private theorem coordinateCast_eq_of_heq
    {Axis : Type*} (Coordinate : Axis → Type*)
    {canonical actual : Axis} (haxis : canonical = actual)
    (actualValue : Coordinate actual) (canonicalValue : Coordinate canonical)
    (hvalue : HEq actualValue canonicalValue) :
    Equiv.cast (congrArg Coordinate haxis.symm) actualValue = canonicalValue := by
  cases haxis
  exact eq_of_heq hvalue

/--
The reflected invariant map transports every low generated invariant.  The
proof evaluates the actual normalized high `invariant_transport` law on the
canonical lift of each low object, then returns through the two generated
invariant observations and the complete reflected-object image.
-/
theorem finiteGeneratedReflectedInvariant_transport
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.invariantReading.Index) :
    Invariant.TransportedAlong
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.invariantReading.invariant
        index)
      (input.lowGeneratedLift.domain.reading.invariantReading.invariant
        (finiteGeneratedReflectedInvariantMap input lift base index))
      _root_.id (finiteGeneratedReflectedArchitectureObject input lift base) := by
  have hactual :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.invariant_transport
      (finiteGeneratedInvariantIndexEquiv.{u}
        (finiteGeneratedOuterInput input base) index)
  have hindex := finiteGeneratedReflectedInvariantMap_high_image.{u}
    input lift base index
  have hactualCanonical :
      Invariant.TransportedAlong
        ((finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.invariantReading.invariant
            (finiteGeneratedInvariantIndexEquiv.{u}
              (finiteGeneratedOuterInput input base) index))
        (input.highGeneratedLift.domain.reading.invariantReading.invariant
          (finiteGeneratedInvariantIndexEquiv.{u} input
            (finiteGeneratedReflectedInvariantMap input lift base index)))
        _root_.id
        (finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap :=
    Eq.mpr
      (congrArg
        (fun targetIndex => Invariant.TransportedAlong
          ((finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.invariantReading.invariant
              (finiteGeneratedInvariantIndexEquiv.{u}
                (finiteGeneratedOuterInput input base) index))
          (input.highGeneratedLift.domain.reading.invariantReading.invariant
            targetIndex)
          _root_.id
          (finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap)
        hindex)
      hactual
  intro object
  have hactualPoint := hactualCanonical
    (finiteModelLiftArchitectureObject.{u} object)
  have hobject := finiteGeneratedReflectedArchitectureObject_high_image.{u}
    input lift base object
  have hactualPointCanonical := Eq.mpr
    ((congrArg
      (fun targetObject =>
        (match
            (finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.invariantReading.invariant
                (finiteGeneratedInvariantIndexEquiv.{u}
                  (finiteGeneratedOuterInput input base) index) with
          | .function _ => False
          | .predicate predicate =>
              predicate.holds (finiteModelLiftArchitectureObject.{u} object)) ↔
        (match input.highGeneratedLift.domain.reading.invariantReading.invariant
            (finiteGeneratedInvariantIndexEquiv.{u} input
              (finiteGeneratedReflectedInvariantMap input lift base index)) with
          | .function _ => False
          | .predicate predicate => predicate.holds targetObject))
      hobject).symm)
    hactualPoint
  have hsource :=
    FiniteGeneratedLiftInput.inverseGeneratedDomain_invariant_holds_iff.{u}
      (finiteGeneratedOuterInput input base) index object
  have htarget :=
    FiniteGeneratedLiftInput.inverseGeneratedDomain_invariant_holds_iff.{u} input
    (finiteGeneratedReflectedInvariantMap input lift base index)
    (finiteGeneratedReflectedArchitectureObject input lift base object)
  simpa only [finiteGeneratedInvariantIndexEquiv_apply] using
    hsource.trans (hactualPointCanonical.trans htarget.symm)

/--
The reflected signature-axis map preserves and reflects selected status.  Its
middle implication is exactly the actual normalized high
`axis_selected_iff`; the generated source and target axis graphs provide the
two outer implications.
-/
theorem finiteGeneratedReflectedAxis_selected_iff
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.selected
        axis ↔
      input.lowGeneratedLift.domain.reading.signatureReading.selected
        (finiteGeneratedReflectedAxisMap input lift base axis) := by
  have hsource :
      (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.selected
          axis ↔
        (finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.signatureReading.selected
            (finiteGeneratedSignatureAxisEquiv.{u}
              (finiteGeneratedOuterInput input base) axis) := by
    simpa only [finiteGeneratedSignatureAxisEquiv_apply] using
      FiniteGeneratedLiftInput.inverseGeneratedDomain_axis_selected_iff.{u}
        (finiteGeneratedOuterInput input base) axis
  have hactual :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.axis_selected_iff
      (finiteGeneratedSignatureAxisEquiv.{u}
        (finiteGeneratedOuterInput input base) axis)
  rw [← finiteGeneratedReflectedAxisMap_high_image
    input lift base axis] at hactual
  have htarget :
      input.lowGeneratedLift.domain.reading.signatureReading.selected
          (finiteGeneratedReflectedAxisMap input lift base axis) ↔
        input.highGeneratedLift.domain.reading.signatureReading.selected
          (finiteGeneratedSignatureAxisEquiv.{u} input
            (finiteGeneratedReflectedAxisMap input lift base axis)) := by
    simpa only [finiteGeneratedSignatureAxisEquiv_apply] using
      FiniteGeneratedLiftInput.inverseGeneratedDomain_axis_selected_iff.{u} input
        (finiteGeneratedReflectedAxisMap input lift base axis)
  exact hsource.trans (hactual.trans htarget.symm)

/--
The reflected coordinate equivalence reads every low object coordinate
correctly.  The proof lifts the source coordinate, applies the actual
normalized high `coordinate_eq`, lands the result along the reflected-axis
graph and complete-object image, and finally reflects the target coordinate.
-/
theorem finiteGeneratedReflectedCoordinate_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedReflectedCoordinateEquiv input lift base axis
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.coordinate
          object axis) =
      input.lowGeneratedLift.domain.reading.signatureReading.coordinate
        (finiteGeneratedReflectedArchitectureObject input lift base object)
        (finiteGeneratedReflectedAxisMap input lift base axis) := by
  let sourceCoordinate :=
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.coordinate
      object axis
  let targetCoordinate :=
    input.lowGeneratedLift.domain.reading.signatureReading.coordinate
      (finiteGeneratedReflectedArchitectureObject input lift base object)
      (finiteGeneratedReflectedAxisMap input lift base axis)
  have hsource :
      (finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.signatureReading.coordinate
            (finiteModelLiftArchitectureObject.{u} object)
            (finiteGeneratedSignatureAxisEquiv.{u}
              (finiteGeneratedOuterInput input base) axis) =
        finiteGeneratedSignatureCoordinateEquiv.{u}
          (finiteGeneratedOuterInput input base) axis sourceCoordinate := by
    simpa only [finiteGeneratedSignatureAxisEquiv_apply,
      finiteGeneratedSignatureCoordinateEquiv_apply] using
      FiniteGeneratedLiftInput.inverseGeneratedDomain_coordinate_graph.{u}
        (finiteGeneratedOuterInput input base) object axis
  have hactual :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.coordinate_eq
      (finiteModelLiftArchitectureObject.{u} object)
      (finiteGeneratedSignatureAxisEquiv.{u}
        (finiteGeneratedOuterInput input base) axis)
  rw [hsource] at hactual
  have hobject := finiteGeneratedReflectedArchitectureObject_high_image.{u}
    input lift base object
  have haxis := finiteGeneratedReflectedAxisMap_high_image.{u}
    input lift base axis
  have hread : HEq
      (input.highGeneratedLift.domain.reading.signatureReading.coordinate
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
          (finiteModelLiftArchitectureObject.{u} object))
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.axisMap
          (finiteGeneratedSignatureAxisEquiv.{u}
            (finiteGeneratedOuterInput input base) axis)))
      (input.highGeneratedLift.domain.reading.signatureReading.coordinate
        (finiteModelLiftArchitectureObject.{u}
          (finiteGeneratedReflectedArchitectureObject input lift base object))
        (finiteGeneratedSignatureAxisEquiv.{u} input
          (finiteGeneratedReflectedAxisMap input lift base axis))) := by
    rw [hobject, haxis]
  have htarget :
      input.highGeneratedLift.domain.reading.signatureReading.coordinate
          (finiteModelLiftArchitectureObject.{u}
            (finiteGeneratedReflectedArchitectureObject input lift base object))
          (finiteGeneratedSignatureAxisEquiv.{u} input
            (finiteGeneratedReflectedAxisMap input lift base axis)) =
        finiteGeneratedSignatureCoordinateEquiv.{u} input
          (finiteGeneratedReflectedAxisMap input lift base axis)
          targetCoordinate := by
    simpa only [finiteGeneratedSignatureAxisEquiv_apply,
      finiteGeneratedSignatureCoordinateEquiv_apply] using
      FiniteGeneratedLiftInput.inverseGeneratedDomain_coordinate_graph.{u} input
        (finiteGeneratedReflectedArchitectureObject input lift base object)
        (finiteGeneratedReflectedAxisMap input lift base axis)
  have hvalue : HEq
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.coordinateEquiv
        (finiteGeneratedSignatureAxisEquiv.{u}
          (finiteGeneratedOuterInput input base) axis)
        (finiteGeneratedSignatureCoordinateEquiv.{u}
          (finiteGeneratedOuterInput input base) axis sourceCoordinate))
      (finiteGeneratedSignatureCoordinateEquiv.{u} input
        (finiteGeneratedReflectedAxisMap input lift base axis)
        targetCoordinate) :=
    HEq.trans (heq_of_eq hactual) (HEq.trans hread (heq_of_eq htarget))
  apply (finiteGeneratedSignatureCoordinateEquiv.{u} input
    (finiteGeneratedReflectedAxisMap input lift base axis)).injective
  rw [finiteGeneratedReflectedCoordinateEquiv_apply_high_image]
  exact coordinateCast_eq_of_heq
    input.highGeneratedLift.domain.reading.signatureReading.Coordinate
    haxis _ _ hvalue

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
