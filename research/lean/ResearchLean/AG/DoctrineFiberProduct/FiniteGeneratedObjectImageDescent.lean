import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedFactorFieldDescent

/-!
# Generated-image architecture-object descent

This module descends the complete architecture object obtained by applying the
actual normalized high factor to a canonically lifted finite-model object.  The
configuration is reflected from the actual high projection.  The two opaque
values are read from that same projection and lowered only after their
canonical `ULift` shapes have been derived internally.

The public producer accepts no image witness, shape equality, preimage, or
comparison certificate.  Its opaque values do not copy the corresponding
inhabitants of the source object.  The normalized/canonical factor equality is
used only to prove the generated-image shape and alignment graph.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Shape-guided opaque-value descent -/

/--
Lower a value after a proved generated-image identification of its carrier
with the canonical universe lift of a base carrier.
-/
def finiteGeneratedULiftValueDown
    {alpha : Type} {beta : Type u}
    (shape : beta = ULift.{u} alpha) (value : beta) : alpha := by
  subst beta
  exact value.down

/-- Lowering a lifted base value along the reflexive image shape recovers it. -/
@[simp]
theorem finiteGeneratedULiftValueDown_up
    {alpha : Type} (value : alpha) :
    finiteGeneratedULiftValueDown
        (alpha := alpha) (beta := ULift.{u} alpha) rfl (ULift.up value) = value :=
  rfl

/-- Every value of a carrier identified with a canonical lift is recovered after lowering. -/
@[simp]
theorem finiteGeneratedULiftValueUp_down
    {alpha : Type} {beta : Type u}
    (shape : beta = ULift.{u} alpha) (value : beta) :
    ULift.up (finiteGeneratedULiftValueDown shape value) = cast shape value := by
  subst beta
  rcases value with ⟨value⟩
  rfl

/-! ## Architecture-object transport composition -/

/-- Architecture-object transport respects first-then-second equivalence composition. -/
theorem transportArchitectureObject_trans {U : AtomCarrier.{u}}
    (first second : U.Atom ≃ U.Atom) (object : ArchitectureObject U) :
    transportArchitectureObject (first.trans second) object =
      transportArchitectureObject second
        (transportArchitectureObject first object) := by
  cases object
  simp [transportArchitectureObject, atomConfiguration_transport_comp]

/-! ## The actual normalized generated-image graph -/

/--
The actual normalized high object map on a lifted object is the canonical lift
of transport by the reflected prefix Atom equivalence.  The comparison with
the named canonical factor is used only in this alignment proof.
-/
theorem finiteGeneratedNormalizedHighFactor_objectMap_lift_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
        (finiteModelLiftArchitectureObject.{u} object) =
      finiteModelLiftArchitectureObject.{u}
        (transportArchitectureObject
          (finiteGeneratedReflectedUpperAtomEquiv input lift base) object) := by
  rw [finiteGeneratedReflectedUpperAtomEquiv_eq input lift base]
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change transportArchitectureObject
      input.highAlignedBaseFromLowData.doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (FiniteGeneratedLiftInput.highPackageHomFromLowData
          (finiteGeneratedOuterInput input base)).upper.atomEquiv
        (finiteModelLiftArchitectureObject.{u} object)) = _
  rw [(finiteGeneratedOuterInput input base).highPackageHomFromLowData_upper_atomEquiv]
  rw [input.highAlignedBaseFromLowData_eq]
  rw [show (finiteGeneratedOuterInput input base).hom = base.comp input.hom by rfl]
  rw [finiteModelLiftExtInstHom_comp]
  change transportArchitectureObject
      (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        ((finiteModelLiftExtInstHom.{u} base).doctrineHom.atomEquiv.trans
          (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv)
        (finiteModelLiftArchitectureObject.{u} object)) = _
  rw [transportArchitectureObject_trans]
  rw [transportArchitectureObject_equiv_symm]
  exact finiteModelLiftArchitectureObject_transport.{u}
    base.doctrineHom object

/--
The opaque `StructureMaps` carrier of the actual normalized high image has the
canonical lift shape generated from the source object's carrier.
-/
theorem finiteGeneratedNormalizedHighFactor_objectMap_structureMaps_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    ((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
      (finiteModelLiftArchitectureObject.{u} object)).StructureMaps =
        ULift.{u} object.StructureMaps := by
  simpa [finiteModelLiftArchitectureObject, transportArchitectureObject] using
    congrArg ArchitectureObject.StructureMaps
      (finiteGeneratedNormalizedHighFactor_objectMap_lift_graph
        input lift base object)

/--
The opaque `SelectedQuantities` carrier of the actual normalized high image
has the canonical lift shape generated from the source object's carrier.
-/
theorem finiteGeneratedNormalizedHighFactor_objectMap_selectedQuantities_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    ((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
      (finiteModelLiftArchitectureObject.{u} object)).SelectedQuantities =
        ULift.{u} object.SelectedQuantities := by
  simpa [finiteModelLiftArchitectureObject, transportArchitectureObject] using
    congrArg ArchitectureObject.SelectedQuantities
      (finiteGeneratedNormalizedHighFactor_objectMap_lift_graph
        input lift base object)

/-! ## Full object reflection from the actual high image -/

private noncomputable def finiteGeneratedReflectArchitectureObjectOnShape
    (highObject : ArchitectureObject finiteModelLiftCarrier.{u})
    (StructureMaps SelectedQuantities : Type)
    (structureMapsShape : highObject.StructureMaps = ULift.{u} StructureMaps)
    (selectedQuantitiesShape :
      highObject.SelectedQuantities = ULift.{u} SelectedQuantities) :
    ArchitectureObject FiniteModel.carrier where
  configuration :=
    finiteModelReflectAtomConfiguration highObject.configuration
  StructureMaps := StructureMaps
  SelectedQuantities := SelectedQuantities
  structureMaps := finiteGeneratedULiftValueDown
    structureMapsShape highObject.structureMaps
  selectedQuantities := finiteGeneratedULiftValueDown
    selectedQuantitiesShape highObject.selectedQuantities

private theorem finiteGeneratedReflectArchitectureObjectOnShape_eq_of_lift
    (highObject : ArchitectureObject finiteModelLiftCarrier.{u})
    (object : ArchitectureObject FiniteModel.carrier)
    (structureMapsShape :
      highObject.StructureMaps = ULift.{u} object.StructureMaps)
    (selectedQuantitiesShape :
      highObject.SelectedQuantities = ULift.{u} object.SelectedQuantities)
    (image : highObject = finiteModelLiftArchitectureObject.{u} object) :
    finiteGeneratedReflectArchitectureObjectOnShape highObject
        object.StructureMaps object.SelectedQuantities
        structureMapsShape selectedQuantitiesShape = object := by
  subst highObject
  cases object with
  | mk configuration StructureMaps SelectedQuantities structureMaps selectedQuantities =>
      cases structureMapsShape
      cases selectedQuantitiesShape
      simp [finiteGeneratedReflectArchitectureObjectOnShape,
        finiteModelLiftArchitectureObject]

/--
Reflect the complete actual normalized high image of a lifted finite-model
object.  Its configuration and both opaque values are read from the actual
high projection; the source object supplies only the generated low carrier
shapes.
-/
noncomputable def finiteGeneratedReflectedArchitectureObject
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    ArchitectureObject FiniteModel.carrier :=
  let highObject :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
      (finiteModelLiftArchitectureObject.{u} object)
  finiteGeneratedReflectArchitectureObjectOnShape highObject
    object.StructureMaps object.SelectedQuantities
    (finiteGeneratedNormalizedHighFactor_objectMap_structureMaps_type
      input lift base object)
    (finiteGeneratedNormalizedHighFactor_objectMap_selectedQuantities_type
      input lift base object)

/-- The reflected object configuration is read from the actual high image. -/
@[simp]
theorem finiteGeneratedReflectedArchitectureObject_configuration
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteGeneratedReflectedArchitectureObject input lift base object).configuration =
      finiteGeneratedReflectedObjectConfiguration input lift base object :=
  rfl

/-- The reflected object retains the generated base `StructureMaps` carrier. -/
@[simp]
theorem finiteGeneratedReflectedArchitectureObject_structureMaps_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteGeneratedReflectedArchitectureObject input lift base object).StructureMaps =
      object.StructureMaps :=
  rfl

/-- The reflected object retains the generated base `SelectedQuantities` carrier. -/
@[simp]
theorem finiteGeneratedReflectedArchitectureObject_selectedQuantities_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteGeneratedReflectedArchitectureObject input lift base object).SelectedQuantities =
      object.SelectedQuantities :=
  rfl

/--
Lifting the reflected `structureMaps` value recovers the cast of the actual
normalized high projection along its internally proved generated-image shape.
-/
theorem finiteGeneratedReflectedArchitectureObject_structureMaps_high_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    ULift.up
        (finiteGeneratedReflectedArchitectureObject input lift base object).structureMaps =
      cast
        (finiteGeneratedNormalizedHighFactor_objectMap_structureMaps_type
          input lift base object)
        (((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
          (finiteModelLiftArchitectureObject.{u} object)).structureMaps) :=
  finiteGeneratedULiftValueUp_down _ _

/--
Lifting the reflected `selectedQuantities` value recovers the cast of the
actual normalized high projection along its internally proved image shape.
-/
theorem finiteGeneratedReflectedArchitectureObject_selectedQuantities_high_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    ULift.up
        (finiteGeneratedReflectedArchitectureObject input lift base object).selectedQuantities =
      cast
        (finiteGeneratedNormalizedHighFactor_objectMap_selectedQuantities_type
          input lift base object)
        (((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
          (finiteModelLiftArchitectureObject.{u} object)).selectedQuantities) :=
  finiteGeneratedULiftValueUp_down _ _

/--
The reflected complete object is transport of the source object by the Atom
equivalence read from the actual normalized high factor.
-/
theorem finiteGeneratedReflectedArchitectureObject_transport
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    finiteGeneratedReflectedArchitectureObject input lift base object =
      transportArchitectureObject
        (finiteGeneratedReflectedUpperAtomEquiv input lift base) object := by
  let highObject :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
      (finiteModelLiftArchitectureObject.{u} object)
  let transported := transportArchitectureObject
    (finiteGeneratedReflectedUpperAtomEquiv input lift base) object
  change finiteGeneratedReflectArchitectureObjectOnShape highObject
      transported.StructureMaps transported.SelectedQuantities
      (finiteGeneratedNormalizedHighFactor_objectMap_structureMaps_type
        input lift base object)
      (finiteGeneratedNormalizedHighFactor_objectMap_selectedQuantities_type
        input lift base object) = transported
  exact finiteGeneratedReflectArchitectureObjectOnShape_eq_of_lift
    highObject transported
    (finiteGeneratedNormalizedHighFactor_objectMap_structureMaps_type
      input lift base object)
    (finiteGeneratedNormalizedHighFactor_objectMap_selectedQuantities_type
      input lift base object)
    (finiteGeneratedNormalizedHighFactor_objectMap_lift_graph
      input lift base object)

/--
The canonical lift of the reflected complete object is exactly the actual
normalized high object-map value, including both opaque fields.
-/
theorem finiteGeneratedReflectedArchitectureObject_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    finiteModelLiftArchitectureObject.{u}
        (finiteGeneratedReflectedArchitectureObject input lift base object) =
      (finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
        (finiteModelLiftArchitectureObject.{u} object) := by
  rw [finiteGeneratedReflectedArchitectureObject_transport]
  exact (finiteGeneratedNormalizedHighFactor_objectMap_lift_graph
    input lift base object).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
