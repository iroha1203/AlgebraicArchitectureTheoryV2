import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedContextEquivalenceCompositionDescent

/-!
# Arbitrary finite-carrier package universe lift

This module extends the canonical finite-carrier `ULift` machinery from the
selected `FiniteModel.corePackage` to the reading data of an arbitrary
`AATCorePackage FiniteModel.carrier`.  The construction normalizes every high
architecture object through the source package's object reading and lifts the
resulting invariant, signature, operation, and context data.

The endpoint package, total-hom rebase, and strong-lift reflection are built on
top of this data layer.  No package, morphism, lift, or reflection certificate
is accepted from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Architecture-object normalization -/

/-- Normalize a high object through a selected low object reading. -/
def finiteModelNormalizeArchitectureObject
    (reading : ObjectReading FiniteModel.carrier)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    ArchitectureObject FiniteModel.carrier :=
  reading.object
    (finiteModelReflectAtomConfiguration.{u} object.configuration)

/-- Normalization exposes the reflected high configuration exactly. -/
@[simp]
theorem finiteModelNormalizeArchitectureObject_configuration
    (reading : ObjectReading FiniteModel.carrier)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    (finiteModelNormalizeArchitectureObject.{u} reading object).configuration =
      finiteModelReflectAtomConfiguration.{u} object.configuration :=
  reading.configuration_eq _

/-- Normalizing a canonically lifted selected object recovers that object. -/
@[simp]
theorem finiteModelNormalizeArchitectureObject_lift
    (reading : ObjectReading FiniteModel.carrier)
    (configuration : AtomConfiguration FiniteModel.carrier) :
    finiteModelNormalizeArchitectureObject.{u} reading
        (finiteModelLiftArchitectureObject.{u}
          (reading.object configuration)) =
      reading.object configuration := by
  apply congrArg reading.object
  change finiteModelReflectAtomConfiguration.{u}
      (finiteModelLiftAtomConfiguration.{u}
        (reading.object configuration).configuration) = configuration
  rw [finiteModelReflectAtomConfiguration_lift, reading.configuration_eq]

/-- The lifted normalized configuration is the actual high configuration. -/
theorem finiteModelLift_normalized_configuration
    (reading : ObjectReading FiniteModel.carrier)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    finiteModelLiftAtomConfiguration.{u}
        (finiteModelNormalizeArchitectureObject.{u} reading object).configuration =
      object.configuration := by
  rw [finiteModelNormalizeArchitectureObject_configuration]
  exact finiteModelLiftAtomConfiguration_reflect.{u} object.configuration

/-! ## Arbitrary invariant and signature readings -/

/-- Lift one invariant after normalizing its high input object. -/
def finiteModelLiftInvariantAt
    (reading : ObjectReading FiniteModel.carrier) :
    Invariant FiniteModel.carrier → Invariant finiteModelLiftCarrier.{u}
  | .function invariant =>
      .function {
        Value := ULift.{u} invariant.Value
        evaluate := fun object =>
          ULift.up (invariant.evaluate
            (finiteModelNormalizeArchitectureObject.{u} reading object))
      }
  | .predicate invariant =>
      .predicate {
        holds := fun object =>
          invariant.holds
            (finiteModelNormalizeArchitectureObject.{u} reading object)
      }

/-- Lift an arbitrary invariant family, including its index carrier. -/
def finiteModelLiftInvariantFamilyAt
    (reading : ObjectReading FiniteModel.carrier)
    (family : InvariantFamily FiniteModel.carrier) :
    InvariantFamily finiteModelLiftCarrier.{u} where
  Index := ULift.{u} family.Index
  invariant index :=
    finiteModelLiftInvariantAt.{u} reading (family.invariant index.down)

/-- Lift an arbitrary architecture signature through object normalization. -/
def finiteModelLiftArchitectureSignatureAt
    (reading : ObjectReading FiniteModel.carrier)
    (signature : ArchitectureSignature FiniteModel.carrier) :
    ArchitectureSignature finiteModelLiftCarrier.{u} where
  Axis := ULift.{u} signature.Axis
  Coordinate axis := ULift.{u} (signature.Coordinate axis.down)
  selected axis := signature.selected axis.down
  coordinate object axis :=
    ULift.up (signature.coordinate
      (finiteModelNormalizeArchitectureObject.{u} reading object) axis.down)

/-- Signature selection is unchanged on lifted axes. -/
@[simp]
theorem finiteModelLiftArchitectureSignatureAt_selected
    (reading : ObjectReading FiniteModel.carrier)
    (signature : ArchitectureSignature FiniteModel.carrier)
    (axis : signature.Axis) :
    (finiteModelLiftArchitectureSignatureAt.{u} reading signature).selected
        (ULift.up axis) ↔
      signature.selected axis :=
  Iff.rfl

/-- Signature coordinates retain the exact source value on selected objects. -/
@[simp]
theorem finiteModelLiftArchitectureSignatureAt_coordinate
    (reading : ObjectReading FiniteModel.carrier)
    (signature : ArchitectureSignature FiniteModel.carrier)
    (configuration : AtomConfiguration FiniteModel.carrier)
    (axis : signature.Axis) :
    (finiteModelLiftArchitectureSignatureAt.{u} reading signature).coordinate
        (finiteModelLiftArchitectureObject.{u}
          (reading.object configuration)) (ULift.up axis) =
      ULift.up (signature.coordinate (reading.object configuration) axis) := by
  simp [finiteModelLiftArchitectureSignatureAt]

/-! ## Arbitrary operation readings -/

/--
Lift an arbitrary operation reading.  The endpoint casts are generated from
the object-reading normalization laws and the configuration lift/reflection
round trip.
-/
noncomputable def finiteModelLiftOperationReadingAt
    (reading : ObjectReading FiniteModel.carrier)
    (operations : OperationReading FiniteModel.carrier) :
    OperationReading finiteModelLiftCarrier.{u} where
  Op source target := ULift.{u}
    (operations.Op
      (finiteModelNormalizeArchitectureObject.{u} reading source)
      (finiteModelNormalizeArchitectureObject.{u} reading target))
  configurationMap := by
    intro source target operation
    exact castConfigurationHom
      (finiteModelLift_normalized_configuration.{u} reading source)
      (finiteModelLift_normalized_configuration.{u} reading target)
      (finiteModelLiftConfigurationHom.{u}
        (operations.configurationMap operation.down))

/-! ## Tagged context embedding

The complete low context is retained as the extension tag at a successor
universe.  This makes the embedding definitionally
injective even though equality of bare `ULift` carrier types is not reflected
by Lean's intensional type theory.
-/

/-- Lift a context and retain the complete low context as an injective tag. -/
def finiteModelTaggedLiftArchitectureContext
    {A : ArchitectureObject FiniteModel.carrier}
    (context : Site.ArchitectureContext A) :
    Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A) where
  minimal := {
    Support := ULift.{u + 1} context.Support
    Axis := ULift.{u + 1} context.Axis
    Observable := ULift.{u + 1} context.Observable
    supportReads := fun support atom =>
      context.minimal.supportReads support.down
        (finiteModelLiftCarrierEquiv.{u + 1}.atom.symm atom)
    supportReads_objectFamily := by
      intro support atom hread
      simpa [finiteModelLiftArchitectureObject,
        finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily] using
        context.supportReads_objectFamily hread
    axisReads := fun axis => context.minimal.axisReads axis.down
    observableReads := fun observable =>
      context.minimal.observableReads observable.down
  }
  Extension := ULift.{u + 1} (Site.ArchitectureContext A)
  extension := ULift.up context

/-- The tag exposes the complete source context. -/
@[simp]
theorem finiteModelTaggedLiftArchitectureContext_extension
    {A : ArchitectureObject FiniteModel.carrier}
    (context : Site.ArchitectureContext A) :
    (finiteModelTaggedLiftArchitectureContext.{u} context).extension =
      ULift.up context :=
  rfl

/-- Tagged context lifting is injective. -/
theorem finiteModelTaggedLiftArchitectureContext_injective
    {A : ArchitectureObject FiniteModel.carrier} :
    Function.Injective
      (finiteModelTaggedLiftArchitectureContext.{u} (A := A)) := by
  intro first second equality
  simp only [finiteModelTaggedLiftArchitectureContext] at equality
  injection equality with _ _ extensionEquality
  exact ULift.up_injective extensionEquality

/-! ## Finite-profile normalization of arbitrary high contexts -/

/-- Support-reading profiles of one arbitrary high context, indexed by low atoms. -/
def FiniteModelSupportProfile
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :=
  {profile : Set FiniteModel.carrier.Atom //
    ∃ support : actual.Support, ∀ atom,
      profile atom ↔ actual.minimal.supportReads support
        (finiteModelLiftCarrierEquiv.{u + 1}.atom atom)}

/-- Axis-reading truth profiles of one arbitrary high context. -/
def FiniteModelAxisProfile
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :=
  {value : Bool // ∃ axis : actual.Axis,
    (value = true ↔ actual.minimal.axisReads axis)}

/-- Observable-reading truth profiles of one arbitrary high context. -/
def FiniteModelObservableProfile
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :=
  {value : Bool // ∃ observable : actual.Observable,
    (value = true ↔ actual.minimal.observableReads observable)}

/-- Canonical low support profile generated by a high support value. -/
noncomputable def finiteModelSupportProfileOf
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A))
    (support : actual.Support) : FiniteModelSupportProfile.{u} actual := by
  classical
  exact ⟨fun atom => actual.minimal.supportReads support
    (finiteModelLiftCarrierEquiv.{u + 1}.atom atom), support, fun _ => Iff.rfl⟩

/-- Canonical low axis profile generated by a high axis value. -/
noncomputable def finiteModelAxisProfileOf
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A))
    (axis : actual.Axis) : FiniteModelAxisProfile actual := by
  classical
  exact ⟨decide (actual.minimal.axisReads axis), axis, by simp⟩

/-- Canonical low observable profile generated by a high observable value. -/
noncomputable def finiteModelObservableProfileOf
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A))
    (observable : actual.Observable) :
    FiniteModelObservableProfile actual := by
  classical
  exact ⟨decide (actual.minimal.observableReads observable), observable, by simp⟩

/-- Every arbitrary high context has a small finite-profile representative. -/
noncomputable def finiteModelProfileArchitectureContext
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    Site.ArchitectureContext A where
  minimal := {
    Support := FiniteModelSupportProfile.{u} actual
    Axis := FiniteModelAxisProfile actual
    Observable := FiniteModelObservableProfile actual
    supportReads := fun support atom => support.1 atom
    supportReads_objectFamily := by
      intro support atom hread
      rcases support.2 with ⟨highSupport, hprofile⟩
      have highFamily := actual.supportReads_objectFamily
        ((hprofile atom).mp hread)
      simpa [finiteModelLiftArchitectureObject,
        finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily] using
        highFamily
    axisReads := fun axis => axis.1 = true
    observableReads := fun observable => observable.1 = true
  }
  Extension := PUnit
  extension := PUnit.unit

/-- A support profile records exactly the originating high support predicate. -/
@[simp]
theorem finiteModelSupportProfileOf_reads
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A))
    (support : actual.Support) (atom : FiniteModel.carrier.Atom) :
    (finiteModelSupportProfileOf.{u} actual support).1 atom ↔
      actual.minimal.supportReads support
        (finiteModelLiftCarrierEquiv.{u + 1}.atom atom) :=
  Iff.rfl

/-- An axis profile records exactly the originating high axis predicate. -/
@[simp]
theorem finiteModelAxisProfileOf_reads
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A))
    (axis : actual.Axis) :
    (finiteModelAxisProfileOf actual axis).1 = true ↔
      actual.minimal.axisReads axis := by
  classical
  simp [finiteModelAxisProfileOf]

/-- An observable profile records exactly the originating high predicate. -/
@[simp]
theorem finiteModelObservableProfileOf_reads
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A))
    (observable : actual.Observable) :
    (finiteModelObservableProfileOf actual observable).1 = true ↔
      actual.minimal.observableReads observable := by
  classical
  simp [finiteModelObservableProfileOf]

/-- Restriction from an arbitrary high context to its tagged finite profile. -/
noncomputable def finiteModelContextToTaggedProfile
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    Site.ContextMorphism actual
      (finiteModelTaggedLiftArchitectureContext.{u}
        (finiteModelProfileArchitectureContext.{u} actual)) where
  supportMap := fun support =>
    ULift.up (finiteModelSupportProfileOf.{u} actual support)
  axisMap := fun axis => ULift.up (finiteModelAxisProfileOf actual axis)
  observableRestrict := fun observable =>
    Classical.choose observable.down.2

/-- Restriction from the tagged finite profile back to the arbitrary context. -/
noncomputable def finiteModelContextFromTaggedProfile
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    Site.ContextMorphism
      (finiteModelTaggedLiftArchitectureContext.{u}
        (finiteModelProfileArchitectureContext.{u} actual)) actual where
  supportMap := fun support => Classical.choose support.down.2
  axisMap := fun axis => Classical.choose axis.down.2
  observableRestrict := fun observable =>
    ULift.up (finiteModelObservableProfileOf actual observable)

/-- The forward profile normalization is a selected restriction. -/
theorem finiteModelContextToTaggedProfile_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    (finiteModelContextToTaggedProfile.{u} actual).IsRestriction := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    simpa [finiteModelContextToTaggedProfile,
      finiteModelTaggedLiftArchitectureContext] using hread
  · intro axis hread
    change (finiteModelAxisProfileOf actual axis).1 = true
    exact (finiteModelAxisProfileOf_reads actual axis).mpr hread
  · intro observable hread
    change actual.minimal.observableReads (Classical.choose observable.down.2)
    exact (Classical.choose_spec observable.down.2).mp hread
  · intro support atom hread
    exact (finiteModelTaggedLiftArchitectureContext.{u}
      (finiteModelProfileArchitectureContext.{u} actual)).supportReads_objectFamily
        hread

/-- The backward profile normalization is a selected restriction. -/
theorem finiteModelContextFromTaggedProfile_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    (finiteModelContextFromTaggedProfile.{u} actual).IsRestriction := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    change actual.minimal.supportReads
      (Classical.choose support.down.2) atom
    have profile := Classical.choose_spec support.down.2
    exact (profile
      (finiteModelLiftCarrierEquiv.{u + 1}.atom.symm atom)).mp (by
        simpa [finiteModelTaggedLiftArchitectureContext] using hread)
  · intro axis hread
    change actual.minimal.axisReads (Classical.choose axis.down.2)
    exact (Classical.choose_spec axis.down.2).mp (by
      simpa [finiteModelTaggedLiftArchitectureContext] using hread)
  · intro observable hread
    change (finiteModelObservableProfileOf actual observable).1 = true
    exact (finiteModelObservableProfileOf_reads actual observable).mpr hread
  · intro support atom hread
    exact actual.supportReads_objectFamily hread

/-! ## Image-aware reflection -/

/-- A high context is in the tagged image when it retains an exact low source tag. -/
def FiniteModelContextInTaggedImage
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) : Prop :=
  ∃ template : Site.ArchitectureContext A,
    finiteModelTaggedLiftArchitectureContext.{u} template = actual

/-- Reflect image contexts to their unique source and normalize all other contexts by profile. -/
noncomputable def finiteModelReflectTaggedArchitectureContext
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    Site.ArchitectureContext A := by
  classical
  exact if h : FiniteModelContextInTaggedImage.{u} actual then
    Classical.choose h
  else finiteModelProfileArchitectureContext.{u} actual

/-- Image-aware reflection is a strict left inverse of tagged lifting. -/
@[simp]
theorem finiteModelReflectTaggedArchitectureContext_lift
    {A : ArchitectureObject FiniteModel.carrier}
    (template : Site.ArchitectureContext A) :
    finiteModelReflectTaggedArchitectureContext.{u}
        (finiteModelTaggedLiftArchitectureContext.{u} template) = template := by
  classical
  unfold finiteModelReflectTaggedArchitectureContext
  rw [dif_pos (show FiniteModelContextInTaggedImage.{u}
    (finiteModelTaggedLiftArchitectureContext.{u} template) from
    ⟨template, rfl⟩)]
  apply finiteModelTaggedLiftArchitectureContext_injective.{u}
  exact Classical.choose_spec
    (show FiniteModelContextInTaggedImage.{u}
      (finiteModelTaggedLiftArchitectureContext.{u} template) from
      ⟨template, rfl⟩)

/-- Every non-image context reflects to its finite-profile normalization. -/
theorem finiteModelReflectTaggedArchitectureContext_eq_profile
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A))
    (outside : ¬ FiniteModelContextInTaggedImage.{u} actual) :
    finiteModelReflectTaggedArchitectureContext.{u} actual =
      finiteModelProfileArchitectureContext.{u} actual := by
  classical
  simp [finiteModelReflectTaggedArchitectureContext, outside]

/-- Transport a raw context morphism across endpoint equalities. -/
def finiteModelCastContextMorphism
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source source' target target' : Site.ArchitectureContext A}
    (sourceEq : source = source') (targetEq : target = target')
    (morphism : Site.ContextMorphism source target) :
    Site.ContextMorphism source' target' := by
  cases sourceEq
  cases targetEq
  exact morphism

/-- Endpoint casting preserves the selected restriction role. -/
theorem finiteModelCastContextMorphism_isRestriction
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source source' target target' : Site.ArchitectureContext A}
    (sourceEq : source = source') (targetEq : target = target')
    (morphism : Site.ContextMorphism source target)
    (restriction : morphism.IsRestriction) :
    (finiteModelCastContextMorphism sourceEq targetEq morphism).IsRestriction := by
  cases sourceEq
  cases targetEq
  exact restriction

/-- On an image context, the tagged reflected choice is the actual context. -/
theorem finiteModelTaggedLift_reflect_eq_of_image
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A))
    (image : FiniteModelContextInTaggedImage.{u} actual) :
    finiteModelTaggedLiftArchitectureContext.{u}
        (finiteModelReflectTaggedArchitectureContext.{u} actual) = actual := by
  classical
  unfold finiteModelReflectTaggedArchitectureContext
  rw [dif_pos image]
  exact Classical.choose_spec image

/-- Every high context restricts to the tagged lift of its reflected representative. -/
noncomputable def finiteModelContextToTaggedReflection
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    Site.ContextMorphism actual
      (finiteModelTaggedLiftArchitectureContext.{u}
        (finiteModelReflectTaggedArchitectureContext.{u} actual)) := by
  classical
  by_cases image : FiniteModelContextInTaggedImage.{u} actual
  · exact finiteModelCastContextMorphism rfl
      (finiteModelTaggedLift_reflect_eq_of_image.{u} actual image).symm
      (Site.identityContextMorphism actual)
  · exact finiteModelCastContextMorphism rfl
      (congrArg finiteModelTaggedLiftArchitectureContext
        (finiteModelReflectTaggedArchitectureContext_eq_profile.{u}
          actual image)).symm
      (finiteModelContextToTaggedProfile.{u} actual)

/-- The tagged reflected representative restricts back to every high context. -/
noncomputable def finiteModelContextFromTaggedReflection
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    Site.ContextMorphism
      (finiteModelTaggedLiftArchitectureContext.{u}
        (finiteModelReflectTaggedArchitectureContext.{u} actual)) actual := by
  classical
  by_cases image : FiniteModelContextInTaggedImage.{u} actual
  · exact finiteModelCastContextMorphism
      (finiteModelTaggedLift_reflect_eq_of_image.{u} actual image).symm rfl
      (Site.identityContextMorphism actual)
  · exact finiteModelCastContextMorphism
      (congrArg finiteModelTaggedLiftArchitectureContext
        (finiteModelReflectTaggedArchitectureContext_eq_profile.{u}
          actual image)).symm rfl
      (finiteModelContextFromTaggedProfile.{u} actual)

/-- Forward image-aware normalization is a selected restriction. -/
theorem finiteModelContextToTaggedReflection_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    (finiteModelContextToTaggedReflection.{u} actual).IsRestriction := by
  classical
  by_cases image : FiniteModelContextInTaggedImage.{u} actual
  · simpa [finiteModelContextToTaggedReflection, image] using
      (finiteModelCastContextMorphism_isRestriction rfl
      (finiteModelTaggedLift_reflect_eq_of_image.{u} actual image).symm
      (Site.identityContextMorphism actual)
      ⟨fun h => h, fun h => h, fun h => h,
        fun h => actual.supportReads_objectFamily h⟩)
  · simpa [finiteModelContextToTaggedReflection, image] using
      (finiteModelCastContextMorphism_isRestriction rfl
      (congrArg finiteModelTaggedLiftArchitectureContext
        (finiteModelReflectTaggedArchitectureContext_eq_profile.{u}
          actual image)).symm
      (finiteModelContextToTaggedProfile.{u} actual)
      (finiteModelContextToTaggedProfile_isRestriction.{u} actual))

/-- Backward image-aware normalization is a selected restriction. -/
theorem finiteModelContextFromTaggedReflection_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    (actual : Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u + 1} A)) :
    (finiteModelContextFromTaggedReflection.{u} actual).IsRestriction := by
  classical
  by_cases image : FiniteModelContextInTaggedImage.{u} actual
  · simpa [finiteModelContextFromTaggedReflection, image] using
      (finiteModelCastContextMorphism_isRestriction
      (finiteModelTaggedLift_reflect_eq_of_image.{u} actual image).symm rfl
      (Site.identityContextMorphism actual)
      ⟨fun h => h, fun h => h, fun h => h,
        fun h => actual.supportReads_objectFamily h⟩)
  · simpa [finiteModelContextFromTaggedReflection, image] using
      (finiteModelCastContextMorphism_isRestriction
      (congrArg finiteModelTaggedLiftArchitectureContext
        (finiteModelReflectTaggedArchitectureContext_eq_profile.{u}
          actual image)).symm rfl
      (finiteModelContextFromTaggedProfile.{u} actual)
      (finiteModelContextFromTaggedProfile_isRestriction.{u} actual))

/-! ## Lifted arbitrary context preorder -/

/-- Lift a raw low context morphism between the tagged context embeddings. -/
def finiteModelTaggedLiftContextMorphism
    {A : ArchitectureObject FiniteModel.carrier}
    {source target : Site.ArchitectureContext A}
    (morphism : Site.ContextMorphism source target) :
    Site.ContextMorphism
      (finiteModelTaggedLiftArchitectureContext.{u} source)
      (finiteModelTaggedLiftArchitectureContext.{u} target) where
  supportMap := fun support => ULift.up (morphism.supportMap support.down)
  axisMap := fun axis => ULift.up (morphism.axisMap axis.down)
  observableRestrict := fun observable =>
    ULift.up (morphism.observableRestrict observable.down)

/-- Tagged lifting preserves the selected restriction role. -/
theorem finiteModelTaggedLiftContextMorphism_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    {source target : Site.ArchitectureContext A}
    (morphism : Site.ContextMorphism source target)
    (restriction : morphism.IsRestriction) :
    (finiteModelTaggedLiftContextMorphism.{u} morphism).IsRestriction := by
  rcases restriction with ⟨support, axis, observable, nongenerating⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro liftedSupport liftedAtom hread
    simpa [finiteModelTaggedLiftContextMorphism,
      finiteModelTaggedLiftArchitectureContext] using
      support (support := liftedSupport.down)
        (atom := finiteModelLiftCarrierEquiv.{u + 1}.atom.symm liftedAtom) hread
  · intro liftedAxis hread
    simpa [finiteModelTaggedLiftContextMorphism,
      finiteModelTaggedLiftArchitectureContext] using axis hread
  · intro liftedObservable hread
    simpa [finiteModelTaggedLiftContextMorphism,
      finiteModelTaggedLiftArchitectureContext] using observable hread
  · intro liftedSupport liftedAtom hread
    exact (finiteModelTaggedLiftArchitectureContext.{u} target).supportReads_objectFamily
      hread

/--
Lift an arbitrary low context preorder.  Every high context is first replaced
by its exact tagged source or finite-profile representative; readable maps are
then conjugated by the two generated profile restrictions.
-/
noncomputable def finiteModelLiftContextPreorderAt
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :
    Site.ContextPreorderCategory
      (finiteModelLiftArchitectureObject.{u + 1} A) where
  le source target :=
    preorder.le
      (finiteModelReflectTaggedArchitectureContext.{u} source)
      (finiteModelReflectTaggedArchitectureContext.{u} target)
  refl context := preorder.refl _
  trans := fun first second => preorder.trans first second
  readableMorphism := by
    intro source target relation
    exact Site.contextMorphismComp
      (finiteModelContextToTaggedReflection.{u} source)
      (Site.contextMorphismComp
        (finiteModelTaggedLiftContextMorphism.{u}
          (preorder.readableMorphism relation))
        (finiteModelContextFromTaggedReflection.{u} target))
  readableMorphism_isRestriction := by
    intro source target relation
    exact Site.contextMorphismComp_isRestriction
      (finiteModelContextToTaggedReflection_isRestriction.{u} source)
      (Site.contextMorphismComp_isRestriction
        (finiteModelTaggedLiftContextMorphism_isRestriction.{u}
          (preorder.readableMorphism relation)
          (preorder.readableMorphism_isRestriction relation))
        (finiteModelContextFromTaggedReflection_isRestriction.{u} target))

/-- Tagged source contexts retain exactly the original low preorder relation. -/
@[simp]
theorem finiteModelLiftContextPreorderAt_tagged_le_iff
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A)
    (source target : Site.ArchitectureContext A) :
    (finiteModelLiftContextPreorderAt.{u} preorder).le
        (finiteModelTaggedLiftArchitectureContext.{u} source)
        (finiteModelTaggedLiftArchitectureContext.{u} target) ↔
      preorder.le source target := by
  simp [finiteModelLiftContextPreorderAt]

/-- Low context-category object type with its universe fixed explicitly. -/
abbrev FiniteModelLowContextObject
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :=
  @Site.ContextCategoryObject FiniteModel.carrier A preorder

/-- High tagged context-category object type with its universe fixed explicitly. -/
abbrev FiniteModelTaggedContextObject
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :=
  @Site.ContextCategoryObject finiteModelLiftCarrier.{u + 1}
    (finiteModelLiftArchitectureObject.{u + 1} A)
    (finiteModelLiftContextPreorderAt.{u} preorder)

/-- Forward functor from the arbitrary low context preorder to its tagged lift. -/
noncomputable def finiteModelTaggedContextFunctor
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :
    FiniteModelLowContextObject preorder ⥤
      FiniteModelTaggedContextObject.{u} preorder where
  obj context :=
    ⟨finiteModelTaggedLiftArchitectureContext.{u} context.ctx⟩
  map := by
    intro source target morphism
    apply homOfLE
    change (finiteModelLiftContextPreorderAt.{u} preorder).le
      (finiteModelTaggedLiftArchitectureContext.{u} source.ctx)
      (finiteModelTaggedLiftArchitectureContext.{u} target.ctx)
    simpa using leOfHom morphism
  map_id := by intros; exact Subsingleton.elim _ _
  map_comp := by intros; exact Subsingleton.elim _ _

/-- Inverse functor sends every high context to its exact tag or finite profile. -/
noncomputable def finiteModelReflectedContextFunctor
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :
    FiniteModelTaggedContextObject.{u} preorder ⥤
      FiniteModelLowContextObject preorder where
  obj context :=
    ⟨finiteModelReflectTaggedArchitectureContext.{u} context.ctx⟩
  map := by
    intro source target morphism
    have relation : (finiteModelLiftContextPreorderAt.{u} preorder).le
        source.ctx target.ctx := leOfHom morphism
    apply homOfLE
    exact relation
  map_id := by intros; exact Subsingleton.elim _ _
  map_comp := by intros; exact Subsingleton.elim _ _

/-- The low unit component is strict on tagged context objects. -/
noncomputable def finiteModelTaggedContextUnitIsoApp
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A)
    (context : FiniteModelLowContextObject preorder) :
    context ≅
      (finiteModelTaggedContextFunctor.{u} preorder ⋙
        finiteModelReflectedContextFunctor.{u} preorder).obj context :=
  eqToIso (by
    rcases context with ⟨context⟩
    simp [finiteModelTaggedContextFunctor,
      finiteModelReflectedContextFunctor])

/-- Every high context is isomorphic, in the lifted preorder, to its tagged reflection. -/
noncomputable def finiteModelTaggedContextCounitIsoApp
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A)
    (context : FiniteModelTaggedContextObject.{u} preorder) :
    (finiteModelReflectedContextFunctor.{u} preorder ⋙
      finiteModelTaggedContextFunctor.{u} preorder).obj context ≅ context where
  hom := by
    apply homOfLE
    change preorder.le
      (finiteModelReflectTaggedArchitectureContext.{u}
        (finiteModelTaggedLiftArchitectureContext.{u}
          (finiteModelReflectTaggedArchitectureContext.{u} context.ctx)))
      (finiteModelReflectTaggedArchitectureContext.{u} context.ctx)
    simpa using preorder.refl
      (finiteModelReflectTaggedArchitectureContext.{u} context.ctx)
  inv := by
    apply homOfLE
    change preorder.le
      (finiteModelReflectTaggedArchitectureContext.{u} context.ctx)
      (finiteModelReflectTaggedArchitectureContext.{u}
        (finiteModelTaggedLiftArchitectureContext.{u}
          (finiteModelReflectTaggedArchitectureContext.{u} context.ctx)))
    simpa using preorder.refl
      (finiteModelReflectTaggedArchitectureContext.{u} context.ctx)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/--
The context category of an arbitrary finite-carrier package has a generated
successor-universe lift.  Tagged image objects are strict, while every
additional high context is represented by its finite Atom-reading profile.

This declaration supplies the successor-form context equivalence used by the
arbitrary-package helper route.  The exact-zero constructor is recorded
separately; the branch-conditioned G-110 contract does not combine them into a
single symbolic-universe producer.
-/
noncomputable def finiteModelTaggedContextEquivalence
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :
    FiniteModelLowContextObject preorder ≌
      FiniteModelTaggedContextObject.{u} preorder where
  functor := finiteModelTaggedContextFunctor.{u} preorder
  inverse := finiteModelReflectedContextFunctor.{u} preorder
  unitIso := NatIso.ofComponents
    (finiteModelTaggedContextUnitIsoApp.{u} preorder)
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (finiteModelTaggedContextCounitIsoApp.{u} preorder)
    (by intros; exact Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
