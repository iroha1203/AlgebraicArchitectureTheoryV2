import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedContextImageFunctor

/-!
# Reflection of the generated high context equivalence

This module reflects the context equivalence carried by the actual normalized
high prefix factor.  Objects retain their finite source carrier types while
their predicates and extension values are read from the actual high forward or
inverse image.  Maps and both sides of the unit and counit are obtained by
fullness of the generated-domain image functors.

The construction accepts no carrier shape, object preimage, functor,
equivalence, unit, or counit from its caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Actual high equivalence and carrier graphs -/

/-- The context equivalence projected from the actual normalized high factor. -/
noncomputable def finiteGeneratedActualHighContextEquivalence
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    Site.ContextCategoryObject
        ((finiteGeneratedOuterInput input base).highGeneratedLift.domain.algebra.contextPreorder) ≌
      Site.ContextCategoryObject
        (input.highGeneratedLift.domain.algebra.contextPreorder) :=
  (finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport.contextEquivalence

/-- The actual forward high image preserves the canonical lifted support carrier. -/
theorem finiteGeneratedActualHighContextEquivalence_functor_support_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
      ((finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj W)).ctx.Support) =
      ULift.{u} W.ctx.Support := by
  unfold finiteGeneratedActualHighContextEquivalence
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change
    (((inverseCorePackageBackwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextForward
      ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        (finiteGeneratedOuterInput input base).highAlignedBaseFromLowData).equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u}
          (finiteGeneratedOuterInput input base)).obj W))).ctx.Support) = _
  rw [inverseCorePackageBackwardUpper_contextFunctor_obj_support_type,
    inverseCorePackageForwardUpper_contextFunctor_obj_support_type]
  exact finiteGeneratedContextImageFunctor_support_type
    (finiteGeneratedOuterInput input base) W

/-- The actual forward high image preserves the canonical lifted axis carrier. -/
theorem finiteGeneratedActualHighContextEquivalence_functor_axis_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
      ((finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj W)).ctx.Axis) =
      ULift.{u} W.ctx.Axis := by
  unfold finiteGeneratedActualHighContextEquivalence
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change
    (((inverseCorePackageBackwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextForward
      ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        (finiteGeneratedOuterInput input base).highAlignedBaseFromLowData).equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u}
          (finiteGeneratedOuterInput input base)).obj W))).ctx.Axis) = _
  rw [inverseCorePackageBackwardUpper_contextFunctor_obj_axis_type,
    inverseCorePackageForwardUpper_contextFunctor_obj_axis_type]
  exact finiteGeneratedContextImageFunctor_axis_type
    (finiteGeneratedOuterInput input base) W

/-- The actual forward high image preserves the canonical lifted observable carrier. -/
theorem finiteGeneratedActualHighContextEquivalence_functor_observable_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
      ((finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj W)).ctx.Observable) =
      ULift.{u} W.ctx.Observable := by
  unfold finiteGeneratedActualHighContextEquivalence
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change
    (((inverseCorePackageBackwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextForward
      ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        (finiteGeneratedOuterInput input base).highAlignedBaseFromLowData).equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u}
          (finiteGeneratedOuterInput input base)).obj W))).ctx.Observable) = _
  rw [inverseCorePackageBackwardUpper_contextFunctor_obj_observable_type,
    inverseCorePackageForwardUpper_contextFunctor_obj_observable_type]
  exact finiteGeneratedContextImageFunctor_observable_type
    (finiteGeneratedOuterInput input base) W

/-- The actual forward high image preserves the canonical lifted extension carrier. -/
theorem finiteGeneratedActualHighContextEquivalence_functor_extension_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
      ((finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj W)).ctx.Extension) =
      ULift.{u} W.ctx.Extension := by
  unfold finiteGeneratedActualHighContextEquivalence
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change
    (((inverseCorePackageBackwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextForward
      ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        (finiteGeneratedOuterInput input base).highAlignedBaseFromLowData).equationTransport.contextForward
        ((finiteGeneratedContextImageFunctor.{u}
          (finiteGeneratedOuterInput input base)).obj W))).ctx.Extension) = _
  rw [inverseCorePackageBackwardUpper_contextFunctor_obj_extension_type,
    inverseCorePackageForwardUpper_contextFunctor_obj_extension_type]
  exact finiteGeneratedContextImageFunctor_extension_type
    (finiteGeneratedOuterInput input base) W

/-- The actual inverse high image preserves the canonical lifted support carrier. -/
theorem finiteGeneratedActualHighContextEquivalence_inverse_support_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (((finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
      ((finiteGeneratedContextImageFunctor.{u} input).obj W)).ctx.Support) =
      ULift.{u} W.ctx.Support := by
  unfold finiteGeneratedActualHighContextEquivalence
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change
    (((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        (finiteGeneratedOuterInput input base).highAlignedBaseFromLowData).equationTransport.contextBackward
      ((inverseCorePackageBackwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextBackward
        ((finiteGeneratedContextImageFunctor.{u} input).obj W))).ctx.Support) = _
  rw [inverseCorePackageForwardUpper_contextInverse_obj_support_type,
    inverseCorePackageBackwardUpper_contextInverse_obj_support_type]
  exact finiteGeneratedContextImageFunctor_support_type input W

/-- The actual inverse high image preserves the canonical lifted axis carrier. -/
theorem finiteGeneratedActualHighContextEquivalence_inverse_axis_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (((finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
      ((finiteGeneratedContextImageFunctor.{u} input).obj W)).ctx.Axis) =
      ULift.{u} W.ctx.Axis := by
  unfold finiteGeneratedActualHighContextEquivalence
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change
    (((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        (finiteGeneratedOuterInput input base).highAlignedBaseFromLowData).equationTransport.contextBackward
      ((inverseCorePackageBackwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextBackward
        ((finiteGeneratedContextImageFunctor.{u} input).obj W))).ctx.Axis) = _
  rw [inverseCorePackageForwardUpper_contextInverse_obj_axis_type,
    inverseCorePackageBackwardUpper_contextInverse_obj_axis_type]
  exact finiteGeneratedContextImageFunctor_axis_type input W

/-- The actual inverse high image preserves the canonical lifted observable carrier. -/
theorem finiteGeneratedActualHighContextEquivalence_inverse_observable_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (((finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
      ((finiteGeneratedContextImageFunctor.{u} input).obj W)).ctx.Observable) =
      ULift.{u} W.ctx.Observable := by
  unfold finiteGeneratedActualHighContextEquivalence
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change
    (((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        (finiteGeneratedOuterInput input base).highAlignedBaseFromLowData).equationTransport.contextBackward
      ((inverseCorePackageBackwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextBackward
        ((finiteGeneratedContextImageFunctor.{u} input).obj W))).ctx.Observable) = _
  rw [inverseCorePackageForwardUpper_contextInverse_obj_observable_type,
    inverseCorePackageBackwardUpper_contextInverse_obj_observable_type]
  exact finiteGeneratedContextImageFunctor_observable_type input W

/-- The actual inverse high image preserves the canonical lifted extension carrier. -/
theorem finiteGeneratedActualHighContextEquivalence_inverse_extension_type
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (((finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
      ((finiteGeneratedContextImageFunctor.{u} input).obj W)).ctx.Extension) =
      ULift.{u} W.ctx.Extension := by
  unfold finiteGeneratedActualHighContextEquivalence
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  change
    (((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        (finiteGeneratedOuterInput input base).highAlignedBaseFromLowData).equationTransport.contextBackward
      ((inverseCorePackageBackwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextBackward
        ((finiteGeneratedContextImageFunctor.{u} input).obj W))).ctx.Extension) = _
  rw [inverseCorePackageForwardUpper_contextInverse_obj_extension_type,
    inverseCorePackageBackwardUpper_contextInverse_obj_extension_type]
  exact finiteGeneratedContextImageFunctor_extension_type input W

private def contextCarrierShapeOfCast
    {A B : ArchitectureObject FiniteModel.carrier}
    {highObject : ArchitectureObject finiteModelLiftCarrier.{u}}
    (template : Site.ArchitectureContext A)
    (actual : Site.ArchitectureContext highObject)
    (object_eq : highObject = finiteModelLiftArchitectureObject.{u} B)
    (support_eq : actual.Support = ULift.{u} template.Support)
    (axis_eq : actual.Axis = ULift.{u} template.Axis)
    (observable_eq : actual.Observable = ULift.{u} template.Observable)
    (extension_eq : actual.Extension = ULift.{u} template.Extension) :
    FiniteModelContextCarrierShape template
      (cast (congrArg Site.ArchitectureContext object_eq) actual) := by
  subst highObject
  exact {
    support_eq := support_eq.symm
    axis_eq := axis_eq.symm
    observable_eq := observable_eq.symm
    extension_eq := extension_eq.symm
  }

/-! ## Reflected objects and image landing -/

/-- The actual forward high context, aligned with the canonical target lift. -/
noncomputable def finiteGeneratedReflectedForwardActualContext
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u}
        input.lowGeneratedLift.domain.object) :=
  cast (congrArg Site.ArchitectureContext
      (finiteGeneratedHighDomain_object_lift.{u} input))
    (((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
      ((finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj W)).ctx)

/-- Internally generated carrier shape of the actual forward high context. -/
noncomputable def finiteGeneratedReflectedForwardCarrierShape
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    FiniteModelContextCarrierShape W.ctx
      (finiteGeneratedReflectedForwardActualContext input lift base W) :=
  contextCarrierShapeOfCast W.ctx _
    (finiteGeneratedHighDomain_object_lift.{u} input)
    (finiteGeneratedActualHighContextEquivalence_functor_support_type
      input lift base W)
    (finiteGeneratedActualHighContextEquivalence_functor_axis_type
      input lift base W)
    (finiteGeneratedActualHighContextEquivalence_functor_observable_type
      input lift base W)
    (finiteGeneratedActualHighContextEquivalence_functor_extension_type
      input lift base W)

/-- Reflect the actual forward high object, including its predicates and extension. -/
noncomputable def finiteGeneratedReflectedForwardObject
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder) where
  ctx := finiteModelReflectArchitectureContextAt W.ctx
    (finiteGeneratedReflectedForwardActualContext input lift base W)
    (finiteGeneratedReflectedForwardCarrierShape input lift base W)

/-- The actual inverse high context, aligned with the canonical outer lift. -/
noncomputable def finiteGeneratedReflectedInverseActualContext
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    Site.ArchitectureContext
      (finiteModelLiftArchitectureObject.{u}
        (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.object) :=
  cast (congrArg Site.ArchitectureContext
      (finiteGeneratedHighDomain_object_lift.{u}
        (finiteGeneratedOuterInput input base)))
    (((finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
      ((finiteGeneratedContextImageFunctor.{u} input).obj W)).ctx)

/-- Internally generated carrier shape of the actual inverse high context. -/
noncomputable def finiteGeneratedReflectedInverseCarrierShape
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    FiniteModelContextCarrierShape W.ctx
      (finiteGeneratedReflectedInverseActualContext input lift base W) :=
  contextCarrierShapeOfCast W.ctx _
    (finiteGeneratedHighDomain_object_lift.{u}
      (finiteGeneratedOuterInput input base))
    (finiteGeneratedActualHighContextEquivalence_inverse_support_type
      input lift base W)
    (finiteGeneratedActualHighContextEquivalence_inverse_axis_type
      input lift base W)
    (finiteGeneratedActualHighContextEquivalence_inverse_observable_type
      input lift base W)
    (finiteGeneratedActualHighContextEquivalence_inverse_extension_type
      input lift base W)

/-- Reflect the actual inverse high object, including its predicates and extension. -/
noncomputable def finiteGeneratedReflectedInverseObject
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder) where
  ctx := finiteModelReflectArchitectureContextAt W.ctx
    (finiteGeneratedReflectedInverseActualContext input lift base W)
    (finiteGeneratedReflectedInverseCarrierShape input lift base W)

private theorem contextCategoryObject_ext
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {W V : Site.ContextCategoryObject C} (h : W.ctx = V.ctx) : W = V := by
  cases W
  cases V
  cases h
  rfl

private theorem cast_injective_local
    {alpha beta : Sort v} (equality : alpha = beta) {first second : alpha}
    (h : cast equality first = cast equality second) : first = second := by
  cases equality
  exact h

/-- The reflected forward object lands exactly on the actual high forward object. -/
theorem finiteGeneratedReflectedForwardObject_image_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u} input).obj
        (finiteGeneratedReflectedForwardObject input lift base W) =
      (finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
        ((finiteGeneratedContextImageFunctor.{u}
          (finiteGeneratedOuterInput input base)).obj W) := by
  apply contextCategoryObject_ext
  apply cast_injective_local (congrArg Site.ArchitectureContext
    (finiteGeneratedHighDomain_object_lift.{u} input))
  calc
    cast (congrArg Site.ArchitectureContext
        (finiteGeneratedHighDomain_object_lift.{u} input))
        (((finiteGeneratedContextImageFunctor.{u} input).obj
          (finiteGeneratedReflectedForwardObject input lift base W)).ctx) =
      finiteModelLiftArchitectureContext.{u}
        (finiteGeneratedReflectedForwardObject input lift base W).ctx :=
      finiteGeneratedContextImageFunctor_obj_ctx_eq_lift input _
    _ = finiteGeneratedReflectedForwardActualContext input lift base W :=
      finiteModelLiftArchitectureContext_reflectAt W.ctx
        (finiteGeneratedReflectedForwardActualContext input lift base W)
        (finiteGeneratedReflectedForwardCarrierShape input lift base W)
    _ = cast (congrArg Site.ArchitectureContext
        (finiteGeneratedHighDomain_object_lift.{u} input))
        (((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
          ((finiteGeneratedContextImageFunctor.{u}
            (finiteGeneratedOuterInput input base)).obj W)).ctx) := rfl

/-- The reflected inverse object lands exactly on the actual high inverse object. -/
theorem finiteGeneratedReflectedInverseObject_image_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj
        (finiteGeneratedReflectedInverseObject input lift base W) =
      (finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
        ((finiteGeneratedContextImageFunctor.{u} input).obj W) := by
  apply contextCategoryObject_ext
  apply cast_injective_local (congrArg Site.ArchitectureContext
    (finiteGeneratedHighDomain_object_lift.{u}
      (finiteGeneratedOuterInput input base)))
  calc
    cast (congrArg Site.ArchitectureContext
        (finiteGeneratedHighDomain_object_lift.{u}
          (finiteGeneratedOuterInput input base)))
        (((finiteGeneratedContextImageFunctor.{u}
          (finiteGeneratedOuterInput input base)).obj
          (finiteGeneratedReflectedInverseObject input lift base W)).ctx) =
      finiteModelLiftArchitectureContext.{u}
        (finiteGeneratedReflectedInverseObject input lift base W).ctx :=
      finiteGeneratedContextImageFunctor_obj_ctx_eq_lift
        (finiteGeneratedOuterInput input base) _
    _ = finiteGeneratedReflectedInverseActualContext input lift base W :=
      finiteModelLiftArchitectureContext_reflectAt W.ctx
        (finiteGeneratedReflectedInverseActualContext input lift base W)
        (finiteGeneratedReflectedInverseCarrierShape input lift base W)
    _ = cast (congrArg Site.ArchitectureContext
        (finiteGeneratedHighDomain_object_lift.{u}
          (finiteGeneratedOuterInput input base)))
        (((finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
          ((finiteGeneratedContextImageFunctor.{u} input).obj W)).ctx) := rfl

/-! ## Reflected maps and functors -/

/-- Actual high forward map with endpoints rewritten to reflected image objects. -/
noncomputable def finiteGeneratedReflectedForwardHighMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {W V : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)}
    (f : W ⟶ V) :
    (finiteGeneratedContextImageFunctor.{u} input).obj
        (finiteGeneratedReflectedForwardObject input lift base W) ⟶
      (finiteGeneratedContextImageFunctor.{u} input).obj
        (finiteGeneratedReflectedForwardObject input lift base V) :=
  eqToHom (finiteGeneratedReflectedForwardObject_image_eq input lift base W) ≫
    (finiteGeneratedActualHighContextEquivalence input lift base).functor.map
      ((finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).map f) ≫
    eqToHom (finiteGeneratedReflectedForwardObject_image_eq
      input lift base V).symm

/-- Reflect an actual high forward map through fullness of the target image functor. -/
noncomputable def finiteGeneratedReflectedForwardMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {W V : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)}
    (f : W ⟶ V) :
    finiteGeneratedReflectedForwardObject input lift base W ⟶
      finiteGeneratedReflectedForwardObject input lift base V :=
  (finiteGeneratedContextImageFunctor.{u} input).preimage
    (finiteGeneratedReflectedForwardHighMap input lift base f)

/-- Actual high inverse map with endpoints rewritten to reflected image objects. -/
noncomputable def finiteGeneratedReflectedInverseHighMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {W V : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)}
    (f : W ⟶ V) :
    (finiteGeneratedContextImageFunctor.{u}
      (finiteGeneratedOuterInput input base)).obj
        (finiteGeneratedReflectedInverseObject input lift base W) ⟶
      (finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj
        (finiteGeneratedReflectedInverseObject input lift base V) :=
  eqToHom (finiteGeneratedReflectedInverseObject_image_eq input lift base W) ≫
    (finiteGeneratedActualHighContextEquivalence input lift base).inverse.map
      ((finiteGeneratedContextImageFunctor.{u} input).map f) ≫
    eqToHom (finiteGeneratedReflectedInverseObject_image_eq
      input lift base V).symm

/-- Reflect an actual high inverse map through fullness of the source image functor. -/
noncomputable def finiteGeneratedReflectedInverseMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {W V : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)}
    (f : W ⟶ V) :
    finiteGeneratedReflectedInverseObject input lift base W ⟶
      finiteGeneratedReflectedInverseObject input lift base V :=
  (finiteGeneratedContextImageFunctor.{u}
    (finiteGeneratedOuterInput input base)).preimage
      (finiteGeneratedReflectedInverseHighMap input lift base f)

/-- Forward functor reflected from the actual high equivalence. -/
noncomputable def finiteGeneratedReflectedForwardFunctor
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    Site.ContextCategoryObject
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder) ⥤
      Site.ContextCategoryObject
        (input.lowGeneratedLift.domain.algebra.contextPreorder) where
  obj := finiteGeneratedReflectedForwardObject input lift base
  map := finiteGeneratedReflectedForwardMap input lift base
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Inverse functor reflected from the actual high equivalence. -/
noncomputable def finiteGeneratedReflectedInverseFunctor
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    Site.ContextCategoryObject
        (input.lowGeneratedLift.domain.algebra.contextPreorder) ⥤
      Site.ContextCategoryObject
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder) where
  obj := finiteGeneratedReflectedInverseObject input lift base
  map := finiteGeneratedReflectedInverseMap input lift base
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-! ## Reflected unit and counit -/

/-- The actual high unit component rewritten between generated-image endpoints. -/
noncomputable def finiteGeneratedReflectedUnitHighHom
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u}
      (finiteGeneratedOuterInput input base)).obj W ⟶
      (finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj
        (finiteGeneratedReflectedInverseObject input lift base
          (finiteGeneratedReflectedForwardObject input lift base W)) :=
  (finiteGeneratedActualHighContextEquivalence input lift base).unitIso.hom.app _ ≫
    (finiteGeneratedActualHighContextEquivalence input lift base).inverse.map
      (eqToHom (finiteGeneratedReflectedForwardObject_image_eq
        input lift base W).symm) ≫
    eqToHom (finiteGeneratedReflectedInverseObject_image_eq input lift base
      (finiteGeneratedReflectedForwardObject input lift base W)).symm

/-- The actual high inverse-unit component rewritten between generated-image endpoints. -/
noncomputable def finiteGeneratedReflectedUnitHighInv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u}
      (finiteGeneratedOuterInput input base)).obj
        (finiteGeneratedReflectedInverseObject input lift base
          (finiteGeneratedReflectedForwardObject input lift base W)) ⟶
      (finiteGeneratedContextImageFunctor.{u}
        (finiteGeneratedOuterInput input base)).obj W :=
  eqToHom (finiteGeneratedReflectedInverseObject_image_eq input lift base
      (finiteGeneratedReflectedForwardObject input lift base W)) ≫
    (finiteGeneratedActualHighContextEquivalence input lift base).inverse.map
      (eqToHom (finiteGeneratedReflectedForwardObject_image_eq
        input lift base W)) ≫
    (finiteGeneratedActualHighContextEquivalence input lift base).unitIso.inv.app _

/-- The reflected unit component is the source-image preimage of the actual high unit. -/
noncomputable def finiteGeneratedReflectedUnitIsoApp
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    W ≅ finiteGeneratedReflectedInverseObject input lift base
      (finiteGeneratedReflectedForwardObject input lift base W) where
  hom := (finiteGeneratedContextImageFunctor.{u}
    (finiteGeneratedOuterInput input base)).preimage
      (finiteGeneratedReflectedUnitHighHom input lift base W)
  inv := (finiteGeneratedContextImageFunctor.{u}
    (finiteGeneratedOuterInput input base)).preimage
      (finiteGeneratedReflectedUnitHighInv input lift base W)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- The actual high counit component rewritten between generated-image endpoints. -/
noncomputable def finiteGeneratedReflectedCounitHighHom
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u} input).obj
        (finiteGeneratedReflectedForwardObject input lift base
          (finiteGeneratedReflectedInverseObject input lift base W)) ⟶
      (finiteGeneratedContextImageFunctor.{u} input).obj W :=
  eqToHom (finiteGeneratedReflectedForwardObject_image_eq input lift base
      (finiteGeneratedReflectedInverseObject input lift base W)) ≫
    (finiteGeneratedActualHighContextEquivalence input lift base).functor.map
      (eqToHom (finiteGeneratedReflectedInverseObject_image_eq
        input lift base W)) ≫
    (finiteGeneratedActualHighContextEquivalence input lift base).counitIso.hom.app _

/-- The actual high inverse-counit component rewritten between generated-image endpoints. -/
noncomputable def finiteGeneratedReflectedCounitHighInv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u} input).obj W ⟶
      (finiteGeneratedContextImageFunctor.{u} input).obj
        (finiteGeneratedReflectedForwardObject input lift base
          (finiteGeneratedReflectedInverseObject input lift base W)) :=
  (finiteGeneratedActualHighContextEquivalence input lift base).counitIso.inv.app _ ≫
    (finiteGeneratedActualHighContextEquivalence input lift base).functor.map
      (eqToHom (finiteGeneratedReflectedInverseObject_image_eq
        input lift base W).symm) ≫
    eqToHom (finiteGeneratedReflectedForwardObject_image_eq input lift base
      (finiteGeneratedReflectedInverseObject input lift base W)).symm

/-- The reflected counit component is the target-image preimage of the actual high counit. -/
noncomputable def finiteGeneratedReflectedCounitIsoApp
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    finiteGeneratedReflectedForwardObject input lift base
        (finiteGeneratedReflectedInverseObject input lift base W) ≅ W where
  hom := (finiteGeneratedContextImageFunctor.{u} input).preimage
    (finiteGeneratedReflectedCounitHighHom input lift base W)
  inv := (finiteGeneratedContextImageFunctor.{u} input).preimage
    (finiteGeneratedReflectedCounitHighInv input lift base W)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-! ## Producer and public computational graphs -/

/--
Reflect the complete context equivalence of the actual normalized high factor.
The triangle law and naturality proofs use thinness only after all object and
map data have been obtained from the actual high equivalence.
-/
noncomputable def finiteGeneratedReflectedContextEquivalence
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    FiniteGeneratedReflectedContextEquivalenceOutput input base where
  functor := finiteGeneratedReflectedForwardFunctor input lift base
  inverse := finiteGeneratedReflectedInverseFunctor input lift base
  unitIso := NatIso.ofComponents
    (finiteGeneratedReflectedUnitIsoApp input lift base)
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (finiteGeneratedReflectedCounitIsoApp input lift base)
    (by intros; exact Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

/-- The producer's forward object is the reflection of the actual high forward object. -/
@[simp]
theorem finiteGeneratedReflectedContextEquivalence_functor_obj
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedReflectedContextEquivalence input lift base).functor.obj W =
      finiteGeneratedReflectedForwardObject input lift base W := rfl

/-- The producer's inverse object is the reflection of the actual high inverse object. -/
@[simp]
theorem finiteGeneratedReflectedContextEquivalence_inverse_obj
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedReflectedContextEquivalence input lift base).inverse.obj W =
      finiteGeneratedReflectedInverseObject input lift base W := rfl

/-- Mapping a reflected forward arrow back to the high image recovers the actual high map. -/
theorem finiteGeneratedReflectedForwardMap_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {W V : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)}
    (f : W ⟶ V) :
    (finiteGeneratedContextImageFunctor.{u} input).map
        (finiteGeneratedReflectedForwardMap input lift base f) =
      finiteGeneratedReflectedForwardHighMap input lift base f :=
  Functor.map_preimage _ _

/-- Mapping a reflected inverse arrow back to the high image recovers the actual high map. -/
theorem finiteGeneratedReflectedInverseMap_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {W V : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)}
    (f : W ⟶ V) :
    (finiteGeneratedContextImageFunctor.{u}
      (finiteGeneratedOuterInput input base)).map
        (finiteGeneratedReflectedInverseMap input lift base f) =
      finiteGeneratedReflectedInverseHighMap input lift base f :=
  Functor.map_preimage _ _

/-- The reflected unit hom maps to the actual high unit route. -/
theorem finiteGeneratedReflectedUnitIsoApp_hom_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u}
      (finiteGeneratedOuterInput input base)).map
        (finiteGeneratedReflectedUnitIsoApp input lift base W).hom =
      finiteGeneratedReflectedUnitHighHom input lift base W :=
  Functor.map_preimage _ _

/-- The reflected unit inverse maps to the actual high inverse-unit route. -/
theorem finiteGeneratedReflectedUnitIsoApp_inv_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u}
      (finiteGeneratedOuterInput input base)).map
        (finiteGeneratedReflectedUnitIsoApp input lift base W).inv =
      finiteGeneratedReflectedUnitHighInv input lift base W :=
  Functor.map_preimage _ _

/-- The reflected counit hom maps to the actual high counit route. -/
theorem finiteGeneratedReflectedCounitIsoApp_hom_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u} input).map
        (finiteGeneratedReflectedCounitIsoApp input lift base W).hom =
      finiteGeneratedReflectedCounitHighHom input lift base W :=
  Functor.map_preimage _ _

/-- The reflected counit inverse maps to the actual high inverse-counit route. -/
theorem finiteGeneratedReflectedCounitIsoApp_inv_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      (input.lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedContextImageFunctor.{u} input).map
        (finiteGeneratedReflectedCounitIsoApp input lift base W).inv =
      finiteGeneratedReflectedCounitHighInv input lift base W :=
  Functor.map_preimage _ _

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
