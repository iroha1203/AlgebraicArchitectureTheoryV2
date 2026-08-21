import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedContextImageDescent
import ResearchLean.AG.DoctrineFiberProduct.CartesianTarget

/-!
# Generated-domain context image functor

This module embeds each generated finite-model context category into its
canonically lifted generated context category.  The construction first uses
the low inverse-package forward context equivalence, then the canonical finite
context lift, and finally the inverse of the independently generated high
forward context equivalence.

No context carrier shape, object equality, context equivalence, or image
certificate is accepted from a caller.  The endpoint and four context-carrier
graphs below are generated from the same finite input.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Canonical Atom and object alignment -/

/-- Conjugate a finite-model Atom permutation through the canonical universe lift. -/
def finiteModelLiftAtomEquiv
    (equiv : Equiv.Perm FiniteModel.carrier.Atom) :
    Equiv.Perm finiteModelLiftCarrier.{u}.Atom :=
  finiteModelLiftCarrierEquiv.{u}.atom.symm.trans
    (equiv.trans finiteModelLiftCarrierEquiv.{u}.atom)

/-- Canonical Atom-permutation lifting commutes with inversion. -/
theorem finiteModelLiftAtomEquiv_symm
    (equiv : Equiv.Perm FiniteModel.carrier.Atom) :
    (finiteModelLiftAtomEquiv.{u} equiv).symm =
      finiteModelLiftAtomEquiv.{u} equiv.symm := by
  apply Equiv.ext
  intro atom
  rcases atom with ⟨atom⟩
  simp [finiteModelLiftAtomEquiv]

/--
Canonical configuration lifting commutes with direct-image transport by an
arbitrary finite-model Atom permutation.
-/
theorem finiteModelLiftAtomConfiguration_transport_equiv
    (equiv : Equiv.Perm FiniteModel.carrier.Atom)
    (configuration : AtomConfiguration FiniteModel.carrier) :
    finiteModelLiftAtomConfiguration.{u}
        (configuration.transport equiv) =
      (finiteModelLiftAtomConfiguration.{u} configuration).transport
        (finiteModelLiftAtomEquiv.{u} equiv) := by
  apply AtomConfiguration.ext
  · ext atom
    rcases atom with ⟨atom⟩
    simp [finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily,
      finiteModelLiftAtomEquiv, AtomConfiguration.transport,
      AtomFamily.transport]
    constructor
    · rintro ⟨source, hsource, htarget⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom source, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom htarget
    · rintro ⟨source, hsource, htarget⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom.symm source, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm htarget
  · intro first second
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    simp [finiteModelLiftAtomConfiguration, finiteModelLiftAtomEquiv,
      AtomConfiguration.transport]
    constructor
    · rintro ⟨source₁, source₂, hsource, hfirst, hsecond⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom source₁,
        finiteModelLiftCarrierEquiv.{u}.atom source₂, ?_, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom hfirst
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom hsecond
    · rintro ⟨source₁, source₂, hsource, hfirst, hsecond⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom.symm source₁,
        finiteModelLiftCarrierEquiv.{u}.atom.symm source₂, ?_, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hfirst
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hsecond
  · intro first second
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    simp [finiteModelLiftAtomConfiguration, finiteModelLiftAtomEquiv,
      AtomConfiguration.transport]
    constructor
    · rintro ⟨source₁, source₂, hsource, hfirst, hsecond⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom source₁,
        finiteModelLiftCarrierEquiv.{u}.atom source₂, ?_, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom hfirst
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom hsecond
    · rintro ⟨source₁, source₂, hsource, hfirst, hsecond⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom.symm source₁,
        finiteModelLiftCarrierEquiv.{u}.atom.symm source₂, ?_, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hfirst
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hsecond

/--
Canonical architecture-object lifting commutes with transport by an arbitrary
finite-model Atom permutation.
-/
theorem finiteModelLiftArchitectureObject_transport_equiv
    (equiv : Equiv.Perm FiniteModel.carrier.Atom)
    (object : ArchitectureObject FiniteModel.carrier) :
    finiteModelLiftArchitectureObject.{u}
        (transportArchitectureObject equiv object) =
      transportArchitectureObject (finiteModelLiftAtomEquiv.{u} equiv)
        (finiteModelLiftArchitectureObject.{u} object) := by
  cases object with
  | mk configuration StructureMaps SelectedQuantities structureMaps selectedQuantities =>
      simp [transportArchitectureObject, finiteModelLiftArchitectureObject,
        finiteModelLiftAtomConfiguration_transport_equiv]

private theorem architectureContext_ext_of_heq
    {U : AtomCarrier.{u}} {object : ArchitectureObject U}
    (first second : Site.ArchitectureContext object)
    (support_type : first.Support = second.Support)
    (axis_type : first.Axis = second.Axis)
    (observable_type : first.Observable = second.Observable)
    (support_reads : HEq first.minimal.supportReads
      second.minimal.supportReads)
    (axis_reads : HEq first.minimal.axisReads second.minimal.axisReads)
    (observable_reads : HEq first.minimal.observableReads
      second.minimal.observableReads)
    (extension_type : first.Extension = second.Extension)
    (extension_value : HEq first.extension second.extension) :
    first = second := by
  rcases first with
    ⟨⟨Support₁, Axis₁, Observable₁, supportReads₁,
      supportReadsObject₁, axisReads₁, observableReads₁⟩,
      Extension₁, extension₁⟩
  rcases second with
    ⟨⟨Support₂, Axis₂, Observable₂, supportReads₂,
      supportReadsObject₂, axisReads₂, observableReads₂⟩,
      Extension₂, extension₂⟩
  dsimp [Site.ArchitectureContext.Support, Site.ArchitectureContext.Axis,
    Site.ArchitectureContext.Observable] at support_type
  dsimp [Site.ArchitectureContext.Support, Site.ArchitectureContext.Axis,
    Site.ArchitectureContext.Observable] at axis_type
  dsimp [Site.ArchitectureContext.Support, Site.ArchitectureContext.Axis,
    Site.ArchitectureContext.Observable] at observable_type
  dsimp at support_reads axis_reads observable_reads extension_type
  dsimp at extension_value
  cases support_type
  cases axis_type
  cases observable_type
  cases extension_type
  have hs : supportReads₁ = supportReads₂ := eq_of_heq support_reads
  have ha : axisReads₁ = axisReads₂ := eq_of_heq axis_reads
  have ho : observableReads₁ = observableReads₂ := eq_of_heq observable_reads
  have he : extension₁ = extension₂ := eq_of_heq extension_value
  cases hs
  cases ha
  cases ho
  cases he
  rfl

private theorem castArchitectureContext_fields
    {U : AtomCarrier.{u}} {source target : ArchitectureObject U}
    (equality : source = target) (context : Site.ArchitectureContext source) :
    let transported := cast (congrArg Site.ArchitectureContext equality) context
    transported.Support = context.Support ∧
      transported.Axis = context.Axis ∧
      transported.Observable = context.Observable ∧
      HEq transported.minimal.supportReads context.minimal.supportReads ∧
      HEq transported.minimal.axisReads context.minimal.axisReads ∧
      HEq transported.minimal.observableReads context.minimal.observableReads ∧
      transported.Extension = context.Extension ∧
      HEq transported.extension context.extension := by
  cases equality
  exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩

/--
Canonical context lifting commutes with forward transport by a finite-model
Atom permutation, including all predicates and the extension value.
-/
theorem finiteModelLiftArchitectureContext_transport_equiv
    (equiv : Equiv.Perm FiniteModel.carrier.Atom)
    {object : ArchitectureObject FiniteModel.carrier}
    (context : Site.ArchitectureContext object) :
    cast (congrArg Site.ArchitectureContext
        (finiteModelLiftArchitectureObject_transport_equiv.{u} equiv object))
        (finiteModelLiftArchitectureContext.{u}
          (transportArchitectureContext equiv object context)) =
      transportArchitectureContext (finiteModelLiftAtomEquiv.{u} equiv)
        (finiteModelLiftArchitectureObject.{u} object)
        (finiteModelLiftArchitectureContext.{u} context) := by
  let hobject :=
    finiteModelLiftArchitectureObject_transport_equiv.{u} equiv object
  let sourceContext := finiteModelLiftArchitectureContext.{u}
    (transportArchitectureContext equiv object context)
  let targetContext :=
    transportArchitectureContext (finiteModelLiftAtomEquiv.{u} equiv)
      (finiteModelLiftArchitectureObject.{u} object)
      (finiteModelLiftArchitectureContext.{u} context)
  have hfields := castArchitectureContext_fields hobject sourceContext
  apply architectureContext_ext_of_heq
  · exact hfields.1
  · exact hfields.2.1
  · exact hfields.2.2.1
  · exact HEq.trans hfields.2.2.2.1 (by
      apply heq_of_eq
      funext support atom
      simp [sourceContext, finiteModelLiftArchitectureContext,
        transportArchitectureContext, finiteModelLiftAtomEquiv])
  · exact HEq.trans hfields.2.2.2.2.1 (by
      apply heq_of_eq
      rfl)
  · exact HEq.trans hfields.2.2.2.2.2.1 (by
      apply heq_of_eq
      rfl)
  · exact hfields.2.2.2.2.2.2.1
  · exact HEq.trans hfields.2.2.2.2.2.2.2 (by
      apply heq_of_eq
      rfl)

/--
Canonical context lifting also commutes with backward transport by a
finite-model Atom permutation.
-/
theorem finiteModelLiftArchitectureContext_transportBackward_equiv
    (equiv : Equiv.Perm FiniteModel.carrier.Atom)
    {object : ArchitectureObject FiniteModel.carrier}
    (context : Site.ArchitectureContext
      (transportArchitectureObject equiv object)) :
    finiteModelLiftArchitectureContext.{u}
        (transportArchitectureContextBackward equiv object context) =
      transportArchitectureContextBackward (finiteModelLiftAtomEquiv.{u} equiv)
        (finiteModelLiftArchitectureObject.{u} object)
        (cast (congrArg Site.ArchitectureContext
          (finiteModelLiftArchitectureObject_transport_equiv.{u} equiv object))
          (finiteModelLiftArchitectureContext.{u} context)) := by
  have hforward := finiteModelLiftArchitectureContext_transport_equiv.{u}
    equiv (transportArchitectureContextBackward equiv object context)
  rw [transportArchitectureContext_forward_backward] at hforward
  have hbackward := congrArg
    (transportArchitectureContextBackward
      (finiteModelLiftAtomEquiv.{u} equiv)
      (finiteModelLiftArchitectureObject.{u} object)) hforward
  simpa only [transportArchitectureContext_backward_forward] using hbackward.symm

/--
The high generated-domain object is the canonical universe lift of the low
generated-domain object.  Both endpoints are generated internally from the
same finite input.
-/
theorem finiteGeneratedHighDomain_object_lift
    (input : FiniteGeneratedLiftInput) :
    input.highGeneratedLift.domain.object =
      finiteModelLiftArchitectureObject.{u}
        input.lowGeneratedLift.domain.object := by
  change inverseBaseObject finiteModelLiftCorePackage.{u}
      input.highAlignedBaseFromLowData =
    finiteModelLiftArchitectureObject.{u}
      (inverseBaseObject FiniteModel.corePackage input.hom)
  rw [inverseBaseObject_eq, inverseBaseObject_eq,
    finiteModelLiftCorePackage_object, input.highAlignedBaseFromLowData_eq]
  change transportArchitectureObject
      (finiteModelLiftAtomEquiv.{u}
        input.hom.doctrineHom.atomEquiv).symm
      (finiteModelLiftArchitectureObject.{u} FiniteModel.corePackage.object) =
    finiteModelLiftArchitectureObject.{u}
      (transportArchitectureObject input.hom.doctrineHom.atomEquiv.symm
        FiniteModel.corePackage.object)
  rw [finiteModelLiftAtomEquiv_symm input.hom.doctrineHom.atomEquiv]
  exact (finiteModelLiftArchitectureObject_transport_equiv.{u}
    input.hom.doctrineHom.atomEquiv.symm FiniteModel.corePackage.object).symm

/-! ## Generated-domain image functor -/

/--
Embed the low generated-domain context category into the high generated-domain
context category through the two internally generated inverse-package context
equivalences and canonical finite-model context lifting.
-/
noncomputable def finiteGeneratedContextImageFunctor
    (input : FiniteGeneratedLiftInput) :
    Site.ContextCategoryObject
        (input.lowGeneratedLift.domain.algebra.contextPreorder) ⥤
      Site.ContextCategoryObject
        (input.highGeneratedLift.domain.algebra.contextPreorder) :=
  (inverseCorePackageForwardUpper FiniteModel.corePackage
      input.hom).equationTransport.contextEquivalence.functor ⋙
    finiteModelLiftContextFunctor.{u} FiniteModel.object ⋙
    (input.highPackageHomFromLowData.upper.equationTransport.contextEquivalence).inverse

/--
The generated-domain context image functor is full.  The proof explicitly
reflects a high arrow through the high inverse equivalence, the canonical
context lift, and the low forward equivalence in that order.
-/
noncomputable instance finiteGeneratedContextImageFunctor_full
    (input : FiniteGeneratedLiftInput) :
    (finiteGeneratedContextImageFunctor.{u} input).Full where
  map_surjective f := by
    obtain ⟨highTargetMap, highTargetMap_eq⟩ :=
      (input.highPackageHomFromLowData.upper.equationTransport.contextEquivalence).inverse.map_surjective f
    obtain ⟨lowTargetMap, lowTargetMap_eq⟩ :=
      (finiteModelLiftContextFunctor.{u} FiniteModel.object).map_surjective
        highTargetMap
    obtain ⟨lowDomainMap, lowDomainMap_eq⟩ :=
      ((inverseCorePackageForwardUpper FiniteModel.corePackage input.hom).equationTransport.contextEquivalence).functor.map_surjective
        lowTargetMap
    refine ⟨lowDomainMap, ?_⟩
    simp only [finiteGeneratedContextImageFunctor, Functor.comp_map]
    rw [lowDomainMap_eq, lowTargetMap_eq, highTargetMap_eq]

/--
The generated-domain context image functor is faithful; its source is a thin
context category, so any two candidate preimages are equal.
-/
instance finiteGeneratedContextImageFunctor_faithful
    (input : FiniteGeneratedLiftInput) :
    (finiteGeneratedContextImageFunctor.{u} input).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-! ## Canonical-image carrier graph -/

/-- The image context has the canonical lifted support carrier. -/
theorem finiteGeneratedContextImageFunctor_support_type
    (input : FiniteGeneratedLiftInput)
    (context : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder) :
    ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx.Support =
      ULift.{u} context.ctx.Support := by
  change ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
      input.highAlignedBaseFromLowData).equationTransport.contextBackward
    ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj
      ((inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).equationTransport.contextForward context))).ctx.Support = _
  rw [inverseCorePackageForwardUpper_contextInverse_obj_support_type]
  change ULift.{u} _ = ULift.{u} _
  rw [inverseCorePackageForwardUpper_contextFunctor_obj_support_type]

/-- The image context has the canonical lifted axis carrier. -/
theorem finiteGeneratedContextImageFunctor_axis_type
    (input : FiniteGeneratedLiftInput)
    (context : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder) :
    ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx.Axis =
      ULift.{u} context.ctx.Axis := by
  change ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
      input.highAlignedBaseFromLowData).equationTransport.contextBackward
    ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj
      ((inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).equationTransport.contextForward context))).ctx.Axis = _
  rw [inverseCorePackageForwardUpper_contextInverse_obj_axis_type]
  change ULift.{u} _ = ULift.{u} _
  rw [inverseCorePackageForwardUpper_contextFunctor_obj_axis_type]

/-- The image context has the canonical lifted observable carrier. -/
theorem finiteGeneratedContextImageFunctor_observable_type
    (input : FiniteGeneratedLiftInput)
    (context : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder) :
    ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx.Observable =
      ULift.{u} context.ctx.Observable := by
  change ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
      input.highAlignedBaseFromLowData).equationTransport.contextBackward
    ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj
      ((inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).equationTransport.contextForward context))).ctx.Observable = _
  rw [inverseCorePackageForwardUpper_contextInverse_obj_observable_type]
  change ULift.{u} _ = ULift.{u} _
  rw [inverseCorePackageForwardUpper_contextFunctor_obj_observable_type]

/-- The image context has the canonical lifted extension carrier. -/
theorem finiteGeneratedContextImageFunctor_extension_type
    (input : FiniteGeneratedLiftInput)
    (context : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder) :
    ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx.Extension =
      ULift.{u} context.ctx.Extension := by
  change ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
      input.highAlignedBaseFromLowData).equationTransport.contextBackward
    ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj
      ((inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).equationTransport.contextForward context))).ctx.Extension = _
  rw [inverseCorePackageForwardUpper_contextInverse_obj_extension_type]
  change ULift.{u} _ = ULift.{u} _
  rw [inverseCorePackageForwardUpper_contextFunctor_obj_extension_type]

private def finiteModelContextCarrierShapeOfCast
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

/--
The four carrier equalities of every generated-domain image context, packaged
as the shape consumed by context reflection after endpoint alignment.
-/
def finiteGeneratedContextImageFunctor_carrierShape
    (input : FiniteGeneratedLiftInput)
    (context : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder) :
    FiniteModelContextCarrierShape context.ctx
      (cast (congrArg Site.ArchitectureContext
        (finiteGeneratedHighDomain_object_lift.{u} input))
        ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx) :=
  finiteModelContextCarrierShapeOfCast context.ctx
    ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx
    (finiteGeneratedHighDomain_object_lift.{u} input)
    (finiteGeneratedContextImageFunctor_support_type.{u} input context)
    (finiteGeneratedContextImageFunctor_axis_type.{u} input context)
    (finiteGeneratedContextImageFunctor_observable_type.{u} input context)
    (finiteGeneratedContextImageFunctor_extension_type.{u} input context)

private theorem cast_heq_self_local
    {α β : Sort v} (equality : α = β) (value : α) :
    HEq (cast equality value) value := by
  cases equality
  rfl

private theorem cast_eq_of_heq_local
    {α β : Sort v} (equality : α = β) (source : α) (target : β)
    (h : HEq source target) : cast equality source = target := by
  cases equality
  exact eq_of_heq h

private theorem finiteModelLiftArchitectureContext_cast_heq
    {A B : ArchitectureObject FiniteModel.carrier}
    (equality : A = B) (source : Site.ArchitectureContext A) :
    HEq (finiteModelLiftArchitectureContext.{u}
        (cast (congrArg Site.ArchitectureContext equality) source))
      (finiteModelLiftArchitectureContext.{u} source) := by
  cases equality
  rfl

private theorem transportArchitectureContext_equiv_heq
    {U : AtomCarrier.{u}} {object : ArchitectureObject U}
    {first second : Equiv.Perm U.Atom} (equality : first = second)
    (context : Site.ArchitectureContext object) :
    HEq (transportArchitectureContext first object context)
      (transportArchitectureContext second object context) := by
  cases equality
  rfl

/--
Every generated-domain image object is the complete canonical lift of its low
context, after the theorem-generated endpoint alignment.  This includes all
three predicates and the extension value, not only their carrier types.
-/
theorem finiteGeneratedContextImageFunctor_obj_ctx_eq_lift
    (input : FiniteGeneratedLiftInput)
    (context : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder) :
    cast (congrArg Site.ArchitectureContext
        (finiteGeneratedHighDomain_object_lift.{u} input))
        ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx =
      finiteModelLiftArchitectureContext.{u} context.ctx := by
  let lowAtom := input.hom.doctrineHom.atomEquiv
  let lowAlignedContext := cast (congrArg Site.ArchitectureContext
      (inverseBaseObject_eq FiniteModel.corePackage input.hom)) context.ctx
  let lowForwardContext :=
    (inverseCorePackageForwardUpper FiniteModel.corePackage input.hom).equationTransport.contextForward
      context
  let liftedLowForwardContext :=
    finiteModelLiftArchitectureContext.{u} lowForwardContext.ctx
  let highTransportedContext :=
    transportArchitectureContext
      input.highAlignedBaseFromLowData.doctrineHom.atomEquiv.symm
      (finiteModelLiftArchitectureObject.{u} FiniteModel.corePackage.object)
      liftedLowForwardContext
  have hImageToTransport :
      HEq ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx
        highTransportedContext := by
    change HEq
      (((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
        input.highAlignedBaseFromLowData).equationTransport.contextBackward
        ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj
          lowForwardContext)).ctx) highTransportedContext
    rw [inverseCorePackageForwardUpper_contextInverse_obj_eq]
    exact cast_heq_self_local _ _
  have hHighAtom :
      input.highAlignedBaseFromLowData.doctrineHom.atomEquiv.symm =
        finiteModelLiftAtomEquiv.{u} lowAtom.symm := by
    rw [input.highAlignedBaseFromLowData_eq]
    change (finiteModelLiftAtomEquiv.{u} lowAtom).symm =
      finiteModelLiftAtomEquiv.{u} lowAtom.symm
    exact finiteModelLiftAtomEquiv_symm lowAtom
  have hTransportNormalize : HEq highTransportedContext
      (transportArchitectureContext
        (finiteModelLiftAtomEquiv.{u} lowAtom.symm)
        (finiteModelLiftArchitectureObject.{u} FiniteModel.corePackage.object)
        liftedLowForwardContext) := by
    exact transportArchitectureContext_equiv_heq hHighAtom _
  have hLowForward : lowForwardContext.ctx =
      transportArchitectureContextBackward lowAtom.symm
        FiniteModel.corePackage.object lowAlignedContext := by
    exact inverseCorePackageForwardUpper_contextFunctor_obj_eq
      FiniteModel.corePackage input.hom context
  have hTransportLowForward :
      transportArchitectureContext
        (finiteModelLiftAtomEquiv.{u} lowAtom.symm)
        (finiteModelLiftArchitectureObject.{u} FiniteModel.corePackage.object)
        liftedLowForwardContext =
      transportArchitectureContext
        (finiteModelLiftAtomEquiv.{u} lowAtom.symm)
        (finiteModelLiftArchitectureObject.{u} FiniteModel.corePackage.object)
        (finiteModelLiftArchitectureContext.{u}
          (transportArchitectureContextBackward lowAtom.symm
            FiniteModel.corePackage.object lowAlignedContext)) := by
    exact congrArg
      (fun W : Site.ArchitectureContext FiniteModel.corePackage.object =>
        transportArchitectureContext
          (finiteModelLiftAtomEquiv.{u} lowAtom.symm)
          (finiteModelLiftArchitectureObject.{u} FiniteModel.corePackage.object)
          (finiteModelLiftArchitectureContext.{u} W)) hLowForward
  have hRoundtrip :
      transportArchitectureContext
        (finiteModelLiftAtomEquiv.{u} lowAtom.symm)
        (finiteModelLiftArchitectureObject.{u} FiniteModel.corePackage.object)
        (finiteModelLiftArchitectureContext.{u}
          (transportArchitectureContextBackward lowAtom.symm
            FiniteModel.corePackage.object lowAlignedContext)) =
      cast (congrArg Site.ArchitectureContext
        (finiteModelLiftArchitectureObject_transport_equiv.{u}
          lowAtom.symm FiniteModel.corePackage.object))
        (finiteModelLiftArchitectureContext.{u} lowAlignedContext) := by
    rw [finiteModelLiftArchitectureContext_transportBackward_equiv]
    exact transportArchitectureContext_forward_backward _ _ _
  have hCommuteCast : HEq
      (cast (congrArg Site.ArchitectureContext
        (finiteModelLiftArchitectureObject_transport_equiv.{u}
          lowAtom.symm FiniteModel.corePackage.object))
        (finiteModelLiftArchitectureContext.{u} lowAlignedContext))
      (finiteModelLiftArchitectureContext.{u} lowAlignedContext) :=
    cast_heq_self_local _ _
  have hLiftLowCast : HEq
      (finiteModelLiftArchitectureContext.{u} lowAlignedContext)
      (finiteModelLiftArchitectureContext.{u} context.ctx) :=
    finiteModelLiftArchitectureContext_cast_heq
      (inverseBaseObject_eq FiniteModel.corePackage input.hom) context.ctx
  have hImage : HEq
      ((finiteGeneratedContextImageFunctor.{u} input).obj context).ctx
      (finiteModelLiftArchitectureContext.{u} context.ctx) :=
    HEq.trans hImageToTransport
      (HEq.trans hTransportNormalize
        (HEq.trans (heq_of_eq hTransportLowForward)
          (HEq.trans (heq_of_eq hRoundtrip)
            (HEq.trans hCommuteCast hLiftLowCast))))
  exact cast_eq_of_heq_local _ _ _ hImage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
