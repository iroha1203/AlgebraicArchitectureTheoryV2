import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportCompositionDescent

/-!
# Generated context-equivalence composition descent

This module reflects the context-equivalence component of the actual
normalized high-factor triangle.  The reflection is restricted to the
generated finite-model image: the four low context carriers are preserved by
the generated forward and inverse transports, while every predicate and
extension value is read through the canonical context lift.

No low factorization theorem, canonical-factor equality, caller image
certificate, or ambient cartesianness proof is used here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- Casting a value along a type equality preserves it heterogeneously. -/
private theorem cast_heq_self
    {alpha beta : Sort v} (equality : alpha = beta) (value : alpha) :
    HEq (cast equality value) value := by
  cases equality
  rfl

/-- Canonical context lifting commutes heterogeneously with an object cast. -/
private theorem finiteModelLiftArchitectureContext_cast_heq
    {A B : ArchitectureObject FiniteModel.carrier}
    (equality : A = B) (source : Site.ArchitectureContext A) :
    HEq (finiteModelLiftArchitectureContext.{u}
        (cast (congrArg Site.ArchitectureContext equality) source))
      (finiteModelLiftArchitectureContext.{u} source) := by
  cases equality
  rfl

/-- Backward context transport respects equality of permutations and contexts. -/
private theorem transportArchitectureContextBackward_heq
    {U : AtomCarrier.{u}} {object : ArchitectureObject U}
    {first second : Equiv.Perm U.Atom}
    (equiv_eq : first = second)
    {source : Site.ArchitectureContext
      (transportArchitectureObject first object)}
    {target : Site.ArchitectureContext
      (transportArchitectureObject second object)}
    (context_eq : HEq source target) :
    HEq (transportArchitectureContextBackward first object source)
      (transportArchitectureContextBackward second object target) := by
  cases equiv_eq
  cases context_eq
  rfl

/-- Context-category objects are determined by their wrapped contexts. -/
private theorem contextCategoryObject_ext
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- Values in propositionally equal subsingleton types are heterogeneously equal. -/
private theorem subsingleton_heq_of_type_eq
    {alpha beta : Sort v} [Subsingleton alpha] [Subsingleton beta]
    (type_eq : alpha = beta) (first : alpha) (second : beta) :
    HEq first second := by
  cases type_eq
  exact heq_of_eq (Subsingleton.elim _ _)

/-- The generated forward context functor cancels its generated inverse on objects. -/
private theorem inverseCorePackageForwardUpper_contextForward_backward
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (f : X ⟶ packagePoint Q)
    (W : Site.ContextCategoryObject Q.algebra.contextPreorder) :
    (inverseCorePackageForwardUpper Q f).equationTransport.contextForward
        ((inverseCorePackageForwardUpper Q f).equationTransport.contextBackward W) =
      W := by
  apply contextCategoryObject_ext
  rw [inverseCorePackageForwardUpper_contextFunctor_obj_eq,
    inverseCorePackageForwardUpper_contextInverse_obj_eq]
  let objectEq := inverseBaseObject_eq Q f
  let transported :=
    transportArchitectureContext f.doctrineHom.atomEquiv.symm Q.object W.ctx
  have hcast :
      cast (congrArg Site.ArchitectureContext objectEq)
          (cast (congrArg Site.ArchitectureContext objectEq.symm) transported) =
        transported := by
    apply eq_of_heq
    exact HEq.trans
      (cast_heq_self (congrArg Site.ArchitectureContext objectEq) _)
      (cast_heq_self (congrArg Site.ArchitectureContext objectEq.symm) _)
  rw [hcast, transportArchitectureContext_backward_forward]

/--
Canonical context lifting reflects equality whenever the four low carrier
types have already been identified.  The proof then reads every predicate and
the extension value through lifted inputs.
-/
theorem finiteModelLiftArchitectureContext_injective_of_carriers
    {A : ArchitectureObject FiniteModel.carrier}
    {first second : Site.ArchitectureContext A}
    (support_type : first.Support = second.Support)
    (axis_type : first.Axis = second.Axis)
    (observable_type : first.Observable = second.Observable)
    (extension_type : first.Extension = second.Extension)
    (equality : finiteModelLiftArchitectureContext.{u} first =
      finiteModelLiftArchitectureContext.{u} second) :
    first = second := by
  rcases first with
    ⟨⟨Support₁, Axis₁, Observable₁, supportReads₁,
      supportReadsObject₁, axisReads₁, observableReads₁⟩,
      Extension₁, extension₁⟩
  rcases second with
    ⟨⟨Support₂, Axis₂, Observable₂, supportReads₂,
      supportReadsObject₂, axisReads₂, observableReads₂⟩,
      Extension₂, extension₂⟩
  dsimp [Site.ArchitectureContext.Support,
    Site.ArchitectureContext.Axis,
    Site.ArchitectureContext.Observable] at support_type axis_type observable_type
  dsimp at extension_type
  cases support_type
  cases axis_type
  cases observable_type
  cases extension_type
  injection equality with hminimal _ hextension
  injection hminimal with _ _ _ hsupport haxis hobservable
  have hsupportLow : supportReads₁ = supportReads₂ := by
    funext support atom
    have point := congrFun (congrFun hsupport (ULift.up support))
      (finiteModelLiftCarrierEquiv.{u}.atom atom)
    simpa [finiteModelLiftArchitectureContext] using point
  have haxisLow : axisReads₁ = axisReads₂ := by
    funext axis
    have point := congrFun haxis (ULift.up axis)
    simpa [finiteModelLiftArchitectureContext] using point
  have hobservableLow : observableReads₁ = observableReads₂ := by
    funext observable
    have point := congrFun hobservable (ULift.up observable)
    simpa [finiteModelLiftArchitectureContext] using point
  have hextensionLow : extension₁ = extension₂ :=
    ULift.up_injective hextension
  cases hsupportLow
  cases haxisLow
  cases hobservableLow
  cases hextensionLow
  rfl

/--
The generated high forward context is the canonical lift of the generated low
forward context on every context in the generated domain image.
-/
theorem finiteGeneratedUpper_contextForward_ctx_eq_lift
    (input : FiniteGeneratedLiftInput)
    (W : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder) :
    (input.highGeneratedLift.hom.upper.equationTransport.contextForward
      ((finiteGeneratedContextImageFunctor.{u} input).obj W)).ctx =
      finiteModelLiftArchitectureContext.{u}
        (input.lowGeneratedLift.hom.upper.equationTransport.contextForward W).ctx := by
  change
    ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
      input.highAlignedBaseFromLowData).equationTransport.contextForward
      ((finiteGeneratedContextImageFunctor.{u} input).obj W)).ctx =
    finiteModelLiftArchitectureContext.{u}
      ((inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).equationTransport.contextForward W).ctx
  rw [inverseCorePackageForwardUpper_contextFunctor_obj_eq,
    inverseCorePackageForwardUpper_contextFunctor_obj_eq]
  let highDomainEq := finiteGeneratedHighDomain_object_lift.{u} input
  let lowDomainEq := inverseBaseObject_eq FiniteModel.corePackage input.hom
  let highTargetEq := inverseBaseObject_eq finiteModelLiftCorePackage.{u}
    input.highAlignedBaseFromLowData
  let transportEq := finiteModelLiftArchitectureObject_transport_equiv.{u}
    input.hom.doctrineHom.atomEquiv.symm FiniteModel.corePackage.object
  have hImage := finiteGeneratedContextImageFunctor_obj_ctx_eq_lift input W
  have hFirstToImage : HEq
      (cast (congrArg Site.ArchitectureContext highTargetEq)
        ((finiteGeneratedContextImageFunctor.{u} input).obj W).ctx)
      ((finiteGeneratedContextImageFunctor.{u} input).obj W).ctx :=
    cast_heq_self (congrArg Site.ArchitectureContext highTargetEq) _
  have hImageToLift : HEq
      ((finiteGeneratedContextImageFunctor.{u} input).obj W).ctx
      (finiteModelLiftArchitectureContext.{u} W.ctx) :=
    HEq.trans
      (cast_heq_self (congrArg Site.ArchitectureContext highDomainEq) _).symm
      (heq_of_eq hImage)
  have hLiftToLowCast : HEq
      (finiteModelLiftArchitectureContext.{u} W.ctx)
      (finiteModelLiftArchitectureContext.{u}
        (cast (congrArg Site.ArchitectureContext lowDomainEq) W.ctx)) :=
    (finiteModelLiftArchitectureContext_cast_heq lowDomainEq W.ctx).symm
  have hLowCastToTarget : HEq
      (finiteModelLiftArchitectureContext.{u}
        (cast (congrArg Site.ArchitectureContext lowDomainEq) W.ctx))
      (cast (congrArg Site.ArchitectureContext transportEq)
        (finiteModelLiftArchitectureContext.{u}
          (cast (congrArg Site.ArchitectureContext lowDomainEq) W.ctx))) :=
    (cast_heq_self (congrArg Site.ArchitectureContext transportEq) _).symm
  have hContext := HEq.trans hFirstToImage
    (HEq.trans hImageToLift (HEq.trans hLiftToLowCast hLowCastToTarget))
  have hHighAtom :
      input.highAlignedBaseFromLowData.doctrineHom.atomEquiv.symm =
        finiteModelLiftAtomEquiv.{u}
          input.hom.doctrineHom.atomEquiv.symm := by
    rw [input.highAlignedBaseFromLowData_eq]
    change (finiteModelLiftAtomEquiv.{u}
      input.hom.doctrineHom.atomEquiv).symm = _
    exact finiteModelLiftAtomEquiv_symm input.hom.doctrineHom.atomEquiv
  have hTransport := eq_of_heq
    (transportArchitectureContextBackward_heq hHighAtom hContext)
  have hLiftBackward :=
    finiteModelLiftArchitectureContext_transportBackward_equiv.{u}
      input.hom.doctrineHom.atomEquiv.symm
      (cast (congrArg Site.ArchitectureContext lowDomainEq) W.ctx)
  exact hTransport.trans hLiftBackward.symm

/--
The context functor of the reflected upper followed by the inner generated
upper equals the outer generated context functor on every object.
-/
theorem finiteGeneratedReflectedUpper_comp_contextForward
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    input.lowGeneratedLift.hom.upper.equationTransport.contextForward
        ((finiteGeneratedReflectedSignedExactCoreReadingHom
          input lift base).equationTransport.contextForward W) =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.equationTransport.contextForward W := by
  let outer := finiteGeneratedOuterInput input base
  change
    input.lowGeneratedLift.hom.upper.equationTransport.contextForward
        (finiteGeneratedReflectedForwardObject input lift base W) =
      outer.lowGeneratedLift.hom.upper.equationTransport.contextForward W
  apply contextCategoryObject_ext
  apply finiteModelLiftArchitectureContext_injective_of_carriers
  · calc
      _ = (finiteGeneratedReflectedForwardObject input lift base W).ctx.Support :=
        inverseCorePackageForwardUpper_contextFunctor_obj_support_type
          FiniteModel.corePackage input.hom _
      _ = W.ctx.Support := rfl
      _ = _ :=
        (inverseCorePackageForwardUpper_contextFunctor_obj_support_type
          FiniteModel.corePackage outer.hom W).symm
  · calc
      _ = (finiteGeneratedReflectedForwardObject input lift base W).ctx.Axis :=
        inverseCorePackageForwardUpper_contextFunctor_obj_axis_type
          FiniteModel.corePackage input.hom _
      _ = W.ctx.Axis := rfl
      _ = _ :=
        (inverseCorePackageForwardUpper_contextFunctor_obj_axis_type
          FiniteModel.corePackage outer.hom W).symm
  · calc
      _ = (finiteGeneratedReflectedForwardObject input lift base W).ctx.Observable :=
        inverseCorePackageForwardUpper_contextFunctor_obj_observable_type
          FiniteModel.corePackage input.hom _
      _ = W.ctx.Observable := rfl
      _ = _ :=
        (inverseCorePackageForwardUpper_contextFunctor_obj_observable_type
          FiniteModel.corePackage outer.hom W).symm
  · calc
      _ = (finiteGeneratedReflectedForwardObject input lift base W).ctx.Extension :=
        inverseCorePackageForwardUpper_contextFunctor_obj_extension_type
          FiniteModel.corePackage input.hom _
      _ = W.ctx.Extension := rfl
      _ = _ :=
        (inverseCorePackageForwardUpper_contextFunctor_obj_extension_type
          FiniteModel.corePackage outer.hom W).symm
  · calc
      finiteModelLiftArchitectureContext.{u}
          (input.lowGeneratedLift.hom.upper.equationTransport.contextForward
            (finiteGeneratedReflectedForwardObject input lift base W)).ctx =
        (input.highGeneratedLift.hom.upper.equationTransport.contextForward
          ((finiteGeneratedContextImageFunctor.{u} input).obj
            (finiteGeneratedReflectedForwardObject input lift base W))).ctx :=
          (finiteGeneratedUpper_contextForward_ctx_eq_lift input _).symm
      _ = (outer.highGeneratedLift.hom.upper.equationTransport.contextForward
          ((finiteGeneratedContextImageFunctor.{u} outer).obj W)).ctx :=
        congrArg Site.ContextCategoryObject.ctx
          (finiteGeneratedReflectedUpper_comp_contextForward_high_image
            input lift base W)
      _ = finiteModelLiftArchitectureContext.{u}
          (outer.lowGeneratedLift.hom.upper.equationTransport.contextForward W).ctx :=
        finiteGeneratedUpper_contextForward_ctx_eq_lift outer W

/--
The generated context image of a low inverse context is exactly the high
inverse context of the canonical lifted target context.
-/
theorem finiteGeneratedUpper_contextBackward_image
    (input : FiniteGeneratedLiftInput)
    (W : Site.ContextCategoryObject
      FiniteModel.corePackage.algebra.contextPreorder) :
    (finiteGeneratedContextImageFunctor.{u} input).obj
        (input.lowGeneratedLift.hom.upper.equationTransport.contextBackward W) =
      input.highGeneratedLift.hom.upper.equationTransport.contextBackward
        ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj W) := by
  change
    ((inverseCorePackageForwardUpper finiteModelLiftCorePackage.{u}
      input.highAlignedBaseFromLowData).equationTransport.contextBackward
      ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj
        ((inverseCorePackageForwardUpper FiniteModel.corePackage
          input.hom).equationTransport.contextForward
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).equationTransport.contextBackward W)))) = _
  rw [inverseCorePackageForwardUpper_contextForward_backward]
  rw [input.highGeneratedLift_hom_eq_highPackageHomFromLowData]
  rfl

/--
The inverse context functor of the reflected upper followed by the inner
generated upper equals the outer generated inverse functor on every object.
-/
theorem finiteGeneratedReflectedUpper_comp_contextBackward
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      FiniteModel.corePackage.algebra.contextPreorder) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom
        input lift base).equationTransport.contextEquivalence.trans
      input.lowGeneratedLift.hom.upper.equationTransport.contextEquivalence).inverse.obj W =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.equationTransport.contextBackward W := by
  let outer := finiteGeneratedOuterInput input base
  let innerBackward :=
    input.lowGeneratedLift.hom.upper.equationTransport.contextBackward W
  let reflectedBackward :=
    finiteGeneratedReflectedInverseObject input lift base innerBackward
  let outerBackward :=
    outer.lowGeneratedLift.hom.upper.equationTransport.contextBackward W
  change reflectedBackward = outerBackward
  have highInverseTriangle := congrArg
    (fun equivalence => equivalence.inverse.obj
      ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj W))
    (finiteGeneratedNormalizedHighFactor_upper_fac_contextEquivalence
      input lift base)
  change
    (finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
        (input.highGeneratedLift.hom.upper.equationTransport.contextBackward
          ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj W)) =
      outer.highGeneratedLift.hom.upper.equationTransport.contextBackward
        ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj W)
      at highInverseTriangle
  have hImage :
      (finiteGeneratedContextImageFunctor.{u} outer).obj reflectedBackward =
        (finiteGeneratedContextImageFunctor.{u} outer).obj outerBackward := by
    calc
      (finiteGeneratedContextImageFunctor.{u} outer).obj reflectedBackward =
          (finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
            ((finiteGeneratedContextImageFunctor.{u} input).obj innerBackward) :=
        finiteGeneratedReflectedInverseObject_image_eq
          input lift base innerBackward
      _ = (finiteGeneratedActualHighContextEquivalence input lift base).inverse.obj
            (input.highGeneratedLift.hom.upper.equationTransport.contextBackward
              ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj W)) := by
        rw [finiteGeneratedUpper_contextBackward_image input W]
      _ = outer.highGeneratedLift.hom.upper.equationTransport.contextBackward
            ((finiteModelLiftContextFunctor.{u} FiniteModel.object).obj W) :=
        highInverseTriangle
      _ = (finiteGeneratedContextImageFunctor.{u} outer).obj outerBackward :=
        (finiteGeneratedUpper_contextBackward_image outer W).symm
  apply contextCategoryObject_ext
  apply finiteModelLiftArchitectureContext_injective_of_carriers
  · calc
      reflectedBackward.ctx.Support = innerBackward.ctx.Support := rfl
      _ = W.ctx.Support :=
        inverseCorePackageForwardUpper_contextInverse_obj_support_type
          FiniteModel.corePackage input.hom W
      _ = outerBackward.ctx.Support :=
        (inverseCorePackageForwardUpper_contextInverse_obj_support_type
          FiniteModel.corePackage outer.hom W).symm
  · calc
      reflectedBackward.ctx.Axis = innerBackward.ctx.Axis := rfl
      _ = W.ctx.Axis :=
        inverseCorePackageForwardUpper_contextInverse_obj_axis_type
          FiniteModel.corePackage input.hom W
      _ = outerBackward.ctx.Axis :=
        (inverseCorePackageForwardUpper_contextInverse_obj_axis_type
          FiniteModel.corePackage outer.hom W).symm
  · calc
      reflectedBackward.ctx.Observable = innerBackward.ctx.Observable := rfl
      _ = W.ctx.Observable :=
        inverseCorePackageForwardUpper_contextInverse_obj_observable_type
          FiniteModel.corePackage input.hom W
      _ = outerBackward.ctx.Observable :=
        (inverseCorePackageForwardUpper_contextInverse_obj_observable_type
          FiniteModel.corePackage outer.hom W).symm
  · calc
      reflectedBackward.ctx.Extension = innerBackward.ctx.Extension := rfl
      _ = W.ctx.Extension :=
        inverseCorePackageForwardUpper_contextInverse_obj_extension_type
          FiniteModel.corePackage input.hom W
      _ = outerBackward.ctx.Extension :=
        (inverseCorePackageForwardUpper_contextInverse_obj_extension_type
          FiniteModel.corePackage outer.hom W).symm
  · let highDomainEq := finiteGeneratedHighDomain_object_lift.{u} outer
    calc
      finiteModelLiftArchitectureContext.{u} reflectedBackward.ctx =
          cast (congrArg Site.ArchitectureContext highDomainEq)
            (((finiteGeneratedContextImageFunctor.{u} outer).obj
              reflectedBackward).ctx) :=
        (finiteGeneratedContextImageFunctor_obj_ctx_eq_lift
          outer reflectedBackward).symm
      _ = cast (congrArg Site.ArchitectureContext highDomainEq)
            (((finiteGeneratedContextImageFunctor.{u} outer).obj
              outerBackward).ctx) := by
        exact congrArg
          (fun context => cast (congrArg Site.ArchitectureContext highDomainEq)
            context.ctx) hImage
      _ = finiteModelLiftArchitectureContext.{u} outerBackward.ctx :=
        finiteGeneratedContextImageFunctor_obj_ctx_eq_lift outer outerBackward

/--
The complete context equivalence of the reflected upper followed by the inner
generated upper is the outer generated context equivalence.  Map, unit, and
counit fields are compared only after their object endpoints are generated;
thinness then makes the corresponding morphisms unique.
-/
theorem finiteGeneratedReflectedUpper_comp_contextEquivalence
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
        input.lowGeneratedLift.hom.upper).equationTransport.contextEquivalence =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.equationTransport.contextEquivalence := by
  let first :=
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
      input.lowGeneratedLift.hom.upper).equationTransport.contextEquivalence
  let second :=
    (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper.equationTransport.contextEquivalence
  have hFunctor : first.functor = second.functor := by
    apply CategoryTheory.Functor.ext
    · intro source target map
      exact Subsingleton.elim _ _
    · intro W
      exact finiteGeneratedReflectedUpper_comp_contextForward
        input lift base W
  have hInverse : first.inverse = second.inverse := by
    apply CategoryTheory.Functor.ext
    · intro source target map
      exact Subsingleton.elim _ _
    · intro W
      exact finiteGeneratedReflectedUpper_comp_contextBackward
        input lift base W
  apply CategoryTheory.Equivalence.ext hFunctor hInverse
  · have hComp : first.functor ⋙ first.inverse =
        second.functor ⋙ second.inverse := by
      rw [hFunctor, hInverse]
    have hUnitType :
        (𝟭 (Site.ContextCategoryObject
          (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder) ≅
            first.functor ⋙ first.inverse) =
          (𝟭 (Site.ContextCategoryObject
            (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder) ≅
              second.functor ⋙ second.inverse) := by
      rw [hComp]
    exact subsingleton_heq_of_type_eq
      hUnitType
      first.unitIso second.unitIso
  · have hComp : first.inverse ⋙ first.functor =
        second.inverse ⋙ second.functor := by
      rw [hFunctor, hInverse]
    have hCounitType :
        (first.inverse ⋙ first.functor ≅
          𝟭 (Site.ContextCategoryObject
            (finiteGeneratedOuterInput input base).lowTarget.val.algebra.contextPreorder)) =
          (second.inverse ⋙ second.functor ≅
            𝟭 (Site.ContextCategoryObject
              (finiteGeneratedOuterInput input base).lowTarget.val.algebra.contextPreorder)) := by
      rw [hComp]
    exact subsingleton_heq_of_type_eq
      hCounitType
      first.counitIso second.counitIso

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
