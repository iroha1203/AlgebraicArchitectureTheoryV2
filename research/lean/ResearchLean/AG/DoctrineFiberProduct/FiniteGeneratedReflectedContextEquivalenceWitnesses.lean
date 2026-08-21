import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedContextEquivalence
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObjectContextImageWitnesses

/-!
# Concrete witnesses for reflected generated context equivalence

This module fires the actual and reflected context-equivalence producers on the
selective two-source generated-factor fixture.  Two concrete finite-model
contexts and their nonidentity raw restriction are transported into the outer
generated domain by the inverse-package context equivalence.  The resulting
objects, arrow, forward and inverse images, and all four unit/counit components
are therefore generated from the same input, supplied high lift, and prefix.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Concrete core contexts and raw restriction -/

/--
The first concrete core context has Boolean support and observables, a
two-element axis carrier, a three-element extension carrier, and extension `1`.
-/
noncomputable def finiteSelectiveTwoContextEquivalenceCoreWContext :
    Site.ArchitectureContext FiniteModel.corePackage.object where
  minimal := {
    Support := Bool
    Axis := Fin 2
    Observable := Bool
    supportReads := fun support atom =>
      support = true ∧ FiniteModel.corePackage.object.configuration.family.mem atom
    supportReads_objectFamily := by
      intro support atom hread
      exact hread.2
    axisReads := fun axis => axis = 1
    observableReads := fun observable => observable = true
  }
  Extension := Fin 3
  extension := 1

/--
The second concrete core context has the same nontrivial carriers and readings,
but selects extension `2`.
-/
noncomputable def finiteSelectiveTwoContextEquivalenceCoreVContext :
    Site.ArchitectureContext FiniteModel.corePackage.object where
  minimal := {
    Support := Bool
    Axis := Fin 2
    Observable := Bool
    supportReads := fun support atom =>
      support = true ∧ FiniteModel.corePackage.object.configuration.family.mem atom
    supportReads_objectFamily := by
      intro support atom hread
      exact hread.2
    axisReads := fun axis => axis = 1
    observableReads := fun observable => observable = true
  }
  Extension := Fin 3
  extension := 2

/-- The first concrete context as an object of the finite core context category. -/
noncomputable def finiteSelectiveTwoContextEquivalenceCoreW :
    Site.ContextCategoryObject FiniteModel.corePackage.contextPreorder :=
  Site.ContextCategoryObject.of FiniteModel.corePackage.contextPreorder
    finiteSelectiveTwoContextEquivalenceCoreWContext

/-- The second concrete context as an object of the finite core context category. -/
noncomputable def finiteSelectiveTwoContextEquivalenceCoreV :
    Site.ContextCategoryObject FiniteModel.corePackage.contextPreorder :=
  Site.ContextCategoryObject.of FiniteModel.corePackage.contextPreorder
    finiteSelectiveTwoContextEquivalenceCoreVContext

/--
The raw restriction sends every support to `true`, every axis to `1`, and
restricts observables by the identity.
-/
noncomputable def finiteSelectiveTwoContextEquivalenceRawRestriction :
    Site.ContextMorphism finiteSelectiveTwoContextEquivalenceCoreWContext
      finiteSelectiveTwoContextEquivalenceCoreVContext where
  supportMap := by
    change Bool → Bool
    exact fun _ => true
  axisMap := by
    change Fin 2 → Fin 2
    exact fun _ => 1
  observableRestrict := by
    change Bool → Bool
    exact id

/-- The concrete raw map satisfies the selected restriction role. -/
theorem finiteSelectiveTwoContextEquivalenceRawRestriction_isRestriction :
    finiteSelectiveTwoContextEquivalenceRawRestriction.IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    exact ⟨rfl, hread.2⟩
  · intro axis hread
    rfl
  · intro observable hread
    exact hread
  · intro support atom hread
    exact hread.2

/-- The actual raw support map sends the negative support to the positive one. -/
@[simp]
theorem finiteSelectiveTwoContextEquivalenceRawRestriction_support_graph :
    finiteSelectiveTwoContextEquivalenceRawRestriction.supportMap false = true :=
  rfl

/-- The actual raw axis map sends the unselected axis to the selected one. -/
@[simp]
theorem finiteSelectiveTwoContextEquivalenceRawRestriction_axis_graph :
    finiteSelectiveTwoContextEquivalenceRawRestriction.axisMap (0 : Fin 2) =
      (1 : Fin 2) :=
  rfl

/-- The actual raw observable restriction fixes the negative observable. -/
@[simp]
theorem finiteSelectiveTwoContextEquivalenceRawRestriction_observable_graph :
    finiteSelectiveTwoContextEquivalenceRawRestriction.observableRestrict false = false :=
  rfl

/-- The raw restriction is the concrete categorical arrow between the two core contexts. -/
noncomputable def finiteSelectiveTwoContextEquivalenceCoreRestriction :
    finiteSelectiveTwoContextEquivalenceCoreW ⟶
      finiteSelectiveTwoContextEquivalenceCoreV := by
  apply homOfLE
  change ∃ restriction : Site.ContextMorphism
      finiteSelectiveTwoContextEquivalenceCoreWContext
      finiteSelectiveTwoContextEquivalenceCoreVContext,
    restriction.IsRestriction
  exact ⟨finiteSelectiveTwoContextEquivalenceRawRestriction,
    finiteSelectiveTwoContextEquivalenceRawRestriction_isRestriction⟩

/-! ## The selective-two outer contexts -/

/-- The outer generated input determined by the selective-two prefix. -/
noncomputable def finiteSelectiveTwoContextEquivalenceOuterInput :
    FiniteGeneratedLiftInput :=
  finiteGeneratedOuterInput finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessBase

/-- Transport the first concrete core context into the outer generated domain. -/
noncomputable def finiteSelectiveTwoContextEquivalenceW :
    Site.ContextCategoryObject
      (finiteSelectiveTwoContextEquivalenceOuterInput.lowGeneratedLift.domain.algebra.contextPreorder) :=
  (inverseCorePackageForwardUpper FiniteModel.corePackage
    finiteSelectiveTwoContextEquivalenceOuterInput.hom).equationTransport.contextBackward
      finiteSelectiveTwoContextEquivalenceCoreW

/-- Transport the second concrete core context into the outer generated domain. -/
noncomputable def finiteSelectiveTwoContextEquivalenceV :
    Site.ContextCategoryObject
      (finiteSelectiveTwoContextEquivalenceOuterInput.lowGeneratedLift.domain.algebra.contextPreorder) :=
  (inverseCorePackageForwardUpper FiniteModel.corePackage
    finiteSelectiveTwoContextEquivalenceOuterInput.hom).equationTransport.contextBackward
      finiteSelectiveTwoContextEquivalenceCoreV

/-- The first outer context retains all four nontrivial carrier types. -/
theorem finiteSelectiveTwoContextEquivalenceW_carrier_types :
    finiteSelectiveTwoContextEquivalenceW.ctx.Support = Bool ∧
      finiteSelectiveTwoContextEquivalenceW.ctx.Axis = Fin 2 ∧
      finiteSelectiveTwoContextEquivalenceW.ctx.Observable = Bool ∧
      finiteSelectiveTwoContextEquivalenceW.ctx.Extension = Fin 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold finiteSelectiveTwoContextEquivalenceW
    exact inverseCorePackageForwardUpper_contextInverse_obj_support_type
      FiniteModel.corePackage finiteSelectiveTwoContextEquivalenceOuterInput.hom
      finiteSelectiveTwoContextEquivalenceCoreW
  · unfold finiteSelectiveTwoContextEquivalenceW
    exact inverseCorePackageForwardUpper_contextInverse_obj_axis_type
      FiniteModel.corePackage finiteSelectiveTwoContextEquivalenceOuterInput.hom
      finiteSelectiveTwoContextEquivalenceCoreW
  · unfold finiteSelectiveTwoContextEquivalenceW
    exact inverseCorePackageForwardUpper_contextInverse_obj_observable_type
      FiniteModel.corePackage finiteSelectiveTwoContextEquivalenceOuterInput.hom
      finiteSelectiveTwoContextEquivalenceCoreW
  · unfold finiteSelectiveTwoContextEquivalenceW
    exact inverseCorePackageForwardUpper_contextInverse_obj_extension_type
      FiniteModel.corePackage finiteSelectiveTwoContextEquivalenceOuterInput.hom
      finiteSelectiveTwoContextEquivalenceCoreW

/-- The second outer context retains all four nontrivial carrier types. -/
theorem finiteSelectiveTwoContextEquivalenceV_carrier_types :
    finiteSelectiveTwoContextEquivalenceV.ctx.Support = Bool ∧
      finiteSelectiveTwoContextEquivalenceV.ctx.Axis = Fin 2 ∧
      finiteSelectiveTwoContextEquivalenceV.ctx.Observable = Bool ∧
      finiteSelectiveTwoContextEquivalenceV.ctx.Extension = Fin 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold finiteSelectiveTwoContextEquivalenceV
    exact inverseCorePackageForwardUpper_contextInverse_obj_support_type
      FiniteModel.corePackage finiteSelectiveTwoContextEquivalenceOuterInput.hom
      finiteSelectiveTwoContextEquivalenceCoreV
  · unfold finiteSelectiveTwoContextEquivalenceV
    exact inverseCorePackageForwardUpper_contextInverse_obj_axis_type
      FiniteModel.corePackage finiteSelectiveTwoContextEquivalenceOuterInput.hom
      finiteSelectiveTwoContextEquivalenceCoreV
  · unfold finiteSelectiveTwoContextEquivalenceV
    exact inverseCorePackageForwardUpper_contextInverse_obj_observable_type
      FiniteModel.corePackage finiteSelectiveTwoContextEquivalenceOuterInput.hom
      finiteSelectiveTwoContextEquivalenceCoreV
  · unfold finiteSelectiveTwoContextEquivalenceV
    exact inverseCorePackageForwardUpper_contextInverse_obj_extension_type
      FiniteModel.corePackage finiteSelectiveTwoContextEquivalenceOuterInput.hom
      finiteSelectiveTwoContextEquivalenceCoreV

private theorem castArchitectureContext_extension_heq_local
    {U : AtomCarrier.{u}} {A B : ArchitectureObject U}
    (equality : A = B) (context : Site.ArchitectureContext A) :
    HEq (cast (congrArg Site.ArchitectureContext equality) context).extension
      context.extension := by
  cases equality
  rfl

/-- The first transported context still carries extension value `1`. -/
theorem finiteSelectiveTwoContextEquivalenceW_extension_heq :
    HEq finiteSelectiveTwoContextEquivalenceW.ctx.extension (1 : Fin 3) := by
  unfold finiteSelectiveTwoContextEquivalenceW
  rw [inverseCorePackageForwardUpper_contextInverse_obj_eq]
  exact HEq.trans (castArchitectureContext_extension_heq_local
      (inverseBaseObject_eq FiniteModel.corePackage
        finiteSelectiveTwoContextEquivalenceOuterInput.hom).symm
      (transportArchitectureContext
        finiteSelectiveTwoContextEquivalenceOuterInput.hom.doctrineHom.atomEquiv.symm
        FiniteModel.corePackage.object
        finiteSelectiveTwoContextEquivalenceCoreW.ctx))
    (heq_of_eq rfl)

/-- The second transported context still carries extension value `2`. -/
theorem finiteSelectiveTwoContextEquivalenceV_extension_heq :
    HEq finiteSelectiveTwoContextEquivalenceV.ctx.extension (2 : Fin 3) := by
  unfold finiteSelectiveTwoContextEquivalenceV
  rw [inverseCorePackageForwardUpper_contextInverse_obj_eq]
  exact HEq.trans (castArchitectureContext_extension_heq_local
      (inverseBaseObject_eq FiniteModel.corePackage
        finiteSelectiveTwoContextEquivalenceOuterInput.hom).symm
      (transportArchitectureContext
        finiteSelectiveTwoContextEquivalenceOuterInput.hom.doctrineHom.atomEquiv.symm
        FiniteModel.corePackage.object
        finiteSelectiveTwoContextEquivalenceCoreV.ctx))
    (heq_of_eq rfl)

/-- The two outer generated-domain contexts are genuinely distinct. -/
theorem finiteSelectiveTwoContextEquivalenceW_ne_V :
    finiteSelectiveTwoContextEquivalenceW ≠
      finiteSelectiveTwoContextEquivalenceV := by
  intro hcontext
  have hctx := congrArg Site.ContextCategoryObject.ctx hcontext
  have hpacked := congrArg
    (fun context : Site.ArchitectureContext
        finiteSelectiveTwoContextEquivalenceOuterInput.lowGeneratedLift.domain.object =>
      Sigma.mk (β := fun carrier : Type => carrier)
        context.Extension context.extension) hctx
  have hextension : HEq
      finiteSelectiveTwoContextEquivalenceW.ctx.extension
      finiteSelectiveTwoContextEquivalenceV.ctx.extension :=
    (Sigma.mk.inj_iff.mp hpacked).2
  have hvalue : HEq (1 : Fin 3) (2 : Fin 3) :=
    HEq.trans finiteSelectiveTwoContextEquivalenceW_extension_heq.symm
      (HEq.trans hextension
        finiteSelectiveTwoContextEquivalenceV_extension_heq)
  have hvalueEq : (1 : Fin 3) = 2 := eq_of_heq hvalue
  have hnat := congrArg Fin.val hvalueEq
  cases hnat

/-- The transported concrete restriction is an outer generated-domain arrow `W ⟶ V`. -/
noncomputable def finiteSelectiveTwoContextEquivalenceRestriction :
    finiteSelectiveTwoContextEquivalenceW ⟶
      finiteSelectiveTwoContextEquivalenceV :=
  (inverseCorePackageForwardUpper FiniteModel.corePackage
    finiteSelectiveTwoContextEquivalenceOuterInput.hom).equationTransport.contextBackward_map
      finiteSelectiveTwoContextEquivalenceCoreRestriction

/-! ## Actual and reflected equivalences -/

/-- The actual normalized high context equivalence on the selective-two fixture. -/
noncomputable def finiteSelectiveTwoActualHighContextEquivalence :=
  finiteGeneratedActualHighContextEquivalence.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/-- The generated low context equivalence reflected from the actual high factor. -/
noncomputable def finiteSelectiveTwoReflectedContextEquivalence :=
  finiteGeneratedReflectedContextEquivalence.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/-- The reflected forward image of the first concrete outer context. -/
noncomputable def finiteSelectiveTwoContextEquivalenceForwardW :=
  finiteSelectiveTwoReflectedContextEquivalence.{u}.functor.obj
    finiteSelectiveTwoContextEquivalenceW

/-- The reflected inverse image of the concrete forward object. -/
noncomputable def finiteSelectiveTwoContextEquivalenceInverseForwardW :=
  finiteSelectiveTwoReflectedContextEquivalence.{u}.inverse.obj
    finiteSelectiveTwoContextEquivalenceForwardW.{u}

/-- The reflected forward object lands on the actual normalized high forward image. -/
theorem finiteSelectiveTwoContextEquivalence_forward_object_landing :
    (finiteGeneratedContextImageFunctor.{u}
        finiteSelectiveTwoObjectContextWitnessInput).obj
        finiteSelectiveTwoContextEquivalenceForwardW.{u} =
      finiteSelectiveTwoActualHighContextEquivalence.{u}.functor.obj
        ((finiteGeneratedContextImageFunctor.{u}
          finiteSelectiveTwoContextEquivalenceOuterInput).obj
          finiteSelectiveTwoContextEquivalenceW) := by
  unfold finiteSelectiveTwoContextEquivalenceForwardW
    finiteSelectiveTwoReflectedContextEquivalence
    finiteSelectiveTwoActualHighContextEquivalence
  rw [finiteGeneratedReflectedContextEquivalence_functor_obj]
  exact finiteGeneratedReflectedForwardObject_image_eq.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoContextEquivalenceW

/-- The reflected inverse object lands on the actual normalized high inverse image. -/
theorem finiteSelectiveTwoContextEquivalence_inverse_object_landing :
    (finiteGeneratedContextImageFunctor.{u}
        finiteSelectiveTwoContextEquivalenceOuterInput).obj
        finiteSelectiveTwoContextEquivalenceInverseForwardW.{u} =
      finiteSelectiveTwoActualHighContextEquivalence.{u}.inverse.obj
        ((finiteGeneratedContextImageFunctor.{u}
          finiteSelectiveTwoObjectContextWitnessInput).obj
          finiteSelectiveTwoContextEquivalenceForwardW.{u}) := by
  unfold finiteSelectiveTwoContextEquivalenceInverseForwardW
    finiteSelectiveTwoReflectedContextEquivalence
    finiteSelectiveTwoActualHighContextEquivalence
  rw [finiteGeneratedReflectedContextEquivalence_inverse_obj]
  exact finiteGeneratedReflectedInverseObject_image_eq.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoContextEquivalenceForwardW.{u}

/-- The reflected forward restriction maps back to the actual high forward map. -/
theorem finiteSelectiveTwoContextEquivalence_forward_map_image :
    (finiteGeneratedContextImageFunctor.{u}
      finiteSelectiveTwoObjectContextWitnessInput).map
        (finiteSelectiveTwoReflectedContextEquivalence.{u}.functor.map
          finiteSelectiveTwoContextEquivalenceRestriction) =
      finiteGeneratedReflectedForwardHighMap.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoContextEquivalenceRestriction := by
  unfold finiteSelectiveTwoReflectedContextEquivalence
  exact finiteGeneratedReflectedForwardMap_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoContextEquivalenceRestriction

/-- The reflected inverse of the forward restriction maps back to the actual high inverse map. -/
theorem finiteSelectiveTwoContextEquivalence_inverse_map_image :
    (finiteGeneratedContextImageFunctor.{u}
      finiteSelectiveTwoContextEquivalenceOuterInput).map
        (finiteSelectiveTwoReflectedContextEquivalence.{u}.inverse.map
          (finiteSelectiveTwoReflectedContextEquivalence.{u}.functor.map
            finiteSelectiveTwoContextEquivalenceRestriction)) =
      finiteGeneratedReflectedInverseHighMap.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        (finiteSelectiveTwoReflectedContextEquivalence.{u}.functor.map
          finiteSelectiveTwoContextEquivalenceRestriction) := by
  unfold finiteSelectiveTwoReflectedContextEquivalence
  exact finiteGeneratedReflectedInverseMap_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    (finiteGeneratedReflectedForwardMap.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoContextEquivalenceRestriction)

/-! ## Unit and counit image graphs -/

/-- The concrete reflected unit hom maps to the actual high unit route. -/
theorem finiteSelectiveTwoContextEquivalence_unit_hom_image :
    (finiteGeneratedContextImageFunctor.{u}
      finiteSelectiveTwoContextEquivalenceOuterInput).map
        (finiteSelectiveTwoReflectedContextEquivalence.{u}.unitIso.hom.app
          finiteSelectiveTwoContextEquivalenceW) =
      finiteGeneratedReflectedUnitHighHom.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoContextEquivalenceW := by
  unfold finiteSelectiveTwoReflectedContextEquivalence
  exact finiteGeneratedReflectedUnitIsoApp_hom_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoContextEquivalenceW

/-- The concrete reflected unit inverse maps to the actual high inverse-unit route. -/
theorem finiteSelectiveTwoContextEquivalence_unit_inv_image :
    (finiteGeneratedContextImageFunctor.{u}
      finiteSelectiveTwoContextEquivalenceOuterInput).map
        (finiteSelectiveTwoReflectedContextEquivalence.{u}.unitIso.inv.app
          finiteSelectiveTwoContextEquivalenceW) =
      finiteGeneratedReflectedUnitHighInv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoContextEquivalenceW := by
  unfold finiteSelectiveTwoReflectedContextEquivalence
  exact finiteGeneratedReflectedUnitIsoApp_inv_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoContextEquivalenceW

/-- The concrete reflected counit hom maps to the actual high counit route. -/
theorem finiteSelectiveTwoContextEquivalence_counit_hom_image :
    (finiteGeneratedContextImageFunctor.{u}
      finiteSelectiveTwoObjectContextWitnessInput).map
        (finiteSelectiveTwoReflectedContextEquivalence.{u}.counitIso.hom.app
          finiteSelectiveTwoContextEquivalenceForwardW.{u}) =
      finiteGeneratedReflectedCounitHighHom.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoContextEquivalenceForwardW.{u} := by
  unfold finiteSelectiveTwoReflectedContextEquivalence
  exact finiteGeneratedReflectedCounitIsoApp_hom_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoContextEquivalenceForwardW.{u}

/-- The concrete reflected counit inverse maps to the actual high inverse-counit route. -/
theorem finiteSelectiveTwoContextEquivalence_counit_inv_image :
    (finiteGeneratedContextImageFunctor.{u}
      finiteSelectiveTwoObjectContextWitnessInput).map
        (finiteSelectiveTwoReflectedContextEquivalence.{u}.counitIso.inv.app
          finiteSelectiveTwoContextEquivalenceForwardW.{u}) =
      finiteGeneratedReflectedCounitHighInv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoContextEquivalenceForwardW.{u} := by
  unfold finiteSelectiveTwoReflectedContextEquivalence
  exact finiteGeneratedReflectedCounitIsoApp_inv_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoContextEquivalenceForwardW.{u}

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
