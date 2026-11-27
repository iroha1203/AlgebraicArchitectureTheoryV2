import Formal.SHIGURE.Part2.Schemes.ModuleSheafTensor
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Tensor operations of arbitrary finite arity on module sheaves

## Implementation notes

The individual arguments can have different module sheaves. Pure tensors
of their sections define a presheaf via the induced semilinear restrictions.
Sheafification then gives exactly the compatible multilinear families of
operations. Iterating the binary sheaf tensor would require choosing
parentheses and transporting the multilinear universal property through
the associators.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite PiTensorProduct
open scoped TensorProduct

noncomputable section

universe u

variable {X : Scheme.{u}} {I : Type u}

section Presheaves

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- A restriction map acts on each argument of a pure tensor. -/
private def moduleMultilinearRestriction (M : I → PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    MultilinearMap (R.obj U) (fun i => (M i).obj U)
      ((ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj V) (⨂[R.obj V] i, (M i).obj V))) where
  toFun x := tprod (R.obj V) (fun i => (M i).map f (x i))
  map_update_add' x i y z := by
    classical
    have update (t : (M i).obj U) :
        (fun j => (M j).map f (Function.update x i t j)) =
          Function.update (fun j => (M j).map f (x j)) i ((M i).map f t) := by
      funext j
      by_cases e : j = i
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne e]
    rw [update, update, update, map_add]
    exact (tprod (R.obj V)).map_update_add _ _ _ _
  map_update_smul' x i a y := by
    classical
    have update (t : (M i).obj U) :
        (fun j => (M j).map f (Function.update x i t j)) =
          Function.update (fun j => (M j).map f (x j)) i ((M i).map f t) := by
      funext j
      by_cases e : j = i
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne e]
    rw [update, update, (M i).map_smul]
    exact (tprod (R.obj V)).map_update_smul _ _ _ _

/-- Form the presheaf of tensors of each local tuple of sections. -/
def moduleMultilinearPresheaf (M : I → PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) where
  obj U := ModuleCat.of (R.obj U) (⨂[R.obj U] i, (M i).obj U)
  map {U V} f :=
    ModuleCat.ofHom (R := R.obj U) (Y :=
      ((ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj V) (⨂[R.obj V] i, (M i).obj V)) : Type u))
      (lift (moduleMultilinearRestriction M f))
  map_id U := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    let tensor (x : ∀ i, (M i).obj U) : ⨂[R.obj U] i, (M i).obj U := tprod (R.obj U) x
    change lift (moduleMultilinearRestriction M (𝟙 U)) (tensor x) = tensor x
    have component : (fun i => (M i).map (𝟙 U) (x i)) = x := by
      funext i
      rw [(M i).map_id]
      rfl
    have value : lift (moduleMultilinearRestriction M (𝟙 U)) (tensor x) =
        tensor (fun i => (M i).map (𝟙 U) (x i)) :=
      lift.tprod _
    exact value.trans (congrArg tensor component)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change lift (moduleMultilinearRestriction M _) (tprod (R.obj _) x) =
      lift (moduleMultilinearRestriction M g)
        (lift (moduleMultilinearRestriction M f) (tprod (R.obj _) x))
    simp only [lift.tprod, moduleMultilinearRestriction, MultilinearMap.coe_mk,
      PresheafOfModules.map_comp_apply]

/-- Restricting a pure tensor restricts all of its input sections. -/
theorem moduleMultilinearPresheaf_map_tprod
    (M : I → PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : ∀ i, (M i).obj U) :
    (moduleMultilinearPresheaf M).map f (tprod (R.obj U) x) =
      tprod (R.obj V) (fun i => (M i).map f (x i)) :=
  lift.tprod _

/-- Multilinear operations on the original sections, compatible with restrictions. -/
@[ext]
structure MultilinearSectionFamily (M : I → PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) where
  app (U : Cᵒᵖ) :
    MultilinearMap (R.obj U) (fun i => (M i).obj U) (P.obj U)
  naturality {U V : Cᵒᵖ} (f : U ⟶ V) (x : ∀ i, (M i).obj U) :
    P.map f (app U x) = app V (fun i => (M i).map f (x i))

variable {M : I → PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
  {P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}


/-- Apply a compatible multilinear family to pure tensors of local sections. -/
def MultilinearSectionFamily.toPresheafHom (a : MultilinearSectionFamily M P) :
    moduleMultilinearPresheaf M ⟶ P where
  app U := ModuleCat.ofHom (lift (a.app U))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change lift (a.app V) ((moduleMultilinearPresheaf M).map f (tprod _ x)) =
      P.map f (lift (a.app U) (tprod _ x))
    have restriction := moduleMultilinearPresheaf_map_tprod (R := R)
      M f x
    rw [restriction]
    exact (lift.tprod _).trans ((a.naturality f x).symm.trans (congrArg (P.map f) (lift.tprod _).symm))


/-- Read a map of tensor presheaves on pure tensors to recover the local operations. -/
def MultilinearSectionFamily.ofPresheafHom (a : moduleMultilinearPresheaf M ⟶ P) :
    MultilinearSectionFamily M P where
  app U := lift.symm (a.app U).hom
  naturality {U V} f x := by
    change (P.map f) ((a.app U) (tprod _ x)) =
      (a.app V) (tprod _ (fun i => (M i).map f (x i)))
    have restriction := moduleMultilinearPresheaf_map_tprod (R := R)
      M f x
    exact (PresheafOfModules.naturality_apply a f (tprod _ x)).symm.trans
      (congrArg (fun v => a.app V v) restriction)


/-- The presheaf tensor represents compatible families before sheafification. -/
private def multilinearPresheafHomEquiv (M : I → PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))
    (P : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    (moduleMultilinearPresheaf M ⟶ P) ≃ MultilinearSectionFamily M P where
  toFun := MultilinearSectionFamily.ofPresheafHom
  invFun := MultilinearSectionFamily.toPresheafHom
  left_inv := fun a => by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    exact lift.apply_symm_apply (a.app U).hom
  right_inv := fun a => by
    apply MultilinearSectionFamily.ext
    funext U
    exact lift.symm_apply_apply (a.app U)

end Presheaves

/-- The tensor product of the module sheaves is the sheafification of
the presheaf of tensors of sections. -/
def moduleMultilinearTensor (M : I → X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj (moduleMultilinearPresheaf (R := X.sheaf.val) (fun i => (M i).val))

/-- Each compatible family is precisely a morphism from the tensor of the sheaves. -/
def moduleMultilinearTensorHomEquiv (M : I → X.Modules) (P : X.Modules) :
    (moduleMultilinearTensor M ⟶ P) ≃ MultilinearSectionFamily (R := X.sheaf.val) (fun i => (M i).val) P.val :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _).trans
    (multilinearPresheafHomEquiv (R := X.sheaf.val) (fun i => (M i).val) P.val)


section Presheaves

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M N P : I → PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}

/-- Tensor all the original section maps and check restriction on pure tensors. -/
def moduleMultilinearPresheafMap (f : ∀ i, M i ⟶ N i) :
    moduleMultilinearPresheaf M ⟶ moduleMultilinearPresheaf N where
  app U := ModuleCat.ofHom (PiTensorProduct.map (fun i => ((f i).app U).hom))
  naturality {U V} a := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change PiTensorProduct.map (fun i => ((f i).app V).hom)
        ((moduleMultilinearPresheaf M).map a (tprod (R.obj U) x)) =
      (moduleMultilinearPresheaf N).map a
        (PiTensorProduct.map (fun i => ((f i).app U).hom) (tprod (R.obj U) x))
    let pulled (i : I) : (M i).obj V := (M i).map a (x i)
    let mapped (i : I) : (N i).obj U := (f i).app U (x i)
    let target (i : I) : (N i).obj V := (N i).map a (mapped i)
    have component : (fun i => (f i).app V (pulled i)) = target :=
      funext fun i => PresheafOfModules.naturality_apply (f i) a (x i)
    calc
      _ = PiTensorProduct.map (fun i => ((f i).app V).hom) (tprod (R.obj V) pulled) :=
        congrArg _ (moduleMultilinearPresheaf_map_tprod M a x)
      _ = tprod (R.obj V) (fun i => (f i).app V (pulled i)) :=
        PiTensorProduct.map_tprod _ _
      _ = tprod (R.obj V) target := congrArg (tprod (R.obj V)) component
      _ = (moduleMultilinearPresheaf N).map a (tprod (R.obj U) mapped) :=
        (moduleMultilinearPresheaf_map_tprod N a mapped).symm
      _ = _ := congrArg ((moduleMultilinearPresheaf N).map a) (PiTensorProduct.map_tprod _ _).symm


/-- The tensor map agrees with the original input maps on pure tensors. -/
theorem moduleMultilinearPresheafMap_app_tprod (f : ∀ i, M i ⟶ N i)
    (U : Cᵒᵖ) (x : ∀ i, (M i).obj U) :
    (moduleMultilinearPresheafMap f).app U (tprod (R.obj U) x) =
      tprod (R.obj U) (fun i => (f i).app U (x i)) :=
  PiTensorProduct.map_tprod _ _

/-- Tensoring the identity family gives the identity of the tensor presheaf. -/
theorem moduleMultilinearPresheafMap_id (M : I → PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)) :
    moduleMultilinearPresheafMap (fun i => 𝟙 (M i)) = 𝟙 (moduleMultilinearPresheaf M) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change (moduleMultilinearPresheafMap (fun i => 𝟙 (M i))).app U (tprod (R.obj U) x) =
    tprod (R.obj U) x
  exact moduleMultilinearPresheafMap_app_tprod (fun i => 𝟙 (M i)) U x

/-- The tensor of the composite family composes the tensor maps. -/
theorem moduleMultilinearPresheafMap_comp (f : ∀ i, M i ⟶ N i) (g : ∀ i, N i ⟶ P i) :
    moduleMultilinearPresheafMap (fun i => f i ≫ g i) =
      moduleMultilinearPresheafMap f ≫ moduleMultilinearPresheafMap g := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  let y (i : I) : (N i).obj U := (f i).app U (x i)
  change (moduleMultilinearPresheafMap (fun i => f i ≫ g i)).app U (tprod (R.obj U) x) =
    (moduleMultilinearPresheafMap g).app U ((moduleMultilinearPresheafMap f).app U (tprod (R.obj U) x))
  have first := moduleMultilinearPresheafMap_app_tprod (fun i => f i ≫ g i) U x
  have second := moduleMultilinearPresheafMap_app_tprod g U y
  have comp := congrArg ((moduleMultilinearPresheafMap g).app U)
    (moduleMultilinearPresheafMap_app_tprod f U x)
  exact first.trans (second.symm.trans comp.symm)

end Presheaves

/-- Mapping the factors of the sheaf tensor uses the sheafification of
the same component maps on local pure tensors. -/
def moduleMultilinearTensorMap {X : Scheme.{u}} {M N : I → X.Modules} (f : ∀ i, M i ⟶ N i) :
    moduleMultilinearTensor M ⟶ moduleMultilinearTensor N :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
    (moduleMultilinearPresheafMap (R := X.sheaf.val) (fun i => (f i).val))

/-- The tensor of module sheaves is functorial in the prescribed input positions. -/
def moduleMultilinearTensorFunctor (X : Scheme.{u}) (I : Type u) : (I → X.Modules) ⥤ X.Modules where
  obj := moduleMultilinearTensor
  map := moduleMultilinearTensorMap
  map_id M := by
    let sheafify := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
    change sheafify.map (moduleMultilinearPresheafMap (R := X.sheaf.val) (fun i => 𝟙 (M i).val)) =
      𝟙 (sheafify.obj _)
    rw [moduleMultilinearPresheafMap_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    let sheafify := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
    change sheafify.map (moduleMultilinearPresheafMap (R := X.sheaf.val) (fun i => (f i).val ≫ (g i).val)) =
      sheafify.map (moduleMultilinearPresheafMap (R := X.sheaf.val) (fun i => (f i).val)) ≫
        sheafify.map (moduleMultilinearPresheafMap (R := X.sheaf.val) (fun i => (g i).val))
    rw [moduleMultilinearPresheafMap_comp, CategoryTheory.Functor.map_comp]

end

end SHIGURE.SchemeDescent
