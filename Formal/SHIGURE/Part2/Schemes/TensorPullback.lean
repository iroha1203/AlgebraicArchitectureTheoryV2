import Formal.SHIGURE.Part2.Schemes.ModuleTensor

/-! # Canonical pullback comparison for module-sheaf tensors

This module supplies the comparison morphism used when pulling back the
primitive operations of Definition 6.1 and Appendix B.3. The construction
applies to arbitrary scheme morphisms and actual module sheaves.

## Implementation notes

The pushforward comparison sends a tensor of sections to the same pure
tensor over the source structure sheaf. Module sheafification then gives
its unique extension to the tensor sheaf. Taking its adjoint after the
pullback-adjunction units defines the pullback comparison. This fixes the
comparison by actual section maps and adjunctions; no comparison isomorphism
is selected as input. Invertibility and coherence are separate properties
of this canonical morphism.
-/
namespace SHIGURE.SchemeDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
noncomputable section
universe u
variable {X Y Z : Scheme.{u}}

/-- The sectionwise tensor comparison for pushforward. It sends
`m ⊗ n` over the target section ring to `m ⊗ n` over the source section ring,
and is the presheaf input to the sheafification construction in B.3. -/
def pushforwardTensorPresheafMap (f : Y ⟶ X) (M N : Y.Modules) :
    PresheafOfModules.Monoidal.tensorObj
      ((Scheme.Modules.pushforward f).obj M).val
      ((Scheme.Modules.pushforward f).obj N).val ⟶
      (PresheafOfModules.pushforward f.toRingCatSheafHom.val).obj
        (PresheafOfModules.Monoidal.tensorObj (R := Y.presheaf) M.val N.val) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n ↦ m ⊗ₜ[Y.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj U)] n)
    (by intros; simp [TensorProduct.add_tmul])
    (by intros; rfl)
    (by intros; simp [TensorProduct.tmul_add])
    (by
      intro a m n
      change M.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U) at m
      change N.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U) at n
      let r : Y.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj U) :=
        (f.toRingCatSheafHom.val.app U).hom a
      change m ⊗ₜ[Y.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj U)]
          (r • n) =
        r •
          (m ⊗ₜ[Y.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj U)] n)
      exact TensorProduct.tmul_smul _ _ _)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    change (PresheafOfModules.Monoidal.tensorObj M.val N.val).map
      ((TopologicalSpace.Opens.map f.base).op.map i) (m ⊗ₜ n) = _
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]

/-- The sectionwise pushforward comparison preserves pure tensors,
while changing their coefficient ring along the scheme morphism. -/
theorem pushforwardTensorPresheafMap_app_tmul (f : Y ⟶ X) (M N : Y.Modules)
    (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (m : ((Scheme.Modules.pushforward f).obj M).val.obj U)
    (n : ((Scheme.Modules.pushforward f).obj N).val.obj U) :
    (pushforwardTensorPresheafMap f M N).app U (m ⊗ₜ[X.presheaf.obj U] n) =
      (show M.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U) from m) ⊗ₜ[
        Y.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj U)]
      (show N.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U) from n) := rfl

/-- The presheaf comparison is natural in both modules. -/
theorem pushforwardTensorPresheafMap_naturality (f : Y ⟶ X)
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    PresheafOfModules.Monoidal.tensorHom
        ((Scheme.Modules.pushforward f).map a).val
        ((Scheme.Modules.pushforward f).map b).val ≫
      pushforwardTensorPresheafMap f M' N' =
    pushforwardTensorPresheafMap f M N ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.val).map
        (PresheafOfModules.Monoidal.tensorHom a.val b.val) := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- The canonical lax tensor comparison for actual module-sheaf pushforward. -/
def pushforwardTensorMap (f : Y ⟶ X) (M N : Y.Modules) :
    tensorModule ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (tensorModule M N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.val)).symm
    (pushforwardTensorPresheafMap f M N ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.val).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
          (tensorPresheaf M N)))

/-- The lax pushforward comparison is natural in both module sheaves. -/
@[reassoc]
theorem pushforwardTensorMap_naturality (f : Y ⟶ X)
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    tensorModuleMap ((Scheme.Modules.pushforward f).map a)
        ((Scheme.Modules.pushforward f).map b) ≫ pushforwardTensorMap f M' N' =
      pushforwardTensorMap f M N ≫
        (Scheme.Modules.pushforward f).map (tensorModuleMap a b) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.val)).injective
  change (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
        (PresheafOfModules.Monoidal.tensorHom
          ((Scheme.Modules.pushforward f).map a).val
          ((Scheme.Modules.pushforward f).map b).val) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left]
  change _ = (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _
    (pushforwardTensorMap f M N ≫ _)
  rw [Adjunction.homEquiv_naturality_right]
  simp only [pushforwardTensorMap,
    PresheafOfModules.sheafificationAdjunction_homEquiv_apply, Equiv.apply_symm_apply]
  erw [Equiv.apply_symm_apply]
  rw [← Category.assoc, pushforwardTensorPresheafMap_naturality]
  rw [Category.assoc, ← Functor.map_comp]
  change pushforwardTensorPresheafMap f M N ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.val).map
        (PresheafOfModules.Monoidal.tensorHom a.val b.val ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
            (tensorPresheaf M' N')) =
    (pushforwardTensorPresheafMap f M N ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.val).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
          (tensorPresheaf M N))) ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.val).map (tensorModuleMap a b).val
  rw [Category.assoc, ← Functor.map_comp]
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.val)).unit.naturality
      (PresheafOfModules.Monoidal.tensorHom a.val b.val)
  change PresheafOfModules.Monoidal.tensorHom a.val b.val ≫ _ =
    _ ≫ (tensorModuleMap a b).val at h
  erw [h]
  rfl

/-- Postcomposition under the tensor-sheaf universal property is
postcomposition of the underlying presheaf-module maps. -/
theorem tensorModuleHomEquiv_comp {M N K K' : X.Modules}
    (a : tensorModule M N ⟶ K) (b : K ⟶ K') :
    tensorModuleHomEquiv M N K' (a ≫ b) =
      tensorModuleHomEquiv M N K a ≫ b.val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv_naturality_right a b

/-- Precomposition by a tensor map under the universal property is
precomposition by the sectionwise tensor map. -/
theorem tensorModuleHomEquiv_map_comp {M M' N N' K : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') (c : tensorModule M' N' ⟶ K) :
    tensorModuleHomEquiv M N K (tensorModuleMap a b ≫ c) =
      PresheafOfModules.Monoidal.tensorHom a.val b.val ≫ tensorModuleHomEquiv M' N' K c :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv_naturality_left
    (PresheafOfModules.Monoidal.tensorHom a.val b.val) c

/-- The pushforward comparison is the unique extension of its sectionwise
pure-tensor map along the module-sheafification unit. -/
theorem pushforwardTensorMap_homEquiv (f : Y ⟶ X) (M N : Y.Modules) :
    tensorModuleHomEquiv ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N)
      ((Scheme.Modules.pushforward f).obj (tensorModule M N)) (pushforwardTensorMap f M N) =
    pushforwardTensorPresheafMap f M N ≫
      (PresheafOfModules.pushforward f.toRingCatSheafHom.val).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
          (tensorPresheaf M N)) :=
  Equiv.apply_symm_apply _ _

/-- The tensor-map image under the sheafification universal property
is determined by the original presheaf tensor map and the sheafification unit. -/
theorem tensorModuleHomEquiv_map {M M' N N' : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') :
    tensorModuleHomEquiv M N (tensorModule M' N') (tensorModuleMap a b) =
      PresheafOfModules.Monoidal.tensorHom a.val b.val ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app
          (tensorPresheaf M' N') := by
  change (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
        (PresheafOfModules.Monoidal.tensorHom a.val b.val)) = _
  rw [Adjunction.homEquiv_unit]
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.naturality
    (PresheafOfModules.Monoidal.tensorHom a.val b.val)).symm

/-- The pushforward comparison agrees with the identity normalization
of the actual module pushforward pseudofunctor. -/
theorem pushforwardTensorMap_id (M N : X.Modules) :
    pushforwardTensorMap (𝟙 X) M N ≫
        (Scheme.Modules.pushforwardId X).hom.app (tensorModule M N) =
      tensorModuleMap ((Scheme.Modules.pushforwardId X).hom.app M)
        ((Scheme.Modules.pushforwardId X).hom.app N) := by
  apply (tensorModuleHomEquiv _ _ _).injective
  simp only [Functor.id_obj, tensorModuleHomEquiv_comp,
    tensorModuleHomEquiv_map, pushforwardTensorMap_homEquiv]
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- The pushforward tensor comparison respects the composition constraint
of actual module pushforwards. Its proof compares the originating pure tensors. -/
theorem pushforwardTensorMap_comp (f : Y ⟶ X) (g : Z ⟶ Y) (M N : Z.Modules) :
    pushforwardTensorMap f ((Scheme.Modules.pushforward g).obj M)
        ((Scheme.Modules.pushforward g).obj N) ≫
      (Scheme.Modules.pushforward f).map (pushforwardTensorMap g M N) ≫
      (Scheme.Modules.pushforwardComp g f).hom.app (tensorModule M N) =
    tensorModuleMap ((Scheme.Modules.pushforwardComp g f).hom.app M)
        ((Scheme.Modules.pushforwardComp g f).hom.app N) ≫
      pushforwardTensorMap (g ≫ f) M N := by
  let P := PresheafOfModules.pushforward f.toRingCatSheafHom.val
  let Q := PresheafOfModules.pushforward g.toRingCatSheafHom.val
  let etaY := (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
    (tensorPresheaf ((Scheme.Modules.pushforward g).obj M) ((Scheme.Modules.pushforward g).obj N))
  let etaZ := (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.val)).unit.app
    (tensorPresheaf M N)
  let p := pushforwardTensorPresheafMap f ((Scheme.Modules.pushforward g).obj M)
    ((Scheme.Modules.pushforward g).obj N)
  let c := pushforwardTensorMap g M N
  let e := (Scheme.Modules.pushforwardComp g f).hom.app (tensorModule M N)
  have h := pushforwardTensorMap_homEquiv g M N
  change etaY ≫ c.val = pushforwardTensorPresheafMap g M N ≫ Q.map etaZ at h
  apply (tensorModuleHomEquiv _ _ _).injective
  rw [tensorModuleHomEquiv_map_comp, tensorModuleHomEquiv_comp]
  rw [pushforwardTensorMap_homEquiv, pushforwardTensorMap_homEquiv]
  change (p ≫ P.map etaY) ≫ (P.map c.val ≫ e.val) = _
  calc
    (p ≫ P.map etaY) ≫ (P.map c.val ≫ e.val) =
        p ≫ P.map (pushforwardTensorPresheafMap g M N ≫ Q.map etaZ) ≫ e.val := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun k ↦ p ≫ P.map k ≫ e.val) h
    _ = _ := by
      ext1 U
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m n
      rfl

/-- The canonical oplax tensor comparison for actual module-sheaf pullback. -/
def pullbackTensorMap (f : Y ⟶ X) (M N : X.Modules) :
    (Scheme.Modules.pullback f).obj (tensorModule M N) ⟶
      tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (tensorModuleMap
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
        pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N))

/-- The canonical pullback comparison is natural in both module sheaves. -/
theorem pullbackTensorMap_naturality (f : Y ⟶ X)
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (tensorModuleMap a b) ≫ pullbackTensorMap f M' N' =
      pullbackTensorMap f M N ≫ tensorModuleMap
        ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [pullbackTensorMap, Equiv.apply_symm_apply]
  rw [← Category.assoc, ← tensorModuleMap_comp]
  have ha := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  have hb := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality b
  change a ≫ _ = _ ≫ (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map a) at ha
  change b ≫ _ = _ ≫ (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map b) at hb
  rw [ha, hb]
  rw [tensorModuleMap_comp, Category.assoc]
  rw [pushforwardTensorMap_naturality, ← Category.assoc]

/-- Bifunctorial form of the canonical pullback tensor comparison. -/
def pullbackTensorNatTrans (f : Y ⟶ X) :
    moduleTensorFunctor X ⋙ Scheme.Modules.pullback f ⟶
      (Scheme.Modules.pullback f).prod (Scheme.Modules.pullback f) ⋙ moduleTensorFunctor Y where
  app MN := pullbackTensorMap f MN.1 MN.2
  naturality {_ _} ab := pullbackTensorMap_naturality f ab.1 ab.2

/-- The adjunction normalization that specifies the comparison canonically. -/
theorem pullbackTensorMap_homEquiv (f : Y ⟶ X) (M N : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackTensorMap f M N) =
      tensorModuleMap
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) :=
  Equiv.apply_symm_apply _ _

/-- The canonical pullback comparison sends a pure tensor of input
sections to the tensor of their pullback-unit images, followed by the actual
module-sheafification unit. This fixes its normalization for affine comparisons. -/
theorem pullbackTensorMap_homEquiv_app_tmul (f : Y ⟶ X) (M N : X.Modules)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (tensorModuleHomEquiv M N
      ((Scheme.Modules.pushforward f).obj
        (tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)))
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (pullbackTensorMap f M N))).app U (m ⊗ₜ[X.presheaf.obj U] n) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
      (tensorPresheaf ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))).app
        ((TopologicalSpace.Opens.map f.base).op.obj U)
      ((show ((Scheme.Modules.pullback f).obj M).val.obj
          ((TopologicalSpace.Opens.map f.base).op.obj U) from
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U m) ⊗ₜ[
          Y.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj U)]
        (show ((Scheme.Modules.pullback f).obj N).val.obj
          ((TopologicalSpace.Opens.map f.base).op.obj U) from
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app U n)) := by
  rw [pullbackTensorMap_homEquiv, tensorModuleHomEquiv_map_comp]
  simp only [Functor.comp_obj]
  rw [pushforwardTensorMap_homEquiv]
  rfl

/-- The pullback identity constraint is adjoint to the inverse
pushforward identity constraint. This API supplies its component normalization. -/
theorem pullbackId_homEquiv (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv M M
        ((Scheme.Modules.pullbackId X).hom.app M) =
      (Scheme.Modules.pushforwardId X).inv.app M := by
  rw [Adjunction.homEquiv_unit]
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  simpa using h.symm

/-- The canonical tensor comparison respects the identity constraint
of the actual module-pullback pseudofunctor, as required for primitive pullback. -/
theorem pullbackTensorMap_id (M N : X.Modules) :
    pullbackTensorMap (𝟙 X) M N ≫
      tensorModuleMap ((Scheme.Modules.pullbackId X).hom.app M)
        ((Scheme.Modules.pullbackId X).hom.app N) =
      (Scheme.Modules.pullbackId X).hom.app (tensorModule M N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_homEquiv]
  simp only [Functor.id_obj]
  rw [pullbackId_homEquiv]
  rw [Category.assoc, ← pushforwardTensorMap_naturality]
  rw [← Category.assoc, ← tensorModuleMap_comp]
  have hM := pullbackId_homEquiv M
  have hN := pullbackId_homEquiv N
  rw [Adjunction.homEquiv_unit] at hM hN
  rw [hM, hN]
  apply (cancel_mono ((Scheme.Modules.pushforwardId X).hom.app (tensorModule M N))).1
  rw [Category.assoc, pushforwardTensorMap_id, ← tensorModuleMap_comp]
  simp only [Iso.inv_hom_id_app, Functor.id_obj, tensorModuleMap_id]

/-- The two-step pullback tensor map has the unit normalization for
the composed adjunction. This API is used to verify composition coherence. -/
theorem pullbackTensorMap_comp_homEquiv (f : Y ⟶ X) (g : Z ⟶ Y) (M N : X.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)).homEquiv _ _
      ((Scheme.Modules.pullback g).map (pullbackTensorMap f M N) ≫
        pullbackTensorMap g ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)) =
    tensorModuleMap
      (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g)).unit.app M)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g)).unit.app N) ≫
      pushforwardTensorMap f
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj
          ((Scheme.Modules.pullback f).obj M)))
        ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj
          ((Scheme.Modules.pullback f).obj N))) ≫
      (Scheme.Modules.pushforward f).map (pushforwardTensorMap g
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M))
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj N))) := by
  rw [Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullback g).map (pullbackTensorMap f M N) ≫
        pullbackTensorMap g ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))) = _
  rw [Adjunction.homEquiv_naturality_left, pullbackTensorMap_homEquiv]
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_homEquiv]
  rw [Functor.map_comp]
  simp only [Adjunction.comp_unit_app, Category.assoc]
  rw [← pushforwardTensorMap_naturality_assoc]
  rw [tensorModuleMap_comp]
  simp only [Category.assoc]
  rfl

/-- The inverse pullback composition constraint has the unit normalization
specified by the actual pushforward composition constraint. -/
theorem pullbackComp_inv_unit (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).unit.app M ≫
      (Scheme.Modules.pushforward (g ≫ f)).map ((Scheme.Modules.pullbackComp g f).inv.app M) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)).unit.app M ≫
      (Scheme.Modules.pushforwardComp g f).hom.app
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f))
    (Scheme.Modules.pullbackComp g f).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact h.symm

/-- Composition coherence in the inverse-constraint form. The proof uses
the actual adjoint mate of the pushforward composition constraint. -/
theorem pullbackTensorMap_comp_inv (f : Y ⟶ X) (g : Z ⟶ Y) (M N : X.Modules) :
    pullbackTensorMap (g ≫ f) M N ≫
      tensorModuleMap ((Scheme.Modules.pullbackComp g f).inv.app M)
        ((Scheme.Modules.pullbackComp g f).inv.app N) =
    (Scheme.Modules.pullbackComp g f).inv.app (tensorModule M N) ≫
      (Scheme.Modules.pullback g).map (pullbackTensorMap f M N) ≫
      pullbackTensorMap g ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  let c := (Scheme.Modules.pullback g).map (pullbackTensorMap f M N) ≫
    pullbackTensorMap g ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_homEquiv]
  change _ = (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).homEquiv _ _
    ((Scheme.Modules.pullbackComp g f).inv.app (tensorModule M N) ≫ c)
  conv_rhs =>
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, pullbackComp_inv_unit]
    rw [Category.assoc, ← (Scheme.Modules.pushforwardComp g f).hom.naturality]
    rw [← Category.assoc]
  change _ =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)).homEquiv _ _ c ≫
      (Scheme.Modules.pushforwardComp g f).hom.app _
  rw [pullbackTensorMap_comp_homEquiv]
  simp only [Category.assoc]
  rw [pushforwardTensorMap_comp, ← pushforwardTensorMap_naturality]
  rw [← Category.assoc, ← tensorModuleMap_comp, pullbackComp_inv_unit, pullbackComp_inv_unit]
  rw [tensorModuleMap_comp]
  simp only [Category.assoc]
  rfl

/-- The canonical tensor comparison respects the composition constraint
of actual module pullbacks. This is the coherence needed to pull back
primitive operations repeatedly without choosing new comparison maps. -/
theorem pullbackTensorMap_comp (f : Y ⟶ X) (g : Z ⟶ Y) (M N : X.Modules) :
    (Scheme.Modules.pullback g).map (pullbackTensorMap f M N) ≫
      pullbackTensorMap g ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) ≫
      tensorModuleMap ((Scheme.Modules.pullbackComp g f).hom.app M)
        ((Scheme.Modules.pullbackComp g f).hom.app N) =
    (Scheme.Modules.pullbackComp g f).hom.app (tensorModule M N) ≫
      pullbackTensorMap (g ≫ f) M N := by
  have h := congrArg
    (fun k ↦ (Scheme.Modules.pullbackComp g f).hom.app (tensorModule M N) ≫ k ≫
      tensorModuleMap ((Scheme.Modules.pullbackComp g f).hom.app M)
        ((Scheme.Modules.pullbackComp g f).hom.app N))
    (pullbackTensorMap_comp_inv f g M N)
  simp only [Category.assoc] at h
  rw [← tensorModuleMap_comp] at h
  simp only [Iso.inv_hom_id_app, tensorModuleMap_id,
    Category.comp_id, Iso.hom_inv_id_app_assoc] at h
  simpa only [Category.assoc] using h.symm

end
end SHIGURE.SchemeDescent
