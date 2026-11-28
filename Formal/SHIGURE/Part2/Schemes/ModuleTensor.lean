import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentPullback

/-! # Tensor products of actual scheme-module sheaves

This is the thin tensor layer for the primitive operations in Definition 6.1
and their descent in Lemma 6.2 and Appendix B.3.

## Implementation notes

The tensor product is the sheafification of mathlib's sectionwise tensor
product of presheaves of modules. Thus its carriers are actual
`Scheme.Modules`, and its morphisms are actual module-sheaf morphisms.
Tensor products of modules of global sections would give the wrong object
on a general scheme. No choice of an affine presentation is part of the
definition. Affine comparison and compatibility with pullback are supplied
by the separate comparison modules.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules

noncomputable section

universe u

variable {X Y : Scheme.{u}}

/-- The structure sheaf as a module over itself. It is the input module
for nullary primitive operations in (6.1). -/
def unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The sectionwise tensor presheaf underlying the tensor sheaf in B.3.
This uses mathlib's tensor product and its semilinear restriction maps. -/
def tensorPresheaf (M N : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val

/-- The tensor bifunctor on module sheaves, constructed by tensoring
underlying presheaves and then applying module sheafification. -/
def moduleTensorFunctor (X : Scheme.{u}) : X.Modules × X.Modules ⥤ X.Modules := by
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact
  (toPresheafOfModules X).prod (toPresheafOfModules X) ⋙
    MonoidalCategory.tensor X.PresheafOfModules ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)

/-- The actual tensor product of two module sheaves in B.3 and (6.1). -/
def tensorModule (M N : X.Modules) : X.Modules :=
  (moduleTensorFunctor X).obj (M, N)

/-- The ordered finite tensor product of a family of carriers. The empty
input list gives the structure sheaf, so it includes designated sections. -/
def tensorModules {S : Type u} (E : S → X.Modules) : List S → X.Modules
  | [] => unitModule X
  | s :: ss => tensorModule (E s) (tensorModules E ss)

/-- Tensoring two module-sheaf morphisms is the sheafification of
mathlib's tensor morphism on the underlying presheaves. -/
def tensorModuleMap {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    tensorModule M N ⟶ tensorModule M' N' :=
  (moduleTensorFunctor X).map (f, g)

/-- Carrier maps induce the map on the ordered finite tensor input module.
For a nullary operation the induced input map is the identity on `𝒪_X`. -/
def tensorModulesMap {S : Type u} {E F : S → X.Modules} (f : ∀ s, E s ⟶ F s) :
    (ss : List S) → tensorModules E ss ⟶ tensorModules F ss
  | [] => 𝟙 _
  | s :: ss => tensorModuleMap (f s) (tensorModulesMap f ss)

/-- Isomorphisms of carriers induce an isomorphism of tensor sheaves.
This is the public comparison API for local tensor presentations. -/
def tensorModuleIso {M M' N N' : X.Modules} (e : M ≅ M') (f : N ≅ N') :
    tensorModule M N ≅ tensorModule M' N' :=
  (moduleTensorFunctor X).mapIso (Iso.prod e f)

/-- Tensor products preserve identity morphisms, as required to form
tensor expressions and structure-preserving maps in Definition 6.1. -/
theorem tensorModuleMap_id (M N : X.Modules) :
    tensorModuleMap (𝟙 M) (𝟙 N) = 𝟙 (tensorModule M N) :=
  (moduleTensorFunctor X).map_id (M, N)

/-- Tensor products preserve simultaneous composition in both arguments. -/
theorem tensorModuleMap_comp {M₁ M₂ M₃ N₁ N₂ N₃ : X.Modules}
    (f₁ : M₁ ⟶ M₂) (f₂ : M₂ ⟶ M₃) (g₁ : N₁ ⟶ N₂) (g₂ : N₂ ⟶ N₃) :
    tensorModuleMap (f₁ ≫ f₂) (g₁ ≫ g₂) =
      tensorModuleMap f₁ g₁ ≫ tensorModuleMap f₂ g₂ := by
  exact (moduleTensorFunctor X).map_comp
    (X := (M₁, N₁)) (Y := (M₂, N₂)) (Z := (M₃, N₃))
    (f₁, g₁) (f₂, g₂)

/-- The module-sheaf tensor has the universal property inherited from
module sheafification. Together with mathlib's sectionwise tensor universal
property, this identifies its maps with compatible bilinear operations. -/
def tensorModuleHomEquiv (M N K : X.Modules) :
    (tensorModule M N ⟶ K) ≃ (tensorPresheaf M N ⟶ K.val) := by
  change ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj
    (tensorPresheaf M N) ⟶ K) ≃ _
  exact PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.val)

/-- A morphism out of a tensor product is determined by the compatible
bilinear operation on the underlying presheaves. This is the public ext API
used when descending primitive operations. -/
theorem tensorModule_hom_ext {M N K : X.Modules}
    {f g : tensorModule M N ⟶ K}
    (h : tensorModuleHomEquiv M N K f = tensorModuleHomEquiv M N K g) : f = g :=
  (tensorModuleHomEquiv M N K).injective h

section PresheafRestriction

open Opposite

/-- The presheaf version of mathlib's module-sheaf pushforward adjunction.
It is used for the restriction/sheafification comparison below. -/
private def modulePresheafPushforwardAdjunction
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {R : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}
    (φ : R ⟶ F.op ⋙ S) (ψ : S ⟶ G.op ⋙ R)
    (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) S = ψ ≫ G.op.whiskerLeft φ)
    (H₂ : φ ≫ F.op.whiskerLeft ψ ≫
      Functor.whiskerRight (NatTrans.op adj.unit) R = 𝟙 R) :
    PresheafOfModules.pushforward φ ⊣ PresheafOfModules.pushforward ψ where
  unit :=
    { app := fun M =>
        { app := fun U => ModuleCat.ofHom (X := M.obj U)
            (Y := ((PresheafOfModules.pushforward ψ).obj
              ((PresheafOfModules.pushforward φ).obj M)).obj U)
            { toFun := M.map (adj.counit.app U.unop).op
              map_add' := map_add _
              map_smul' := fun r m => by
                change M.map (adj.counit.app U.unop).op (r • m) =
                  φ.app (op (G.obj U.unop)) (ψ.app U r) •
                    (M.map (adj.counit.app U.unop).op m : M.obj (op (F.obj (G.obj U.unop))))
                rw [M.map_smul]
                congr 1
                exact ConcreteCategory.congr_hom
                  (congrArg (fun t => t.app U) H₁) r }
          naturality := by
            intro U V i
            ext m
            change (M.presheaf.map i ≫ M.presheaf.map (adj.counit.app V.unop).op) m =
              (M.presheaf.map (adj.counit.app U.unop).op ≫
                M.presheaf.map ((G ⋙ F).op.map i)) m
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg (fun k => M.presheaf.map k m)
              ((NatTrans.op adj.counit).naturality i) }
      naturality := by
        intro M N h
        ext U m
        exact (PresheafOfModules.naturality_apply h (adj.counit.app U.unop).op m).symm }
  counit :=
    { app := fun M =>
        { app := fun U => ModuleCat.ofHom
            (X := ((PresheafOfModules.pushforward φ).obj
              ((PresheafOfModules.pushforward ψ).obj M)).obj U) (Y := M.obj U)
            { toFun := M.map (adj.unit.app U.unop).op
              map_add' := map_add _
              map_smul' := fun r m => by
                let m' : M.obj (op (G.obj (F.obj U.unop))) := m
                let a : R.obj (op (G.obj (F.obj U.unop))) :=
                  ψ.app (op (F.obj U.unop)) (φ.app U r)
                change M.map (adj.unit.app U.unop).op
                  (a • m') = r • (M.map (adj.unit.app U.unop).op m' : M.obj U)
                rw [M.map_smul]
                congr 1
                exact ConcreteCategory.congr_hom
                  (congrArg (fun t => t.app U) H₂) r }
          naturality := by
            intro U V i
            ext m
            change (M.presheaf.map ((F ⋙ G).op.map i) ≫
                M.presheaf.map (adj.unit.app V.unop).op) m =
              (M.presheaf.map (adj.unit.app U.unop).op ≫ M.presheaf.map i) m
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg (fun k => M.presheaf.map k m)
              ((NatTrans.op adj.unit).naturality i) }
      naturality := by
        intro M N h
        ext U m
        exact (PresheafOfModules.naturality_apply h (adj.unit.app U.unop).op m).symm }
  left_triangle_components M := by
    ext U m
    change (M.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      M.presheaf.map (F.map (adj.unit.app U.unop)).op) m = m
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    simp
  right_triangle_components M := by
    ext U m
    change (M.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      M.presheaf.map (adj.unit.app (G.obj U.unop)).op) m = m
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    simp

/-- Restriction of presheaves of modules along an open immersion, using
its actual image-open functor and the isomorphism of section rings. -/
def restrictModulePresheafFunctor (f : Y ⟶ X) [IsOpenImmersion f] :
    X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app U := (f.appIso U.unop).inv }
  PresheafOfModules.pushforward (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

/-- Restriction to image opens is left adjoint to the usual presheaf
pushforward. Its section-ring equations are the open-immersion equations. -/
private def restrictModulePresheafAdjunction (f : Y ⟶ X) [IsOpenImmersion f] :
    restrictModulePresheafFunctor f ⊣
      PresheafOfModules.pushforward f.toRingCatSheafHom.val := by
  apply modulePresheafPushforwardAdjunction
    (by exact f.isOpenEmbedding.isOpenMap.adjunction)
  · ext U x
    exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have equal : (f.appIso U.unop).inv ≫ f.app _ ≫
        Y.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← Y.presheaf.map_id]
      rfl
    exact congr($equal x)

/-- Module sheafification commutes with restriction to an open subscheme.
This is an isomorphism of actual functors, obtained from their two
adjunctions and the equality of their right adjoints. -/
def restrictModuleSheafificationIso (f : Y ⟶ X) [IsOpenImmersion f] :
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val) ⋙ restrictFunctor f ≅
      restrictModulePresheafFunctor f ⋙
        PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).comp
    (restrictAdjunction f)).leftAdjointUniq
      ((restrictModulePresheafAdjunction f).comp
        (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)))

/-- The sectionwise tensor comparison for restriction along an open
immersion. The component is the map `m ⊗ n ↦ m ⊗ n` along the actual
isomorphism of section rings. -/
def restrictTensorPresheafMap (f : Y ⟶ X) [IsOpenImmersion f] (M N : X.Modules) :
    tensorPresheaf (M.restrict f) (N.restrict f) ⟶
      (restrictModulePresheafFunctor f).obj (tensorPresheaf M N) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n => m ⊗ₜ[X.presheaf.obj (f.opensFunctor.op.obj U)] n)
    (by intros; simp [TensorProduct.add_tmul])
    (by intros; rfl)
    (by intros; simp [TensorProduct.tmul_add])
    (by
      intro a m n
      change M.val.obj (f.opensFunctor.op.obj U) at m
      change N.val.obj (f.opensFunctor.op.obj U) at n
      let r : X.presheaf.obj (f.opensFunctor.op.obj U) := (f.appIso U.unop).inv a
      change m ⊗ₜ[X.presheaf.obj (f.opensFunctor.op.obj U)] (r • n) =
        r • (m ⊗ₜ[X.presheaf.obj (f.opensFunctor.op.obj U)] n)
      exact TensorProduct.tmul_smul _ _ _)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    change (tensorPresheaf M N).map (f.opensFunctor.op.map i) (m ⊗ₜ n) = _
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]

/-- Restriction along an open immersion does not change tensor products
of presheaves: its coefficient maps are isomorphisms. -/
theorem restrictTensorPresheafMap_app_isIso (f : Y ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules) (U : Y.Opensᵒᵖ) :
    IsIso ((restrictTensorPresheafMap f M N).app U) := by
  let e := (f.appIso U.unop).symm.commRingCatIsoToRingEquiv
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom := by
    simpa only [RingEquiv.toRingHom_eq_coe] using RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm e.toRingHom e.symm.toRingHom
  let eM : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((M.restrict f).val.obj U) (M.val.obj (f.opensFunctor.op.obj U)) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eN : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((N.restrict f).val.obj U) (N.val.obj (f.opensFunctor.op.obj U)) :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let t := TensorProduct.congr eM eN
  have agrees (x : (tensorPresheaf (M.restrict f) (N.restrict f)).obj U) :
      (restrictTensorPresheafMap f M N).app U x = t x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (fun x => (restrictTensorPresheafMap f M N).app U x)
  rw [show (fun x => (restrictTensorPresheafMap f M N).app U x) = t from funext agrees]
  exact t.bijective

/-- The actual tensor presheaf is unchanged by restriction to an open
subscheme, after transporting the coefficients by its section-ring isomorphism. -/
def restrictTensorPresheafIso (f : Y ⟶ X) [IsOpenImmersion f] (M N : X.Modules) :
    tensorPresheaf (M.restrict f) (N.restrict f) ≅
      (restrictModulePresheafFunctor f).obj (tensorPresheaf M N) := by
  let a := restrictTensorPresheafMap f M N
  letI : ∀ U, IsIso (a.app U) := fun U => restrictTensorPresheafMap_app_isIso f M N U
  exact PresheafOfModules.isoMk (fun U => asIso (a.app U))
    (by intro U V i; exact a.naturality i)

/-- Restriction of the sheafified tensor product is the tensor product of
the actual restricted sheaves. This supplies the affine-local comparison
needed to prove quasi-coherence without assuming the general pullback theorem. -/
def restrictTensorModuleIso (f : Y ⟶ X) [IsOpenImmersion f] (M N : X.Modules) :
    (tensorModule M N).restrict f ≅ tensorModule (M.restrict f) (N.restrict f) :=
  (restrictModuleSheafificationIso f).app (tensorPresheaf M N) ≪≫
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).mapIso
      (restrictTensorPresheafIso f M N).symm

end PresheafRestriction

end

end SHIGURE.SchemeDescent
