import Formal.SHIGURE.Part2.Families.SchemeTensorStructures
import Formal.SHIGURE.Part2.Schemes.ModuleTensorComparisons
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Canonical pullback comparisons for ordered finite tensor inputs

Definition 6.1 includes nullary operations. The canonical unit comparison
and the binary comparison therefore form one finite-input family. The
identity and composition equations below use the actual scheme module
pullback constraints, at every arity including zero.
-/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SchemeDescent

noncomputable section

universe u

variable {X Y Z : Scheme.{u}}

/-- API for nullary operations: the canonical module pullback preserves
its unit, by the free-module pullback comparison. -/
def unitModulePullbackIso (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).obj (unitModule X) ≅ unitModule Y := by
  letI : (TopologicalSpace.Opens.map f.base).Final := ⟨fun U => by
    let T : StructuredArrow U (TopologicalSpace.Opens.map f.base) :=
      StructuredArrow.mk (homOfLE (show U ≤ f ⁻¹ᵁ (⊤ : X.Opens) from by simp))
    exact isConnected_of_isTerminal (StructuredArrow U (TopologicalSpace.Opens.map f.base)) (x := T)
      { lift := fun A => StructuredArrow.homMk (homOfLE le_top)
        uniq := fun A m _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _) }⟩
  let e : (SheafOfModules.pullback f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
    asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  exact e

/-- The forward unit comparison is mathlib's normalized adjoint mate. -/
theorem unitModulePullbackIso_hom (f : Y ⟶ X) :
    (unitModulePullbackIso f).hom =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := rfl

/-- The unit comparison has the canonical scheme pullback-adjunction
normalization, expressed without changing adjunction instances. -/
theorem unitModulePullbackIso_homEquiv (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (unitModule X) (unitModule Y)
        (unitModulePullbackIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

/-- The empty input tensor is quasi-coherent: on each affine open its
presentation is the rank-one coefficient module. -/
theorem unitModule_isQuasiCoherent (X : Scheme.{u}) :
    IsQuasiCoherentModule (unitModule X) := by
  intro U
  refine ⟨ModuleCat.of Γ(X, U.1) Γ(X, U.1), ⟨?_⟩⟩
  exact tildeSelf ≪≫ (unitModulePullbackIso U.property.fromSpec).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.property.fromSpec).app (unitModule X)).symm

/-- Finite input tensors of quasi-coherent carriers remain quasi-coherent. -/
theorem tensorModules_isQuasiCoherent {S : Type u} (E : S → X.Modules)
    (h : ∀ s, IsQuasiCoherentModule (E s)) (ss : List S) :
    IsQuasiCoherentModule (tensorModules E ss) := by
  induction ss with
  | nil => exact unitModule_isQuasiCoherent X
  | cons s ss ih => exact tensorModule_isQuasiCoherent (h s) ih

/-- The ordered finite-tensor pullback comparison, including nullary
inputs, built from the canonical binary and unit comparisons. -/
def tensorModulesPullbackIso {S : Type u} (f : Y ⟶ X) (E : S → X.Modules)
    (h : ∀ s, IsQuasiCoherentModule (E s)) : (ss : List S) →
    (Scheme.Modules.pullback f).obj (tensorModules E ss) ≅
      tensorModules (fun s => (Scheme.Modules.pullback f).obj (E s)) ss
  | [] => unitModulePullbackIso f
  | s :: ss => quasiCoherentPullbackTensorIso f (h s)
      (tensorModules_isQuasiCoherent E h ss) ≪≫
    tensorModuleIso (Iso.refl _) (tensorModulesPullbackIso f E h ss)

/-- Naturality of the finite-tensor pullback comparison in every carrier
map. The empty tensor has the identity map on the structure sheaf. -/
theorem tensorModulesPullbackIso_naturality {S : Type u} (f : Y ⟶ X)
    {E F : S → X.Modules} (hE : ∀ s, IsQuasiCoherentModule (E s))
    (hF : ∀ s, IsQuasiCoherentModule (F s)) (m : ∀ s, E s ⟶ F s) (ss : List S) :
    (Scheme.Modules.pullback f).map (tensorModulesMap m ss) ≫
        (tensorModulesPullbackIso f F hF ss).hom =
      (tensorModulesPullbackIso f E hE ss).hom ≫
        tensorModulesMap (fun s => (Scheme.Modules.pullback f).map (m s)) ss := by
  induction ss with
  | nil =>
    change (Scheme.Modules.pullback f).map (𝟙 (unitModule X)) ≫ _ = _ ≫ 𝟙 _
    rw [(Scheme.Modules.pullback f).map_id, Category.id_comp, Category.comp_id]
    rfl
  | cons s ss ih =>
    change (Scheme.Modules.pullback f).map (tensorModuleMap (m s) (tensorModulesMap m ss)) ≫
      (pullbackTensorMap f (F s) (tensorModules F ss) ≫
        tensorModuleMap (𝟙 _) (tensorModulesPullbackIso f F hF ss).hom) =
      (pullbackTensorMap f (E s) (tensorModules E ss) ≫
        tensorModuleMap (𝟙 _) (tensorModulesPullbackIso f E hE ss).hom) ≫
        tensorModuleMap ((Scheme.Modules.pullback f).map (m s))
          (tensorModulesMap (fun s => (Scheme.Modules.pullback f).map (m s)) ss)
    rw [← Category.assoc, pullbackTensorMap_naturality]
    simp only [Category.assoc]
    rw [← tensorModuleMap_comp, ← tensorModuleMap_comp]
    simp only [Category.comp_id, Category.id_comp, ih]

/-- The nullary pullback comparison has the module pseudofunctor's
identity normalization. -/
theorem unitModulePullbackIso_id (X : Scheme.{u}) :
    (unitModulePullbackIso (𝟙 X)).hom =
      (Scheme.Modules.pullbackId X).hom.app (unitModule X) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [pullbackId_homEquiv]
  rw [unitModulePullbackIso_homEquiv]
  ext U x
  rfl

/-- The finite-tensor pullback comparison respects the module
pseudofunctor's identity constraint at every arity. -/
theorem tensorModulesPullbackIso_id {S : Type u} (E : S → X.Modules)
    (h : ∀ s, IsQuasiCoherentModule (E s)) (ss : List S) :
    (tensorModulesPullbackIso (𝟙 X) E h ss).hom ≫
      tensorModulesMap (fun s => (Scheme.Modules.pullbackId X).hom.app (E s)) ss =
      (Scheme.Modules.pullbackId X).hom.app (tensorModules E ss) := by
  induction ss with
  | nil =>
    change (unitModulePullbackIso (𝟙 X)).hom ≫ 𝟙 _ = _
    rw [Category.comp_id, unitModulePullbackIso_id]
    rfl
  | cons s ss ih =>
    change (pullbackTensorMap (𝟙 X) (E s) (tensorModules E ss) ≫
        tensorModuleMap (𝟙 _) (tensorModulesPullbackIso (𝟙 X) E h ss).hom) ≫
      tensorModuleMap ((Scheme.Modules.pullbackId X).hom.app (E s))
        (tensorModulesMap (fun s => (Scheme.Modules.pullbackId X).hom.app (E s)) ss) = _
    rw [Category.assoc, ← tensorModuleMap_comp, Category.id_comp, ih,
      pullbackTensorMap_id]
    rfl

/-- The nullary comparison respects composition, with the canonical
module pullback composition constraint. -/
theorem unitModulePullbackIso_comp (f : Y ⟶ X) (g : Z ⟶ Y) :
    (Scheme.Modules.pullback g).map (unitModulePullbackIso f).hom ≫
        (unitModulePullbackIso g).hom =
      (Scheme.Modules.pullbackComp g f).hom.app (unitModule X) ≫
        (unitModulePullbackIso (g ≫ f)).hom := by
  let c := (Scheme.Modules.pullback g).map (unitModulePullbackIso f).hom ≫
    (unitModulePullbackIso g).hom
  apply (cancel_epi ((Scheme.Modules.pullbackComp g f).inv.app (unitModule X))).1
  change (Scheme.Modules.pullbackComp g f).inv.app (unitModule X) ≫ c = _
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).homEquiv _ _).injective
  conv_lhs =>
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      pullbackComp_inv_unit, Category.assoc,
      ← (Scheme.Modules.pushforwardComp g f).hom.naturality, ← Category.assoc]
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.pullbackPushforwardAdjunction g)).homEquiv _ _ c ≫
    (Scheme.Modules.pushforwardComp g f).hom.app (unitModule Z) = _
  rw [Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ c) ≫ _ = _
  rw [show c = (Scheme.Modules.pullback g).map (unitModulePullbackIso f).hom ≫
    (unitModulePullbackIso g).hom from rfl, Adjunction.homEquiv_naturality_left]
  rw [unitModulePullbackIso_homEquiv g, Adjunction.homEquiv_naturality_right,
    unitModulePullbackIso_homEquiv f, unitModulePullbackIso_homEquiv (g ≫ f)]
  ext U x
  rfl

/-- The finite-tensor comparison respects composition of pullbacks.
This lifts the binary comparison and the nullary normalization to every
ordered input list. -/
theorem tensorModulesPullbackIso_comp {S : Type u} (f : Y ⟶ X) (g : Z ⟶ Y)
    (E : S → X.Modules) (h : ∀ s, IsQuasiCoherentModule (E s)) (ss : List S) :
    (Scheme.Modules.pullback g).map (tensorModulesPullbackIso f E h ss).hom ≫
      (tensorModulesPullbackIso g (fun s => (Scheme.Modules.pullback f).obj (E s))
        (fun s => (h s).pullback) ss).hom ≫
      tensorModulesMap (fun s => (Scheme.Modules.pullbackComp g f).hom.app (E s)) ss =
    (Scheme.Modules.pullbackComp g f).hom.app (tensorModules E ss) ≫
      (tensorModulesPullbackIso (g ≫ f) E h ss).hom := by
  induction ss with
  | nil =>
    change (Scheme.Modules.pullback g).map (unitModulePullbackIso f).hom ≫
      (unitModulePullbackIso g).hom ≫ 𝟙 _ = _
    rw [Category.comp_id, unitModulePullbackIso_comp]
    rfl
  | cons s ss ih =>
    change (Scheme.Modules.pullback g).map
      (pullbackTensorMap f (E s) (tensorModules E ss) ≫
        tensorModuleMap (𝟙 _) (tensorModulesPullbackIso f E h ss).hom) ≫
      (pullbackTensorMap g ((Scheme.Modules.pullback f).obj (E s))
        (tensorModules (fun s => (Scheme.Modules.pullback f).obj (E s)) ss) ≫
        tensorModuleMap (𝟙 _) (tensorModulesPullbackIso g
          (fun s => (Scheme.Modules.pullback f).obj (E s))
          (fun s => (h s).pullback) ss).hom) ≫
      tensorModuleMap ((Scheme.Modules.pullbackComp g f).hom.app (E s))
        (tensorModulesMap (fun s => (Scheme.Modules.pullbackComp g f).hom.app (E s)) ss) =
      (Scheme.Modules.pullbackComp g f).hom.app (tensorModule (E s) (tensorModules E ss)) ≫
        (pullbackTensorMap (g ≫ f) (E s) (tensorModules E ss) ≫
          tensorModuleMap (𝟙 _) (tensorModulesPullbackIso (g ≫ f) E h ss).hom)
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc _ (pullbackTensorMap g _ _) _, pullbackTensorMap_naturality]
    simp only [Category.assoc]
    rw [← tensorModuleMap_comp, ← tensorModuleMap_comp]
    simp only [(Scheme.Modules.pullback g).map_id, Category.id_comp]
    rw [ih, ← Category.comp_id ((Scheme.Modules.pullbackComp g f).hom.app (E s)),
      tensorModuleMap_comp]
    have comparison := congrArg
      (fun q => q ≫ tensorModuleMap (𝟙 _) (tensorModulesPullbackIso (g ≫ f) E h ss).hom)
      (pullbackTensorMap_comp f g (E s) (tensorModules E ss))
    simpa only [Category.assoc] using comparison

end

end SHIGURE.RealizationFamilies
