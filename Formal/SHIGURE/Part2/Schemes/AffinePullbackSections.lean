import Formal.SHIGURE.Part2.Schemes.ModuleTensorComparisons
import Formal.SHIGURE.Part2.Schemes.AffineModuleSections
import Formal.SHIGURE.Part2.Descent.ExtensionAlgebraTensor

/-! # Actual affine sections of pullback modules

The pullback adjunction unit followed by restriction is scalar extension
on related affine opens for a quasi-coherent module.

## Implementation notes

The affine tilde presentation gives the tensor comparison. Its normalization
is proved against the actual adjunction units, so the resulting base-change
statement concerns the original section map.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Scheme.Modules
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

variable {X Y Z : Scheme.{u}}

/-- The hom followed by its inverse fixes every actual sheaf section. -/
private theorem moduleIso_hom_inv_apply {P Q : X.Modules} (e : P ≅ Q)
    (W : X.Opens) (x : P.val.obj (op W)) :
    e.inv.val.app (op W) (e.hom.val.app (op W) x) = x := by
  exact congrArg (fun m : P ⟶ P => m.val.app (op W) x) e.hom_inv_id

/-- The inverse followed by its hom fixes every actual sheaf section. -/
private theorem moduleIso_inv_hom_apply {P Q : X.Modules} (e : P ≅ Q)
    (W : X.Opens) (x : Q.val.obj (op W)) :
    e.hom.val.app (op W) (e.inv.val.app (op W) x) = x := by
  exact congrArg (fun m : Q ⟶ Q => m.val.app (op W) x) e.inv_hom_id

/-- Composition of module-sheaf maps evaluates as composition on sections. -/
private theorem moduleHom_comp_apply {P Q K : X.Modules} (f : P ⟶ Q) (g : Q ⟶ K)
    (W : X.Opens) (x : P.val.obj (op W)) :
    (f ≫ g).val.app (op W) x = g.val.app (op W) (f.val.app (op W) x) := rfl

/-- Combine six pointwise normalization equations without unfolding their maps. -/
private theorem eq_chain_five
    {A₀ A₁ A₂ A₃ A₄ A₅ B : Type*}
    {f₁ : A₀ → A₁} {f₂ : A₁ → A₂} {f₃ : A₂ → A₃}
    {f₄ : A₃ → A₄} {f₅ : A₄ → A₅} {tail : A₅ → B}
    {x₀ : A₀} {x₁ : A₁} {x₂ : A₂} {x₃ : A₃} {x₄ : A₄} {x₅ : A₅} {y : B}
    (h₁ : f₁ x₀ = x₁) (h₂ : f₂ x₁ = x₂) (h₃ : f₃ x₂ = x₃)
    (h₄ : f₄ x₃ = x₄) (h₅ : f₅ x₄ = x₅) (h₆ : tail x₅ = y) :
    tail (f₅ (f₄ (f₃ (f₂ (f₁ x₀))))) = y := by
  rw [h₁, h₂, h₃, h₄, h₅, h₆]

/-- Read the affine presentation comparison on an original coefficient section. -/
private theorem presentationSections_apply {U : X.Opens} (hU : IsAffineOpen U)
    (M : X.Modules) (N : ModuleCat.{u} Γ(X, U))
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec) (x : N) :
    (affinePresentationSectionsIso hU M N e).hom x =
      (affineModuleSectionsIso hU M).hom
        (e.hom.val.app (op ⊤) (StructureSheaf.toOpenₗ Γ(X, U) N ⊤ x)) := rfl

/-- Normalize a six-map presentation chain using its pointwise comparison equations. -/
private theorem presentationSections_chain_core {U : X.Opens} (hU : IsAffineOpen U)
    (M : X.Modules) (N : ModuleCat.{u} Γ(X, U))
    (e : tilde N ≅ M.restrict hU.fromSpec)
    {P₁ P₂ P₃ P₄ P₅ : (Spec Γ(X, U)).Modules}
    (d₁ : tilde N ⟶ P₁) (d₂ : P₁ ⟶ P₂) (d₃ : P₂ ⟶ P₃)
    (d₄ : P₃ ⟶ P₄) (d₅ : P₄ ⟶ P₅) (d₆ : P₅ ⟶ M.restrict hU.fromSpec)
    (hd : e.hom = d₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ d₅ ≫ d₆)
    (x : N) (z₁ : P₁.val.obj (op ⊤)) (z₂ : P₂.val.obj (op ⊤))
    (z₃ : P₃.val.obj (op ⊤)) (z₄ : P₄.val.obj (op ⊤)) (z₅ : P₅.val.obj (op ⊤))
    (y : M.val.obj (op U))
    (h₁ : d₁.val.app (op ⊤) (StructureSheaf.toOpenₗ Γ(X, U) N ⊤ x) = z₁)
    (h₂ : d₂.val.app (op ⊤) z₁ = z₂) (h₃ : d₃.val.app (op ⊤) z₂ = z₃)
    (h₄ : d₄.val.app (op ⊤) z₃ = z₄) (h₅ : d₅.val.app (op ⊤) z₄ = z₅)
    (h₆ : (affineModuleSectionsIso hU M).hom (d₆.val.app (op ⊤) z₅) = y) :
    (affinePresentationSectionsIso hU M N e).hom x = y := by
  rw [presentationSections_apply, hd]
  simp only [moduleHom_comp_apply]
  exact eq_chain_five
    (f₁ := d₁.val.app (op ⊤)) (f₂ := d₂.val.app (op ⊤))
    (f₃ := d₃.val.app (op ⊤)) (f₄ := d₄.val.app (op ⊤))
    (f₅ := d₅.val.app (op ⊤))
    (tail := fun z => (affineModuleSectionsIso hU M).hom (d₆.val.app (op ⊤) z))
    h₁ h₂ h₃ h₄ h₅ h₆

/-- Pull a section along the actual adjunction unit and restrict to a related open. -/
private def sectionPull (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (inside : V ≤ f ⁻¹ᵁ U)
    (x : M.val.obj (op U)) : ((pullback f).obj M).val.obj (op V) :=
  ((pullback f).obj M).presheaf.map (homOfLE inside).op
    (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U) x)

/-- The actual unit and restriction define the section map over the actual
map of section rings. This is the linear map used by affine base change. -/
def affinePullbackSectionsMap (f : Y ⟶ X) (M : X.Modules)
    (U : X.affineOpens) (V : Y.affineOpens) (inside : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
    letI : Module Γ(X, U.1) (((pullback f).obj M).val.obj (op V.1)) :=
      Module.compHom _ (f.appLE U.1 V.1 inside).hom
    M.val.obj (op U.1) →ₗ[Γ(X, U.1)] ((pullback f).obj M).val.obj (op V.1) := by
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
  letI : Module Γ(X, U.1) (((pullback f).obj M).val.obj (op V.1)) :=
    Module.compHom _ (f.appLE U.1 V.1 inside).hom
  refine { toFun := sectionPull f M U.1 V.1 inside
           map_add' := fun x y => ?_
           map_smul' := fun r x => ?_ }
  · simp only [sectionPull, map_add]
  · have scalar := (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U.1)).hom.map_smul r x
    change ((pullback f).obj M).presheaf.map (homOfLE inside).op
        (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U.1) (r • x)) = _
    rw [scalar]
    exact ((pullback f).obj M).map_smul (homOfLE inside) ((f.app U.1) r) _

/-- Evaluation of the affine section map is the actual pullback-unit image
followed by the sheaf restriction; its normal form exposes these maps. -/
theorem affinePullbackSectionsMap_apply (f : Y ⟶ X) (M : X.Modules)
    (U : X.affineOpens) (V : Y.affineOpens) (inside : V.1 ≤ f ⁻¹ᵁ U.1)
    (x : M.val.obj (op U.1)) :
    affinePullbackSectionsMap f M U V inside x =
      ((pullback f).obj M).val.map (homOfLE inside).op
        (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U.1) x) := rfl

/-- The actual section pull commutes with a morphism of source module sheaves. -/
private theorem sectionPull_naturality (f : Y ⟶ X) {M N : X.Modules} (q : M ⟶ N)
    (U : X.Opens) (V : Y.Opens) (inside : V ≤ f ⁻¹ᵁ U) (x : M.val.obj (op U)) :
    ((pullback f).map q).val.app (op V) (sectionPull f M U V inside x) =
      sectionPull f N U V inside (q.val.app (op U) x) := by
  have h := congrArg (fun m => m.val.app (op U) x)
    ((pullbackPushforwardAdjunction f).unit.naturality q)
  have n := congrArg (fun m => m
    (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U) x))
    (((pullback f).map q).val.naturality (homOfLE inside).op)
  change _ = _ at h
  change _ = _ at n
  exact n.trans (congrArg (((pullback f).obj N).presheaf.map (homOfLE inside).op) h.symm)

/-- Normalize two section pulls through the inverse pullback-composition comparison. -/
private theorem sectionPull_comp_inv (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (inside : V ≤ f ⁻¹ᵁ U) (inside' : W ≤ g ⁻¹ᵁ V) (x : M.val.obj (op U)) :
    ((pullbackComp g f).inv.app M).val.app (op W)
      (sectionPull (g ≫ f) M U W (inside'.trans (g.preimage_mono inside)) x) =
      sectionPull g ((pullback f).obj M) V W inside' (sectionPull f M U V inside x) := by
  let P := (pullback f).obj M
  let Q := (pullback g).obj P
  have h := congrArg (fun m => m.val.app (op U) x) (pullbackComp_inv_unit f g M)
  change ((pullbackComp g f).inv.app M).val.app (op ((g ≫ f) ⁻¹ᵁ U))
      (((pullbackPushforwardAdjunction (g ≫ f)).unit.app M).val.app (op U) x) =
    (((pullbackPushforwardAdjunction g).unit.app P).val.app (op (f ⁻¹ᵁ U)))
      (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U) x) at h
  have natural := congrArg (fun m => m
    (((pullbackPushforwardAdjunction (g ≫ f)).unit.app M).val.app (op U) x))
    (((pullbackComp g f).inv.app M).val.naturality
      (homOfLE (inside'.trans (g.preimage_mono inside))).op)
  change ((pullbackComp g f).inv.app M).val.app (op W)
      (((pullback (g ≫ f)).obj M).presheaf.map _ _) =
    Q.presheaf.map _ (((pullbackComp g f).inv.app M).val.app (op ((g ≫ f) ⁻¹ᵁ U)) _) at natural
  unfold sectionPull
  apply natural.trans
  rw [h]
  have un := congrArg (fun m => m
    (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U) x))
    (((pullbackPushforwardAdjunction g).unit.app P).val.naturality (homOfLE inside).op)
  change (((pullbackPushforwardAdjunction g).unit.app P).val.app (op V))
      (P.presheaf.map (homOfLE inside).op _) =
    Q.presheaf.map (homOfLE (g.preimage_mono inside)).op
      (((pullbackPushforwardAdjunction g).unit.app P).val.app (op (f ⁻¹ᵁ U)) _) at un
  rw [un, ← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Transport section pull along an equality of the underlying scheme morphisms. -/
private theorem sectionPull_congr {f g : Y ⟶ X} (same : f = g) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (inside : V ≤ f ⁻¹ᵁ U)
    (inside' : V ≤ g ⁻¹ᵁ U) (x : M.val.obj (op U)) :
    ((pullbackCongr same).hom.app M).val.app (op V)
      (sectionPull f M U V inside x) = sectionPull g M U V inside' x := by
  subst g
  rfl

/-- The section pull for a composite agrees with successive actual section pulls. -/
private theorem sectionPull_comp (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules)
    (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (inside : V ≤ f ⁻¹ᵁ U) (inside' : W ≤ g ⁻¹ᵁ V) (x : M.val.obj (op U)) :
    ((pullbackComp g f).hom.app M).val.app (op W)
      (sectionPull g ((pullback f).obj M) V W inside' (sectionPull f M U V inside x)) =
    sectionPull (g ≫ f) M U W (inside'.trans (g.preimage_mono inside)) x := by
  rw [← sectionPull_comp_inv]
  exact moduleIso_inv_hom_apply ((pullbackComp g f).app M) W _

/-- On an affine chart, section pull along its inclusion is the restriction-unit map. -/
private theorem sectionPull_restrict_unit {U : X.Opens} (hU : IsAffineOpen U)
    (M : X.Modules) (inside : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U)
    (x : M.val.obj (op U)) :
    (affineModuleSectionsIso hU M).hom
      (((restrictFunctorIsoPullback hU.fromSpec).inv.app M).val.app (op ⊤)
        (sectionPull hU.fromSpec M U ⊤ inside x)) = x := by
  have unit := restrictFunctorIsoPullback_unit_eq hU.fromSpec M
  have hu := congrArg (fun m => m.val.app (op U) x) unit
  change ((restrictFunctorIsoPullback hU.fromSpec).hom.app M).val.app
      (op (hU.fromSpec ⁻¹ᵁ U))
      (((restrictAdjunction hU.fromSpec).unit.app M).val.app (op U) x) =
    (((pullbackPushforwardAdjunction hU.fromSpec).unit.app M).val.app (op U) x) at hu
  unfold sectionPull
  rw [← hu]
  have natural := congrArg (fun m => m
    (((restrictAdjunction hU.fromSpec).unit.app M).val.app (op U) x))
    (((restrictFunctorIsoPullback hU.fromSpec).hom.app M).val.naturality
      (homOfLE inside).op)
  change ((restrictFunctorIsoPullback hU.fromSpec).hom.app M).val.app (op ⊤)
      ((M.restrict hU.fromSpec).presheaf.map (homOfLE inside).op
        (((restrictAdjunction hU.fromSpec).unit.app M).val.app (op U) x)) =
    ((pullback hU.fromSpec).obj M).presheaf.map (homOfLE inside).op
      (((restrictFunctorIsoPullback hU.fromSpec).hom.app M).val.app
        (op (hU.fromSpec ⁻¹ᵁ U))
        (((restrictAdjunction hU.fromSpec).unit.app M).val.app (op U) x)) at natural
  rw [← natural]
  have inverse := moduleIso_hom_inv_apply ((restrictFunctorIsoPullback hU.fromSpec).app M) ⊤
    ((M.restrict hU.fromSpec).presheaf.map (homOfLE inside).op
      (((restrictAdjunction hU.fromSpec).unit.app M).val.app (op U) x))
  apply (congrArg (fun z => (affineModuleSectionsIso hU M).hom z) inverse).trans
  rw [affineModuleSectionsIso_hom_apply]
  have hx : (((restrictAdjunction hU.fromSpec).unit.app M).val.app (op U) x) =
      M.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op x :=
    congrArg (fun m => m x) (restrictAdjunction_unit_app_app hU.fromSpec M U)
  rw [hx]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ x)) = x
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp,
    ← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  have id : (homOfLE (hU.fromSpec.image_preimage_le U)).op ≫
      hU.fromSpec.opensFunctor.op.map (homOfLE inside).op ≫
      (eqToHom (hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec).symm).op =
      𝟙 (op U) := Subsingleton.elim _ _
  rw [id, M.presheaf.map_id]
  rfl

/-- The affine chart presentation carries an original section to its actual restriction. -/
private theorem chartPresentation_unit {U : X.Opens} (hU : IsAffineOpen U)
    (M : X.Modules) (N : ModuleCat.{u} Γ(X, U))
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec)
    (inside : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) (x : N) :
    ((restrictFunctorIsoPullback hU.fromSpec).hom.app M).val.app (op ⊤)
      (e.hom.val.app (op ⊤) (StructureSheaf.toOpenₗ Γ(X, U) N ⊤ x)) =
    sectionPull hU.fromSpec M U ⊤ inside ((affinePresentationSectionsIso hU M N e).hom x) := by
  let y := (affinePresentationSectionsIso hU M N e).hom x
  have inverse :
      ((restrictFunctorIsoPullback hU.fromSpec).inv.app M).val.app (op ⊤)
        (sectionPull hU.fromSpec M U ⊤ inside y) =
      e.hom.val.app (op ⊤) (StructureSheaf.toOpenₗ Γ(X, U) N ⊤ x) := by
    apply (affineModuleSectionsIso hU M).toLinearEquiv.injective
    exact sectionPull_restrict_unit hU M inside y
  rw [← inverse]
  exact moduleIso_inv_hom_apply ((restrictFunctorIsoPullback hU.fromSpec).app M) ⊤ _

/-- At the whole open, section pull is evaluation of the pullback adjunction unit. -/
private theorem sectionPull_top (f : Y ⟶ X) (M : X.Modules)
    (x : M.val.obj (op ⊤)) :
    sectionPull f M ⊤ ⊤ le_top x =
      ((pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) x := by
  unfold sectionPull
  have eq : (homOfLE (show (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤ from le_top)).op =
      𝟙 (op (⊤ : Y.Opens)) := Subsingleton.elim _ _
  rw [eq]
  exact congrArg (fun m => m
    (((pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) x))
    (((pullback f).obj M).presheaf.map_id (op ⊤))

/-- Normalize the affine pullback presentation against the original section-unit map. -/
private theorem pullbackPresentationSections_unit {f : Y ⟶ X} {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (M : X.Modules)
    (inside : V ≤ f ⁻¹ᵁ U) (N : ModuleCat.{u} Γ(X, U))
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec) (x : N) :
    let a := f.appLE U V inside
    (affinePresentationSectionsIso hV ((pullback f).obj M)
      ((ModuleCat.extendScalars a.hom).obj N) (pullbackTildePresentationIso inside e)).hom
        ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), a.hom] x) =
      sectionPull f M U V inside ((affinePresentationSectionsIso hU M N e).hom x) := by
  let a := f.appLE U V inside
  let g := hU.fromSpec
  let h := hV.fromSpec
  let b := Spec.map a
  let P := (pullback f).obj M
  let n := StructureSheaf.toOpenₗ Γ(X, U) N ⊤ x
  let y := (affinePresentationSectionsIso hU M N e).hom x
  have iu : (⊤ : (Spec Γ(X, U)).Opens) ≤ g ⁻¹ᵁ U := hU.fromSpec_preimage_self.symm.le
  have iv : (⊤ : (Spec Γ(Y, V)).Opens) ≤ h ⁻¹ᵁ V := hV.fromSpec_preimage_self.symm.le
  have square : b ≫ g = h ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV inside
  let q := e.hom ≫ (restrictFunctorIsoPullback g).hom.app M
  have first :
      ((tildePullbackIso a).inv.app N).val.app (op ⊤)
        (StructureSheaf.toOpenₗ Γ(Y, V) ((ModuleCat.extendScalars a.hom).obj N) ⊤
          ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), a.hom] x)) =
      sectionPull b (tilde N) ⊤ ⊤ le_top n := by
    rw [sectionPull_top]
    have unit := affineTildePullbackIso_unit_top a N x
    exact (congrArg (fun z => ((tildePullbackIso a).inv.app N).val.app (op ⊤) z)
      unit.symm).trans (moduleIso_hom_inv_apply ((tildePullbackIso a).app N) ⊤ _)
  have second :
      ((pullback b).map q).val.app (op ⊤) (sectionPull b (tilde N) ⊤ ⊤ le_top n) =
      sectionPull b ((pullback g).obj M) ⊤ ⊤ le_top (sectionPull g M U ⊤ iu y) := by
    apply (sectionPull_naturality b q ⊤ ⊤ le_top n).trans
    exact congrArg (sectionPull b ((pullback g).obj M) ⊤ ⊤ le_top)
      (chartPresentation_unit hU M N e iu x)
  have third := sectionPull_comp g b M U ⊤ ⊤ iu le_top y
  have fourth := sectionPull_congr square M U ⊤
    ((show (⊤ : (Spec Γ(Y, V)).Opens) ≤ b ⁻¹ᵁ ⊤ from le_top).trans (b.preimage_mono iu))
    (iv.trans (h.preimage_mono inside)) y
  have fifth := sectionPull_comp_inv f h M U V ⊤ inside iv y
  have last := sectionPull_restrict_unit hV P iv (sectionPull f M U V inside y)
  have displayed : (pullbackTildePresentationIso (hU := hU) (hV := hV) inside e).hom =
      (tildePullbackIso a).inv.app N ≫
        (pullback b).map q ≫
          (pullbackComp b g).hom.app M ≫
            (pullbackCongr square).hom.app M ≫
              (pullbackComp h f).inv.app M ≫
                (restrictFunctorIsoPullback h).inv.app P := rfl
  have normalized := presentationSections_chain_core (X := Y) (U := V) hV P
    ((ModuleCat.extendScalars a.hom).obj N)
    (pullbackTildePresentationIso (hU := hU) (hV := hV) inside e)
    (P₁ := (pullback b).obj (tilde N))
    (P₂ := (pullback b).obj ((pullback g).obj M))
    (P₃ := (pullback (b ≫ g)).obj M)
    (P₄ := (pullback (h ≫ f)).obj M)
    (P₅ := (pullback h).obj P)
    ((tildePullbackIso a).inv.app N) ((pullback b).map q)
    ((pullbackComp b g).hom.app M) ((pullbackCongr square).hom.app M)
    ((pullbackComp h f).inv.app M) ((restrictFunctorIsoPullback h).inv.app P)
    displayed ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), a.hom] x) _ _ _ _ _
    (sectionPull f M U V inside y) first second third fourth fifth last
  simpa only [a, P, y] using normalized

/-- Compose coefficient-presentation isomorphisms into the scalar-extension comparison. -/
@[irreducible] private def coefficientSectionsEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {N A : ModuleCat.{u} R} {K B : ModuleCat.{u} S}
    (eU : N ≅ A) (eT : K ≅ ModuleCat.of S (S ⊗[R] N)) (eV : K ≅ B) :
    (S ⊗[R] A) ≃ₗ[S] B :=
  (eU.toLinearEquiv.symm.baseChange R S _ _).trans
    (eT.toLinearEquiv.symm.trans eV.toLinearEquiv)

/-- The abstract coefficient comparison has the prescribed value on a unit tensor. -/
private theorem coefficientSectionsEquiv_unit_apply
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {N A : ModuleCat.{u} R} {K B : ModuleCat.{u} S}
    (eU : N ≅ A) (eT : K ≅ ModuleCat.of S (S ⊗[R] N)) (eV : K ≅ B) (x : A) :
    coefficientSectionsEquiv eU eT eV ((1 : S) ⊗ₜ[R] x) =
      eV.hom (eT.inv ((1 : S) ⊗ₜ[R] (eU.inv x))) := by
  unfold coefficientSectionsEquiv
  rfl

/-- Propagate unit-tensor normalization through the abstract coefficient comparisons. -/
private theorem coefficientSectionsEquiv_unit_core
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {N A : ModuleCat.{u} R} {K B : ModuleCat.{u} S}
    (eU : N ≅ A) (eT : K ≅ ModuleCat.of S (S ⊗[R] N)) (eV : K ≅ B)
    (unit : N → K) (j : A → B)
    (hT : ∀ n, eT.hom (unit n) = (1 : S) ⊗ₜ[R] n)
    (hV : ∀ n, eV.hom (unit n) = j (eU.hom n)) (x : A) :
    coefficientSectionsEquiv eU eT eV ((1 : S) ⊗ₜ[R] x) = j x := by
  rw [coefficientSectionsEquiv_unit_apply]
  have inverse : eT.inv ((1 : S) ⊗ₜ[R] (eU.inv x)) = unit (eU.inv x) := by
    apply eT.toLinearEquiv.symm_apply_eq.mpr
    exact (hT (eU.inv x)).symm
  rw [inverse, hV]
  exact congrArg j (eU.toLinearEquiv.apply_symm_apply x)

/-- Compare affine pullback sections with scalar extension through actual tilde presentations. -/
@[irreducible] private def presentationPullbackSectionsEquiv
    {f : Y ⟶ X} {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (M : X.Modules)
    (inside : V ≤ f ⁻¹ᵁ U) (N : ModuleCat.{u} Γ(X, U))
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec) :
    letI : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V inside).hom.toAlgebra
    (Γ(Y, V) ⊗[Γ(X, U)] M.val.obj (op U)) ≃ₗ[Γ(Y, V)]
      ((pullback f).obj M).val.obj (op V) := by
  let a := f.appLE U V inside
  letI : Algebra Γ(X, U) Γ(Y, V) := a.hom.toAlgebra
  let eU : N ≅ M.val.obj (op U) := affinePresentationSectionsIso hU M N e
  let eV : (ModuleCat.extendScalars a.hom).obj N ≅ ((pullback f).obj M).val.obj (op V) :=
    affinePresentationSectionsIso hV ((pullback f).obj M)
    ((ModuleCat.extendScalars a.hom).obj N) (pullbackTildePresentationIso inside e)
  exact coefficientSectionsEquiv eU
    (CoefficientDescent.extendScalarsTensorIso (B := Γ(Y, V)) N) eV

/-- The presentation-based comparison takes a unit tensor to actual section pull. -/
private theorem presentationPullbackSectionsEquiv_unit {f : Y ⟶ X} {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (M : X.Modules)
    (inside : V ≤ f ⁻¹ᵁ U) (N : ModuleCat.{u} Γ(X, U))
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec)
    (x : M.val.obj (op U)) :
    letI : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V inside).hom.toAlgebra
    presentationPullbackSectionsEquiv hU hV M inside N e ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] x) =
      sectionPull f M U V inside x := by
  let a := f.appLE U V inside
  letI : Algebra Γ(X, U) Γ(Y, V) := a.hom.toAlgebra
  let eU : N ≅ M.val.obj (op U) := affinePresentationSectionsIso hU M N e
  let eV : (ModuleCat.extendScalars a.hom).obj N ≅ ((pullback f).obj M).val.obj (op V) :=
    affinePresentationSectionsIso hV ((pullback f).obj M)
    ((ModuleCat.extendScalars a.hom).obj N) (pullbackTildePresentationIso inside e)
  let eT : (ModuleCat.extendScalars a.hom).obj N ≅ ModuleCat.of Γ(Y, V) (Γ(Y, V) ⊗[Γ(X, U)] N) :=
    CoefficientDescent.extendScalarsTensorIso (B := Γ(Y, V)) N
  have hT : ∀ n, eT.hom ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), a.hom] n) =
      (1 : Γ(Y, V)) ⊗ₜ[Γ(X, U)] n := by
    intro n
    exact CoefficientDescent.extendScalarsTensorIso_unit (B := Γ(Y, V)) N n
  have normalV : ∀ n, eV.hom ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), a.hom] n) =
      sectionPull f M U V inside (eU.hom n) := by
    intro n
    have normalized := pullbackPresentationSections_unit hU hV M inside N e n
    simpa only [a, eU, eV] using normalized
  have normalized := coefficientSectionsEquiv_unit_core
    (R := Γ(X, U)) (S := Γ(Y, V)) (N := N) (A := M.val.obj (op U))
    (K := (ModuleCat.extendScalars a.hom).obj N) (B := ((pullback f).obj M).val.obj (op V))
    eU eT eV (fun n => (1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), a.hom] n)
    (sectionPull f M U V inside) hT (fun n => by simpa only [] using normalV n) x
  unfold presentationPullbackSectionsEquiv
  simpa only [a, eU, eT, eV] using normalized

/-- Quasi-coherent pullback sections on related affine opens are the tensor
extension along the actual map of section rings. The presentation is
constructed from quasi-coherence; no comparison is supplied as a premise. -/
def affinePullbackSectionsEquiv (f : Y ⟶ X) (M : X.Modules)
    (hM : IsQuasiCoherentModule M) (U : X.affineOpens) (V : Y.affineOpens)
    (inside : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
    (Γ(Y, V.1) ⊗[Γ(X, U.1)] M.val.obj (op U.1)) ≃ₗ[Γ(Y, V.1)]
      ((pullback f).obj M).val.obj (op V.1) :=
  presentationPullbackSectionsEquiv U.property V.property M inside
    (Classical.choose (hM U)) (Classical.choice (Classical.choose_spec (hM U)))

/-- Unit tensors are sent to the actual pullback adjunction unit followed
by restriction. This normal form connects the tensor comparison to sections. -/
theorem affinePullbackSectionsEquiv_unit (f : Y ⟶ X) (M : X.Modules)
    (hM : IsQuasiCoherentModule M) (U : X.affineOpens) (V : Y.affineOpens)
    (inside : V.1 ≤ f ⁻¹ᵁ U.1) (x : M.val.obj (op U.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
    affinePullbackSectionsEquiv f M hM U V inside ((1 : Γ(Y, V.1)) ⊗ₜ[Γ(X, U.1)] x) =
      affinePullbackSectionsMap f M U V inside x := by
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
  exact presentationPullbackSectionsEquiv_unit U.property V.property M inside
    (Classical.choose (hM U)) (Classical.choice (Classical.choose_spec (hM U))) x

/-- The actual section pullback map exhibits base change for an arbitrary
scheme morphism and a quasi-coherent module on related affine opens. -/
theorem affinePullbackSections_isBaseChange (f : Y ⟶ X) (M : X.Modules)
    (hM : IsQuasiCoherentModule M) (U : X.affineOpens) (V : Y.affineOpens)
    (inside : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
    letI : Module Γ(X, U.1) (((pullback f).obj M).val.obj (op V.1)) :=
      Module.compHom _ (f.appLE U.1 V.1 inside).hom
    letI : IsScalarTower Γ(X, U.1) Γ(Y, V.1) (((pullback f).obj M).val.obj (op V.1)) :=
      IsScalarTower.of_compHom Γ(X, U.1) Γ(Y, V.1) _
    IsBaseChange Γ(Y, V.1) (affinePullbackSectionsMap f M U V inside) := by
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 inside).hom.toAlgebra
  letI : Module Γ(X, U.1) (((pullback f).obj M).val.obj (op V.1)) :=
    Module.compHom _ (f.appLE U.1 V.1 inside).hom
  letI : IsScalarTower Γ(X, U.1) Γ(Y, V.1) (((pullback f).obj M).val.obj (op V.1)) :=
    IsScalarTower.of_compHom Γ(X, U.1) Γ(Y, V.1) _
  let E : (Γ(Y, V.1) ⊗[Γ(X, U.1)] M.val.obj (op U.1)) ≃ₗ[Γ(Y, V.1)]
      ((pullback f).obj M).val.obj (op V.1) := affinePullbackSectionsEquiv f M hM U V inside
  have H : ∀ x, E ((1 : Γ(Y, V.1)) ⊗ₜ[Γ(X, U.1)] x) =
      affinePullbackSectionsMap f M U V inside x := affinePullbackSectionsEquiv_unit f M hM U V inside
  exact IsBaseChange.of_equiv (R := Γ(X, U.1)) (M := M.val.obj (op U.1))
    (N := ((pullback f).obj M).val.obj (op V.1))
    (f := affinePullbackSectionsMap f M U V inside) E H

end

end SHIGURE.SchemeDescent
