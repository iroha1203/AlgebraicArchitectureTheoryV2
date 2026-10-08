import ResearchLean.AG.AtlasCoefficientFiber.SupportCarrier
import ResearchLean.AG.AtlasCoefficientFiber.PushforwardCoefficient

/-!
# G-135 D：実comma包含による順像係数の制限

## Implementation notes

同じ実comma圏の連結成分写像を前合成し、原右Kan係数の可逆座標を戻す。
成分間の新同型を仮定する案は、追加セルが成分を結ぶ場合の制限を失うため採らない。
係数incidence自然性は同じcomma対象の全射等号で証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CategoryTheory.Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u

/-- 実関手の連結成分写像による、定数有理係数極限の関数制限。 -/
def componentFunctionRestrict {J K : Type u} [Category.{u} J] [Category.{u} K] (F : J ⥤ K) :
    (ConnectedComponents K → ULift.{u} ℚ) →ₗ[ℚ] (ConnectedComponents J → ULift.{u} ℚ) where
  toFun z c := z (F.mapConnectedComponents c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 制限は全連結成分で同じ前合成値。 -/
theorem componentFunctionRestrict_apply {J K : Type u} [Category.{u} J] [Category.{u} K]
    (F : J ⥤ K) (z : ConnectedComponents K → ULift.{u} ℚ) (c : ConnectedComponents J) :
    componentFunctionRestrict F z c = z (F.mapConnectedComponents c) := rfl

/-- 恒等関手の成分制限は同じ関数空間の恒等。 -/
theorem componentFunctionRestrict_refl (J : Type u) [Category.{u} J] :
    componentFunctionRestrict (𝟭 J) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  funext c
  induction c using Quotient.inductionOn with
  | h j => rfl

/-- 成分制限は実関手の合成に反変に従う。 -/
theorem componentFunctionRestrict_comp {J K L : Type u} [Category.{u} J] [Category.{u} K]
    [Category.{u} L] (F : J ⥤ K) (G : K ⥤ L) :
    componentFunctionRestrict (F ⋙ G) =
      (componentFunctionRestrict F).comp (componentFunctionRestrict G) := by
  apply LinearMap.ext
  intro z
  funext c
  induction c using Quotient.inductionOn with
  | h j => rfl

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 原右Kan係数を同じcomma成分前合成で制限する実線形射。 -/
def supportCoefficientRestrict (σ : Inc Nc A) :
    ((pushforwardCoefficients M B).obj ((supportIncFunctor Nc hab).obj σ)) →ₗ[ℚ]
      ((pushforwardCoefficients M A).obj σ) :=
  (coefficientCellIso (Carrier.preimageFunctor M A) σ).toLinearEquiv.symm.toLinearMap.comp
    ((componentFunctionRestrict (supportCommaFunctor M hab σ)).comp
      (coefficientCellIso (Carrier.preimageFunctor M B)
        ((supportIncFunctor Nc hab).obj σ)).toLinearEquiv.toLinearMap)

/-- 元の可逆係数座標では、全comma成分の値が同じ前合成式になる。 -/
theorem supportCoefficientRestrict_component (σ : Inc Nc A)
    (z : (pushforwardCoefficients M B).obj ((supportIncFunctor Nc hab).obj σ))
    (c : ConnectedComponents (StructuredArrow σ (Carrier.preimageFunctor M A))) :
    (coefficientCellIso (Carrier.preimageFunctor M A) σ).hom
      (supportCoefficientRestrict M hab σ z) c =
    (coefficientCellIso (Carrier.preimageFunctor M B) ((supportIncFunctor Nc hab).obj σ)).hom z
      ((supportCommaFunctor M hab σ).mapConnectedComponents c) := by
  change (coefficientCellIso (Carrier.preimageFunctor M A) σ).toLinearEquiv
    ((coefficientCellIso (Carrier.preimageFunctor M A) σ).toLinearEquiv.symm _) c = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- 任意comma対象での評価も元の同じ包含対象の値。 -/
theorem supportCoefficientRestrict_eval (σ : Inc Nc A)
    (z : (pushforwardCoefficients M B).obj ((supportIncFunctor Nc hab).obj σ))
    (j : StructuredArrow σ (Carrier.preimageFunctor M A)) :
    (coefficientCellIso (Carrier.preimageFunctor M A) σ).hom
      (supportCoefficientRestrict M hab σ z) (CategoryTheory.ConnectedComponents.mk j) =
    (coefficientCellIso (Carrier.preimageFunctor M B) ((supportIncFunctor Nc hab).obj σ)).hom z
      (CategoryTheory.ConnectedComponents.mk ((supportCommaFunctor M hab σ).obj j)) := by
  rw [supportCoefficientRestrict_component, CategoryTheory.Functor.mapConnectedComponents_mk]

/-- 同じcomma包含は原incidence射の前合成と全対象で可換。 -/
theorem supportCommaFunctor_precomp {σ τ : Inc Nc A} (f : σ ⟶ τ)
    (j : StructuredArrow τ (Carrier.preimageFunctor M A)) :
    (StructuredArrow.map ((supportIncFunctor Nc hab).map f)).obj
        ((supportCommaFunctor M hab τ).obj j) =
      (supportCommaFunctor M hab σ).obj ((StructuredArrow.map f).obj j) := by
  apply StructuredArrow.obj_ext _ _ (show
    ((StructuredArrow.map ((supportIncFunctor Nc hab).map f)).obj
      ((supportCommaFunctor M hab τ).obj j)).right =
    ((supportCommaFunctor M hab σ).obj ((StructuredArrow.map f).obj j)).right from rfl)
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id,
    StructuredArrow.map_obj_hom, supportCommaFunctor_obj_hom,
    StructuredArrow.map_obj_right, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 原係数制限は原右Kan係数の全incidence射と自然。 -/
theorem supportCoefficientRestrict_natural {σ τ : Inc Nc A} (f : σ ⟶ τ)
    (z : (pushforwardCoefficients M B).obj ((supportIncFunctor Nc hab).obj σ)) :
    supportCoefficientRestrict M hab τ
      ((pushforwardCoefficients M B).map ((supportIncFunctor Nc hab).map f) z) =
      (pushforwardCoefficients M A).map f (supportCoefficientRestrict M hab σ z) := by
  apply (coefficientCellIso (Carrier.preimageFunctor M A) τ).toLinearEquiv.injective
  funext c
  change (coefficientCellIso (Carrier.preimageFunctor M A) τ).hom
    (supportCoefficientRestrict M hab τ
      ((pushforwardCoefficients M B).map ((supportIncFunctor Nc hab).map f) z)) c =
    (coefficientCellIso (Carrier.preimageFunctor M A) τ).hom
      ((pushforwardCoefficients M A).map f (supportCoefficientRestrict M hab σ z)) c
  rw [supportCoefficientRestrict_component,
    pushforwardCoefficients_map_component_eval M B
      ((supportIncFunctor Nc hab).map f),
    pushforwardCoefficients_map_component_eval M A f,
    supportCoefficientRestrict_component]
  induction c using Quotient.inductionOn with
  | h j =>
      rw [CategoryTheory.Functor.mapConnectedComponents_mk,
        CategoryTheory.Functor.mapConnectedComponents_mk,
        CategoryTheory.Functor.mapConnectedComponents_mk,
        CategoryTheory.Functor.mapConnectedComponents_mk]
      rw [supportCommaFunctor_precomp]

/-- 同じ右Kan係数の制限を全incidence自然変換として接続する。 -/
def supportCoefficientsRestriction :
    supportIncFunctor Nc hab ⋙ pushforwardCoefficients M B ⟶ pushforwardCoefficients M A where
  app σ := ModuleCat.ofHom (supportCoefficientRestrict M hab σ)
  naturality σ τ f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact supportCoefficientRestrict_natural M hab f z

/-- 自然変換の各係数成分は同じcomma生成の実線形射。 -/
theorem supportCoefficientsRestriction_app (σ : Inc Nc A) :
    (supportCoefficientsRestriction M hab).app σ = ModuleCat.ofHom (supportCoefficientRestrict M hab σ) := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.componentFunctionRestrict
#print axioms AAT.AG.AtlasCoefficientFiber.componentFunctionRestrict_apply
#print axioms AAT.AG.AtlasCoefficientFiber.componentFunctionRestrict_refl
#print axioms AAT.AG.AtlasCoefficientFiber.componentFunctionRestrict_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientRestrict
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientRestrict_component
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientRestrict_eval
#print axioms AAT.AG.AtlasCoefficientFiber.supportCommaFunctor_precomp
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientRestrict_natural
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientsRestriction
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientsRestriction_app
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
