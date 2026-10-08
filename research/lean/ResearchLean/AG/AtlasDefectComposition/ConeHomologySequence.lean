import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Formal.Util.AssertStandardAxioms
/-! # 標準錐の長完全列と実homology

G-133 Cの長完全列を全整数次数で実線形射へ接続する。

Implementation notes: mathlibの標準distinguished mappingCone triangleへhomological
functorを適用し、homologyFunctorFactorsの自然同型で各項と射を移す。
独自exactness certificateを受け取る経路は使わない。三つの中間項の完全性を
別々に証明し、余核/核の短完全列の生成へ渡す。
-/

noncomputable section
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
universe w
variable {A B C : ModuleCat.{w} ℚ}
/-- Cの標準長完全列を指定線形同型で移す短複体。入力exactnessはこの構成へ供給しない。 -/
def transportShortComplex (S : ShortComplex (ModuleCat.{w} ℚ))
    (e₀ : S.X₁ ≅ A) (e₁ : S.X₂ ≅ B) (e₂ : S.X₃ ≅ C) :
    ShortComplex (ModuleCat.{w} ℚ) :=
  ShortComplex.mk (e₀.inv ≫ S.f ≫ e₁.hom) (e₁.inv ≫ S.g ≫ e₂.hom) (by simp [Category.assoc])

/-- 次数別標準homology同型で短複体の全三項と二射を同定する。 -/
def transportShortComplexIso (S : ShortComplex (ModuleCat.{w} ℚ))
    (e₀ : S.X₁ ≅ A) (e₁ : S.X₂ ≅ B) (e₂ : S.X₃ ≅ C) :
    S ≅ transportShortComplex S e₀ e₁ e₂ :=
  ShortComplex.isoMk e₀ e₁ e₂ (by simp [transportShortComplex])
    (by simp [transportShortComplex])

/-- 方向仮定である標準短複体の完全性を線形同型に沿って移送する。 -/
theorem transportShortComplex_exact (S : ShortComplex (ModuleCat.{w} ℚ))
    (e₀ : S.X₁ ≅ A) (e₁ : S.X₂ ≅ B) (e₂ : S.X₃ ≅ C) (hS : S.Exact) :
    Function.Exact (transportShortComplex S e₀ e₁ e₂).f.hom
      (transportShortComplex S e₀ e₁ e₂).g.hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (ShortComplex.exact_of_iso (transportShortComplexIso S e₀ e₁ e₂) hS)

variable {F G : CochainComplex (ModuleCat.{w} ℚ) ℤ} (φ : F ⟶ G)
/-- 標準錐triangleの連結射を実complex homologyへ移す。全整数mを量化する。 -/
def coneConnecting (m : ℤ) : (mappingCone φ).homology m ⟶ F.homology (m+1) :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).inv.app
    (mappingCone φ) ≫
  (HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) 0).homologySequenceδ
    (mappingCone.triangleh φ) m (m+1) rfl ≫
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) (m+1)).hom.app F

/-- 原short exact列の錐連結射は標準商評価の後に同じ列のδを作用させる。 -/
theorem coneConnecting_shortExact (S : ShortComplex (CochainComplex (ModuleCat.{w} ℚ) ℤ))
    (hS : S.ShortExact) (m : ℤ) :
    coneConnecting S.f m = HomologicalComplex.homologyMap
      (mappingCone.descShortComplex S) m ≫ hS.δ m (m+1) rfl := by
  dsimp only [coneConnecting]
  rw [mappingCone.homologySequenceδ_triangleh hS m (m+1) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  exact congrArg (fun t : S.X₃.homology m ⟶ S.X₁.homology (m+1) =>
    HomologicalComplex.homologyMap (mappingCone.descShortComplex S) m ≫ t)
      (Category.comp_id (hS.δ m (m+1) rfl))

/-- 標準錐長完全列のsource/target/cone三項を実homologyで読む。 -/
def coneTargetSequence (m : ℤ) : ShortComplex (ModuleCat.{w} ℚ) :=
  transportShortComplex
    (ShortComplex.mk _ _ ((HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ)
      (ComplexShape.up ℤ) 0).homologySequence_comp (mappingCone.triangleh φ)
        (HomotopyCategory.mappingCone_triangleh_distinguished φ) m))
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app F)
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app G)
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app
      (mappingCone φ))

/-- 長完全列の最初の射は元のchain mapの標準homology mapである。 -/
theorem coneTargetSequence_f (m : ℤ) :
    (coneTargetSequence φ m).f = HomologicalComplex.homologyMap φ m := by
  change (HomotopyCategory.homologyFunctorFactors _ _ m).inv.app F ≫
    ((HomotopyCategory.quotient _ _ ⋙ HomotopyCategory.homologyFunctor _ _ m).map φ) ≫
    (HomotopyCategory.homologyFunctorFactors _ _ m).hom.app G = _
  rw [(HomotopyCategory.homologyFunctorFactors _ _ m).hom.naturality]
  simp

/-- 長完全列の二射目は標準錐への実包含のhomology mapである。 -/
theorem coneTargetSequence_g (m : ℤ) :
    (coneTargetSequence φ m).g = HomologicalComplex.homologyMap (mappingCone.inr φ) m := by
  change (HomotopyCategory.homologyFunctorFactors _ _ m).inv.app G ≫
    ((HomotopyCategory.quotient _ _ ⋙ HomotopyCategory.homologyFunctor _ _ m).map
      (mappingCone.inr φ)) ≫
    (HomotopyCategory.homologyFunctorFactors _ _ m).hom.app (mappingCone φ) = _
  rw [(HomotopyCategory.homologyFunctorFactors _ _ m).hom.naturality]
  simp

/-- 標準distinguished triangleから元の比較と錐包含での完全性を全整数次数で放電する。 -/
theorem cone_target_exact (m : ℤ) :
    Function.Exact (HomologicalComplex.homologyMap φ m).hom
      (HomologicalComplex.homologyMap (mappingCone.inr φ) m).hom := by
  have h := (HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) 0).homologySequence_exact₂ (mappingCone.triangleh φ)
      (HomotopyCategory.mappingCone_triangleh_distinguished φ) m
  have ht := transportShortComplex_exact _
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app F)
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app G)
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app
      (mappingCone φ)) h
  change Function.Exact (coneTargetSequence φ m).f.hom (coneTargetSequence φ m).g.hom at ht
  rw [coneTargetSequence_f, coneTargetSequence_g] at ht
  exact ht

/-- 標準錐長完全列のtarget/cone/次source三項を実homologyで読む。 -/
def coneMiddleSequence (m : ℤ) : ShortComplex (ModuleCat.{w} ℚ) :=
  transportShortComplex
    (ShortComplex.mk _ _ ((HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ)
      (ComplexShape.up ℤ) 0).comp_homologySequenceδ (mappingCone.triangleh φ)
        (HomotopyCategory.mappingCone_triangleh_distinguished φ) m (m+1) rfl))
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app G)
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app (mappingCone φ))
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) (m+1)).app F)

/-- 中間短複体の最初の射は標準錐包含の実homology mapである。 -/
theorem coneMiddleSequence_f (m : ℤ) :
    (coneMiddleSequence φ m).f = HomologicalComplex.homologyMap (mappingCone.inr φ) m := by
  change (HomotopyCategory.homologyFunctorFactors _ _ m).inv.app G ≫
    ((HomotopyCategory.quotient _ _ ⋙ HomotopyCategory.homologyFunctor _ _ m).map
      (mappingCone.inr φ)) ≫
    (HomotopyCategory.homologyFunctorFactors _ _ m).hom.app (mappingCone φ) = _
  rw [(HomotopyCategory.homologyFunctorFactors _ _ m).hom.naturality]
  simp

/-- 中間短複体の二射目は移送済みの標準連結射である。 -/
theorem coneMiddleSequence_g (m : ℤ) : (coneMiddleSequence φ m).g = coneConnecting φ m := rfl

/-- 標準distinguished triangleから錐包含と連結射での完全性を放電する。 -/
theorem cone_middle_exact (m : ℤ) :
    Function.Exact (HomologicalComplex.homologyMap (mappingCone.inr φ) m).hom
      (coneConnecting φ m).hom := by
  have h := (HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) 0).homologySequence_exact₃
    (mappingCone.triangleh φ) (HomotopyCategory.mappingCone_triangleh_distinguished φ) m (m+1) rfl
  have ht := transportShortComplex_exact _
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app G)
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app (mappingCone φ))
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) (m+1)).app F) h
  change Function.Exact (coneMiddleSequence φ m).f.hom (coneMiddleSequence φ m).g.hom at ht
  rw [coneMiddleSequence_f, coneMiddleSequence_g] at ht
  exact ht

/-- 標準錐長完全列のcone/次source/次target三項を実homologyで読む。 -/
def coneSourceSequence (m : ℤ) : ShortComplex (ModuleCat.{w} ℚ) :=
  transportShortComplex
    (ShortComplex.mk _ _ ((HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ)
      (ComplexShape.up ℤ) 0).homologySequenceδ_comp (mappingCone.triangleh φ)
        (HomotopyCategory.mappingCone_triangleh_distinguished φ) m (m+1) rfl))
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app (mappingCone φ))
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) (m+1)).app F)
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) (m+1)).app G)

/-- 後続短複体の最初の射は標準連結射である。 -/
theorem coneSourceSequence_f (m : ℤ) : (coneSourceSequence φ m).f = coneConnecting φ m := rfl

/-- 後続短複体の二射目は次次数の実比較homology mapである。 -/
theorem coneSourceSequence_g (m : ℤ) :
    (coneSourceSequence φ m).g = HomologicalComplex.homologyMap φ (m+1) := by
  change (HomotopyCategory.homologyFunctorFactors _ _ (m+1)).inv.app F ≫
    ((HomotopyCategory.quotient _ _ ⋙ HomotopyCategory.homologyFunctor _ _ (m+1)).map φ) ≫
    (HomotopyCategory.homologyFunctorFactors _ _ (m+1)).hom.app G = _
  rw [(HomotopyCategory.homologyFunctorFactors _ _ (m+1)).hom.naturality]
  simp

/-- 標準distinguished triangleから連結射と次次数の比較での完全性を放電する。 -/
theorem cone_source_exact (m : ℤ) :
    Function.Exact (coneConnecting φ m).hom
      (HomologicalComplex.homologyMap φ (m+1)).hom := by
  have h := (HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) 0).homologySequence_exact₁
    (mappingCone.triangleh φ) (HomotopyCategory.mappingCone_triangleh_distinguished φ) m (m+1) rfl
  have ht := transportShortComplex_exact _
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) m).app (mappingCone φ))
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) (m+1)).app F)
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{w} ℚ) (ComplexShape.up ℤ) (m+1)).app G) h
  change Function.Exact (coneSourceSequence φ m).f.hom (coneSourceSequence φ m).g.hom at ht
  rw [coneSourceSequence_f, coneSourceSequence_g] at ht
  exact ht

/-- HomotopyCategoryのhomology同定の逆射は全chain mapと可換である。 -/
theorem homologyFactors_inv_natural {K L : CochainComplex (ModuleCat.{w} ℚ) ℤ}
    (f : K ⟶ L) (m : ℤ) :
    HomologicalComplex.homologyMap f m ≫
        (HomotopyCategory.homologyFunctorFactors _ _ m).inv.app L =
      (HomotopyCategory.homologyFunctorFactors _ _ m).inv.app K ≫
        ((HomotopyCategory.quotient _ _ ⋙ HomotopyCategory.homologyFunctor _ _ m).map f) :=
  (HomotopyCategory.homologyFunctorFactors _ _ m).inv.naturality f

/-- HomotopyCategoryのhomology同定の順射は全chain mapと可換である。 -/
theorem homologyFactors_hom_natural {K L : CochainComplex (ModuleCat.{w} ℚ) ℤ}
    (f : K ⟶ L) (m : ℤ) :
    ((HomotopyCategory.quotient _ _ ⋙ HomotopyCategory.homologyFunctor _ _ m).map f) ≫
        (HomotopyCategory.homologyFunctorFactors _ _ m).hom.app L =
      (HomotopyCategory.homologyFunctorFactors _ _ m).hom.app K ≫
        HomologicalComplex.homologyMap f m :=
  (HomotopyCategory.homologyFunctorFactors _ _ m).hom.naturality f

/-- 標準長完全列の連結射は任意の比較可換正方形に対して自然である。 -/
theorem coneConnecting_natural {F' G' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
    (φ' : F' ⟶ G') (a : F ⟶ F') (b : G ⟶ G') (comm : φ ≫ b = a ≫ φ') (m : ℤ) :
    HomologicalComplex.homologyMap (mappingCone.map φ φ' a b comm) m ≫ coneConnecting φ' m =
      coneConnecting φ m ≫ HomologicalComplex.homologyMap a (m+1) := by
  let tmap := (HomotopyCategory.quotient (ModuleCat.{w} ℚ) (ComplexShape.up ℤ)).mapTriangle.map
    (mappingCone.triangleMap φ φ' a b comm)
  have hd := (HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ)
    (ComplexShape.up ℤ) 0).homologySequenceδ_naturality
      (mappingCone.triangleh φ) (mappingCone.triangleh φ') tmap m (m+1) rfl
  change ((HomotopyCategory.quotient _ _ ⋙ HomotopyCategory.homologyFunctor _ _ m).map
      (mappingCone.map φ φ' a b comm)) ≫ _ = _ ≫
      ((HomotopyCategory.quotient _ _ ⋙ HomotopyCategory.homologyFunctor _ _ (m+1)).map a) at hd
  dsimp only [coneConnecting]
  rw [← Category.assoc, homologyFactors_inv_natural]
  simp only [Category.assoc]
  simp only [Functor.comp_map] at hd ⊢
  rw [reassoc_of% hd]
  simpa only [Functor.comp_map] using
    congrArg (fun t => (HomotopyCategory.homologyFunctorFactors _ _ m).inv.app
      (mappingCone φ) ≫ (HomotopyCategory.homologyFunctor (ModuleCat.{w} ℚ)
      (ComplexShape.up ℤ) 0).homologySequenceδ (mappingCone.triangleh φ) m (m+1) rfl ≫ t)
      (homologyFactors_hom_natural a (m+1))

end AAT.AG.AtlasDefectComposition
#print axioms AAT.AG.AtlasDefectComposition.transportShortComplex
#print axioms AAT.AG.AtlasDefectComposition.transportShortComplexIso
#print axioms AAT.AG.AtlasDefectComposition.transportShortComplex_exact
#print axioms AAT.AG.AtlasDefectComposition.coneConnecting
#print axioms AAT.AG.AtlasDefectComposition.coneConnecting_shortExact
#print axioms AAT.AG.AtlasDefectComposition.coneTargetSequence
#print axioms AAT.AG.AtlasDefectComposition.coneTargetSequence_f
#print axioms AAT.AG.AtlasDefectComposition.coneTargetSequence_g
#print axioms AAT.AG.AtlasDefectComposition.cone_target_exact
#print axioms AAT.AG.AtlasDefectComposition.coneMiddleSequence
#print axioms AAT.AG.AtlasDefectComposition.coneMiddleSequence_f
#print axioms AAT.AG.AtlasDefectComposition.coneMiddleSequence_g
#print axioms AAT.AG.AtlasDefectComposition.cone_middle_exact
#print axioms AAT.AG.AtlasDefectComposition.coneSourceSequence
#print axioms AAT.AG.AtlasDefectComposition.coneSourceSequence_f
#print axioms AAT.AG.AtlasDefectComposition.coneSourceSequence_g
#print axioms AAT.AG.AtlasDefectComposition.cone_source_exact
#print axioms AAT.AG.AtlasDefectComposition.homologyFactors_inv_natural
#print axioms AAT.AG.AtlasDefectComposition.homologyFactors_hom_natural
#print axioms AAT.AG.AtlasDefectComposition.coneConnecting_natural
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
