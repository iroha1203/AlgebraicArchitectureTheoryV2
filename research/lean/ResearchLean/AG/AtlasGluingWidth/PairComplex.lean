import ResearchLean.AG.AtlasGluingWidth.StandardShortExact
import Formal.Util.AssertStandardAxioms
/-! # 二領域積の標準零延長の座標

Implementation notes: 三項の積と次数外の零対象を同じ標準複体の積座標へ移す。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth
namespace PairComplex
open TwoPhase AtlasDefectComposition
universe u
variable (C D : ThreeCochainComplex.{0,u} ℚ)
/-- 二領域積から第一領域への実cochain制限。 -/
def fst : ThreeCochainComplex.Hom (pairComplex C D) C where
  f0 := LinearMap.fst ℚ _ _
  f1 := LinearMap.fst ℚ _ _
  f2 := LinearMap.fst ℚ _ _
  comm0 _ := rfl
  comm1 _ := rfl
/-- 二領域積から第二領域への実cochain制限。 -/
def snd : ThreeCochainComplex.Hom (pairComplex C D) D where
  f0 := LinearMap.snd ℚ _ _
  f1 := LinearMap.snd ℚ _ _
  f2 := LinearMap.snd ℚ _ _
  comm0 _ := rfl
  comm1 _ := rfl
/-- 第1制限の次数0成分は同じ積の成分評価。 -/
@[simp] theorem fst_f0 (x : C.C0 × D.C0) : (fst C D).f0 x = x.1 := rfl
/-- 第1制限の次数1成分は同じ積の成分評価。 -/
@[simp] theorem fst_f1 (x : C.C1 × D.C1) : (fst C D).f1 x = x.1 := rfl
/-- 第1制限の次数2成分は同じ積の成分評価。 -/
@[simp] theorem fst_f2 (x : C.C2 × D.C2) : (fst C D).f2 x = x.1 := rfl
/-- 第2制限の次数0成分は同じ積の成分評価。 -/
@[simp] theorem snd_f0 (x : C.C0 × D.C0) : (snd C D).f0 x = x.2 := rfl
/-- 第2制限の次数1成分は同じ積の成分評価。 -/
@[simp] theorem snd_f1 (x : C.C1 × D.C1) : (snd C D).f1 x = x.2 := rfl
/-- 第2制限の次数2成分は同じ積の成分評価。 -/
@[simp] theorem snd_f2 (x : C.C2 × D.C2) : (snd C D).f2 x = x.2 := rfl

/-- 零延長の積座標。次数外では両辺が標準零対象である。 -/
def degreeEquiv (m : ℤ) : (zeroExtension (pairComplex C D)).X m ≃ₗ[ℚ]
    ((zeroExtension C).X m × (zeroExtension D).X m) := by
  by_cases h0 : m = 0
  · subst m; exact LinearEquiv.refl ℚ _
  · by_cases h1 : m = 1
    · subst m; exact LinearEquiv.refl ℚ _
    · by_cases h2 : m = 2
      · subst m; exact LinearEquiv.refl ℚ _
      · letI : Subsingleton ((zeroExtension C).X m) :=
          ModuleCat.subsingleton_of_isZero (by
            simpa only [zeroExtension_X] using degreeObject_isZero C m h0 h1 h2)
        letI : Subsingleton ((zeroExtension D).X m) :=
          ModuleCat.subsingleton_of_isZero (by
            simpa only [zeroExtension_X] using degreeObject_isZero D m h0 h1 h2)
        letI : Subsingleton ((zeroExtension (pairComplex C D)).X m) :=
          ModuleCat.subsingleton_of_isZero (by
            simpa only [zeroExtension_X] using degreeObject_isZero (pairComplex C D) m h0 h1 h2)
        exact LinearEquiv.ofSubsingleton _ _
/-- 第一制限の全整数次数評価は同じ積座標の第一成分。 -/
theorem degreeEquiv_fst (m : ℤ) (x : (zeroExtension (pairComplex C D)).X m) :
    (zeroExtensionMap (fst C D)).f m x = (degreeEquiv C D m x).1 := by
  by_cases h0 : m = 0
  · subst m; rfl
  · by_cases h1 : m = 1
    · subst m; simp only [degreeEquiv, dif_neg (by norm_num : (1:ℤ) ≠ 0)]; rfl
    · by_cases h2 : m = 2
      · subst m; simp only [degreeEquiv, dif_neg (by norm_num : (2:ℤ) ≠ 0), dif_neg (by norm_num : (2:ℤ) ≠ 1)]; rfl
      · letI : Subsingleton ((zeroExtension C).X m) :=
          ModuleCat.subsingleton_of_isZero (by
            simpa only [zeroExtension_X] using degreeObject_isZero C m h0 h1 h2)
        exact Subsingleton.elim _ _
/-- 第二制限の全整数次数評価は同じ積座標の第二成分。 -/
theorem degreeEquiv_snd (m : ℤ) (x : (zeroExtension (pairComplex C D)).X m) :
    (zeroExtensionMap (snd C D)).f m x = (degreeEquiv C D m x).2 := by
  by_cases h0 : m = 0
  · subst m; rfl
  · by_cases h1 : m = 1
    · subst m; simp only [degreeEquiv, dif_neg (by norm_num : (1:ℤ) ≠ 0)]; rfl
    · by_cases h2 : m = 2
      · subst m; simp only [degreeEquiv, dif_neg (by norm_num : (2:ℤ) ≠ 0), dif_neg (by norm_num : (2:ℤ) ≠ 1)]; rfl
      · letI : Subsingleton ((zeroExtension D).X m) :=
          ModuleCat.subsingleton_of_isZero (by
            simpa only [zeroExtension_X] using degreeObject_isZero D m h0 h1 h2)
        exact Subsingleton.elim _ _
variable {C D} {E F : ThreeCochainComplex.{0,u} ℚ}
/-- 二領域比較の第一制限正方形は全cochain射の等号。 -/
theorem map_fst (f : ThreeCochainComplex.Hom C E) (g : ThreeCochainComplex.Hom D F) :
    zeroExtensionMap (StandardRow.pairHom f g) ≫ zeroExtensionMap (fst E F) =
      zeroExtensionMap (fst C D) ≫ zeroExtensionMap f := by
  rw [← zeroExtensionMap_comp, ← zeroExtensionMap_comp]
  apply congrArg zeroExtensionMap
  apply cochain_ext
  · ext x; simp only [cochainComp_f0, StandardRow.pairHom_f0, fst_f0]
  · ext x; simp only [cochainComp_f1, StandardRow.pairHom_f1, fst_f1]
  · ext x; simp only [cochainComp_f2, StandardRow.pairHom_f2, fst_f2]
/-- 二領域比較の第二制限正方形は全cochain射の等号。 -/
theorem map_snd (f : ThreeCochainComplex.Hom C E) (g : ThreeCochainComplex.Hom D F) :
    zeroExtensionMap (StandardRow.pairHom f g) ≫ zeroExtensionMap (snd E F) =
      zeroExtensionMap (snd C D) ≫ zeroExtensionMap g := by
  rw [← zeroExtensionMap_comp, ← zeroExtensionMap_comp]
  apply congrArg zeroExtensionMap
  apply cochain_ext
  · ext x; simp only [cochainComp_f0, StandardRow.pairHom_f0, snd_f0]
  · ext x; simp only [cochainComp_f1, StandardRow.pairHom_f1, snd_f1]
  · ext x; simp only [cochainComp_f2, StandardRow.pairHom_f2, snd_f2]
end PairComplex
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
