import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import ResearchLean.AG.AtlasDefectComposition.ZeroExtension
import Formal.Util.AssertStandardAxioms
/-! # 三項複体族と標準有限直和の接続

Implementation notes: 三つの実次数を成分ごとの族とし、零延長の次数外だけは零加群間の同型で同定する。微分と実比較の全次数可換式を構成してから同型へ渡す。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
namespace ThreeComplexFamily
open TwoPhase
universe v w
variable {J : Type v} [Fintype J]
variable (C D : J → ThreeCochainComplex.{0,max v w} ℚ)
/-- 有限族の各三項空間と実微分を成分ごとに保持する三項複体。 -/
def complex : ThreeCochainComplex.{0,max v w} ℚ where
  C0 := (j : J) → (C j).C0
  C1 := (j : J) → (C j).C1
  C2 := (j : J) → (C j).C2
  d0 := LinearMap.pi fun j => (C j).d0.comp (LinearMap.proj j)
  d1 := LinearMap.pi fun j => (C j).d1.comp (LinearMap.proj j)
  d1_comp_d0 x := by funext j;exact (C j).d1_comp_d0 (x j)
/-- 次数0微分の実成分式。 -/
@[simp] theorem d0_apply (x : (complex C).C0) (j : J) :
    (complex C).d0 x j = (C j).d0 (x j) := rfl
/-- 次数1微分の実成分式。 -/
@[simp] theorem d1_apply (x : (complex C).C1) (j : J) :
    (complex C).d1 x j = (C j).d1 (x j) := rfl
/-- 族の各実三項Homを成分ごとに作用させる。 -/
def map (f : ∀ j, ThreeCochainComplex.Hom (C j) (D j)) :
    ThreeCochainComplex.Hom (complex C) (complex D) where
  f0 := LinearMap.pi fun j => (f j).f0.comp (LinearMap.proj j)
  f1 := LinearMap.pi fun j => (f j).f1.comp (LinearMap.proj j)
  f2 := LinearMap.pi fun j => (f j).f2.comp (LinearMap.proj j)
  comm0 x := by funext j;exact (f j).comm0 (x j)
  comm1 x := by funext j;exact (f j).comm1 (x j)
/-- 族Hom次数0の元を成分で評価する。 -/
@[simp] theorem map0_apply (f : ∀ j, ThreeCochainComplex.Hom (C j) (D j))
    (x : (complex C).C0) (j : J) : (map C D f).f0 x j = (f j).f0 (x j) := rfl
/-- 族Hom次数1の元を成分で評価する。 -/
@[simp] theorem map1_apply (f : ∀ j, ThreeCochainComplex.Hom (C j) (D j))
    (x : (complex C).C1) (j : J) : (map C D f).f1 x j = (f j).f1 (x j) := rfl
/-- 族Hom次数2の元を成分で評価する。 -/
@[simp] theorem map2_apply (f : ∀ j, ThreeCochainComplex.Hom (C j) (D j))
    (x : (complex C).C2) (j : J) : (map C D f).f2 x j = (f j).f2 (x j) := rfl
/-- 零延長と全次数の有限族を交換する元の同定。 -/
def degreeEquiv (m : ℤ) : (zeroExtension (complex C)).X m ≃ₗ[ℚ]
    (FiniteComplexFamily.complex (fun j => zeroExtension (C j))).X m := by
  by_cases h₀ : m=0
  · subst m;exact LinearEquiv.refl ℚ _
  by_cases h₁ : m=1
  · subst m;exact LinearEquiv.refl ℚ _
  by_cases h₂ : m=2
  · subst m;exact LinearEquiv.refl ℚ _
  letI : Subsingleton ((zeroExtension (complex C)).X m) :=
    ModuleCat.subsingleton_of_isZero (degreeObject_isZero _ m h₀ h₁ h₂)
  letI (j : J) : Subsingleton ((zeroExtension (C j)).X m) :=
    ModuleCat.subsingleton_of_isZero (degreeObject_isZero _ m h₀ h₁ h₂)
  exact LinearEquiv.ofSubsingleton _ _
/-- 同定は次数0の全成分値を保持する。 -/
@[simp] theorem degreeEquiv0_apply (x : (complex C).C0) (j : J) :
    degreeEquiv C 0 x j = x j := rfl
/-- 同定は次数1の全成分値を保持する。 -/
@[simp] theorem degreeEquiv1_apply (x : (complex C).C1) (j : J) :
    degreeEquiv C 1 x j = x j := rfl
/-- 同定は次数2の全成分値を保持する。 -/
@[simp] theorem degreeEquiv2_apply (x : (complex C).C2) (j : J) :
    degreeEquiv C 2 x j = x j := rfl
/-- 零延長の族同定は隣接する実微分と可換である。 -/
theorem degreeEquiv_d (m : ℤ) (x : (zeroExtension (complex C)).X m) :
    degreeEquiv C (m+1) ((zeroExtension (complex C)).d m (m+1) x) =
      (FiniteComplexFamily.complex (fun j => zeroExtension (C j))).d m (m+1)
        (degreeEquiv C m x) := by
  by_cases h₀ : m=0
  · subst m
    change degreeEquiv C 1 ((zeroExtension (complex C)).d 0 1 x) =
      (FiniteComplexFamily.complex (fun j => zeroExtension (C j))).d 0 1 (degreeEquiv C 0 x)
    funext j
    simpa only [degreeEquiv0_apply,degreeEquiv1_apply,zeroExtension_d0_apply,d0_apply] using
      (FiniteComplexFamily.d_apply (fun j => zeroExtension (C j)) 0 (degreeEquiv C 0 x) j).symm
  by_cases h₁ : m=1
  · subst m
    change degreeEquiv C 2 ((zeroExtension (complex C)).d 1 2 x) =
      (FiniteComplexFamily.complex (fun j => zeroExtension (C j))).d 1 2 (degreeEquiv C 1 x)
    funext j
    simpa only [degreeEquiv1_apply,degreeEquiv2_apply,zeroExtension_d1_apply,d1_apply] using
      (FiniteComplexFamily.d_apply (fun j => zeroExtension (C j)) 1 (degreeEquiv C 1 x) j).symm
  by_cases h₂ : m=2
  · subst m
    letI (j : J) : Subsingleton ((zeroExtension (C j)).X (2+1)) :=
      by
        change Subsingleton (degreeObject (C j) 3)
        exact ModuleCat.subsingleton_of_isZero (degreeObject_isZero (C j) 3 (by decide) (by decide) (by decide))
    exact Subsingleton.elim _ _
  letI : Subsingleton ((zeroExtension (complex C)).X m) :=
    ModuleCat.subsingleton_of_isZero (degreeObject_isZero _ m h₀ h₁ h₂)
  rw [show x=0 from Subsingleton.elim _ _]
  simp only [map_zero]
/-- 三項族の零延長と全次数有限族の標準複体は同型である。 -/
def zeroExtensionIso : zeroExtension (complex C) ≅
    FiniteComplexFamily.complex (fun j => zeroExtension (C j)) :=
  HomologicalComplex.Hom.isoOfComponents (fun m => (degreeEquiv C m).toModuleIso) (by
    intro m n h
    change m+1=n at h
    subst n
    ext x
    exact (degreeEquiv_d C m x).symm)
/-- 零延長族の同型の次数成分は構成した元の同定そのものである。 -/
@[simp] theorem zeroExtensionIso_apply (m : ℤ) (x : (zeroExtension (complex C)).X m) :
    (zeroExtensionIso C).hom.f m x = degreeEquiv C m x := rfl
/-- 全次数で、零延長族の同定は成分ごとの実Homと可換である。 -/
theorem degreeEquiv_natural (f : ∀ j, ThreeCochainComplex.Hom (C j) (D j))
    (m : ℤ) (x : (zeroExtension (complex C)).X m) :
    degreeEquiv D m ((zeroExtensionMap (map C D f)).f m x) =
      (FiniteComplexFamily.map (fun j => zeroExtension (C j))
        (fun j => zeroExtension (D j)) (fun j => zeroExtensionMap (f j))).f m
        (degreeEquiv C m x) := by
  by_cases h₀ : m=0
  · subst m
    funext j
    simp only [FiniteComplexFamily.map_apply,degreeEquiv0_apply,zeroExtensionMap_f0_apply,map0_apply]
  by_cases h₁ : m=1
  · subst m
    funext j
    simp only [FiniteComplexFamily.map_apply,degreeEquiv1_apply,zeroExtensionMap_f1_apply,map1_apply]
  by_cases h₂ : m=2
  · subst m
    funext j
    simp only [FiniteComplexFamily.map_apply,degreeEquiv2_apply,zeroExtensionMap_f2_apply,map2_apply]
  letI : Subsingleton ((zeroExtension (complex C)).X m) :=
    ModuleCat.subsingleton_of_isZero (degreeObject_isZero _ m h₀ h₁ h₂)
  rw [show x=0 from Subsingleton.elim _ _]
  simp only [map_zero]
/-- 標準複体同型の全射成分も独立生成Homと可換である。 -/
theorem zeroExtensionIso_natural (f : ∀ j, ThreeCochainComplex.Hom (C j) (D j)) :
    zeroExtensionMap (map C D f) ≫ (zeroExtensionIso D).hom =
      (zeroExtensionIso C).hom ≫
        FiniteComplexFamily.map (fun j => zeroExtension (C j))
          (fun j => zeroExtension (D j)) (fun j => zeroExtensionMap (f j)) := by
  ext m x
  exact degreeEquiv_natural C D f m x
end ThreeComplexFamily
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
