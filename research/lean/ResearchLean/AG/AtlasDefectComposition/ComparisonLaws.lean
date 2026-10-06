import ResearchLean.AG.AtlasDefectComposition.GeneratedComposition
import ResearchLean.AG.UniformInvariance.UniformityInstancePairs
import Formal.Util.AssertStandardAxioms

/-!
# 原始比較の恒等と結合則

G-133 A の合成を既存の `identityMorphism` に接続する。
等号は全 chart・edge・face 成分を含み、証明 field の差は proof irrelevance で処理する。
-/

noncomputable section

namespace AAT.AG.AtlasDefectComposition

open CanonicalResolution ResolutionInvariance

universe u
variable {Source : Type u}
variable {q₀ q₁ q₂ q₃ : Reading Source}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {h₂₃ : q₂.CoarserThan q₃}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂} {N₃ : TargetSupportedNerve q₃}

/-- 原始比較の ext API。全計算成分の等号から構造全体の等号を得る。 -/
theorem comparison_ext
    {M M' : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁}
    (hc : M.chartMap = M'.chartMap) (he : M.edgeMap = M'.edgeMap)
    (hf : M.faceMap = M'.faceMap) : M = M' := by
  cases M
  cases M'
  cases hc
  cases he
  cases hf
  rfl

/-- A の左恒等則。恒等は既存の入力幾何から生成した射を再利用する。 -/
theorem comparisonComp_id_left
    (M : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁) :
    comparisonComp (TargetSupportedNerveMorphism.identityMorphism q₀ N₀) M = M := by
  apply comparison_ext
  · rfl
  · funext e
    simp only [comparisonComp_edgeMap]
    cases M.edgeMap e <;> rfl
  · funext f
    simp only [comparisonComp_faceMap]
    cases M.faceMap f <;> rfl

/-- A の右恒等則。部分辺・面も全成分で恒等になる。 -/
theorem comparisonComp_id_right
    (M : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁) :
    comparisonComp M (TargetSupportedNerveMorphism.identityMorphism q₁ N₁) = M := by
  apply comparison_ext <;> rfl

/-- A の結合則。Option の退化宣言を含む全成分で等しい。 -/
theorem comparisonComp_assoc
    (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂)
    (M₂₃ : TargetSupportedNerveMorphism q₂ q₃ h₂₃ N₂ N₃) :
    comparisonComp (comparisonComp M₀₁ M₁₂) M₂₃ =
      comparisonComp M₀₁ (comparisonComp M₁₂ M₂₃) := by
  apply comparison_ext
  · rfl
  · funext e
    simp only [comparisonComp_edgeMap, Option.bind_assoc]
  · funext f
    simp only [comparisonComp_faceMap, Option.bind_assoc]

/-- A の生成関手で用いる三項複体の恒等Hom。既存線形恒等を使う。 -/
def cochainId (C : TwoPhase.ThreeCochainComplex ℚ) : TwoPhase.ThreeCochainComplex.Hom C C where
  f0 := LinearMap.id
  f1 := LinearMap.id
  f2 := LinearMap.id
  comm0 _ := rfl
  comm1 _ := rfl

/-- 三項恒等射の次数0評価を公開する。 -/
@[simp] theorem cochainId_f0 (C : TwoPhase.ThreeCochainComplex ℚ) (x : C.C0) :
    (cochainId C).f0 x = x := rfl
/-- 三項恒等射の次数1評価を公開する。 -/
@[simp] theorem cochainId_f1 (C : TwoPhase.ThreeCochainComplex ℚ) (x : C.C1) :
    (cochainId C).f1 x = x := rfl
/-- 三項恒等射の次数2評価を公開する。 -/
@[simp] theorem cochainId_f2 (C : TwoPhase.ThreeCochainComplex ℚ) (x : C.C2) :
    (cochainId C).f2 x = x := rfl

/-- 三項複体恒等Homは既存H¹商でも恒等に作用する。 -/
theorem cochainId_h1Map (C : TwoPhase.ThreeCochainComplex ℚ) :
    (cochainId C).h1Map = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (LinearMap.range C.boundaryToCycles).mkQ_surjective x
  rw [TwoPhase.ThreeCochainComplex.Hom.h1Map_mk]
  rfl

/-- A の恒等原始比較から直接生成した全Law Homは恒等Homである。 -/
theorem identity_generatedComparisonHom [Fintype Source]
    (q : Reading Source) (N : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (ha : laws.Adequate q) :
    (TargetSupportedNerveMorphism.identityMorphism q N).generatedComparisonHom laws ha ha =
      cochainId (N.lawGeneratedComplex laws ha) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro x
    funext c
    change (TargetSupportedNerveMorphism.identityMorphism q N).generatedPullback0 laws ha ha x c = x c
    rw [TargetSupportedNerveMorphism.generatedPullback0_apply]
    rfl
  · apply LinearMap.ext
    intro x
    funext c
    change (TargetSupportedNerveMorphism.identityMorphism q N).generatedPullback1 laws ha ha x c = x c
    rw [TargetSupportedNerveMorphism.generatedPullback1_apply,
      TargetSupportedNerveMorphism.edgeCoordinateMapOption_eq_some _ laws ha ha c c.cell rfl]
    rfl
  · apply LinearMap.ext
    intro x
    funext c
    change (TargetSupportedNerveMorphism.identityMorphism q N).generatedPullback2 laws ha ha x c = x c
    rw [TargetSupportedNerveMorphism.generatedPullback2_apply,
      TargetSupportedNerveMorphism.faceCoordinateMapOption_eq_some _ laws ha ha c c.cell rfl]
    rfl

/-- A の恒等原始比較から生成した全Law H¹写像は恒等である。 -/
theorem identity_generatedComparisonH1Map [Fintype Source]
    (q : Reading Source) (N : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (ha : laws.Adequate q) :
    (TargetSupportedNerveMorphism.identityMorphism q N).generatedComparisonH1Map laws ha ha = LinearMap.id := by
  change ((TargetSupportedNerveMorphism.identityMorphism q N).generatedComparisonHom laws ha ha).h1Map = _
  rw [identity_generatedComparisonHom, cochainId_h1Map]

end AAT.AG.AtlasDefectComposition

#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
