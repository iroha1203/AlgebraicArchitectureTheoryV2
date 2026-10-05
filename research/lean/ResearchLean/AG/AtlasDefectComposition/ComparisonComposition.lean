import ResearchLean.AG.ResolutionInvariance.SupportedNerveMorphism
import Formal.Util.AssertStandardAxioms

/-!
# 原始セル比較の合成

G-133 A の入力幾何から、chart の合成と edge・face の `Option.bind` によって
直接比較を構成する。全 incidence 条件と K1 支持の適合は入力二射から証明する。

## Implementation notes

比較因子は既存 `comparisonFactor` を使い、その合成等式は Source 上の可換性と
全射性から得る。cochain 写像を入力に加えず、元の hereditary な部分セル射を使う。
-/

noncomputable section

namespace AAT.AG.AtlasDefectComposition

open CanonicalResolution ResolutionInvariance

universe u

variable {Source : Type u}
variable {q₀ q₁ q₂ : Reading Source}

/-- A の因子合成。入力は T0 の二つの reading 順序だけである。 -/
theorem comparisonFactor_comp (h₀₁ : q₀.CoarserThan q₁)
    (h₁₂ : q₁.CoarserThan q₂) :
    comparisonFactor q₀ q₂ (Reading.coarserThan_trans h₀₁ h₁₂) =
      comparisonFactor q₀ q₁ h₀₁ ∘ comparisonFactor q₁ q₂ h₁₂ := by
  symm
  apply comparisonFactor_unique
  intro s
  simp only [Function.comp_apply, comparisonFactor_commutes]

/-- T0 の細 reading の adequacy は粗 reading の adequacy から放電する。 -/
theorem adequate_of_coarser (laws : FiniteLawFamily Source)
    (h₀₁ : q₀.CoarserThan q₁) (h₀ : laws.Adequate q₀) :
    laws.Adequate q₁ := by
  apply (laws.adequate_iff_kernel q₁).2
  intro x y h
  exact (laws.adequate_iff_kernel q₀).1 h₀ (h₀₁ h)

/-- A の全 subset の逆像合成。空集合も量化に含む。 -/
theorem comparisonFactor_preimage_comp (h₀₁ : q₀.CoarserThan q₁)
    (h₁₂ : q₁.CoarserThan q₂) (A : Set q₀.Target) :
    comparisonFactor q₀ q₂ (Reading.coarserThan_trans h₀₁ h₁₂) ⁻¹' A =
      comparisonFactor q₁ q₂ h₁₂ ⁻¹' (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A) := by
  rw [comparisonFactor_comp]
  rfl

/-- A の三段Law降下の一致。二段の既存降下定理を同じLawへ接続する。 -/
theorem lawDescend_comp_three (laws : FiniteLawFamily Source)
    (h₀₁ : q₀.CoarserThan q₁) (h₁₂ : q₁.CoarserThan q₂)
    (ha₀ : laws.Adequate q₀) (ha₁ : laws.Adequate q₁) (ha₂ : laws.Adequate q₂)
    (l : laws.Law) :
    lawDescend laws q₀ ha₀ l ∘ comparisonFactor q₀ q₁ h₀₁ ∘ comparisonFactor q₁ q₂ h₁₂ =
      lawDescend laws q₂ ha₂ l := by
  funext t
  simp only [Function.comp_apply,
    lawDescend_comparisonFactor laws q₀ q₁ ha₀ ha₁ h₀₁ l,
    lawDescend_comparisonFactor laws q₁ q₂ ha₁ ha₂ h₁₂ l]

variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}

/-- A の直接セル比較。Option の三経路を保持し、全 field を二射から生成する。 -/
def comparisonComp
    (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂) :
    TargetSupportedNerveMorphism q₀ q₂ (Reading.coarserThan_trans h₀₁ h₁₂) N₀ N₂ where
  chartMap := M₀₁.chartMap ∘ M₁₂.chartMap
  edgeMap := fun e => (M₁₂.edgeMap e).bind M₀₁.edgeMap
  faceMap := fun f => (M₁₂.faceMap f).bind M₀₁.faceMap
  edge_some_left := by
    intro e c h
    cases he : M₁₂.edgeMap e with
    | none => simp [he] at h
    | some b =>
      simp only [he, Option.bind_some] at h
      change M₀₁.chartMap (M₁₂.chartMap (N₂.nerve.edgeLeft e)) = _
      rw [M₁₂.edge_some_left e b he, M₀₁.edge_some_left b c h]
  edge_some_right := by
    intro e c h
    cases he : M₁₂.edgeMap e with
    | none => simp [he] at h
    | some b =>
      simp only [he, Option.bind_some] at h
      change M₀₁.chartMap (M₁₂.chartMap (N₂.nerve.edgeRight e)) = _
      rw [M₁₂.edge_some_right e b he, M₀₁.edge_some_right b c h]
  edge_none_fiber := by
    intro e h
    change M₀₁.chartMap (M₁₂.chartMap (N₂.nerve.edgeLeft e)) =
      M₀₁.chartMap (M₁₂.chartMap (N₂.nerve.edgeRight e))
    cases he : M₁₂.edgeMap e with
    | none => rw [M₁₂.edge_none_fiber e he]
    | some b =>
      simp only [he, Option.bind_some] at h
      rw [M₁₂.edge_some_left e b he, M₁₂.edge_some_right e b he]
      exact M₀₁.edge_none_fiber b h
  face_some_edge0 := by
    intro f c h
    cases hf : M₁₂.faceMap f with
    | none => simp [hf] at h
    | some b =>
      simp only [hf, Option.bind_some] at h
      rw [M₁₂.face_some_edge0 f b hf]
      exact M₀₁.face_some_edge0 b c h
  face_some_edge1 := by
    intro f c h
    cases hf : M₁₂.faceMap f with
    | none => simp [hf] at h
    | some b =>
      simp only [hf, Option.bind_some] at h
      rw [M₁₂.face_some_edge1 f b hf]
      exact M₀₁.face_some_edge1 b c h
  face_some_edge2 := by
    intro f c h
    cases hf : M₁₂.faceMap f with
    | none => simp [hf] at h
    | some b =>
      simp only [hf, Option.bind_some] at h
      rw [M₁₂.face_some_edge2 f b hf]
      exact M₀₁.face_some_edge2 b c h
  face_none_edge0 := by
    intro f h
    cases hf : M₁₂.faceMap f with
    | none => rw [M₁₂.face_none_edge0 f hf]; rfl
    | some b =>
      simp only [hf, Option.bind_some] at h
      rw [M₁₂.face_some_edge0 f b hf]
      exact M₀₁.face_none_edge0 b h
  face_none_edge1 := by
    intro f h
    cases hf : M₁₂.faceMap f with
    | none => rw [M₁₂.face_none_edge1 f hf]; rfl
    | some b =>
      simp only [hf, Option.bind_some] at h
      rw [M₁₂.face_some_edge1 f b hf]
      exact M₀₁.face_none_edge1 b h
  face_none_edge2 := by
    intro f h
    cases hf : M₁₂.faceMap f with
    | none => rw [M₁₂.face_none_edge2 f hf]; rfl
    | some b =>
      simp only [hf, Option.bind_some] at h
      rw [M₁₂.face_some_edge2 f b hf]
      exact M₀₁.face_none_edge2 b h
  chartSupport_compatible := by
    intro c t ht
    rw [comparisonFactor_comp h₀₁ h₁₂]
    exact M₀₁.chartSupport_compatible _ _ (M₁₂.chartSupport_compatible c t ht)

/-- `comparisonComp` の chart 評価 API。 -/
@[simp] theorem comparisonComp_chartMap
    (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂) (c : N₂.nerve.Chart) :
    (comparisonComp M₀₁ M₁₂).chartMap c = M₀₁.chartMap (M₁₂.chartMap c) := rfl

/-- `comparisonComp` の edge 評価 API。 -/
@[simp] theorem comparisonComp_edgeMap
    (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂) (e : N₂.nerve.EdgeComponent) :
    (comparisonComp M₀₁ M₁₂).edgeMap e = (M₁₂.edgeMap e).bind M₀₁.edgeMap := rfl

/-- `comparisonComp` の face 評価 API。 -/
@[simp] theorem comparisonComp_faceMap
    (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂) (f : N₂.nerve.FaceComponent) :
    (comparisonComp M₀₁ M₁₂).faceMap f = (M₁₂.faceMap f).bind M₀₁.faceMap := rfl

end AAT.AG.AtlasDefectComposition

#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
