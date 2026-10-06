import ResearchLean.AG.FaceRelationSubdivision.SubsetComparison
import ResearchLean.AG.AtlasDefectComposition.SubsetComposition
import Formal.Util.AssertStandardAxioms

/-!
# 全支持subsetでの直接生成と合成

G-134 A・D。全subsetの逆像と共通Law fiberについて同じ生成写像を合成へ接続する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u w₀ w₁

variable {Source : Type u}
variable {q₀ q₁ q₂ : Reading Source}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}
variable (M₀₁ : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : IncidenceSupportedComparison q₁ q₂ h₁₂ N₁ N₂)
variable (A₀ : Set q₀.Target) (A₁ : Set q₁.Target) (A₂ : Set q₂.Target)
variable (hs₀₁ : ∀ t, t ∈ A₁ → comparisonFactor q₀ q₁ h₀₁ t ∈ A₀)
variable (hs₁₂ : ∀ t, t ∈ A₂ → comparisonFactor q₁ q₂ h₁₂ t ∈ A₁)

include hs₀₁ hs₁₂ in
/-- subset適合の合成API。構成の結論を追加の仮定として受け取らない。 -/
theorem subsetMapsTo_comp : ∀ t, t ∈ A₂ →
    comparisonFactor q₀ q₂ (Reading.coarserThan_trans h₀₁ h₁₂) t ∈ A₀ := by
  intro t ht
  rw [comparisonFactor_comp h₀₁ h₁₂]
  exact hs₀₁ _ (hs₁₂ t ht)

/-- A の選択chart射の合成。同じ名付きセルへのsubset同定を保持する。 -/
theorem targetSubsetChartMap_comp (c : N₂.ChartInTargetSubset A₂) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetChartMap A₀ A₂
      (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c =
      M₀₁.targetSubsetChartMap A₀ A₁ hs₀₁
        (M₁₂.targetSubsetChartMap A₁ A₂ hs₁₂ c) := by
  apply Subtype.ext
  rfl

/-- A の選択edge射の部分合成。両退化経路を含む。 -/
theorem targetSubsetEdgeMapOption_comp (c : N₂.EdgeInTargetSubset A₂) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetEdgeMapOption A₀ A₂
      (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c =
      (M₁₂.targetSubsetEdgeMapOption A₁ A₂ hs₁₂ c).bind
        (M₀₁.targetSubsetEdgeMapOption A₀ A₁ hs₀₁) := by
  cases hb : M₁₂.edgeMap c.1 with
  | none =>
    have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.1 = none := by
      simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_none]
    rw [M₁₂.targetSubsetEdgeMapOption_eq_none A₁ A₂ hs₁₂ c hb,
      (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetEdgeMapOption_eq_none A₀ A₂
        (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c hc]
    rfl
  | some b =>
    let cb := M₁₂.targetSubsetEdgeMap A₁ A₂ hs₁₂ c b hb
    have hcb : cb.1 = b := rfl
    rw [M₁₂.targetSubsetEdgeMapOption_eq_some A₁ A₂ hs₁₂ c b hb, Option.bind_some]
    cases ha : M₀₁.edgeMap b with
    | none =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.1 = none := by
        simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetEdgeMapOption_eq_none A₀ A₂
          (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c hc,
        M₀₁.targetSubsetEdgeMapOption_eq_none A₀ A₁ hs₀₁ cb (by rw [hcb]; exact ha)]
    | some a =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.1 = some a := by
        simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetEdgeMapOption_eq_some A₀ A₂
          (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c a hc,
        M₀₁.targetSubsetEdgeMapOption_eq_some A₀ A₁ hs₀₁ cb a (by rw [hcb]; exact ha)]
      rfl

/-- A の選択face射の部分合成。両退化経路を含む。 -/
theorem targetSubsetFaceMapOption_comp (c : N₂.FaceInTargetSubset A₂) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetFaceMapOption A₀ A₂
      (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c =
      (M₁₂.targetSubsetFaceMapOption A₁ A₂ hs₁₂ c).bind
        (M₀₁.targetSubsetFaceMapOption A₀ A₁ hs₀₁) := by
  cases hb : M₁₂.faceMap c.1 with
  | none =>
    have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.1 = none := by
      simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_none]
    rw [M₁₂.targetSubsetFaceMapOption_eq_none A₁ A₂ hs₁₂ c hb,
      (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetFaceMapOption_eq_none A₀ A₂
        (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c hc]
    rfl
  | some b =>
    let cb := M₁₂.targetSubsetFaceMap A₁ A₂ hs₁₂ c b hb
    have hcb : cb.1 = b := rfl
    rw [M₁₂.targetSubsetFaceMapOption_eq_some A₁ A₂ hs₁₂ c b hb, Option.bind_some]
    cases ha : M₀₁.faceMap b with
    | none =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.1 = none := by
        simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetFaceMapOption_eq_none A₀ A₂
          (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c hc,
        M₀₁.targetSubsetFaceMapOption_eq_none A₀ A₁ hs₀₁ cb (by rw [hcb]; exact ha)]
    | some a =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.1 = some a := by
        simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetFaceMapOption_eq_some A₀ A₂
          (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) c a hc,
        M₀₁.targetSubsetFaceMapOption_eq_some A₀ A₁ hs₀₁ cb a (by rw [hcb]; exact ha)]
      rfl

/-- A のsubset次数0の直接生成pullbackと合成の一致。 -/
theorem targetSubsetPullback0_comp (x : N₀.ChartInTargetSubset A₀ → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetPullback0 A₀ A₂
      (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) x =
      M₁₂.targetSubsetPullback0 A₁ A₂ hs₁₂ (M₀₁.targetSubsetPullback0 A₀ A₁ hs₀₁ x) := by
  funext c
  simp only [IncidenceSupportedComparison.targetSubsetPullback0_apply,
    targetSubsetChartMap_comp M₀₁ M₁₂ A₀ A₁ A₂ hs₀₁ hs₁₂]

/-- A のsubset次数1の直接生成pullbackと合成の一致。 -/
theorem targetSubsetPullback1_comp (x : N₀.EdgeInTargetSubset A₀ → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetPullback1 A₀ A₂
      (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) x =
      M₁₂.targetSubsetPullback1 A₁ A₂ hs₁₂ (M₀₁.targetSubsetPullback1 A₀ A₁ hs₀₁ x) := by
  funext c
  rw [IncidenceSupportedComparison.targetSubsetPullback1_apply,
    IncidenceSupportedComparison.targetSubsetPullback1_apply,
    targetSubsetEdgeMapOption_comp M₀₁ M₁₂ A₀ A₁ A₂ hs₀₁ hs₁₂]
  cases M₁₂.targetSubsetEdgeMapOption A₁ A₂ hs₁₂ c with
  | none => rfl
  | some b => exact (M₀₁.targetSubsetPullback1_apply A₀ A₁ hs₀₁ x b).symm

/-- A のsubset次数2の直接生成pullbackと合成の一致。 -/
theorem targetSubsetPullback2_comp (x : N₀.FaceInTargetSubset A₀ → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetPullback2 A₀ A₂
      (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) x =
      M₁₂.targetSubsetPullback2 A₁ A₂ hs₁₂ (M₀₁.targetSubsetPullback2 A₀ A₁ hs₀₁ x) := by
  funext c
  rw [IncidenceSupportedComparison.targetSubsetPullback2_apply,
    IncidenceSupportedComparison.targetSubsetPullback2_apply,
    targetSubsetFaceMapOption_comp M₀₁ M₁₂ A₀ A₁ A₂ hs₀₁ hs₁₂]
  cases M₁₂.targetSubsetFaceMapOption A₁ A₂ hs₁₂ c with
  | none => rfl
  | some b => exact (M₀₁.targetSubsetPullback2_apply A₀ A₁ hs₀₁ x b).symm

/-- A のsubset全次数での直接生成Homの合成。 -/
theorem targetSubsetComparisonHom_comp :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetComparisonHom A₀ A₂
      (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂) =
      cochainComp (M₀₁.targetSubsetComparisonHom A₀ A₁ hs₀₁)
        (M₁₂.targetSubsetComparisonHom A₁ A₂ hs₁₂) := by
  apply cochain_ext
  · exact LinearMap.ext (targetSubsetPullback0_comp M₀₁ M₁₂ A₀ A₁ A₂ hs₀₁ hs₁₂)
  · exact LinearMap.ext (targetSubsetPullback1_comp M₀₁ M₁₂ A₀ A₁ A₂ hs₀₁ hs₁₂)
  · exact LinearMap.ext (targetSubsetPullback2_comp M₀₁ M₁₂ A₀ A₁ A₂ hs₀₁ hs₁₂)

set_option maxHeartbeats 800000 in
/-- A のsubset比較と既存H¹商の合成。 -/
theorem targetSubsetComparisonHom_h1Map_comp :
    ((IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetComparisonHom A₀ A₂
      (subsetMapsTo_comp A₀ A₁ A₂ hs₀₁ hs₁₂)).h1Map =
      (M₁₂.targetSubsetComparisonHom A₁ A₂ hs₁₂).h1Map.comp
        (M₀₁.targetSubsetComparisonHom A₀ A₁ hs₀₁).h1Map := by
  have h := congrArg (fun f : ThreeCochainComplex.Hom
    (N₀.targetSubsetComplex A₀) (N₂.targetSubsetComplex A₂) => f.h1Map)
    (targetSubsetComparisonHom_comp M₀₁ M₁₂ A₀ A₁ A₂ hs₀₁ hs₁₂)
  exact h.trans (cochainComp_h1Map _ _)

/-- A のsubset同定で用いる標準等号transport。target複体全体を移送する。 -/
def subsetTransportHom {C : ThreeCochainComplex.{0,w₀} ℚ} {D E : ThreeCochainComplex.{0,w₁} ℚ} (h : D = E)
    (f : ThreeCochainComplex.Hom C D) : ThreeCochainComplex.Hom C E := h ▸ f

/-- 等号transportのrefl評価API。 -/
@[simp] theorem transportHom_rfl {C : ThreeCochainComplex.{0,w₀} ℚ} {D : ThreeCochainComplex.{0,w₁} ℚ}
    (f : ThreeCochainComplex.Hom C D) : subsetTransportHom rfl f = f := rfl

/-- 選択subsetの等号で、既存生成Homを全次数について移送する。 -/
theorem targetSubsetComparisonHom_transport
    {q r : Reading Source} {hr : q.CoarserThan r}
    {N : TargetSupportedNerve q} {N' : TargetSupportedNerve r}
    (M : IncidenceSupportedComparison q r hr N N')
    (A : Set q.Target) (B B' : Set r.Target) (hB : B = B')
    (hs : ∀ t, t ∈ B → comparisonFactor q r hr t ∈ A)
    (hs' : ∀ t, t ∈ B' → comparisonFactor q r hr t ∈ A) :
    subsetTransportHom (congrArg N'.targetSubsetComplex hB)
      (M.targetSubsetComparisonHom A B hs) = M.targetSubsetComparisonHom A B' hs' := by
  cases hB
  rfl

/-- A のcanonical逆像族。直接生成したaSubnerve Homを逆像合成等号で移送して比較する。 -/
theorem aSubnerveComparisonHom_comp (A : Set q₀.Target) :
    subsetTransportHom (congrArg N₂.targetSubsetComplex
      (comparisonFactor_preimage_comp h₀₁ h₁₂ A))
      ((IncidenceSupportedComparison.comp M₀₁ M₁₂).aSubnerveComparisonHom A) =
      cochainComp (M₀₁.aSubnerveComparisonHom A)
        (M₁₂.aSubnerveComparisonHom (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A)) := by
  let A₁ := comparisonFactor q₀ q₁ h₀₁ ⁻¹' A
  let A₂ := comparisonFactor q₁ q₂ h₁₂ ⁻¹' A₁
  let hs := subsetMapsTo_comp A A₁ A₂ (fun _ h => h) (fun _ h => h)
  calc
    _ = (IncidenceSupportedComparison.comp M₀₁ M₁₂).targetSubsetComparisonHom A A₂ hs :=
      targetSubsetComparisonHom_transport (IncidenceSupportedComparison.comp M₀₁ M₁₂) A _ _
        (comparisonFactor_preimage_comp h₀₁ h₁₂ A) (fun _ h => h) hs
    _ = _ := targetSubsetComparisonHom_comp M₀₁ M₁₂ A A₁ A₂ (fun _ h => h) (fun _ h => h)

set_option maxHeartbeats 800000 in
/-- A のcanonical逆像族でのH¹商の合成。全subsetと全類を量化する。 -/
theorem aSubnerveComparisonHom_h1Map_comp (A : Set q₀.Target) :
    (subsetTransportHom (congrArg N₂.targetSubsetComplex
      (comparisonFactor_preimage_comp h₀₁ h₁₂ A))
      ((IncidenceSupportedComparison.comp M₀₁ M₁₂).aSubnerveComparisonHom A)).h1Map =
      (M₁₂.aSubnerveComparisonHom (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A)).h1Map.comp
        (M₀₁.aSubnerveComparisonHom A).h1Map := by
  have h := congrArg (fun f : ThreeCochainComplex.Hom
    (N₀.targetSubsetComplex A) (N₂.targetSubsetComplex
      (comparisonFactor q₁ q₂ h₁₂ ⁻¹' (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A))) => f.h1Map)
    (aSubnerveComparisonHom_comp M₀₁ M₁₂ A)
  exact h.trans (cochainComp_h1Map _ _)


end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
