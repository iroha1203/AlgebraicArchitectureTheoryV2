import ResearchLean.AG.AtlasDefectComposition.ComparisonComposition
import ResearchLean.AG.ResolutionInvariance.GeneratedComparisonMap
import Formal.Util.AssertStandardAxioms

/-!
# 全Lawの実生成比較と合成の一致

G-133 A の原始 `comparisonComp` に既存の生成APIを適用し、全三次数と既存H¹商で
cochain合成との一致を示す。有限SourceとadequacyはT0の入力に由来する。

## Implementation notes

直接比較の生成は既存APIに委ねる。新しい `cochainComp` は右辺だけに使い、
直接比較を定義する手段にはしない。K0座標の同定はcell・law・valueの等号を保持する。
-/

noncomputable section

namespace AAT.AG.AtlasDefectComposition

open CanonicalResolution ResolutionInvariance TwoPhase

universe u v w₀ w₁ w₂

section Cochains
variable {k : Type v} [Field k]
variable {C₀ : ThreeCochainComplex.{v,w₀} k}
variable {C₁ : ThreeCochainComplex.{v,w₁} k}
variable {C₂ : ThreeCochainComplex.{v,w₂} k}

/-- A の右辺に用いる既存三項複体Homの合成。微分との可換性を二射から証明する。 -/
def cochainComp (f : ThreeCochainComplex.Hom C₀ C₁)
    (g : ThreeCochainComplex.Hom C₁ C₂) : ThreeCochainComplex.Hom C₀ C₂ where
  f0 := g.f0.comp f.f0
  f1 := g.f1.comp f.f1
  f2 := g.f2.comp f.f2
  comm0 c := by simp only [LinearMap.comp_apply, f.comm0, g.comm0]
  comm1 c := by simp only [LinearMap.comp_apply, f.comm1, g.comm1]

/-- cochain合成の次数0評価API。 -/
@[simp] theorem cochainComp_f0 (f : ThreeCochainComplex.Hom C₀ C₁)
    (g : ThreeCochainComplex.Hom C₁ C₂) (x : C₀.C0) :
    (cochainComp f g).f0 x = g.f0 (f.f0 x) := rfl

/-- cochain合成の次数1評価API。 -/
@[simp] theorem cochainComp_f1 (f : ThreeCochainComplex.Hom C₀ C₁)
    (g : ThreeCochainComplex.Hom C₁ C₂) (x : C₀.C1) :
    (cochainComp f g).f1 x = g.f1 (f.f1 x) := rfl

/-- cochain合成の次数2評価API。 -/
@[simp] theorem cochainComp_f2 (f : ThreeCochainComplex.Hom C₀ C₁)
    (g : ThreeCochainComplex.Hom C₁ C₂) (x : C₀.C2) :
    (cochainComp f g).f2 x = g.f2 (f.f2 x) := rfl

/-- 三項複体Homの全成分ext API。 -/
theorem cochain_ext {f g : ThreeCochainComplex.Hom C₀ C₁}
    (h₀ : f.f0 = g.f0) (h₁ : f.f1 = g.f1) (h₂ : f.f2 = g.f2) : f = g := by
  cases f
  cases g
  cases h₀
  cases h₁
  cases h₂
  rfl

/-- A の既存H¹商での関手性。全類を代表cocycleへ降ろして証明する。 -/
theorem cochainComp_h1Map (f : ThreeCochainComplex.Hom C₀ C₁)
    (g : ThreeCochainComplex.Hom C₁ C₂) :
    (cochainComp f g).h1Map = g.h1Map.comp f.h1Map := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (LinearMap.range C₀.boundaryToCycles).mkQ_surjective x
  simp only [LinearMap.comp_apply, ThreeCochainComplex.Hom.h1Map_mk]
  congr 1
end Cochains

variable {Source : Type u}
variable {q₀ q₁ q₂ : Reading Source}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}
variable (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂)
variable (laws : FiniteLawFamily Source)
variable (h₀ : laws.Adequate q₀) (h₁ : laws.Adequate q₁) (h₂ : laws.Adequate q₂)

/-- A の次数0座標の合成。Lawと値の同定を保持する。 -/
theorem chartCoordinateMap_comp (c : N₂.ChartCoordinate laws h₂) :
    (comparisonComp M₀₁ M₁₂).chartCoordinateMap laws h₀ h₂ c =
      M₀₁.chartCoordinateMap laws h₀ h₁ (M₁₂.chartCoordinateMap laws h₁ h₂ c) := by
  apply CellCoordinate.ext <;> rfl

/-- A の edge 座標の部分合成。二つの退化経路とmapped経路を区別する。 -/
theorem edgeCoordinateMapOption_comp (c : N₂.EdgeCoordinate laws h₂) :
    (comparisonComp M₀₁ M₁₂).edgeCoordinateMapOption laws h₀ h₂ c =
      (M₁₂.edgeCoordinateMapOption laws h₁ h₂ c).bind
        (M₀₁.edgeCoordinateMapOption laws h₀ h₁) := by
  cases hb : M₁₂.edgeMap c.cell with
  | none =>
    have hc : (comparisonComp M₀₁ M₁₂).edgeMap c.cell = none := by
      simp only [comparisonComp_edgeMap, hb, Option.bind_none]
    rw [M₁₂.edgeCoordinateMapOption_eq_none laws h₁ h₂ c hb,
      (comparisonComp M₀₁ M₁₂).edgeCoordinateMapOption_eq_none laws h₀ h₂ c hc]
    rfl
  | some b =>
    let cb := M₁₂.edgeCoordinateMap laws h₁ h₂ c b hb
    have hcb : cb.cell = b := rfl
    rw [M₁₂.edgeCoordinateMapOption_eq_some laws h₁ h₂ c b hb, Option.bind_some]
    cases ha : M₀₁.edgeMap b with
    | none =>
      have hc : (comparisonComp M₀₁ M₁₂).edgeMap c.cell = none := by
        simp only [comparisonComp_edgeMap, hb, Option.bind_some, ha]
      rw [(comparisonComp M₀₁ M₁₂).edgeCoordinateMapOption_eq_none laws h₀ h₂ c hc,
        M₀₁.edgeCoordinateMapOption_eq_none laws h₀ h₁ cb (by rw [hcb]; exact ha)]
    | some a =>
      have hc : (comparisonComp M₀₁ M₁₂).edgeMap c.cell = some a := by
        simp only [comparisonComp_edgeMap, hb, Option.bind_some, ha]
      rw [(comparisonComp M₀₁ M₁₂).edgeCoordinateMapOption_eq_some laws h₀ h₂ c a hc,
        M₀₁.edgeCoordinateMapOption_eq_some laws h₀ h₁ cb a (by rw [hcb]; exact ha)]
      rfl

/-- A の face 座標の部分合成。二つの退化経路とmapped経路を区別する。 -/
theorem faceCoordinateMapOption_comp (c : N₂.FaceCoordinate laws h₂) :
    (comparisonComp M₀₁ M₁₂).faceCoordinateMapOption laws h₀ h₂ c =
      (M₁₂.faceCoordinateMapOption laws h₁ h₂ c).bind
        (M₀₁.faceCoordinateMapOption laws h₀ h₁) := by
  cases hb : M₁₂.faceMap c.cell with
  | none =>
    have hc : (comparisonComp M₀₁ M₁₂).faceMap c.cell = none := by
      simp only [comparisonComp_faceMap, hb, Option.bind_none]
    rw [M₁₂.faceCoordinateMapOption_eq_none laws h₁ h₂ c hb,
      (comparisonComp M₀₁ M₁₂).faceCoordinateMapOption_eq_none laws h₀ h₂ c hc]
    rfl
  | some b =>
    let cb := M₁₂.faceCoordinateMap laws h₁ h₂ c b hb
    have hcb : cb.cell = b := rfl
    rw [M₁₂.faceCoordinateMapOption_eq_some laws h₁ h₂ c b hb, Option.bind_some]
    cases ha : M₀₁.faceMap b with
    | none =>
      have hc : (comparisonComp M₀₁ M₁₂).faceMap c.cell = none := by
        simp only [comparisonComp_faceMap, hb, Option.bind_some, ha]
      rw [(comparisonComp M₀₁ M₁₂).faceCoordinateMapOption_eq_none laws h₀ h₂ c hc,
        M₀₁.faceCoordinateMapOption_eq_none laws h₀ h₁ cb (by rw [hcb]; exact ha)]
    | some a =>
      have hc : (comparisonComp M₀₁ M₁₂).faceMap c.cell = some a := by
        simp only [comparisonComp_faceMap, hb, Option.bind_some, ha]
      rw [(comparisonComp M₀₁ M₁₂).faceCoordinateMapOption_eq_some laws h₀ h₂ c a hc,
        M₀₁.faceCoordinateMapOption_eq_some laws h₀ h₁ cb a (by rw [hcb]; exact ha)]
      rfl

/-- A の次数0の直接生成pullbackと合成の一致。 -/
theorem generatedPullback0_comp (x : N₀.ChartCoordinate laws h₀ → ℚ) :
    (comparisonComp M₀₁ M₁₂).generatedPullback0 laws h₀ h₂ x =
      M₁₂.generatedPullback0 laws h₁ h₂ (M₀₁.generatedPullback0 laws h₀ h₁ x) := by
  funext c
  simp only [TargetSupportedNerveMorphism.generatedPullback0_apply,
    chartCoordinateMap_comp M₀₁ M₁₂ laws h₀ h₁ h₂]

/-- A の次数1の直接生成pullbackと合成の一致。 -/
theorem generatedPullback1_comp (x : N₀.EdgeCoordinate laws h₀ → ℚ) :
    (comparisonComp M₀₁ M₁₂).generatedPullback1 laws h₀ h₂ x =
      M₁₂.generatedPullback1 laws h₁ h₂ (M₀₁.generatedPullback1 laws h₀ h₁ x) := by
  funext c
  rw [TargetSupportedNerveMorphism.generatedPullback1_apply,
    TargetSupportedNerveMorphism.generatedPullback1_apply,
    edgeCoordinateMapOption_comp M₀₁ M₁₂ laws h₀ h₁ h₂]
  cases M₁₂.edgeCoordinateMapOption laws h₁ h₂ c with
  | none => rfl
  | some b => exact (M₀₁.generatedPullback1_apply laws h₀ h₁ x b).symm

/-- A の次数2の直接生成pullbackと合成の一致。 -/
theorem generatedPullback2_comp (x : N₀.FaceCoordinate laws h₀ → ℚ) :
    (comparisonComp M₀₁ M₁₂).generatedPullback2 laws h₀ h₂ x =
      M₁₂.generatedPullback2 laws h₁ h₂ (M₀₁.generatedPullback2 laws h₀ h₁ x) := by
  funext c
  rw [TargetSupportedNerveMorphism.generatedPullback2_apply,
    TargetSupportedNerveMorphism.generatedPullback2_apply,
    faceCoordinateMapOption_comp M₀₁ M₁₂ laws h₀ h₁ h₂]
  cases M₁₂.faceCoordinateMapOption laws h₁ h₂ c with
  | none => rfl
  | some b => exact (M₀₁.generatedPullback2_apply laws h₀ h₁ x b).symm

/-- A の全Law直接生成Homの一致。全三計算成分と可換性を含む等号。 -/
theorem generatedComparisonHom_comp [Fintype Source] :
    (comparisonComp M₀₁ M₁₂).generatedComparisonHom laws h₀ h₂ =
      cochainComp (M₀₁.generatedComparisonHom laws h₀ h₁)
        (M₁₂.generatedComparisonHom laws h₁ h₂) := by
  apply cochain_ext
  · exact LinearMap.ext (generatedPullback0_comp M₀₁ M₁₂ laws h₀ h₁ h₂)
  · exact LinearMap.ext (generatedPullback1_comp M₀₁ M₁₂ laws h₀ h₁ h₂)
  · exact LinearMap.ext (generatedPullback2_comp M₀₁ M₁₂ laws h₀ h₁ h₂)

/-- A の全Law既存H¹商での直接生成比較の合成。 -/
theorem generatedComparisonH1Map_comp [Fintype Source] :
    (comparisonComp M₀₁ M₁₂).generatedComparisonH1Map laws h₀ h₂ =
      (M₁₂.generatedComparisonH1Map laws h₁ h₂).comp
        (M₀₁.generatedComparisonH1Map laws h₀ h₁) := by
  change ((comparisonComp M₀₁ M₁₂).generatedComparisonHom laws h₀ h₂).h1Map = _
  rw [generatedComparisonHom_comp M₀₁ M₁₂ laws h₀ h₁ h₂, cochainComp_h1Map]
  rfl

end AAT.AG.AtlasDefectComposition

#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
