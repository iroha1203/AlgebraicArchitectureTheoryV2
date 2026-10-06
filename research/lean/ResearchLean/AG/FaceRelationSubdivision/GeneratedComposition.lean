import ResearchLean.AG.FaceRelationSubdivision.GeneratedComparison
import ResearchLean.AG.AtlasDefectComposition.ComparisonLaws
import ResearchLean.AG.ResolutionInvariance.GeneratedComparisonMap
import Formal.Util.AssertStandardAxioms

/-!
# 混在比較の生成合成と旧比較への特殊化

G-134 A。直接生成した写像と合成を全三次数・既存H¹商で照合する。

## Implementation notes

合成の右辺はG-133の汎用Hom合成を再利用する。直接生成は原始Option.bindから行う。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u

variable {Source : Type u}
variable {q₀ q₁ q₂ : Reading Source}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}
variable (M₀₁ : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : IncidenceSupportedComparison q₁ q₂ h₁₂ N₁ N₂)
variable (laws : FiniteLawFamily Source)
variable (h₀ : laws.Adequate q₀) (h₁ : laws.Adequate q₁) (h₂ : laws.Adequate q₂)

/-- A の次数0座標の合成。Lawと値の同定を保持する。 -/
theorem chartCoordinateMap_comp (c : N₂.ChartCoordinate laws h₂) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).chartCoordinateMap laws h₀ h₂ c =
      M₀₁.chartCoordinateMap laws h₀ h₁ (M₁₂.chartCoordinateMap laws h₁ h₂ c) := by
  apply CellCoordinate.ext <;> rfl

/-- A の edge 座標の部分合成。二つの退化経路とmapped経路を区別する。 -/
theorem edgeCoordinateMapOption_comp (c : N₂.EdgeCoordinate laws h₂) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeCoordinateMapOption laws h₀ h₂ c =
      (M₁₂.edgeCoordinateMapOption laws h₁ h₂ c).bind
        (M₀₁.edgeCoordinateMapOption laws h₀ h₁) := by
  cases hb : M₁₂.edgeMap c.cell with
  | none =>
    have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.cell = none := by
      simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_none]
    rw [M₁₂.edgeCoordinateMapOption_eq_none laws h₁ h₂ c hb,
      (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeCoordinateMapOption_eq_none laws h₀ h₂ c hc]
    rfl
  | some b =>
    let cb := M₁₂.edgeCoordinateMap laws h₁ h₂ c b hb
    have hcb : cb.cell = b := rfl
    rw [M₁₂.edgeCoordinateMapOption_eq_some laws h₁ h₂ c b hb, Option.bind_some]
    cases ha : M₀₁.edgeMap b with
    | none =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.cell = none := by
        simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeCoordinateMapOption_eq_none laws h₀ h₂ c hc,
        M₀₁.edgeCoordinateMapOption_eq_none laws h₀ h₁ cb (by rw [hcb]; exact ha)]
    | some a =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeMap c.cell = some a := by
        simp only [IncidenceSupportedComparison.comp_edgeMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).edgeCoordinateMapOption_eq_some laws h₀ h₂ c a hc,
        M₀₁.edgeCoordinateMapOption_eq_some laws h₀ h₁ cb a (by rw [hcb]; exact ha)]
      rfl

/-- A の face 座標の部分合成。二つの退化経路とmapped経路を区別する。 -/
theorem faceCoordinateMapOption_comp (c : N₂.FaceCoordinate laws h₂) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceCoordinateMapOption laws h₀ h₂ c =
      (M₁₂.faceCoordinateMapOption laws h₁ h₂ c).bind
        (M₀₁.faceCoordinateMapOption laws h₀ h₁) := by
  cases hb : M₁₂.faceMap c.cell with
  | none =>
    have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.cell = none := by
      simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_none]
    rw [M₁₂.faceCoordinateMapOption_eq_none laws h₁ h₂ c hb,
      (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceCoordinateMapOption_eq_none laws h₀ h₂ c hc]
    rfl
  | some b =>
    let cb := M₁₂.faceCoordinateMap laws h₁ h₂ c b hb
    have hcb : cb.cell = b := rfl
    rw [M₁₂.faceCoordinateMapOption_eq_some laws h₁ h₂ c b hb, Option.bind_some]
    cases ha : M₀₁.faceMap b with
    | none =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.cell = none := by
        simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).faceCoordinateMapOption_eq_none laws h₀ h₂ c hc,
        M₀₁.faceCoordinateMapOption_eq_none laws h₀ h₁ cb (by rw [hcb]; exact ha)]
    | some a =>
      have hc : (IncidenceSupportedComparison.comp M₀₁ M₁₂).faceMap c.cell = some a := by
        simp only [IncidenceSupportedComparison.comp_faceMap, hb, Option.bind_some, ha]
      rw [(IncidenceSupportedComparison.comp M₀₁ M₁₂).faceCoordinateMapOption_eq_some laws h₀ h₂ c a hc,
        M₀₁.faceCoordinateMapOption_eq_some laws h₀ h₁ cb a (by rw [hcb]; exact ha)]
      rfl

/-- A の次数0の直接生成pullbackと合成の一致。 -/
theorem generatedPullback0_comp (x : N₀.ChartCoordinate laws h₀ → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedPullback0 laws h₀ h₂ x =
      M₁₂.generatedPullback0 laws h₁ h₂ (M₀₁.generatedPullback0 laws h₀ h₁ x) := by
  funext c
  simp only [IncidenceSupportedComparison.generatedPullback0_apply,
    chartCoordinateMap_comp M₀₁ M₁₂ laws h₀ h₁ h₂]

/-- A の次数1の直接生成pullbackと合成の一致。 -/
theorem generatedPullback1_comp (x : N₀.EdgeCoordinate laws h₀ → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedPullback1 laws h₀ h₂ x =
      M₁₂.generatedPullback1 laws h₁ h₂ (M₀₁.generatedPullback1 laws h₀ h₁ x) := by
  funext c
  rw [IncidenceSupportedComparison.generatedPullback1_apply,
    IncidenceSupportedComparison.generatedPullback1_apply,
    edgeCoordinateMapOption_comp M₀₁ M₁₂ laws h₀ h₁ h₂]
  cases M₁₂.edgeCoordinateMapOption laws h₁ h₂ c with
  | none => rfl
  | some b => exact (M₀₁.generatedPullback1_apply laws h₀ h₁ x b).symm

/-- A の次数2の直接生成pullbackと合成の一致。 -/
theorem generatedPullback2_comp (x : N₀.FaceCoordinate laws h₀ → ℚ) :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedPullback2 laws h₀ h₂ x =
      M₁₂.generatedPullback2 laws h₁ h₂ (M₀₁.generatedPullback2 laws h₀ h₁ x) := by
  funext c
  rw [IncidenceSupportedComparison.generatedPullback2_apply,
    IncidenceSupportedComparison.generatedPullback2_apply,
    faceCoordinateMapOption_comp M₀₁ M₁₂ laws h₀ h₁ h₂]
  cases M₁₂.faceCoordinateMapOption laws h₁ h₂ c with
  | none => rfl
  | some b => exact (M₀₁.generatedPullback2_apply laws h₀ h₁ x b).symm

/-- A の全Law直接生成Homの一致。全三計算成分と可換性を含む等号。 -/
theorem generatedComparisonHom_comp [Fintype Source] :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedComparisonHom laws h₀ h₂ =
      cochainComp (M₀₁.generatedComparisonHom laws h₀ h₁)
        (M₁₂.generatedComparisonHom laws h₁ h₂) := by
  apply cochain_ext
  · exact LinearMap.ext (generatedPullback0_comp M₀₁ M₁₂ laws h₀ h₁ h₂)
  · exact LinearMap.ext (generatedPullback1_comp M₀₁ M₁₂ laws h₀ h₁ h₂)
  · exact LinearMap.ext (generatedPullback2_comp M₀₁ M₁₂ laws h₀ h₁ h₂)

/-- A の全Law既存H¹商での直接生成比較の合成。 -/
theorem generatedComparisonH1Map_comp [Fintype Source] :
    (IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedComparisonH1Map laws h₀ h₂ =
      (M₁₂.generatedComparisonH1Map laws h₁ h₂).comp
        (M₀₁.generatedComparisonH1Map laws h₀ h₁) := by
  change ((IncidenceSupportedComparison.comp M₀₁ M₁₂).generatedComparisonHom laws h₀ h₂).h1Map = _
  rw [generatedComparisonHom_comp M₀₁ M₁₂ laws h₀ h₁ h₂, cochainComp_h1Map]
  rfl


/-- 恒等の原始比較から生成した実Homは三次数の恒等。 -/
theorem identity_generatedComparisonHom [Fintype Source]
    (q : Reading Source) (N : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (ha : laws.Adequate q) :
    (IncidenceSupportedComparison.identity q N).generatedComparisonHom laws ha ha =
      cochainId (N.lawGeneratedComplex laws ha) := by
  apply cochain_ext <;> rfl

/-- 原始恒等からの実H¹写像は既存商の恒等。 -/
theorem identity_generatedComparisonH1Map [Fintype Source]
    (q : Reading Source) (N : TargetSupportedNerve q) (laws : FiniteLawFamily Source)
    (ha : laws.Adequate q) :
    (IncidenceSupportedComparison.identity q N).generatedComparisonH1Map laws ha ha =
      LinearMap.id := by
  change ((IncidenceSupportedComparison.identity q N).generatedComparisonHom laws ha ha).h1Map = _
  rw [identity_generatedComparisonHom, cochainId_h1Map]

/-- T0の粗adequacyだけから細adequacyを放電して実Law Homを生成する。 -/
def generatedComparisonHomFromCoarse [Fintype Source]
    (M : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
    (laws : FiniteLawFamily Source) (ha : laws.Adequate q₀) :
    ThreeCochainComplex.Hom (N₀.lawGeneratedComplex laws ha)
      (N₁.lawGeneratedComplex laws (adequate_of_coarser laws h₀₁ ha)) :=
  M.generatedComparisonHom laws ha (adequate_of_coarser laws h₀₁ ha)

section Hereditary
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : TargetSupportedNerveMorphism qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc) (hf : laws.Adequate qf)

/-- 埋め込みのdegree 0座標は旧生成座標と一致する。 -/
theorem ofHereditary_chartCoordinateMap (x : Nf.ChartCoordinate laws hf) :
    (IncidenceSupportedComparison.ofHereditary M).chartCoordinateMap laws hc hf x =
      M.chartCoordinateMap laws hc hf x := rfl

/-- 埋め込みのdegree 1部分座標は旧生成座標と一致する。 -/
theorem ofHereditary_edgeCoordinateMapOption (x : Nf.EdgeCoordinate laws hf) :
    (IncidenceSupportedComparison.ofHereditary M).edgeCoordinateMapOption laws hc hf x =
      M.edgeCoordinateMapOption laws hc hf x := rfl

/-- 埋め込みのdegree 2部分座標は旧生成座標と一致する。 -/
theorem ofHereditary_faceCoordinateMapOption (x : Nf.FaceCoordinate laws hf) :
    (IncidenceSupportedComparison.ofHereditary M).faceCoordinateMapOption laws hc hf x =
      M.faceCoordinateMapOption laws hc hf x := rfl

/-- 原始埋め込み後の実生成Homは旧Homの全三成分と一致する。 -/
theorem ofHereditary_generatedComparisonHom [Fintype Source] :
    (IncidenceSupportedComparison.ofHereditary M).generatedComparisonHom laws hc hf =
      M.generatedComparisonHom laws hc hf := by
  apply cochain_ext <;> rfl

/-- 埋め込み後の既存H¹商への写像も旧生成写像と一致する。 -/
theorem ofHereditary_generatedComparisonH1Map [Fintype Source] :
    (IncidenceSupportedComparison.ofHereditary M).generatedComparisonH1Map laws hc hf =
      M.generatedComparisonH1Map laws hc hf := by
  change ((IncidenceSupportedComparison.ofHereditary M).generatedComparisonHom laws hc hf).h1Map = _
  rw [ofHereditary_generatedComparisonHom]
  rfl
end Hereditary

end AAT.AG.FaceRelationSubdivision

#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
