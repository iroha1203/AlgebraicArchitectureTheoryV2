import ResearchLean.AG.AtlasDefectComposition.SupportSignature
import ResearchLean.AG.AtlasDefectComposition.ComparisonLaws
import Formal.Util.AssertStandardAxioms
/-! # 選択セル包含による実 A-subnerve の台制限

Implementation notes: chart・edge・face の選択包含から incidence を保存する
逆向き cochain map を構成する。target subset の包含より弱いセル包含も扱う。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SubsetRestriction
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {q : Reading Source} (N : TargetSupportedNerve q)
/-- 全三次数における実選択セルの包含。 -/
def SelectedLE (A B : Set q.Target) : Prop :=
  (∀ c, (∃ t, t ∈ N.chartSupport c ∧ t ∈ A) → (∃ t, t ∈ N.chartSupport c ∧ t ∈ B)) ∧
  (∀ c, (∃ t, t ∈ N.edgeSupport c ∧ t ∈ A) → (∃ t, t ∈ N.edgeSupport c ∧ t ∈ B)) ∧
  (∀ c, (∃ t, t ∈ N.faceSupport c ∧ t ∈ A) → (∃ t, t ∈ N.faceSupport c ∧ t ∈ B))
/-- 選択セル包含の反射律。 -/
theorem selectedLE_refl (A : Set q.Target) : SelectedLE N A A := ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩
/-- 選択セル包含の推移律。 -/
theorem selectedLE_trans {A B C : Set q.Target} (h : SelectedLE N A B) (k : SelectedLE N B C) :
    SelectedLE N A C := ⟨fun c ha => k.1 c (h.1 c ha), fun c ha => k.2.1 c (h.2.1 c ha), fun c ha => k.2.2 c (h.2.2 c ha)⟩
/-- target subset 包含は全選択セルの包含を生成する。 -/
theorem selectedLE_of_subset {A B : Set q.Target} (h : A ⊆ B) : SelectedLE N A B := by
  refine ⟨?_,?_,?_⟩ <;> intro c hc <;> rcases hc with ⟨t, hs, ht⟩ <;> exact ⟨t, hs, h ht⟩
variable {A B C : Set q.Target} (h : SelectedLE N A B)
/-- 同じ名付き chart セルへの選択包含。 -/
def chartInclusion (c : N.ChartInTargetSubset A) : N.ChartInTargetSubset B := ⟨c.1, h.1 c.1 c.2⟩
/-- chart 選択包含は元のセル名を保持する。 -/
@[simp] theorem chartInclusion_val (c : N.ChartInTargetSubset A) : (chartInclusion N h c).1 = c.1 := rfl
/-- 同じ名付き edge セルへの選択包含。 -/
def edgeInclusion (c : N.EdgeInTargetSubset A) : N.EdgeInTargetSubset B := ⟨c.1, h.2.1 c.1 c.2⟩
/-- edge 選択包含は元のセル名を保持する。 -/
@[simp] theorem edgeInclusion_val (c : N.EdgeInTargetSubset A) : (edgeInclusion N h c).1 = c.1 := rfl
/-- 同じ名付き face セルへの選択包含。 -/
def faceInclusion (c : N.FaceInTargetSubset A) : N.FaceInTargetSubset B := ⟨c.1, h.2.2 c.1 c.2⟩
/-- face 選択包含は元のセル名を保持する。 -/
@[simp] theorem faceInclusion_val (c : N.FaceInTargetSubset A) : (faceInclusion N h c).1 = c.1 := rfl
/-- 選択包含は edge の left incidence を保存する。 -/
@[simp] theorem chartInclusion_edgeLeft (c : N.EdgeInTargetSubset A) :
    chartInclusion N h (N.targetSubsetEdgeLeft A c) = N.targetSubsetEdgeLeft B (edgeInclusion N h c) := by
  apply Subtype.ext
  rfl
/-- 選択包含は edge の right incidence を保存する。 -/
@[simp] theorem chartInclusion_edgeRight (c : N.EdgeInTargetSubset A) :
    chartInclusion N h (N.targetSubsetEdgeRight A c) = N.targetSubsetEdgeRight B (edgeInclusion N h c) := by
  apply Subtype.ext
  rfl
/-- 選択包含は face の incidence slot 0 を保存する。 -/
@[simp] theorem edgeInclusion_faceEdge0 (c : N.FaceInTargetSubset A) :
    edgeInclusion N h (N.targetSubsetFaceEdge0 A c) = N.targetSubsetFaceEdge0 B (faceInclusion N h c) := by
  apply Subtype.ext
  rfl
/-- 選択包含は face の incidence slot 1 を保存する。 -/
@[simp] theorem edgeInclusion_faceEdge1 (c : N.FaceInTargetSubset A) :
    edgeInclusion N h (N.targetSubsetFaceEdge1 A c) = N.targetSubsetFaceEdge1 B (faceInclusion N h c) := by
  apply Subtype.ext
  rfl
/-- 選択包含は face の incidence slot 2 を保存する。 -/
@[simp] theorem edgeInclusion_faceEdge2 (c : N.FaceInTargetSubset A) :
    edgeInclusion N h (N.targetSubsetFaceEdge2 A c) = N.targetSubsetFaceEdge2 B (faceInclusion N h c) := by
  apply Subtype.ext
  rfl
/-- 次数 0 の実セル座標制限。 -/
def restrict0 : (N.targetSubsetComplex B).C0 →ₗ[ℚ] (N.targetSubsetComplex A).C0 :=
  LinearMap.pi (fun c => LinearMap.proj (chartInclusion N h c))
/-- 次数 0 の制限は同じ名付きセルで評価する。 -/
@[simp] theorem restrict0_apply (x : (N.targetSubsetComplex B).C0) (c : N.ChartInTargetSubset A) :
    restrict0 N h x c = x (chartInclusion N h c) := rfl
/-- 次数 1 の実セル座標制限。 -/
def restrict1 : (N.targetSubsetComplex B).C1 →ₗ[ℚ] (N.targetSubsetComplex A).C1 :=
  LinearMap.pi (fun c => LinearMap.proj (edgeInclusion N h c))
/-- 次数 1 の制限は同じ名付きセルで評価する。 -/
@[simp] theorem restrict1_apply (x : (N.targetSubsetComplex B).C1) (c : N.EdgeInTargetSubset A) :
    restrict1 N h x c = x (edgeInclusion N h c) := rfl
/-- 次数 2 の実セル座標制限。 -/
def restrict2 : (N.targetSubsetComplex B).C2 →ₗ[ℚ] (N.targetSubsetComplex A).C2 :=
  LinearMap.pi (fun c => LinearMap.proj (faceInclusion N h c))
/-- 次数 2 の制限は同じ名付きセルで評価する。 -/
@[simp] theorem restrict2_apply (x : (N.targetSubsetComplex B).C2) (c : N.FaceInTargetSubset A) :
    restrict2 N h x c = x (faceInclusion N h c) := rfl
/-- 台制限は次数零の実 incidence differential と可換する。 -/
theorem restrict_d0 (x : (N.targetSubsetComplex B).C0) :
    restrict1 N h ((N.targetSubsetComplex B).d0 x) = (N.targetSubsetComplex A).d0 (restrict0 N h x) := by
  funext c
  simp only [restrict1_apply, TargetSupportedNerve.targetSubsetComplex_d0_apply,
    restrict0_apply, chartInclusion_edgeRight, chartInclusion_edgeLeft]
/-- 台制限は次数一の実三 slot differential と可換する。 -/
theorem restrict_d1 (x : (N.targetSubsetComplex B).C1) :
    restrict2 N h ((N.targetSubsetComplex B).d1 x) = (N.targetSubsetComplex A).d1 (restrict1 N h x) := by
  funext c
  simp only [restrict2_apply, TargetSupportedNerve.targetSubsetComplex_d1_apply,
    restrict1_apply, edgeInclusion_faceEdge0, edgeInclusion_faceEdge1, edgeInclusion_faceEdge2]
/-- 全選択セル包含から生成した逆向き cochain map。 -/
def hom : ThreeCochainComplex.Hom (N.targetSubsetComplex B) (N.targetSubsetComplex A) where
  f0 := restrict0 N h
  f1 := restrict1 N h
  f2 := restrict2 N h
  comm0 := restrict_d0 N h
  comm1 := restrict_d1 N h
/-- 生成 Hom の次数 0 は実セル制限である。 -/
@[simp] theorem hom_f0 : (hom N h).f0 = restrict0 N h := rfl
/-- 生成 Hom の次数 1 は実セル制限である。 -/
@[simp] theorem hom_f1 : (hom N h).f1 = restrict1 N h := rfl
/-- 生成 Hom の次数 2 は実セル制限である。 -/
@[simp] theorem hom_f2 : (hom N h).f2 = restrict2 N h := rfl
/-- 反射的台制限は実 complex の恒等射である。 -/
theorem hom_id (A : Set q.Target) : hom N (selectedLE_refl N A) = cochainId (N.targetSubsetComplex A) := by
  apply cochain_ext <;> ext x <;> rfl
/-- 台制限の推移は cochain map の合成と一致する。 -/
theorem hom_comp (k : SelectedLE N B C) :
    hom N (selectedLE_trans N h k) = cochainComp (hom N k) (hom N h) := by
  apply cochain_ext <;> ext x <;> rfl
end AAT.AG.AtlasDefectComposition.SubsetRestriction
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SubsetRestriction
