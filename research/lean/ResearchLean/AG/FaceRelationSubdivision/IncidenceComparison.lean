import ResearchLean.AG.ResolutionInvariance.SupportedNerveMorphism
import Mathlib.Data.Finsupp.Single
import ResearchLean.AG.AtlasDefectComposition.ComparisonComposition
import Formal.Util.AssertStandardAxioms

/-!
# 混在退化面の原始比較

G-134 A の符号付き自由ℤ加群の条件を入力とし、K1台の輸送を導出する。

## Implementation notes

`Option` のセル像を自由ℤ加群の基底へ送る。面の三辺が個別に退化する条件は
使わず、符号付き和だけを課す。診断の写像・同型は入力fieldに含まない。
-/

noncomputable section

namespace AAT.AG.FaceRelationSubdivision

open CanonicalResolution Cohomology ResolutionInvariance

universe u

variable {Source : Type u}

/-- 原始部分セル像。`none` は零、`some e` は係数1の基底である。 -/
def optionCell {Cell : Type u} (e : Option Cell) : Cell →₀ ℤ :=
  e.elim 0 (fun a => Finsupp.single a 1)

/-- `none` の像は零。正規形は自由加群の零へ向ける。 -/
@[simp] theorem optionCell_none {Cell : Type u} : optionCell (none : Option Cell) = 0 := rfl

/-- 写るセルの像はその基底。正規形は `Finsupp.single` へ向ける。 -/
@[simp] theorem optionCell_some {Cell : Type u} (e : Cell) :
    optionCell (some e) = Finsupp.single e 1 := rfl

/-- 三項の符号付き零和の完全な形。重複セルも区別して検査する。 -/
theorem optionCell_incidence_iff {Cell : Type u} (a b c : Option Cell) :
    optionCell a - optionCell b + optionCell c = 0 ↔
      (a = none ∧ b = c) ∨ (c = none ∧ a = b) := by
  classical
  constructor
  · intro h
    cases a with
    | none =>
      left
      refine ⟨rfl, ?_⟩
      cases b with
      | none =>
        cases c with
        | none => rfl
        | some z =>
          have hz := congrArg (fun f : Cell →₀ ℤ => f z) h
          simp at hz
      | some y =>
        cases c with
        | none =>
          have hy := congrArg (fun f : Cell →₀ ℤ => f y) h
          simp at hy
        | some z =>
          have heq : Finsupp.single y (1 : ℤ) = Finsupp.single z 1 := by
            simpa using (sub_eq_zero.mp (by simpa [neg_add_eq_sub] using h) :
              Finsupp.single z (1 : ℤ) = Finsupp.single y 1).symm
          exact congrArg some (Finsupp.single_left_injective (by decide : (1 : ℤ) ≠ 0) heq)
    | some x =>
      right
      cases c with
      | none =>
        refine ⟨rfl, ?_⟩
        cases b with
        | none =>
          have hx := congrArg (fun f : Cell →₀ ℤ => f x) h
          simp at hx
        | some y =>
          have heq : Finsupp.single x (1 : ℤ) = Finsupp.single y 1 := by
            apply sub_eq_zero.mp
            simpa using h
          exact congrArg some (Finsupp.single_left_injective (by decide : (1 : ℤ) ≠ 0) heq)
      | some z =>
        have hx := congrArg (fun f : Cell →₀ ℤ => f x) h
        cases b with
        | none =>
          by_cases hzx : z = x <;> simp [hzx] at hx
        | some y =>
          by_cases hyx : y = x
          · subst y
            have hz := congrArg (fun f : Cell →₀ ℤ => f z) h
            simp at hz
          · by_cases hzx : z = x <;> simp [hyx, hzx] at hx
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- 部分セル像への再代入は原始零和を保つ。AのOption.bind合成で使う。 -/
theorem optionCell_incidence_bind {Cell Next : Type u} (a b c : Option Cell)
    (φ : Cell → Option Next) (h : optionCell a - optionCell b + optionCell c = 0) :
    optionCell (a.bind φ) - optionCell (b.bind φ) + optionCell (c.bind φ) = 0 := by
  rcases (optionCell_incidence_iff a b c).1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- G-134 A の原始比較。結論に相当する線形写像の条件はfieldに持たない。 -/
structure IncidenceSupportedComparison
    (coarseReading fineReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan fineReading)
    (coarse : TargetSupportedNerve coarseReading)
    (fine : TargetSupportedNerve fineReading) where
  chartMap : fine.nerve.Chart → coarse.nerve.Chart
  edgeMap : fine.nerve.EdgeComponent → Option coarse.nerve.EdgeComponent
  faceMap : fine.nerve.FaceComponent → Option coarse.nerve.FaceComponent
  edge_some_left : ∀ fineEdge coarseEdge,
    edgeMap fineEdge = some coarseEdge →
      chartMap (fine.nerve.edgeLeft fineEdge) =
        coarse.nerve.edgeLeft coarseEdge
  edge_some_right : ∀ fineEdge coarseEdge,
    edgeMap fineEdge = some coarseEdge →
      chartMap (fine.nerve.edgeRight fineEdge) =
        coarse.nerve.edgeRight coarseEdge
  edge_none_fiber : ∀ fineEdge,
    edgeMap fineEdge = none →
      chartMap (fine.nerve.edgeLeft fineEdge) =
        chartMap (fine.nerve.edgeRight fineEdge)
  face_some_edge0 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.nerve.faceEdge0 fineFace) =
        some (coarse.nerve.faceEdge0 coarseFace)
  face_some_edge1 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.nerve.faceEdge1 fineFace) =
        some (coarse.nerve.faceEdge1 coarseFace)
  face_some_edge2 : ∀ fineFace coarseFace,
    faceMap fineFace = some coarseFace →
      edgeMap (fine.nerve.faceEdge2 fineFace) =
        some (coarse.nerve.faceEdge2 coarseFace)
  face_none_incidence : ∀ fineFace,
    faceMap fineFace = none →
      optionCell (edgeMap (fine.nerve.faceEdge0 fineFace)) -
        optionCell (edgeMap (fine.nerve.faceEdge1 fineFace)) +
        optionCell (edgeMap (fine.nerve.faceEdge2 fineFace)) = 0
  chartSupport_compatible : ∀ fineChart fineTarget,
    fineTarget ∈ fine.chartSupport fineChart →
      comparisonFactor coarseReading fineReading hcoarser fineTarget ∈
        coarse.chartSupport (chartMap fineChart)

namespace IncidenceSupportedComparison

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-- 旧hereditary比較の埋め込み。原始零和は三つの旧退化条件から放電する。 -/
def ofHereditary (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
    coarse fine) : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine where
  chartMap := M.chartMap
  edgeMap := M.edgeMap
  faceMap := M.faceMap
  edge_some_left := M.edge_some_left
  edge_some_right := M.edge_some_right
  edge_none_fiber := M.edge_none_fiber
  face_some_edge0 := M.face_some_edge0
  face_some_edge1 := M.face_some_edge1
  face_some_edge2 := M.face_some_edge2
  face_none_incidence := by
    intro f hf
    rw [M.face_none_edge0 f hf, M.face_none_edge1 f hf, M.face_none_edge2 f hf]
    simp
  chartSupport_compatible := M.chartSupport_compatible

/-- 比較のext API。全計算成分を含む構造の等号。 -/
@[ext] theorem ext {M M' : IncidenceSupportedComparison coarseReading fineReading hcoarser coarse fine}
    (hc : M.chartMap = M'.chartMap) (he : M.edgeMap = M'.edgeMap)
    (hf : M.faceMap = M'.faceMap) : M = M' := by
  cases M
  cases M'
  cases hc
  cases he
  cases hf
  rfl

/-! ## K1-derived support transport -/

/--
Mapped edge support compatibility follows from endpoint incidence, chart
support compatibility, and the K1 endpoint intersection.
-/
theorem edgeSupport_compatible
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    {fineEdge : fine.nerve.EdgeComponent}
    {coarseEdge : coarse.nerve.EdgeComponent}
    (hmap : M.edgeMap fineEdge = some coarseEdge)
    {fineTarget : fineReading.Target}
    (htarget : fineTarget ∈ fine.edgeSupport fineEdge) :
    comparisonFactor coarseReading fineReading hcoarser fineTarget ∈
      coarse.edgeSupport coarseEdge := by
  rw [fine.mem_edgeSupport_iff] at htarget
  rw [coarse.mem_edgeSupport_iff]
  constructor
  · rw [← M.edge_some_left fineEdge coarseEdge hmap]
    exact M.chartSupport_compatible _ _ htarget.1
  · rw [← M.edge_some_right fineEdge coarseEdge hmap]
    exact M.chartSupport_compatible _ _ htarget.2

/--
Mapped face support compatibility follows from boundary incidence and the K1
intersection of the three already-derived edge supports.
-/
theorem faceSupport_compatible
    (M : IncidenceSupportedComparison coarseReading fineReading hcoarser
      coarse fine)
    {fineFace : fine.nerve.FaceComponent}
    {coarseFace : coarse.nerve.FaceComponent}
    (hmap : M.faceMap fineFace = some coarseFace)
    {fineTarget : fineReading.Target}
    (htarget : fineTarget ∈ fine.faceSupport fineFace) :
    comparisonFactor coarseReading fineReading hcoarser fineTarget ∈
      coarse.faceSupport coarseFace := by
  rw [fine.mem_faceSupport_iff] at htarget
  rw [coarse.mem_faceSupport_iff]
  exact ⟨
    M.edgeSupport_compatible
      (M.face_some_edge0 fineFace coarseFace hmap) htarget.1,
    M.edgeSupport_compatible
      (M.face_some_edge1 fineFace coarseFace hmap) htarget.2.1,
    M.edgeSupport_compatible
      (M.face_some_edge2 fineFace coarseFace hmap) htarget.2.2⟩

variable {q₀ q₁ q₂ q₃ : Reading Source}

variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}

/-- A の直接セル比較。Option の三経路を保持し、全 field を二射から生成する。 -/
def comp
    (M₀₁ : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : IncidenceSupportedComparison q₁ q₂ h₁₂ N₁ N₂) :
    IncidenceSupportedComparison q₀ q₂ (Reading.coarserThan_trans h₀₁ h₁₂) N₀ N₂ where
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
  face_none_incidence := by
    intro f h
    cases hf : M₁₂.faceMap f with
    | none =>
      exact optionCell_incidence_bind _ _ _ M₀₁.edgeMap (M₁₂.face_none_incidence f hf)
    | some b =>
      simp only [hf, Option.bind_some] at h
      rw [M₁₂.face_some_edge0 f b hf, M₁₂.face_some_edge1 f b hf,
        M₁₂.face_some_edge2 f b hf]
      exact M₀₁.face_none_incidence b h
  chartSupport_compatible := by
    intro c t ht
    rw [AtlasDefectComposition.comparisonFactor_comp h₀₁ h₁₂]
    exact M₀₁.chartSupport_compatible _ _ (M₁₂.chartSupport_compatible c t ht)

/-- `comp` の chart 評価 API。 -/
@[simp] theorem comp_chartMap
    (M₀₁ : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : IncidenceSupportedComparison q₁ q₂ h₁₂ N₁ N₂) (c : N₂.nerve.Chart) :
    (comp M₀₁ M₁₂).chartMap c = M₀₁.chartMap (M₁₂.chartMap c) := rfl

/-- `comp` の edge 評価 API。 -/
@[simp] theorem comp_edgeMap
    (M₀₁ : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : IncidenceSupportedComparison q₁ q₂ h₁₂ N₁ N₂) (e : N₂.nerve.EdgeComponent) :
    (comp M₀₁ M₁₂).edgeMap e = (M₁₂.edgeMap e).bind M₀₁.edgeMap := rfl

/-- `comp` の face 評価 API。 -/
@[simp] theorem comp_faceMap
    (M₀₁ : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : IncidenceSupportedComparison q₁ q₂ h₁₂ N₁ N₂) (f : N₂.nerve.FaceComponent) :
    (comp M₀₁ M₁₂).faceMap f = (M₁₂.faceMap f).bind M₀₁.faceMap := rfl

/-- 全セルを同名へ送る原始恒等。 -/
def identity (q : Reading Source) (N : TargetSupportedNerve q) :
    IncidenceSupportedComparison q q (Reading.coarserThan_refl q) N N where
  chartMap := id
  edgeMap := some
  faceMap := some
  edge_some_left := by intros _ _ h; cases Option.some.inj h; rfl
  edge_some_right := by intros _ _ h; cases Option.some.inj h; rfl
  edge_none_fiber := by intros _ h; cases h
  face_some_edge0 := by intros _ _ h; cases Option.some.inj h; rfl
  face_some_edge1 := by intros _ _ h; cases Option.some.inj h; rfl
  face_some_edge2 := by intros _ _ h; cases Option.some.inj h; rfl
  face_none_incidence := by intros _ h; cases h
  chartSupport_compatible := by
    intro c t ht
    obtain ⟨s, rfl⟩ := q.surjective t
    rw [comparisonFactor_commutes]
    exact ht

/-- 左恒等は全計算成分で成立する。 -/
theorem comp_identity_left
    (M : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁) :
    comp (identity q₀ N₀) M = M := by
  apply ext
  · rfl
  · funext e
    rw [comp_edgeMap]
    cases M.edgeMap e <;> rfl
  · funext f
    rw [comp_faceMap]
    cases M.faceMap f <;> rfl

/-- 右恒等は全計算成分で成立する。 -/
theorem comp_identity_right
    (M : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁) :
    comp M (identity q₁ N₁) = M := by
  apply ext <;> rfl

/-- Option.bindの結合則をchart・edge・faceすべてへ適用する。 -/
theorem comp_assoc {h₂₃ : q₂.CoarserThan q₃} {N₃ : TargetSupportedNerve q₃}
    (M₀₁ : IncidenceSupportedComparison q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : IncidenceSupportedComparison q₁ q₂ h₁₂ N₁ N₂)
    (M₂₃ : IncidenceSupportedComparison q₂ q₃ h₂₃ N₂ N₃) :
    comp (comp M₀₁ M₁₂) M₂₃ = comp M₀₁ (comp M₁₂ M₂₃) := by
  apply ext
  · rfl
  · funext e
    simp only [comp_edgeMap, Option.bind_assoc]
  · funext f
    simp only [comp_faceMap, Option.bind_assoc]

/-- 旧比較の埋め込みは原始合成と可換。 -/
theorem ofHereditary_comp
    (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
    (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂) :
    ofHereditary (AtlasDefectComposition.comparisonComp M₀₁ M₁₂) =
      comp (ofHereditary M₀₁) (ofHereditary M₁₂) := by
  apply ext <;> rfl

end IncidenceSupportedComparison

end AAT.AG.FaceRelationSubdivision

#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
