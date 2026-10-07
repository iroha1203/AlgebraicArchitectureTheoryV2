import ResearchLean.AG.FaceRelationSubdivision.WitnessOneInput
import ResearchLean.AG.FaceRelationSubdivision.IncidenceNamedComparison
import ResearchLean.AG.FaceRelationSubdivision.BlockComposition
import ResearchLean.AG.FaceRelationSubdivision.GeneratedComposition
import ResearchLean.AG.FaceRelationSubdivision.SubsetComposition
import Formal.Util.AssertStandardAxioms
/-!
# W1 の同じ原始比較と全三成分生成

## Implementation notes

rplus は reading 逆像比較と三角形収縮の原始合成、rminus は面を除いた包含との原始合成。
実 Law/block 射はそれぞれ独立に生成し、生成関手性で合成と一致させる。
旧 hereditary 型に混在退化を押し込める表現は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
/-- 面なしから面ありへの原始包含。 -/
def inclusion : TargetSupportedNerveMorphism qf qf (Reading.coarserThan_refl qf) plus minus where
  chartMap := id
  edgeMap := some
  faceMap := Empty.elim
  edge_some_left := by intro e d h; cases Option.some.inj h; rfl
  edge_some_right := by intro e d h; cases Option.some.inj h; rfl
  edge_none_fiber := by intro e h; cases h
  face_some_edge0 := fun f => nomatch f
  face_some_edge1 := fun f => nomatch f
  face_some_edge2 := fun f => nomatch f
  face_none_edge0 := fun f => nomatch f
  face_none_edge1 := fun f => nomatch f
  face_none_edge2 := fun f => nomatch f
  chartSupport_compatible := by
    intro v t ht
    rw [TriangleAddition.self_factor]
    exact ht
/-- j を新比較クラスへ埋め込む。 -/
abbrev j := IncidenceSupportedComparison.ofHereditary inclusion
/-- reading 逆像操作と三角形追加の直接原始比較。 -/
abbrev rPlus := IncidenceSupportedComparison.comp (readingPresentation N coarser).comparison
  (TriangleAddition.collapse pulled (0 : Fin 2))
/-- 同じ頂点・辺を保った面なし原始比較。 -/
abbrev rMinus := IncidenceSupportedComparison.comp rPlus j
/-- 指定原始合成 rminus=rplus j。 -/
theorem primitive_composition : rMinus = IncidenceSupportedComparison.comp rPlus j := rfl
/-- rplus は旧 chart を同名へ送る。 -/
@[simp] theorem rPlus_chart_old (v : Fin 2) : rPlus.chartMap (.inl v) = v := rfl
/-- rplus は fresh chart を v へ送る。 -/
@[simp] theorem rPlus_chart_new : rPlus.chartMap (.inr PUnit.unit) = (0 : Fin 2) := rfl
/-- rplus は旧辺を同名へ送る。 -/
@[simp] theorem rPlus_edge_old (e : Fin 2) : rPlus.edgeMap (.inl e) = some e := rfl
/-- rplus は c を零へ送る。 -/
@[simp] theorem rPlus_edge_c : rPlus.edgeMap (.inr false) = none := rfl
/-- rplus は e2 を e1 へ送る。 -/
@[simp] theorem rPlus_edge_e2 : rPlus.edgeMap (.inr true) = some (0 : Fin 2) := rfl
/-- rplus は f を零へ送る混在退化比較。 -/
@[simp] theorem rPlus_face (f : plus.nerve.FaceComponent) : rPlus.faceMap f = none := by
  cases f with
  | inl f => exact Empty.elim f
  | inr f => cases f; rfl
/-- rminus は同じ chart 表を使う。 -/
@[simp] theorem rMinus_chart (v : minus.nerve.Chart) : rMinus.chartMap v = rPlus.chartMap v := rfl
/-- rminus は同じ辺表を使う。 -/
@[simp] theorem rMinus_edge (e : minus.nerve.EdgeComponent) : rMinus.edgeMap e = rPlus.edgeMap e := rfl
/-- 異なる二辺が同じ粗辺へ写り、指定 C5 の一意性が破れる。 -/
theorem distinct_lifts_same_image : (.inl (0 : Fin 2) : plus.nerve.EdgeComponent) ≠ .inr true ∧
    rPlus.edgeMap (.inl (0 : Fin 2)) = rPlus.edgeMap (.inr true) := ⟨Sum.inl_ne_inr,rfl⟩
/-- 同じ原始辺表について C5 の全辺一意 lift 式が成立しない。 -/
theorem edge_lift_uniqueness_fails : ¬ ∀ (d : Fin 2) (a b : plus.nerve.EdgeComponent),
    rPlus.edgeMap a=some d → rPlus.edgeMap b=some d → a=b := by
  intro h
  exact Sum.inl_ne_inr (h 0 (.inl (0 : Fin 2)) (.inr true) rfl rfl)
/-- 同じ原始 rplus 表は旧 hereditary 退化面条件を満たさない。 -/
theorem not_hereditary : ¬ ∃ M : TargetSupportedNerveMorphism qc qf
    (Reading.coarserThan_trans coarser (Reading.coarserThan_refl qf)) N plus,
    M.edgeMap = rPlus.edgeMap ∧ M.faceMap = rPlus.faceMap := by
  rintro ⟨M,he,hf⟩
  have hm := M.face_none_edge1 (.inr PUnit.unit) (by rw [hf,rPlus_face])
  rw [he,TriangleAddition.faceEdge1_new,rPlus_edge_old] at hm
  cases hm
/-- 粗実 block の原始名付き同定。 -/
def blockEquiv (l : LawValueLabel laws) := fullBlockNamedEquivalence N laws coarseAdequate chart_full edge_full face_full l
/-- plus 実 block の原始名付き同定。 -/
def plusBlockEquiv (l : LawValueLabel laws) := fullBlockNamedEquivalence plus laws fineAdequate plus_chart_full plus_edge_full plus_face_full l
/-- minus 実 block の原始名付き同定。 -/
def minusBlockEquiv (l : LawValueLabel laws) := fullBlockNamedEquivalence minus laws fineAdequate minus_chart_full minus_edge_full minus_face_full l
/-- 同じ rplus を独立実 block 生成に渡す。 -/
abbrev plusBlockHom (l : LawValueLabel laws) := rPlus.generatedBlockComparisonHom laws coarseAdequate fineAdequate l
/-- 同じ rminus を独立実 block 生成に渡す。 -/
abbrev minusBlockHom (l : LawValueLabel laws) := rMinus.generatedBlockComparisonHom laws coarseAdequate fineAdequate l
/-- 実 block の全三成分で uminus=jstar uplus。 -/
theorem block_composition (l : LawValueLabel laws) : minusBlockHom l =
    cochainComp (plusBlockHom l) (j.generatedBlockComparisonHom laws fineAdequate fineAdequate l) :=
  AAT.AG.FaceRelationSubdivision.generatedBlockComparisonHom_comp rPlus j laws l coarseAdequate fineAdequate fineAdequate
/-- 全 Law の同じ原始 rplus 独立生成。 -/
abbrev plusLawHom := rPlus.generatedComparisonHom laws coarseAdequate fineAdequate
/-- 全 Law の同じ原始 rminus 独立生成。 -/
abbrev minusLawHom := rMinus.generatedComparisonHom laws coarseAdequate fineAdequate
/-- 実全 Law の全三成分で uminus=jstar uplus。 -/
theorem law_composition : minusLawHom = cochainComp plusLawHom
    (j.generatedComparisonHom laws fineAdequate fineAdequate) :=
  AAT.AG.FaceRelationSubdivision.generatedComparisonHom_comp rPlus j laws coarseAdequate fineAdequate fineAdequate
/-- 原始名付き rplus 射。 -/
abbrev plusNamedHom := incidenceNamedHom rPlus
/-- 原始名付き rminus 射。 -/
abbrev minusNamedHom := incidenceNamedHom rMinus
/-- plus の同じ独立実射と名付き射の全三成分正方形。 -/
theorem plus_named_square (l : LawValueLabel laws) :
    cochainComp (plusBlockHom l) (plusBlockEquiv l).toHom = cochainComp (blockEquiv l).toHom plusNamedHom :=
  incidenceNamedHom_square rPlus laws coarseAdequate fineAdequate chart_full edge_full face_full
    plus_chart_full plus_edge_full plus_face_full l
/-- minus の同じ独立実射と名付き射の全三成分正方形。 -/
theorem minus_named_square (l : LawValueLabel laws) :
    cochainComp (minusBlockHom l) (minusBlockEquiv l).toHom = cochainComp (blockEquiv l).toHom minusNamedHom :=
  incidenceNamedHom_square rMinus laws coarseAdequate fineAdequate chart_full edge_full face_full
    minus_chart_full minus_edge_full minus_face_full l
end AAT.AG.FaceRelationSubdivision.WitnessOne
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessOne
