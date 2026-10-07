import ResearchLean.AG.FaceRelationSubdivision.FullSupportSubset
import ResearchLean.AG.FaceRelationSubdivision.SubsetComparison
import Formal.Util.AssertStandardAxioms
/-!
# 同じ混在比較の全非空 subset 正方形

## Implementation notes

subset 射を原始入力から独立に生成した後、全台セル選択の同型で名付き射へ接続する。
選択証明の一致をセル名から証明するので、期待 period や rank を入力しない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q r : Reading Source} {h : q.CoarserThan r}
variable {D : TargetSupportedNerve q} {E : TargetSupportedNerve r}
variable (M : IncidenceSupportedComparison q r h D E)
variable (hD : ∀ v, D.chartSupport v=Set.univ) (hE : ∀ v, E.chartSupport v=Set.univ)
variable (A : Set q.Target) (B : Set r.Target) (hA : A.Nonempty) (hB : B.Nonempty)
variable (hs : ∀ t, t∈B → comparisonFactor q r h t∈A)
/-- 同じ実 subset 射と名付き射の全三成分正方形。 -/
theorem fullSubsetNamed_square :
    cochainComp (M.targetSubsetComparisonHom A B hs) (fullSubsetNamedEquiv E hE B hB).toHom =
    cochainComp (fullSubsetNamedEquiv D hD A hA).toHom (incidenceNamedHom M) := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro z <;> funext x
  · rw [cochainComp_f0,cochainComp_f0,incidenceNamedHom_f0]
    let ec := fullSelected E.chartSupport hE B hB x
    have hc : M.targetSubsetChartMap A B hs ec=fullSelected D.chartSupport hD A hA (M.chartMap x) := by
      apply Subtype.ext
      exact M.targetSubsetChartMap_val A B hs ec
    exact (fullSubsetNamedEquiv_e0 E hE B hB _ x).trans
      ((M.targetSubsetPullback0_apply A B hs z ec).trans (congrArg z hc))
  · rw [cochainComp_f1,cochainComp_f1,incidenceNamedHom_f1]
    let ec := fullSelected E.edgeSupport (fullSupport_edge E hE) B hB x
    cases he : M.edgeMap x with
    | none =>
        simp only [Option.elim_none]
        have hh := M.targetSubsetPullback1_apply A B hs z ec
        rw [M.targetSubsetEdgeMapOption_eq_none A B hs ec he] at hh
        exact (fullSubsetNamedEquiv_e1 E hE B hB _ x).trans hh
    | some c =>
        simp only [Option.elim_some]
        have hc : M.targetSubsetEdgeMap A B hs ec c he =
            fullSelected D.edgeSupport (fullSupport_edge D hD) A hA c := by
          apply Subtype.ext
          exact M.targetSubsetEdgeMap_val A B hs ec c he
        have hh := M.targetSubsetPullback1_apply A B hs z ec
        rw [M.targetSubsetEdgeMapOption_eq_some A B hs ec c he] at hh
        exact (fullSubsetNamedEquiv_e1 E hE B hB _ x).trans (hh.trans (congrArg z hc))
  · rw [cochainComp_f2,cochainComp_f2,incidenceNamedHom_f2]
    let ec := fullSelected E.faceSupport (fullSupport_face E hE) B hB x
    cases he : M.faceMap x with
    | none =>
        simp only [Option.elim_none]
        have hh := M.targetSubsetPullback2_apply A B hs z ec
        rw [M.targetSubsetFaceMapOption_eq_none A B hs ec he] at hh
        exact (fullSubsetNamedEquiv_e2 E hE B hB _ x).trans hh
    | some c =>
        simp only [Option.elim_some]
        have hc : M.targetSubsetFaceMap A B hs ec c he =
            fullSelected D.faceSupport (fullSupport_face D hD) A hA c := by
          apply Subtype.ext
          exact M.targetSubsetFaceMap_val A B hs ec c he
        have hh := M.targetSubsetPullback2_apply A B hs z ec
        rw [M.targetSubsetFaceMapOption_eq_some A B hs ec c he] at hh
        exact (fullSubsetNamedEquiv_e2 E hE B hB _ x).trans (hh.trans (congrArg z hc))
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
