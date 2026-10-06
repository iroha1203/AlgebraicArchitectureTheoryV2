import ResearchLean.AG.FaceRelationSubdivision.SubsetComparison
import ResearchLean.AG.FaceRelationSubdivision.GeneratedComposition
import Formal.Util.AssertStandardAxioms

/-!
# 旧hereditary比較への全成分特殊化

G-134 A・Dの旧比較との接続。新比較を旧型へ戻す操作は使わず、
旧入力からの埋め込みで全計算成分を直接照合する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : TargetSupportedNerveMorphism qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc) (hf : laws.Adequate qf)

/-- 埋め込み後の全ラベルの実成分Homは旧生成Homと一致する。 -/
theorem ofHereditary_generatedBlockComparisonHom [Fintype Source] (label : LawValueLabel laws) :
    (IncidenceSupportedComparison.ofHereditary M).generatedBlockComparisonHom laws hc hf label =
      M.generatedBlockComparisonHom laws hc hf label := by
  apply cochain_ext <;> rfl

/-- 埋め込み後の成分H¹商写像は旧生成写像と一致する。 -/
theorem ofHereditary_generatedBlockComparisonH1Map [Fintype Source] (label : LawValueLabel laws) :
    (IncidenceSupportedComparison.ofHereditary M).generatedBlockComparisonH1Map laws hc hf label =
      M.generatedBlockComparisonH1Map laws hc hf label := by
  change ((IncidenceSupportedComparison.ofHereditary M).generatedBlockComparisonHom laws hc hf label).h1Map = _
  rw [ofHereditary_generatedBlockComparisonHom]
  rfl

/-- 任意の支持部分集合の新生成Homは旧subset比較と一致する。 -/
theorem ofHereditary_targetSubsetComparisonHom (Ac : Set qc.Target) (Af : Set qf.Target)
    (hs : ∀ t, t ∈ Af → comparisonFactor qc qf h t ∈ Ac) :
    (IncidenceSupportedComparison.ofHereditary M).targetSubsetComparisonHom Ac Af hs =
      M.targetSubsetComparisonHom Ac Af hs := by
  apply cochain_ext <;> rfl

/-- 全Aの逆像での同じ比較への特殊化。 -/
theorem ofHereditary_aSubnerveComparisonHom (A : Set qc.Target) :
    (IncidenceSupportedComparison.ofHereditary M).aSubnerveComparisonHom A =
      M.aSubnerveComparisonHom A := by
  apply cochain_ext <;> rfl

/-- 全Aの既存H¹商でも同じ旧比較になる。 -/
theorem ofHereditary_aSubnerveComparisonHom_h1Map (A : Set qc.Target) :
    ((IncidenceSupportedComparison.ofHereditary M).aSubnerveComparisonHom A).h1Map =
      (M.aSubnerveComparisonHom A).h1Map := by
  rw [ofHereditary_aSubnerveComparisonHom]

/-- 実Law fiberの全三次数の射も旧比較へ特殊化する。 -/
theorem ofHereditary_labelFiberComparisonHom [Fintype Source] (label : LawValueLabel laws) :
    (IncidenceSupportedComparison.ofHereditary M).labelFiberComparisonHom laws hc hf label =
      M.labelFiberComparisonHom laws hc hf label := by
  apply cochain_ext <;> rfl

/-- 旧原始恒等の埋め込みは新原始恒等である。 -/
theorem ofHereditary_identity (q : Reading Source) (N : TargetSupportedNerve q) :
    IncidenceSupportedComparison.ofHereditary (TargetSupportedNerveMorphism.identityMorphism q N) =
      IncidenceSupportedComparison.identity q N := by
  apply IncidenceSupportedComparison.ext <;> rfl

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
