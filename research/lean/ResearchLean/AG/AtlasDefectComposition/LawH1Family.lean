import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonNaturality
import Formal.Util.AssertStandardAxioms

/-! # 既存H¹のLaw直和の成分API

既存の有限直和同定・生成写像の自然性を、全発生ラベルを保持する関数表示へ戻す。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase DirectSum
universe u
variable {Source : Type u} [Fintype Source]

/-- 既存の全Law実H¹を、全発生ラベルの実H¹族へ同定する。 -/
def lawH1FamilyEquiv {q : Reading Source} (D : TargetSupportedNerve q)
    (laws : FiniteLawFamily Source) (ha : laws.Adequate q) :
    (D.lawGeneratedComplex laws ha).H1 ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (D.lawValueBlockComplex laws ha l).H1) :=
  (D.lawGeneratedH1BlockEquiv laws ha).trans
    (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
      (fun l => (D.lawValueBlockComplex laws ha l).H1))

/-- 関数表示の各成分も、原始比較から生成した実block写像で作用する。 -/
theorem lawH1FamilyMap_component {q r : Reading Source} {h : q.CoarserThan r}
    {D : TargetSupportedNerve q} {E : TargetSupportedNerve r}
    (M : TargetSupportedNerveMorphism q r h D E)
    (laws : FiniteLawFamily Source) (hq : laws.Adequate q) (hr : laws.Adequate r)
    (x : (D.lawGeneratedComplex laws hq).H1) (l : LawValueLabel laws) :
    lawH1FamilyEquiv E laws hr (M.generatedComparisonH1Map laws hq hr x) l =
      M.generatedBlockComparisonH1Map laws hq hr l (lawH1FamilyEquiv D laws hq x l) := by
  have hh := congrArg (fun f => f x) (M.generatedComparisonH1Map_block_naturality laws hq hr)
  have hc := congrArg (fun s => (DirectSum.linearEquivFunOnFintype ℚ (LawValueLabel laws)
    (fun l => (E.lawValueBlockComplex laws hr l).H1)) s l) hh
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TargetSupportedNerveMorphism.generatedBlockComparisonH1DirectSumMap_component] using hc

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
