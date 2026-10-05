import ResearchLean.AG.AtlasDefectComposition.SupportStageProjections
import ResearchLean.AG.AtlasDefectComposition.SubsetComparisonNaturality
import Formal.Util.AssertStandardAxioms
/-! # 全段署名の同じ台制限と実比較

Implementation notes: 各段への逆像を先に固定して既存生成手続きを適用する。
各対の canonical A-subnerve との同定も全三次数の transport で述べる。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SupportStages
open CanonicalResolution ResolutionInvariance TwoPhase
universe u v w
variable {Source : Type u} {base : Reading Source} {I : Type v}
variable (q : I → Reading Source) (N : ∀ i, TargetSupportedNerve.{u,w} (q i))
variable (h : ∀ i, base.CoarserThan (q i)) (i j : I) (hij : (q i).CoarserThan (q j))
/-- 同じ基底 subset の各逆像は原始比較因子に沿って適合する。 -/
theorem pair_mapsTo (A : Set base.Target) (a : (q j).Target)
    (ha : a ∈ comparisonFactor base (q j) (h j) ⁻¹' A) :
    comparisonFactor (q i) (q j) hij a ∈ comparisonFactor base (q i) (h i) ⁻¹' A := by
  change comparisonFactor base (q i) (h i) (comparisonFactor (q i) (q j) hij a) ∈ A
  rw [factor_pair q h i j hij]
  exact ha
variable (M : TargetSupportedNerveMorphism (q i) (q j) hij (N i) (N j))
/-- 同じ全段逆像族から独立に生成する各対の実比較。 -/
def pairComparison (A : Set base.Target) : ThreeCochainComplex.Hom (stageComplex q N h A i) (stageComplex q N h A j) :=
  M.targetSubsetComparisonHom _ _ (pair_mapsTo q h i j hij A)
/-- 実各対比較は各対の A-subnerve の全三次数を同定したものである。 -/
theorem pairComparison_canonical (A : Set base.Target) :
    transportHom (congrArg (N j).targetSubsetComplex (pair_preimage q h i j hij A))
      (M.aSubnerveComparisonHom (comparisonFactor base (q i) (h i) ⁻¹' A)) =
      pairComparison q N h i j hij M A :=
  targetSubsetComparisonHom_transport M _ _ _ (pair_preimage q h i j hij A) (fun _ ht => ht) _
variable {A B : Set base.Target} (hAB : alpha q N h A ⊆ alpha q N h B)
/-- 各対の実比較は全段共通署名の同じ台制限と可換する。 -/
theorem pairComparison_square :
    cochainComp (pairComparison q N h i j hij M B) (stageRestriction q N h hAB j) =
      cochainComp (stageRestriction q N h hAB i) (pairComparison q N h i j hij M A) :=
  SubsetComparisonNaturality.comparison_square (N i) (N j) hij M
    (stageLE q N h hAB i) (stageLE q N h hAB j)
    (pair_mapsTo q h i j hij A) (pair_mapsTo q h i j hij B)
/-- 各対の実旧 H¹ 商は全段共通署名の台制限と可換する。 -/
theorem pairH1_square (x : (stageComplex q N h B i).H1) :
    (stageRestriction q N h hAB j).h1Map ((pairComparison q N h i j hij M B).h1Map x) =
      (pairComparison q N h i j hij M A).h1Map ((stageRestriction q N h hAB i).h1Map x) := by
  have hh := congrArg (fun f => f.h1Map x) (pairComparison_square q N h i j hij M hAB)
  simpa only [cochainComp_h1Map,LinearMap.comp_apply] using hh
end AAT.AG.AtlasDefectComposition.SupportStages
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportStages
