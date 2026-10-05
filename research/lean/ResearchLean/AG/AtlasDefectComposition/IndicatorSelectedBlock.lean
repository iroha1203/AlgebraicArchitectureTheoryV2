import ResearchLean.AG.AtlasDefectComposition.LawFiberDecomposition
import ResearchLean.AG.UniformInvariance.IndicatorLawFamily
import Formal.Util.AssertStandardAxioms
/-! # 非空台の指示Lawのselected true blockの実現

Implementation notes: G-107の指示Lawの実true labelと両fiber等号を使う。Law全体にある補集合blockと区別して、selected blockの複体・錐だけを指定Aへ同定する。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source] {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (M : TargetSupportedNerveMorphism q r h N E) (A : Set q.Target) (hA : A.Nonempty)
/-- 指示Lawのselected true blockだけが指定した非空Aの実複体を実現する。 -/
def indicatorSelectedZeroExtensionIso :
    zeroExtension (N.lawValueBlockComplex (indicatorLawFamily q A)
      (indicatorLawFamily_adequate q A) (indicatorLawFamilyTrueLabel q A hA)) ≅
        zeroExtension (N.targetSubsetComplex A) :=
  lawBlockSelectedSubsetZeroExtensionIso N _ _ _ A (indicatorLawFamily_trueFiber_eq q A hA)
/-- selected true blockの実比較錐は、Aとそのcanonical逆像の実比較錐である。 -/
def indicatorSelectedConeIso :
    mappingCone (zeroExtensionMap (M.generatedBlockComparisonHom (indicatorLawFamily q A)
      (indicatorLawFamily_adequate q A) (indicatorLawFamily_adequate_of_coarserThan q r h A)
      (indicatorLawFamilyTrueLabel q A hA))) ≅
    mappingCone (zeroExtensionMap (M.aSubnerveComparisonHom A)) :=
  lawBlockSelectedSubsetConeIso N E _ _ M _ _ A _
    (indicatorLawFamily_trueFiber_eq q A hA)
    (indicatorLawFamily_trueFineFiber_eq_preimage q r h A hA) (fun _ ht => ht)
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
