import ResearchLean.AG.AtlasDefectComposition.LawCochainDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 実Law零延長と全発生ラベル族の自然な同定

Implementation notes: 三次数の実Law同値を零延長し、全整数次数で同じ実block比較へ接続する。標準homologyには同じ複体同型とprojectionを通す。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source]
variable {q : Reading Source} (N : TargetSupportedNerve q)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
/-- 全Law零延長を、同じ全ラベルの実block零延長の有限族へ同定する。 -/
def lawZeroExtensionIso : zeroExtension (N.lawGeneratedComplex laws ha) ≅
    FiniteComplexFamily.complex (fun l => zeroExtension (N.lawValueBlockComplex laws ha l)) :=
  cochainEquivZeroExtensionIso (lawFamilyCochainEquiv N laws ha) ≪≫
    ThreeComplexFamily.zeroExtensionIso (fun l => N.lawValueBlockComplex laws ha l)
variable {r : Reading Source} {h : q.CoarserThan r} {E : TargetSupportedNerve r}
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 全三成分の比較正方形は既存の独立block生成式から成立する。 -/
theorem lawFamily_comparison_square :
    cochainComp (M.generatedComparisonHom laws ha hr) (lawFamilyCochainEquiv E laws hr).toHom =
      cochainComp (lawFamilyCochainEquiv N laws ha).toHom
        (ThreeComplexFamily.map (fun l => N.lawValueBlockComplex laws ha l)
          (fun l => E.lawValueBlockComplex laws hr l)
          (fun l => M.generatedBlockComparisonHom laws ha hr l)) := by
  apply cochain_ext
  · apply LinearMap.ext;intro x;funext l
    exact lawFamily_natural0 N laws ha M hr x l
  · apply LinearMap.ext;intro x;funext l
    exact lawFamily_natural1 N laws ha M hr x l
  · apply LinearMap.ext;intro x;funext l
    exact lawFamily_natural2 N laws ha M hr x l
/-- Law零延長の同型は、全次数で実比較と実block族比較を接続する。 -/
theorem lawZeroExtensionIso_natural :
    zeroExtensionMap (M.generatedComparisonHom laws ha hr) ≫ (lawZeroExtensionIso E laws hr).hom =
      (lawZeroExtensionIso N laws ha).hom ≫
        FiniteComplexFamily.map (fun l => zeroExtension (N.lawValueBlockComplex laws ha l))
          (fun l => zeroExtension (E.lawValueBlockComplex laws hr l))
          (fun l => zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) := by
  have hs := congrArg zeroExtensionMap (lawFamily_comparison_square N laws ha M hr)
  rw [zeroExtensionMap_comp,zeroExtensionMap_comp] at hs
  dsimp only [lawZeroExtensionIso,Iso.trans_hom]
  rw [cochainEquivZeroExtensionIso_hom,cochainEquivZeroExtensionIso_hom]
  rw [← Category.assoc,hs,Category.assoc,ThreeComplexFamily.zeroExtensionIso_natural]
  simp only [Category.assoc]
/-- 全Lawの各次数homologyを実blockの同次数homology族へ読む。 -/
def lawStandardHomologyEquiv (m : ℤ) :
    (zeroExtension (N.lawGeneratedComplex laws ha)).homology m ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (zeroExtension (N.lawValueBlockComplex laws ha l)).homology m) :=
  (homologyMapIso (lawZeroExtensionIso N laws ha) m).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ m)
/-- 標準homologyの全整数次数で実Law比較と成分実比較が可換である。 -/
theorem lawStandardHomologyEquiv_natural (m : ℤ)
    (x : (zeroExtension (N.lawGeneratedComplex laws ha)).homology m) (l : LawValueLabel laws) :
    lawStandardHomologyEquiv E laws hr m
        (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m x) l =
      homologyMap (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m
        (lawStandardHomologyEquiv N laws ha m x l) := by
  have hs := congrArg (fun (f : zeroExtension (N.lawGeneratedComplex laws ha) ⟶
      FiniteComplexFamily.complex (fun l => zeroExtension (E.lawValueBlockComplex laws hr l))) =>
      homologyMap f m) (lawZeroExtensionIso_natural N laws ha M hr)
  simp only [homologyMap_comp] at hs
  have hx := congrArg (fun f => f x) hs
  dsimp only [lawStandardHomologyEquiv,LinearEquiv.trans_apply]
  change FiniteComplexFamily.homologyEquiv _ m
    ((homologyMapIso (lawZeroExtensionIso E laws hr) m).hom
      (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m x)) l =
      homologyMap (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m
        (FiniteComplexFamily.homologyEquiv _ m
          ((homologyMapIso (lawZeroExtensionIso N laws ha) m).hom x) l)
  rw [show (homologyMapIso (lawZeroExtensionIso E laws hr) m).hom
      (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m x) =
        homologyMap (FiniteComplexFamily.map
          (fun l => zeroExtension (N.lawValueBlockComplex laws ha l))
          (fun l => zeroExtension (E.lawValueBlockComplex laws hr l))
          (fun l => zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l))) m
          ((homologyMapIso (lawZeroExtensionIso N laws ha) m).hom x) from hx]
  exact FiniteComplexFamily.homologyEquiv_natural _ _ _ m _ l
/-- 全次数homology族の成分は同じ実零延長同型からのprojectionである。 -/
theorem lawStandardHomologyEquiv_component_family (m : ℤ)
    (x : (zeroExtension (N.lawGeneratedComplex laws ha)).homology m) (l : LawValueLabel laws) :
    lawStandardHomologyEquiv N laws ha m x l =
      homologyMap ((lawZeroExtensionIso N laws ha).hom ≫ FiniteComplexFamily.projection _ l) m x := by
  dsimp only [lawStandardHomologyEquiv,LinearEquiv.trans_apply]
  rw [FiniteComplexFamily.homologyEquiv_component,homologyMap_comp]
  rfl
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
