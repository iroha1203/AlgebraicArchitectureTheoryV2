import ResearchLean.AG.FaceRelationSubdivision.LawBlockComparison
import ResearchLean.AG.AtlasDefectComposition.LawStandardDecomposition
import ResearchLean.AG.AtlasDefectComposition.LawH1Family

/-!
# 同じ実Law射を全ラベル族の射へ接続する

## Implementation notes

一般bridgeでは成分可換式を方向仮定とし、新混在比較の原始生成式から
具体適用を放電する。対象同型と射の同定を分け、全三次数・旧商・全整数次数を保持する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q) (hr : laws.Adequate r)
namespace LawMapDecomposition
variable (f : ThreeCochainComplex.Hom (N.lawGeneratedComplex laws ha) (E.lawGeneratedComplex laws hr))
variable (fb : ∀ l : LawValueLabel laws,
  ThreeCochainComplex.Hom (N.lawValueBlockComplex laws ha l) (E.lawValueBlockComplex laws hr l))
variable (h0 : ∀ x l, lawFamily0Equiv E laws hr (f.f0 x) l = (fb l).f0 (lawFamily0Equiv N laws ha x l))
variable (h1 : ∀ x l, lawFamily1Equiv E laws hr (f.f1 x) l = (fb l).f1 (lawFamily1Equiv N laws ha x l))
variable (h2 : ∀ x l, lawFamily2Equiv E laws hr (f.f2 x) l = (fb l).f2 (lawFamily2Equiv N laws ha x l))

include h0 h1 h2 in
/-- 同じ実全Law射と各独立ラベル射の全三成分正方形。 -/
theorem family_square : cochainComp f (lawFamilyCochainEquiv E laws hr).toHom =
    cochainComp (lawFamilyCochainEquiv N laws ha).toHom
      (ThreeComplexFamily.map (fun l => N.lawValueBlockComplex laws ha l)
        (fun l => E.lawValueBlockComplex laws hr l) fb) := by
  apply cochain_ext
  · apply LinearMap.ext; intro x
    rw [cochainComp_f0, cochainComp_f0, lawFamilyCochainEquiv_f0, lawFamilyCochainEquiv_f0]
    funext l
    exact h0 x l
  · apply LinearMap.ext; intro x
    rw [cochainComp_f1, cochainComp_f1, lawFamilyCochainEquiv_f1, lawFamilyCochainEquiv_f1]
    funext l
    exact h1 x l
  · apply LinearMap.ext; intro x
    rw [cochainComp_f2, cochainComp_f2, lawFamilyCochainEquiv_f2, lawFamilyCochainEquiv_f2]
    funext l
    exact h2 x l

include h0 h1 h2 in
/-- 同じ全Law/ラベル射を既存標準零延長同型へ全次数で接続する。 -/
theorem zeroExtension_square : zeroExtensionMap f ≫ (lawZeroExtensionIso E laws hr).hom =
    (lawZeroExtensionIso N laws ha).hom ≫
      FiniteComplexFamily.map (fun l => zeroExtension (N.lawValueBlockComplex laws ha l))
        (fun l => zeroExtension (E.lawValueBlockComplex laws hr l)) (fun l => zeroExtensionMap (fb l)) := by
  have hs := congrArg zeroExtensionMap (family_square N E laws ha hr f fb h0 h1 h2)
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp] at hs
  rw [lawZeroExtensionIso_hom, lawZeroExtensionIso_hom,
    cochainEquivZeroExtensionIso_hom, cochainEquivZeroExtensionIso_hom]
  rw [← Category.assoc, hs, Category.assoc, ThreeComplexFamily.zeroExtensionIso_natural]
  simp only [Category.assoc]

include h0 h1 h2 in
/-- 標準全整数次数で同じLaw homology射は同じラベル射と可換。 -/
theorem standard_homology_natural (m : ℤ)
    (x : (zeroExtension (N.lawGeneratedComplex laws ha)).homology m) (l : LawValueLabel laws) :
    lawStandardHomologyEquiv E laws hr m (homologyMap (zeroExtensionMap f) m x) l =
      homologyMap (zeroExtensionMap (fb l)) m (lawStandardHomologyEquiv N laws ha m x l) := by
  have hs := congrArg (fun g => homologyMap g m) (zeroExtension_square N E laws ha hr f fb h0 h1 h2)
  simp only [homologyMap_comp] at hs
  have hx := congrArg (fun g => g x) hs
  simp only [ModuleCat.comp_apply] at hx
  rw [lawStandardHomologyEquiv_apply, lawStandardHomologyEquiv_apply]
  simp only [homologyMapIso_hom]
  rw [hx]
  exact FiniteComplexFamily.homologyEquiv_natural _ _ _ m _ l

include h1 in
/-- 同じdegree1成分可換性は既存H1商の同じラベル成分へ降りる。 -/
theorem h1_natural (x : (N.lawGeneratedComplex laws ha).H1) (l : LawValueLabel laws) :
    lawH1FamilyEquiv E laws hr (f.h1Map x) l =
      (fb l).h1Map (lawH1FamilyEquiv N laws ha x l) := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    change lawH1FamilyEquiv E laws hr
        (f.h1Map ((LinearMap.range (N.lawGeneratedComplex laws ha).boundaryToCycles).mkQ z)) l =
      (fb l).h1Map (lawH1FamilyEquiv N laws ha
        ((LinearMap.range (N.lawGeneratedComplex laws ha).boundaryToCycles).mkQ z) l)
    rw [ThreeCochainComplex.Hom.h1Map_mk, lawH1FamilyEquiv_mk_component,
      lawH1FamilyEquiv_mk_component, ThreeCochainComplex.Hom.h1Map_mk]
    apply congrArg (LinearMap.range (E.lawValueBlockComplex laws hr l).boundaryToCycles).mkQ
    apply Subtype.ext
    have he : ((N.lawGeneratedBlockCyclesEquiv laws ha z) l).val =
        lawFamily1Equiv N laws ha z.val l := by
      funext y
      rw [TargetSupportedNerve.lawGeneratedBlockCyclesEquiv_component_val, lawFamily1Equiv_apply]
    funext y
    simp only [ThreeCochainComplex.Hom.cyclesMap_apply,
      TargetSupportedNerve.lawGeneratedBlockCyclesEquiv_component_val]
    rw [he]
    have hn := congrArg (fun w => w y) (h1 z.val l)
    simpa only [lawFamily1Equiv_apply] using hn

end LawMapDecomposition

namespace IncidenceSupportedComparison
variable {N E} {h : q.CoarserThan r}
variable (M : IncidenceSupportedComparison q r h N E)
/-- 原始新比較の同じLaw次数0を同じ発生ラベル射に接続する。 -/
theorem lawFamily_natural0 (x : (N.lawGeneratedComplex laws ha).C0) (l : LawValueLabel laws) :
    lawFamily0Equiv E laws hr ((M.generatedComparisonHom laws ha hr).f0 x) l =
      (M.generatedBlockComparisonHom laws ha hr l).f0 (lawFamily0Equiv N laws ha x l) :=
  M.generatedPullback0_block_component laws ha hr x l
/-- 原始新比較の同じLaw次数1を同じ発生ラベル射に接続する。 -/
theorem lawFamily_natural1 (x : (N.lawGeneratedComplex laws ha).C1) (l : LawValueLabel laws) :
    lawFamily1Equiv E laws hr ((M.generatedComparisonHom laws ha hr).f1 x) l =
      (M.generatedBlockComparisonHom laws ha hr l).f1 (lawFamily1Equiv N laws ha x l) :=
  M.generatedPullback1_block_component laws ha hr x l
/-- 原始新比較の同じLaw次数2を同じ発生ラベル射に接続する。 -/
theorem lawFamily_natural2 (x : (N.lawGeneratedComplex laws ha).C2) (l : LawValueLabel laws) :
    lawFamily2Equiv E laws hr ((M.generatedComparisonHom laws ha hr).f2 x) l =
      (M.generatedBlockComparisonHom laws ha hr l).f2 (lawFamily2Equiv N laws ha x l) :=
  M.generatedPullback2_block_component laws ha hr x l

/-- 原始新比較が生成した同じ二系統のLaw/ラベル射の正方形。 -/
theorem lawFamily_square : cochainComp (M.generatedComparisonHom laws ha hr)
    (lawFamilyCochainEquiv E laws hr).toHom =
      cochainComp (lawFamilyCochainEquiv N laws ha).toHom
        (ThreeComplexFamily.map (fun l => N.lawValueBlockComplex laws ha l)
          (fun l => E.lawValueBlockComplex laws hr l)
          (fun l => M.generatedBlockComparisonHom laws ha hr l)) :=
  LawMapDecomposition.family_square N E laws ha hr _ _
    (M.lawFamily_natural0 laws ha hr) (M.lawFamily_natural1 laws ha hr) (M.lawFamily_natural2 laws ha hr)

/-- 新比較の同じLaw零延長射を全整数次数のラベル族射へ接続。 -/
theorem lawZeroExtension_square : zeroExtensionMap (M.generatedComparisonHom laws ha hr) ≫
    (lawZeroExtensionIso E laws hr).hom = (lawZeroExtensionIso N laws ha).hom ≫
      FiniteComplexFamily.map (fun l => zeroExtension (N.lawValueBlockComplex laws ha l))
        (fun l => zeroExtension (E.lawValueBlockComplex laws hr l))
        (fun l => zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) :=
  LawMapDecomposition.zeroExtension_square N E laws ha hr _ _
    (M.lawFamily_natural0 laws ha hr) (M.lawFamily_natural1 laws ha hr) (M.lawFamily_natural2 laws ha hr)

/-- 新比較の同じ標準homology射を全次数の全ラベルへ読む。 -/
theorem lawStandardHomology_natural (m : ℤ)
    (x : (zeroExtension (N.lawGeneratedComplex laws ha)).homology m) (l : LawValueLabel laws) :
    lawStandardHomologyEquiv E laws hr m
        (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m x) l =
      homologyMap (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m
        (lawStandardHomologyEquiv N laws ha m x l) :=
  LawMapDecomposition.standard_homology_natural N E laws ha hr _ _
    (M.lawFamily_natural0 laws ha hr) (M.lawFamily_natural1 laws ha hr) (M.lawFamily_natural2 laws ha hr) m x l

/-- 新比較の同じ実H1写像を既存ラベル商へ接続。 -/
theorem lawH1Family_natural (x : (N.lawGeneratedComplex laws ha).H1) (l : LawValueLabel laws) :
    lawH1FamilyEquiv E laws hr ((M.generatedComparisonHom laws ha hr).h1Map x) l =
      (M.generatedBlockComparisonHom laws ha hr l).h1Map (lawH1FamilyEquiv N laws ha x l) :=
  LawMapDecomposition.h1_natural N E laws ha hr _ _ (M.lawFamily_natural1 laws ha hr) x l

end IncidenceSupportedComparison
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
