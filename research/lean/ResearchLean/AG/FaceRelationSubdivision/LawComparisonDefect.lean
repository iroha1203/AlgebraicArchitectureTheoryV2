import ResearchLean.AG.FaceRelationSubdivision.LawComparisonDecomposition
import ResearchLean.AG.AtlasDefectComposition.FiniteDefectFamily
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology

/-!
# 新混在比較の同じ実Law核・余核・欠損分解

## Implementation notes

独立生成した全Law射とラベル射の可換式から実核と実余核の同値を作る。
次元式はこの実同値の帰結として導く。
次元式だけを置く案は実核・実余核の写像を供給しないため採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : IncidenceSupportedComparison q r h N E) (hr : laws.Adequate r)
/-- 既存実H¹のLaw分解と、独立生成した全block比較の族との可換式。 -/
theorem lawH1Comparison_square (x : (N.lawGeneratedComplex laws ha).H1) :
    lawH1FamilyEquiv E laws hr (M.generatedComparisonH1Map laws ha hr x) =
      FiniteLinearFamily.map (fun l => M.generatedBlockComparisonH1Map laws ha hr l)
        (lawH1FamilyEquiv N laws ha x) := by
  funext l
  exact M.lawH1Family_natural laws ha hr x l
/-- 全Law既存実H¹比較の核を、全発生ラベルの実核へ同定する。 -/
def lawH1KernelFamilyEquiv : LinearMap.ker (M.generatedComparisonH1Map laws ha hr) ≃ₗ[ℚ]
    ((l : LawValueLabel laws) → LinearMap.ker (M.generatedBlockComparisonH1Map laws ha hr l)) :=
  (LinearConjugation.kernelEquiv _ _ (lawH1FamilyEquiv N laws ha)
    (lawH1FamilyEquiv E laws hr) (lawH1Comparison_square N E laws ha M hr)).trans
      (FiniteLinearFamily.kernelEquiv _)
/-- 全Law既存実H¹比較の余核を、全発生ラベルの実余核へ同定する。 -/
def lawH1CokernelFamilyEquiv :
    ((E.lawGeneratedComplex laws hr).H1 ⧸ LinearMap.range (M.generatedComparisonH1Map laws ha hr)) ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (E.lawValueBlockComplex laws hr l).H1 ⧸
        LinearMap.range (M.generatedBlockComparisonH1Map laws ha hr l)) :=
  (LinearConjugation.cokernelEquiv _ _ (lawH1FamilyEquiv N laws ha)
    (lawH1FamilyEquiv E laws hr) (lawH1Comparison_square N E laws ha M hr)).trans
      (FiniteLinearFamily.cokernelEquiv _)
/-- 核同定は同じ実H¹の各ラベル成分を読む。 -/
@[simp] theorem lawH1KernelFamilyEquiv_val
    (x : LinearMap.ker (M.generatedComparisonH1Map laws ha hr)) (l : LawValueLabel laws) :
    (lawH1KernelFamilyEquiv N E laws ha M hr x l).val =
      lawH1FamilyEquiv N laws ha x.val l := rfl
/-- 余核同定は同じ実H¹代表元の各ラベル商類を読む。 -/
@[simp] theorem lawH1CokernelFamilyEquiv_mk (x : (E.lawGeneratedComplex laws hr).H1)
    (l : LawValueLabel laws) : lawH1CokernelFamilyEquiv N E laws ha M hr
      ((LinearMap.range (M.generatedComparisonH1Map laws ha hr)).mkQ x) l =
        (LinearMap.range (M.generatedBlockComparisonH1Map laws ha hr l)).mkQ
          (lawH1FamilyEquiv E laws hr x l) := by
  dsimp only [lawH1CokernelFamilyEquiv,LinearEquiv.trans_apply]
  rw [LinearConjugation.cokernelEquiv_mk,FiniteLinearFamily.cokernelEquiv_mk]
/-- 二つのLaw欠損は、全発生ラベルを重複込みで足した値である。 -/
theorem lawH1Defect_sum : blockDefect (M.generatedComparisonH1Map laws ha hr) =
    (∑ l, (blockDefect (M.generatedBlockComparisonH1Map laws ha hr l)).1,
      ∑ l, (blockDefect (M.generatedBlockComparisonH1Map laws ha hr l)).2) := by
  apply Prod.ext
  · simp only [blockDefect_kernel_dimension]
    rw [(lawH1KernelFamilyEquiv N E laws ha M hr).finrank_eq]
    exact Module.finrank_pi_fintype ℚ
  · simp only [blockDefect_cokernel_dimension]
    rw [(lawH1CokernelFamilyEquiv N E laws ha M hr).finrank_eq]
    exact Module.finrank_pi_fintype ℚ
/-- 標準homologyの全次数について同じ実Law比較の核を分解する。 -/
def lawStandardKernelFamilyEquiv (m : ℤ) :
    LinearMap.ker (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → LinearMap.ker
        (homologyMap (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m).hom) :=
  (LinearConjugation.kernelEquiv _ _ (lawStandardHomologyEquiv N laws ha m)
    (lawStandardHomologyEquiv E laws hr m) (by
      intro x;funext l;exact M.lawStandardHomology_natural laws ha hr m x l)).trans
        (FiniteLinearFamily.kernelEquiv _)
/-- 標準homologyの全次数について同じ実Law比較の余核を分解する。 -/
def lawStandardCokernelFamilyEquiv (m : ℤ) :
    ((zeroExtension (E.lawGeneratedComplex laws hr)).homology m ⧸ LinearMap.range
      (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom) ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (zeroExtension (E.lawValueBlockComplex laws hr l)).homology m ⧸
        LinearMap.range (homologyMap
          (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m).hom) :=
  (LinearConjugation.cokernelEquiv _ _ (lawStandardHomologyEquiv N laws ha m)
    (lawStandardHomologyEquiv E laws hr m) (by
      intro x;funext l;exact M.lawStandardHomology_natural laws ha hr m x l)).trans
        (FiniteLinearFamily.cokernelEquiv _)
/-- 標準homology核の同定も同じ実source類の各成分を読む。 -/
@[simp] theorem lawStandardKernelFamilyEquiv_val (m : ℤ)
    (x : LinearMap.ker (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom)
    (l : LawValueLabel laws) : (lawStandardKernelFamilyEquiv N E laws ha M hr m x l).val =
      lawStandardHomologyEquiv N laws ha m x.val l := rfl
/-- 標準homology余核の同定も同じ実target代表元の各商類を読む。 -/
@[simp] theorem lawStandardCokernelFamilyEquiv_mk (m : ℤ)
    (x : (zeroExtension (E.lawGeneratedComplex laws hr)).homology m) (l : LawValueLabel laws) :
    lawStandardCokernelFamilyEquiv N E laws ha M hr m
      ((LinearMap.range (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom).mkQ x) l =
        (LinearMap.range (homologyMap (zeroExtensionMap
          (M.generatedBlockComparisonHom laws ha hr l)) m).hom).mkQ
            (lawStandardHomologyEquiv E laws hr m x l) := by
  dsimp only [lawStandardCokernelFamilyEquiv,LinearEquiv.trans_apply]
  rw [LinearConjugation.cokernelEquiv_mk,FiniteLinearFamily.cokernelEquiv_mk]
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
