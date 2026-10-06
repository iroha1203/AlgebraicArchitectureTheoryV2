import ResearchLean.AG.FaceRelationSubdivision.HereditarySpecialization
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonFiberDiagnostics
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteDecomposition

/-!
# 旧hereditary実射への新分解APIの特殊化

## Implementation notes

原始旧比較を新比較へ埋め込んだ後、受理済み全三成分等号で射を置き換える。
対象同値だけを用いる案は、分解する比較射を固定しないため採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)

/-- 新クラスの三成分Law自然性は同じ旧生成Law/block比較に特殊化する。 -/
theorem hereditary_lawFamily_square :
    cochainComp (M.generatedComparisonHom laws ha hr) (lawFamilyCochainEquiv E laws hr).toHom =
      cochainComp (lawFamilyCochainEquiv N laws ha).toHom
        (ThreeComplexFamily.map (fun l => N.lawValueBlockComplex laws ha l)
          (fun l => E.lawValueBlockComplex laws hr l)
          (fun l => M.generatedBlockComparisonHom laws ha hr l)) := by
  have hs := (IncidenceSupportedComparison.ofHereditary M).lawFamily_square laws ha hr
  simpa only [ofHereditary_generatedComparisonHom, ofHereditary_generatedBlockComparisonHom] using hs

/-- 新クラスの全次数のLaw正方形は同じ旧実射へ特殊化する。 -/
theorem hereditary_lawZeroExtension_square :
    zeroExtensionMap (M.generatedComparisonHom laws ha hr) ≫ (lawZeroExtensionIso E laws hr).hom =
      (lawZeroExtensionIso N laws ha).hom ≫
        FiniteComplexFamily.map (fun l => zeroExtension (N.lawValueBlockComplex laws ha l))
          (fun l => zeroExtension (E.lawValueBlockComplex laws hr l))
          (fun l => zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) := by
  have hs := (IncidenceSupportedComparison.ofHereditary M).lawZeroExtension_square laws ha hr
  simpa only [ofHereditary_generatedComparisonHom, ofHereditary_generatedBlockComparisonHom] using hs

/-- 新クラスの実H1欠損分解は同じ旧原始fiber比較の欠損分解に特殊化する。 -/
theorem hereditary_lawH1Defect_subset_sum : blockDefect (M.generatedComparisonH1Map laws ha hr) =
    (∑ l, (blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)).h1Map).1,
      ∑ l, (blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)).h1Map).2) := by
  have hs := lawH1Defect_subset_sum N E laws ha (IncidenceSupportedComparison.ofHereditary M) hr
  simpa only [ofHereditary_generatedComparisonH1Map, ofHereditary_aSubnerveComparisonHom] using hs

/-- 新クラスから得た実錐同型の両端は同じ旧Law/fiber比較錐である。 -/
def hereditary_lawSubsetConeFamilyIso : mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) ≅
    FiniteComplexFamily.complex (fun l => mappingCone (zeroExtensionMap
      (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)))) := by
  have hi := lawSubsetConeFamilyIso N E laws ha (IncidenceSupportedComparison.ofHereditary M) hr
  simpa only [ofHereditary_generatedComparisonHom, ofHereditary_aSubnerveComparisonHom] using hi

/-- この同じ旧実比較の錐の全整数次数を同じ原始fiber錐に読む。 -/
def hereditary_lawSubsetConeHomologyEquiv (m : ℤ) :
    (mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (mappingCone (zeroExtensionMap
        (M.aSubnerveComparisonHom (labelValueFiber laws q ha l)))).homology m) :=
  (homologyMapIso (hereditary_lawSubsetConeFamilyIso N E laws ha M hr) m).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ m)

/-- 特殊化した同じ錐同型からの実projectionを各homology成分に使う。 -/
theorem hereditary_lawSubsetConeHomologyEquiv_component (m : ℤ)
    (x : (mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m)
    (l : LawValueLabel laws) : hereditary_lawSubsetConeHomologyEquiv N E laws ha M hr m x l =
      homologyMap ((hereditary_lawSubsetConeFamilyIso N E laws ha M hr).hom ≫
        FiniteComplexFamily.projection _ l) m x := by
  rw [hereditary_lawSubsetConeHomologyEquiv, LinearEquiv.trans_apply,
    FiniteComplexFamily.homologyEquiv_component, homologyMap_comp]
  rfl

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
