import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationHomology
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonFiberDiagnostics
import Formal.Util.AssertStandardAxioms

/-!
# 面複製の独立実Law比較

## Implementation notes

原始新比較から既存CellCoordinate/Law微分で独立生成した全LawとblockのHomを使う。
C9の全三成分正方形を通して同じ実subset射と同定し、H¹の逆と選択面のH²余核を読む。
Law比較をsubset同型の共役で定義する方式は採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 原始比較から独立に生成した同じ全Law三項Hom。 -/
def lawHom : ThreeCochainComplex.Hom (N.lawGeneratedComplex laws ha)
    ((supported N F).lawGeneratedComplex laws ha) :=
  (comparison N F).generatedComparisonHom laws ha ha
/-- 原始比較から独立に生成した同じラベル三項Hom。 -/
def blockHom (l : LawValueLabel laws) : ThreeCochainComplex.Hom
    (N.lawValueBlockComplex laws ha l) ((supported N F).lawValueBlockComplex laws ha l) :=
  (comparison N F).generatedBlockComparisonHom laws ha ha l
/-- 新比較の独立block射は旧hereditary生成と全三成分で同じ射。 -/
theorem blockHom_eq_hereditary (l : LawValueLabel laws) :
    blockHom N F laws ha l = (collapse N F).generatedBlockComparisonHom laws ha ha l := by
  rw [blockHom, comparison_eq_ofHereditary, ofHereditary_generatedBlockComparisonHom]
/-- 全三成分の実block/fiber正方形に同じ原始subset比較が現れる。 -/
theorem block_subset_square (l : LawValueLabel laws) :
    cochainComp (blockHom N F laws ha l)
      ((supported N F).lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom =
    cochainComp (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom
      (subsetHom N F (labelValueFiber laws q ha l)) :=
  lawBlockFiber_comparison_square N (supported N F) laws ha (comparison N F) ha l
/-- 任意発生ラベルで同じ実H¹比較を読む線形同値。 -/
def blockH1Equiv (l : LawValueLabel laws) :
    (N.lawValueBlockComplex laws ha l).H1 ≃ₗ[ℚ] ((supported N F).lawValueBlockComplex laws ha l).H1 :=
  (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).h1Equiv.trans
    ((subsetH1Equiv N F (labelValueFiber laws q ha l)).trans
      ((supported N F).lawValueBlockTargetSubsetComplexEquiv laws ha l).h1Equiv.symm)
/-- ラベルH¹同値の正方向は同じ独立実block比較。 -/
theorem blockH1Equiv_toLinearMap (l : LawValueLabel laws) :
    (blockH1Equiv N F laws ha l).toLinearMap = (blockHom N F laws ha l).h1Map := by
  apply LinearMap.ext
  intro x
  apply ((supported N F).lawValueBlockTargetSubsetComplexEquiv laws ha l).h1Equiv.injective
  simp only [blockH1Equiv, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact (labelFiberH1_natural N (supported N F) laws ha (comparison N F) ha l x).symm
/-- 同じ全Law実比較から得るH¹同値。ラベルを個別に保つ。 -/
def lawH1Equiv : (N.lawGeneratedComplex laws ha).H1 ≃ₗ[ℚ]
    ((supported N F).lawGeneratedComplex laws ha).H1 :=
  (lawH1FamilyEquiv N laws ha).trans
    ((LinearEquiv.piCongrRight (fun l => blockH1Equiv N F laws ha l)).trans
      (lawH1FamilyEquiv (supported N F) laws ha).symm)
/-- 全LawH¹同値の正方向は同じ独立実Law比較。 -/
theorem lawH1Equiv_toLinearMap :
    (lawH1Equiv N F laws ha).toLinearMap = (lawHom N F laws ha).h1Map := by
  apply LinearMap.ext
  intro x
  apply (lawH1FamilyEquiv (supported N F) laws ha).injective
  funext l
  simp only [lawH1Equiv, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.piCongrRight_apply]
  have h := congrArg (fun f => f (lawH1FamilyEquiv N laws ha x l))
    (blockH1Equiv_toLinearMap N F laws ha l)
  exact h.trans ((comparison N F).lawH1Family_natural laws ha ha x l).symm

variable (l : LawValueLabel laws)
variable (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ labelValueFiber laws q ha l)
/-- 選択された元面を含む実blockの同じ標準錐H²はℚ。 -/
def blockConeH2Equiv : (comparisonCone (blockHom N F laws ha l)).homology 2 ≃ₗ[ℚ] ℚ :=
  (homologyMapIso (lawBlockSelectedSubsetConeIso N (supported N F) laws ha
    (comparison N F) ha l _ _ rfl rfl (subset_compatible (labelValueFiber laws q ha l))) 2).toLinearEquiv.trans
      (coneH2Equiv N F (labelValueFiber laws q ha l) hF)
/-- 同じ実block標準H²比較の余核はℚ。 -/
def blockStandardH2CokernelEquiv :
    ((zeroExtension ((supported N F).lawValueBlockComplex laws ha l)).homology 2 ⧸
      LinearMap.range (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) 2).hom) ≃ₗ[ℚ] ℚ :=
  (comparisonConeHTwoEquiv (blockHom N F laws ha l)).symm.trans (blockConeH2Equiv N F laws ha l hF)
/-- 同じ実blockの元のH²商射の余核も標準自然性からℚになる。 -/
def blockOldH2CokernelEquiv :
    ((((supported N F).lawValueBlockComplex laws ha l).C2 ⧸
      LinearMap.range ((supported N F).lawValueBlockComplex laws ha l).d1) ⧸
      LinearMap.range (oldH2Map (blockHom N F laws ha l))) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv (oldH2Map (blockHom N F laws ha l))
    (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) 2).hom
    (oldH2Equiv (N.lawValueBlockComplex laws ha l))
    (oldH2Equiv ((supported N F).lawValueBlockComplex laws ha l))
    (oldH2Equiv_natural (blockHom N F laws ha l))).trans
      (blockStandardH2CokernelEquiv N F laws ha l hF)
omit l hF in
/-- 全ラベルが元面を選択する場合、同じ全Law錐H²はラベルを保ったℚ族。 -/
def lawConeH2Equiv
    (hAll : ∀ l : LawValueLabel laws, ∃ t, t ∈ N.faceSupport F ∧ t ∈ labelValueFiber laws q ha l) :
    (comparisonCone (lawHom N F laws ha)).homology 2 ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawConeHomologyEquiv N (supported N F) laws ha (comparison N F) ha 2).trans
    (LinearEquiv.piCongrRight (fun l => blockConeH2Equiv N F laws ha l (hAll l)))
omit l hF in
/-- 全ラベル選択時、同じ全Law標準H²比較の実余核はラベルごとのℚ。 -/
def lawStandardH2CokernelEquiv
    (hAll : ∀ l : LawValueLabel laws, ∃ t, t ∈ N.faceSupport F ∧ t ∈ labelValueFiber laws q ha l) :
    ((zeroExtension ((supported N F).lawGeneratedComplex laws ha)).homology 2 ⧸
      LinearMap.range (homologyMap (zeroExtensionMap (lawHom N F laws ha)) 2).hom) ≃ₗ[ℚ]
        (LawValueLabel laws → ℚ) :=
  (comparisonConeHTwoEquiv (lawHom N F laws ha)).symm.trans (lawConeH2Equiv N F laws ha hAll)

end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
