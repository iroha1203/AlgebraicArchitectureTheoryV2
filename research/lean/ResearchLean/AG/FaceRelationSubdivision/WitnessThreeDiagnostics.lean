import ResearchLean.AG.FaceRelationSubdivision.WitnessThreePeriods
import ResearchLean.AG.FaceRelationSubdivision.WitnessThreeDegreeTwo
import Formal.Util.AssertStandardAxioms

/-!
# W3の同じ独立実Law比較の全評価

## Implementation notes

旧・細periodを独立実block比較の同じ三成分正方形へ接続する。
Eの一般構成に同じ原始F・Law fiberを渡し、錐と余核を二ラベルを保って読む。
全Lawで重複ラベルを集合として統合する表現は採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision.WitnessThree
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label labelEquiv)

/-- 各ラベルの旧実H¹を同じloop periodでℚへ送る。 -/
def blockH1Period (l : LawValueLabel laws) : (N.lawValueBlockComplex laws adequate l).H1 ≃ₗ[ℚ] ℚ :=
  (blockEquiv l).h1Equiv.trans namedH1Equiv
/-- 各ラベルの細実H¹を同じloop periodでℚへ送る。 -/
def fineBlockH1Period (l : LawValueLabel laws) : (fine.lawValueBlockComplex laws adequate l).H1 ≃ₗ[ℚ] ℚ :=
  (fineBlockEquiv l).h1Equiv.trans fineNamedH1Equiv
/-- 各ラベルの同じ独立実比較はperiod座標で恒等。 -/
theorem block_h1_identity (l : LawValueLabel laws) (x : (N.lawValueBlockComplex laws adequate l).H1) :
    fineBlockH1Period l ((FaceDuplication.blockHom N () laws adequate l).h1Map x) = blockH1Period l x := by
  have hs := named_square l
  have hn : ∀ z, (fineBlockEquiv l).e1 ((FaceDuplication.blockHom N () laws adequate l).f1 z) =
      (namedHom l).f1 ((blockEquiv l).e1 z) := by
    intro z
    have he := congrArg (fun f => f.f1 z) hs
    exact he
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply (blockEquiv l)
    (fineBlockEquiv l) (FaceDuplication.blockHom N () laws adequate l) (namedHom l) hn x
  exact (congrArg fineNamedH1Equiv hh).trans (named_h1_identity l _)
/-- 同じ旧loop単独1を実Law blockへ移した非零類。 -/
def blockLoopClass (l : LawValueLabel laws) : (N.lawValueBlockComplex laws adequate l).H1 :=
  (blockEquiv l).h1Equiv.symm ((LinearMap.range (namedComplex N).boundaryToCycles).mkQ (loopOnly 1))
/-- 同じ旧実loop類のperiodは1。 -/
@[simp] theorem blockLoopClass_period (l : LawValueLabel laws) : blockH1Period l (blockLoopClass l) = 1 := by
  simp only [blockH1Period, blockLoopClass, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    namedH1Equiv_mk]
  rfl
/-- 同じ旧実loop類は非零。 -/
theorem blockLoopClass_nonzero (l : LawValueLabel laws) : blockLoopClass l ≠ 0 := by
  intro hz
  have he := congrArg (blockH1Period l) hz
  rw [blockLoopClass_period, map_zero] at he
  exact one_ne_zero he
/-- 同じ実比較が保つ細loop類は非零。 -/
theorem mapped_blockLoopClass_nonzero (l : LawValueLabel laws) :
    (FaceDuplication.blockHom N () laws adequate l).h1Map (blockLoopClass l) ≠ 0 := by
  intro hz
  have he := congrArg (fineBlockH1Period l) hz
  rw [block_h1_identity, blockLoopClass_period, map_zero] at he
  exact one_ne_zero he
/-- 同じloop単独1を細実Law blockへ移した具体的な類。 -/
def fineBlockLoopClass (l : LawValueLabel laws) : (fine.lawValueBlockComplex laws adequate l).H1 :=
  (fineBlockEquiv l).h1Equiv.symm
    ((LinearMap.range (namedComplex fine).boundaryToCycles).mkQ (fineLoopOnly 1))
/-- 細側の同じloop類も同じperiodを持つ。 -/
@[simp] theorem fineBlockLoopClass_period (l : LawValueLabel laws) :
    fineBlockH1Period l (fineBlockLoopClass l) = 1 := by
  simp only [fineBlockH1Period, fineBlockLoopClass, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, fineNamedH1Equiv_mk]
  rfl
/-- 実際の比較は旧loop単独類を細側の同じloop単独類に送る。 -/
theorem mapped_blockLoopClass (l : LawValueLabel laws) :
    (FaceDuplication.blockHom N () laws adequate l).h1Map (blockLoopClass l) = fineBlockLoopClass l := by
  apply (fineBlockH1Period l).injective
  rw [block_h1_identity, blockLoopClass_period, fineBlockLoopClass_period]
/-- 各ラベルfiberは元のFを実際に選択する。 -/
theorem face_selected (l : LawValueLabel laws) : ∃ t, t ∈ N.faceSupport () ∧ t ∈ labelValueFiber laws q adequate l := by
  obtain ⟨a,ha⟩ := labelValueFiber_nonempty laws q adequate l
  exact ⟨a, by rw [face_full]; exact Set.mem_univ _, ha⟩
/-- Eの一般対照操作に同じ原始W3を渡した標準H²余核。 -/
def blockH2CokernelEquiv (l : LawValueLabel laws) :=
  FaceDuplication.blockStandardH2CokernelEquiv N () laws adequate l (face_selected l)
/-- Eの同じ比較の標準錐H²。 -/
def blockConeH2Equiv (l : LawValueLabel laws) :=
  FaceDuplication.blockConeH2Equiv N () laws adequate l (face_selected l)
/-- 全Lawで二つの元ラベルを保持する標準H²余核。 -/
def lawH2CokernelFamilyEquiv := FaceDuplication.lawStandardH2CokernelEquiv N () laws adequate face_selected
/-- 全Lawで二つの元ラベルを保持する同じ標準錐H²。 -/
def lawConeH2FamilyEquiv := FaceDuplication.lawConeH2Equiv N () laws adequate face_selected
/-- 二発生ラベルの有理値族を、順序false/trueのℚ²へ送る。 -/
def labelPairEquiv : (LawValueLabel laws → ℚ) ≃ₗ[ℚ] ℚ × ℚ where
  toFun z := (z (label false),z (label true))
  invFun z l := if labelEquiv l then z.2 else z.1
  left_inv z := by
    funext l
    have he := labelEquiv.symm_apply_apply l
    cases h : labelEquiv l <;> rw [h] at he <;>
      simpa only [h, Bool.false_eq_true, ↓reduceIte, ConnectedFaceWitness.labelEquiv_symm] using congrArg z he
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 全Lawの旧実H¹を元ラベル別のloop periodへ送る。 -/
def lawH1Period : (N.lawGeneratedComplex laws adequate).H1 ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawH1FamilyEquiv N laws adequate).trans (LinearEquiv.piCongrRight blockH1Period)
/-- 全Lawの細実H¹を同じ元ラベル別のloop periodへ送る。 -/
def fineLawH1Period : (fine.lawGeneratedComplex laws adequate).H1 ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawH1FamilyEquiv fine laws adequate).trans (LinearEquiv.piCongrRight fineBlockH1Period)
/-- 全Lawでも同じ独立生成H¹比較は二ラベルのperiodを個別に保つ。 -/
theorem law_h1_identity (x : (N.lawGeneratedComplex laws adequate).H1) :
    fineLawH1Period ((FaceDuplication.lawHom N () laws adequate).h1Map x) = lawH1Period x := by
  funext l
  simp only [fineLawH1Period, lawH1Period, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  have hn := comparison.lawH1Family_natural laws adequate adequate x l
  exact (congrArg (fineBlockH1Period l) hn).trans (block_h1_identity l _)
/-- 全Law旧H¹は二ラベルのloop periodによりℚ²。 -/
def lawH1PairEquiv := lawH1Period.trans labelPairEquiv
/-- 全Law細H¹も同じ二ラベルのloop periodによりℚ²。 -/
def fineLawH1PairEquiv := fineLawH1Period.trans labelPairEquiv
/-- 同じ全Law実生成旧複体の標準H²は零。 -/
theorem law_standardH2_subsingleton : Subsingleton ((zeroExtension (N.lawGeneratedComplex laws adequate)).homology 2) := by
  letI (l : LawValueLabel laws) : Subsingleton ((zeroExtension (N.lawValueBlockComplex laws adequate l)).homology 2) :=
    block_standardH2_subsingleton l
  exact (lawStandardHomologyEquiv N laws adequate 2).toEquiv.subsingleton
/-- 同じ全Law実生成細複体の標準H²は二つのラベルを保ったℚ²。 -/
def fineLawStandardH2PairEquiv : (zeroExtension (fine.lawGeneratedComplex laws adequate)).homology 2 ≃ₗ[ℚ] ℚ × ℚ :=
  (lawStandardHomologyEquiv fine laws adequate 2).trans
    ((LinearEquiv.piCongrRight fineBlockStandardH2Equiv).trans labelPairEquiv)
/-- 同じ全Law標準H²比較は零空間からの零射。 -/
theorem law_h2Map_zero : (homologyMap (zeroExtensionMap (FaceDuplication.lawHom N () laws adequate)) 2).hom = 0 := by
  letI := law_standardH2_subsingleton
  apply LinearMap.ext
  intro x
  rw [Subsingleton.elim x 0, map_zero]
  rfl
/-- 同じ全Law標準H²比較の実余核はℚ²。 -/
def lawH2CokernelPairEquiv := lawH2CokernelFamilyEquiv.trans labelPairEquiv
/-- 同じ全Law標準錐のH²はℚ²。 -/
def lawConeH2PairEquiv := lawConeH2FamilyEquiv.trans labelPairEquiv

end AAT.AG.FaceRelationSubdivision.WitnessThree
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessThree
