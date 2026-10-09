import ResearchLean.AG.AtlasCoefficientFiber.FaceCloneLaw
import ResearchLean.AG.AtlasCoefficientFiber.PhiInterval
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFullSupport
import ResearchLean.AG.FaceRelationSubdivision.WitnessThreeDiagnostics

/-!
# W4：G134の同じ面複製と原Λ・P・二射・H²

Implementation notes: 原N/F=()の同じ比較を使う。Λの二liftとη対角を原Kanで
計算し、元fresh差の非零類を原H²余核へ移す。全Aの非選択場合も同じ表で扱う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication
open CategoryTheory Limits HomologicalComplex CochainComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
open FaceRelationSubdivision.WitnessThree (N fine comparison)
open ConnectedFaceWitness (q laws adequate)

/-- 固定原Fの選択は非空Aから元全台で導く。 -/
theorem face_selected (A : Set Bool) (hA : A.Nonempty) : ∃ t, t ∈ N.faceSupport () ∧ t ∈ A := by
  obtain ⟨t,ht⟩ := hA
  exact ⟨t, by rw [FaceRelationSubdivision.WitnessThree.face_full]; exact Set.mem_univ _, ht⟩
/-- 原FのΛ二liftは旧F/freshFの別名を保持する。 -/
def lambdaEquiv (A : Set Bool) (F : N.FaceInTargetSubset A) : LambdaFace comparison A F ≃ Bool where
  toFun f := match f.1.1 with | .inl _ => false | .inr _ => true
  invFun b := by
    have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := F.2; exact ⟨t,ha⟩
    refine ⟨fullSelected fine.faceSupport FaceRelationSubdivision.WitnessThree.fine_face_full _
      (by simpa only [comparisonFactor_self, Set.preimage_id_eq] using hA)
      (if b then .inr PUnit.unit else .inl ()), ?_⟩
    cases b <;> exact congrArg some (Subsingleton.elim _ _)
  left_inv f := by
    apply Subtype.ext; apply Subtype.ext
    rcases h : f.1.1 with G | u
    · cases G; simp [h, fullSelected]
    · cases u; simp [h, fullSelected]
  right_inv b := by cases b <;> rfl
/-- 原右Kan面係数の二座標は同じΛ全liftから生成する。 -/
def faceCoefficientEquiv (A : Set Bool) (F : N.FaceInTargetSubset A) :
    (pushforwardCoefficients comparison A).obj (.face F) ≃ₗ[ℚ] (Bool → ℚ) :=
  (lambdaCoefficientEquiv comparison A F).trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : LambdaFace comparison A F => ℚ) (lambdaEquiv A F))
/-- 元η面成分は同じ値を旧/freshの両方へ置く対角。 -/
theorem eta_face_diagonal (A : Set Bool) (F : N.FaceInTargetSubset A) (r : ℚ) :
    faceCoefficientEquiv A F
      (coefficientConstant (Carrier.preimageFunctor comparison A) (.face F) r) = fun _ => r := by
  funext b
  exact lambdaCoefficientConstant_apply comparison A F r _

/-- 全mappedの同じ原L0は零。 -/
theorem L0_zero (A : Set Bool) : degenerateL0 comparison A = ⊥ := FaceClone.L0_zero N () A
/-- 全mappedの同じ原L1は零。 -/
theorem L1_zero (A : Set Bool) : degenerateL1 comparison A = ⊥ := FaceClone.L1_zero N () A
/-- 全mappedの同じ原L2は零。 -/
theorem L2_zero (A : Set Bool) : degenerateL2 comparison A = ⊥ := FaceClone.L2_zero N () A
/-- 原Pの同じ評価を細cochainへ全三次数で両逆同定する。 -/
def pFineIso (A : Set Bool) := FaceClone.coefficientStandardIso N () A
/-- この全次数同定の順写像は元εと自己reading輸送。 -/
theorem pFineIso_hom (A : Set Bool) : (pFineIso A).hom =
    zeroExtensionMap (evaluationHom comparison A) ≫ (FaceClone.fineStandardIso N () A).hom :=
  FaceClone.coefficientStandardIso_hom N () A
/-- 同じ元η・εは元G134の独立比較と全次数で可換。 -/
theorem unit_square (A : Set Bool) :
    zeroExtensionMap (unitHom comparison A) ≫ (pFineIso A).hom =
      zeroExtensionMap (FaceDuplication.subsetHom N () A) := FaceClone.unit_standard_square N () A
/-- 原aは元H¹保存と元ε同定から全Aで両方向同型。 -/
def unitEquiv (A : Set Bool) := FaceClone.unitEquiv N () A
/-- 同じ両逆の順値は原aそのもの。 -/
theorem unitEquiv_apply (A : Set Bool) (x) : unitEquiv A x = unitH1 comparison A x :=
  FaceClone.unitEquiv_apply N () A x
/-- 同じ独立原比較のH¹診断は全Aで零。 -/
theorem defect_zero (A : Set Bool) : blockDefect (comparison.aSubnerveComparisonHom A).h1Map = (0,0) :=
  FaceClone.defect_zero N () A
/-- mapped粗loopを含めない元ΦのH¹は零。 -/
theorem phiH1_zero (A : Set Bool) (c : N.ChartInTargetSubset A) : Subsingleton (phiComplex comparison A c).H1 :=
  FaceClone.phiH1_zero N () A c
/-- 原κの全値も同じΦ双対から零。 -/
theorem kappa_zero (A : Set Bool) : kappa comparison A = 0 :=
  kappa_zero_of_phiH1_zero comparison A (phiH1_zero A)
/-- 同じ原κ*は全原Φ H¹零から零。 -/
theorem kappaStar_zero (A : Set Bool) : kappaStar comparison A = 0 := by
  letI (c : N.ChartInTargetSubset A) := phiH1_zero A c
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
/-- literal原Rは全Aで零。 -/
theorem R_zero (A : Set Bool) : Subsingleton (R comparison A) := FaceClone.R_zero N () A
/-- 原標準接続射τは全Aで零。 -/
theorem tau_zero (A : Set Bool) : connectingTau comparison A = 0 := FaceClone.tau_zero N () A

/-- 非空Aの同じ原H²比較余核は元fresh差を読んでℚ。 -/
def h2CokernelEquiv (A : Set Bool) (hA : A.Nonempty) :=
  FaceClone.nativeH2CokernelEquiv N () A (face_selected A hA)
/-- 非空Aの同じ原総錐H²は元比較錐との両逆からℚ。 -/
def totalConeH2Equiv (A : Set Bool) (hA : A.Nonempty) :=
  FaceClone.totalConeH2Equiv N () A (face_selected A hA)
/-- 元fresh面だけ1の代表を同じcanonical原H²余核へ移す。 -/
def freshClass (A : Set Bool) := FaceClone.nativeFreshCokernelClass N () A
/-- 同じ原差periodにおけるfresh類の値は1。 -/
theorem fresh_period (A : Set Bool) (hA : A.Nonempty) : h2CokernelEquiv A hA (freshClass A) = 1 :=
  FaceClone.nativeFreshCokernelClass_value N () A (face_selected A hA)
/-- 同じ元H²余核のfresh類は非零。 -/
theorem fresh_nonzero (A : Set Bool) (hA : A.Nonempty) : freshClass A ≠ 0 :=
  FaceClone.nativeFreshCokernelClass_nonzero N () A (face_selected A hA)
/-- 同じ非空Aの総錐H²は一次元。H¹保存から錐全体零を推論しない。 -/
theorem totalConeH2_dimension (A : Set Bool) (hA : A.Nonempty) :
    Module.finrank ℚ ((totalCone comparison A).homology (2 : ℤ)) = 1 := by
  rw [(totalConeH2Equiv A hA).finrank_eq]
  exact Module.finrank_self ℚ
/-- 空Aの同じ原総錐は全整数次数零。 -/
theorem empty_totalCone_zero (n : ℤ) : IsZero ((totalCone comparison ∅).homology n) :=
  FaceClone.absent_totalCone_zero N () ∅ (by simp) n
/-- 同じ原εのfiber錐は全A全次数零。 -/
theorem fiberCone_zero (A : Set Bool) (n : ℤ) : IsZero ((fiberCone comparison A).homology n) :=
  FaceClone.fiberCone_zero N () A n

/-- 同じ元二Lawラベルの原a両逆。 -/
def lawUnitEquiv := FaceClone.lawUnitEquiv N () laws adequate
/-- 同じ原全LawのH¹比較診断は零。 -/
theorem law_defect_zero : blockDefect (comparison.generatedComparisonHom laws adequate
    (lawFineAdequate (h := Reading.coarserThan_refl q) laws adequate)).h1Map = (0,0) :=
  FaceClone.lawDefect_zero N () laws adequate
/-- 同じ原全Law literal Rは零。 -/
theorem law_R_zero : Subsingleton (lawR comparison laws adequate) := FaceClone.lawR_zero N () laws adequate
/-- 同じ原全Law標準τは零。 -/
theorem law_tau_zero : lawConnectingTau comparison laws adequate = 0 := FaceClone.lawTau_zero N () laws adequate
/-- 同じ原全Law総錐H²の元ラベルを保持する座標。 -/
def lawTotalH2Equiv := FaceClone.lawTotalH2Equiv N () laws adequate
/-- 同じG134二発生ラベルのH²余核・総錐は二つのfresh差を個別に保持する。 -/
def lawH2CokernelEquiv := FaceClone.lawH2CokernelEquiv N () laws adequate

/-- 同じ原FはG134の全発生ラベルで選択される。ラベルは同定しない。 -/
def selectedLabelEquiv : FaceClone.SelectedLabel N () laws adequate ≃ LawValueLabel laws where
  toFun := Subtype.val
  invFun l := ⟨l, FaceRelationSubdivision.WitnessThree.face_selected l⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- 原選択族座標を元の二発生ラベル族へ両方向同定する。 -/
def selectedCoefficientEquiv : (FaceClone.SelectedLabel N () laws adequate → ℚ) ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ : FaceClone.SelectedLabel N () laws adequate => ℚ) selectedLabelEquiv
/-- 同じ原全Law総錐H²は元二labelの差periodでℚ²。 -/
def lawTotalH2PairEquiv := lawTotalH2Equiv.trans
  (selectedCoefficientEquiv.trans FaceRelationSubdivision.WitnessThree.labelPairEquiv)
/-- 同じ原全Law H²比較余核も二つのfresh差でℚ²。 -/
def lawH2CokernelPairEquiv := lawH2CokernelEquiv.trans
  (selectedCoefficientEquiv.trans FaceRelationSubdivision.WitnessThree.labelPairEquiv)
/-- 同じ全Law総錐H²は二次元。 -/
theorem lawTotalH2_dimension : Module.finrank ℚ ((lawTotalCone comparison laws adequate).homology (2 : ℤ)) = 2 := by
  rw [lawTotalH2PairEquiv.finrank_eq]
  simp only [Module.finrank_prod, Module.finrank_self]

/-- 同じ非空Aの旧H¹k period座標。 -/
def oldHPeriod (A : Set Bool) (hA : A.Nonempty) : (N.targetSubsetComplex A).H1 ≃ₗ[ℚ] ℚ :=
  (fullSubsetNamedEquiv N FaceRelationSubdivision.WitnessThree.chart_full A hA).h1Equiv.trans
    FaceRelationSubdivision.WitnessThree.namedH1Equiv
/-- 原kだけ1の閉cochainを同じ元subset商へ移す。 -/
def oldHClass (A : Set Bool) (hA : A.Nonempty) : (N.targetSubsetComplex A).H1 :=
  (fullSubsetNamedEquiv N FaceRelationSubdivision.WitnessThree.chart_full A hA).h1Equiv.symm
    ((LinearMap.range (namedComplex N).boundaryToCycles).mkQ
      (FaceRelationSubdivision.WitnessThree.loopOnly 1))
/-- 原k代表の同じperiodは1。 -/
theorem old_h_period (A : Set Bool) (hA : A.Nonempty) : oldHPeriod A hA (oldHClass A hA) = 1 := by
  dsimp only [oldHPeriod, oldHClass, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply, FaceRelationSubdivision.WitnessThree.namedH1Equiv_mk]
  rfl
/-- 同じ元k代表は全非空Aで非零。 -/
theorem old_h_nonzero (A : Set Bool) (hA : A.Nonempty) : oldHClass A hA ≠ 0 := by
  intro hh
  have he := congrArg (oldHPeriod A hA) hh
  rw [old_h_period, map_zero] at he
  exact one_ne_zero he
/-- 独立原uが同じ旧k代表を送るfine実H¹類。 -/
def fineHClass (A : Set Bool) (hA : A.Nonempty) := (comparison.aSubnerveComparisonHom A).h1Map (oldHClass A hA)
/-- 同じ保存された原k類は全非空Aで非零。 -/
theorem fine_h_nonzero (A : Set Bool) (hA : A.Nonempty) : fineHClass A hA ≠ 0 := by
  intro hh
  apply old_h_nonzero A hA
  have hi := ((blockDefect_eq_zero_iff_bijective _).mp (defect_zero A)).1
  exact hi (hh.trans (map_zero _).symm)

/-- 原η2の全値は元Λ二lift上で同じ粗面値。 -/
theorem eta2_values (A : Set Bool) (z : (N.targetSubsetComplex A).C2) (F : N.FaceInTargetSubset A) :
    faceCoefficientEquiv A F (unit2 comparison A z F) = fun _ => z F := eta_face_diagonal A F (z F)
/-- 同じ元P評価座標では原εは全次数の恒等を実現する。 -/
theorem epsilon_coordinates_identity (A : Set Bool) :
    (pFineIso A).inv ≫ zeroExtensionMap (evaluationHom comparison A) ≫
      (FaceClone.fineStandardIso N () A).hom = 𝟙 _ := by
  rw [← pFineIso_hom, Iso.inv_hom_id]
/-- 同じ原面複製Law κは全元labelの原κ零から零。 -/
theorem law_kappa_zero : lawKappa comparison laws adequate = 0 := by
  apply LinearMap.ext
  intro x
  funext l
  rw [lawKappa_apply, kappa_zero, LinearMap.zero_apply]
  rfl
/-- 同じ原面複製Law κ*も全元labelの原κ*零から零。 -/
theorem law_kappaStar_zero : lawKappaStar comparison laws adequate = 0 := by
  apply LinearMap.ext
  intro x
  funext l
  rw [lawKappaStar_apply, kappaStar_zero, LinearMap.zero_apply]
  rfl
end AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.face_selected
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.lambdaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.faceCoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.eta_face_diagonal
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.L0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.L1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.L2_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.pFineIso
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.pFineIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.unit_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.unitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.unitEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.defect_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.phiH1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.h2CokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.totalConeH2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.freshClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.fresh_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.fresh_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.totalConeH2_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.empty_totalCone_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.fiberCone_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.lawUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.law_defect_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.law_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.law_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.lawTotalH2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.lawH2CokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.selectedLabelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.selectedCoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.lawTotalH2PairEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.lawH2CokernelPairEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.lawTotalH2_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.oldHPeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.oldHClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.old_h_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.old_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.fineHClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.fine_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.eta2_values
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.epsilon_coordinates_identity
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.law_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication.law_kappaStar_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourDuplication
