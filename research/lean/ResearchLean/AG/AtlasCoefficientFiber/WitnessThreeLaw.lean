import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeTransgression
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreePairedFiber
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeCones
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeRankTable
import ResearchLean.AG.AtlasCoefficientFiber.LawHomologyCoordinates
import ResearchLean.AG.AtlasCoefficientFiber.LawDefectDiagnostics
import ResearchLean.AG.AtlasCoefficientFiber.LawCoefficientCones
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonFiberDiagnostics

/-!
# G-135 W3：二つの元Law発生成分

## Implementation notes

元非定数Lawの二labelを保ち、同原射の族自然性と商の両逆で計算する。
同台labelの商は発生重複度を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 原Law粗block全h座標。 -/
def coarseBlockCoordinates (l : LawValueLabel laws) :
    (Nc.lawValueBlockComplex laws adequate_coarse l).H1 ≃ₗ[ℚ] ℚ :=
  (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
    (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l).h1Equiv.trans coarseNamedCoordinates
/-- 面あり原Law細block全h座標。 -/
def fineBlockCoordinates (l : LawValueLabel laws) :
    (Nf.lawValueBlockComplex laws adequate_fine l).H1 ≃ₗ[ℚ] ℚ :=
  (fullBlockNamedEquivalence Nf laws adequate_fine (fun _ => rfl)
    (fullSupport_edge Nf (fun _ => rfl)) (fullSupport_face Nf (fun _ => rfl)) l).h1Equiv.trans fineNamedCoordinates
/-- mなし原Law細block全h/k座標。 -/
def pairedBlockCoordinates (l : LawValueLabel laws) :
    (pairedNf.lawValueBlockComplex laws adequate_fine l).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullBlockNamedEquivalence pairedNf laws adequate_fine (fun _ => rfl)
    (fullSupport_edge pairedNf (fun _ => rfl)) (fullSupport_face pairedNf (fun _ => rfl)) l).h1Equiv.trans pairedNamedCoordinates
/-- 面あり実Law block射は元全h類で恒等。 -/
theorem block_map (l : LawValueLabel laws) (x : (Nc.lawValueBlockComplex laws adequate_coarse l).H1) :
    fineBlockCoordinates l ((M.generatedBlockComparisonHom laws adequate_coarse adequate_fine l).h1Map x) = coarseBlockCoordinates l x := by
  have hs := incidenceNamedHom_square M laws adequate_coarse adequate_fine
    (fun _ => rfl) (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl))
    (fun _ => rfl) (fullSupport_edge Nf (fun _ => rfl)) (fullSupport_face Nf (fun _ => rfl)) l
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
      (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l)
    (fullBlockNamedEquivalence Nf laws adequate_fine (fun _ => rfl)
      (fullSupport_edge Nf (fun _ => rfl)) (fullSupport_face Nf (fun _ => rfl)) l)
    (M.generatedBlockComparisonHom laws adequate_coarse adequate_fine l) (incidenceNamedHom M)
    (fun z => congrArg (fun f => f.f1 z) hs) x
  exact (congrArg fineNamedCoordinates hh).trans (named_map _)
/-- mなし実Law block全元射は(h,0)。 -/
theorem paired_block_map (l : LawValueLabel laws) (x : (Nc.lawValueBlockComplex laws adequate_coarse l).H1) :
    pairedBlockCoordinates l ((pairedM.generatedBlockComparisonHom laws adequate_coarse adequate_fine l).h1Map x) =
      pairedCoordinateMap (coarseBlockCoordinates l x) := by
  have hs := incidenceNamedHom_square pairedM laws adequate_coarse adequate_fine
    (fun _ => rfl) (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl))
    (fun _ => rfl) (fullSupport_edge pairedNf (fun _ => rfl)) (fullSupport_face pairedNf (fun _ => rfl)) l
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
      (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l)
    (fullBlockNamedEquivalence pairedNf laws adequate_fine (fun _ => rfl)
      (fullSupport_edge pairedNf (fun _ => rfl)) (fullSupport_face pairedNf (fun _ => rfl)) l)
    (pairedM.generatedBlockComparisonHom laws adequate_coarse adequate_fine l) (incidenceNamedHom pairedM)
    (fun z => congrArg (fun f => f.f1 z) hs) x
  exact (congrArg pairedNamedCoordinates hh).trans (paired_named_map _)
/-- 同実全Law粗H¹の二label全座標。 -/
def coarseLawCoordinates := (lawH1FamilyEquiv Nc laws adequate_coarse).trans (LinearEquiv.piCongrRight coarseBlockCoordinates)
/-- 面あり全Law細H¹の二label全座標。 -/
def fineLawCoordinates := (lawH1FamilyEquiv Nf laws adequate_fine).trans (LinearEquiv.piCongrRight fineBlockCoordinates)
/-- mなし全Law細H¹の二label全h/k座標。 -/
def pairedLawCoordinates := (lawH1FamilyEquiv pairedNf laws adequate_fine).trans (LinearEquiv.piCongrRight pairedBlockCoordinates)
/-- 同実全Law射の全元・各元labelでの恒等式。 -/
theorem law_map (x : (Nc.lawGeneratedComplex laws adequate_coarse).H1) (l : LawValueLabel laws) :
    fineLawCoordinates (M.generatedComparisonH1Map laws adequate_coarse adequate_fine x) l = coarseLawCoordinates x l := by
  simp only [fineLawCoordinates,coarseLawCoordinates,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply]
  exact (congrArg (fineBlockCoordinates l) (M.lawH1Family_natural laws adequate_coarse adequate_fine x l)).trans (block_map l _)
/-- mなし同全Law射の全元・各元labelでの(h,0)。 -/
theorem paired_law_map (x : (Nc.lawGeneratedComplex laws adequate_coarse).H1) (l : LawValueLabel laws) :
    pairedLawCoordinates (pairedM.generatedComparisonH1Map laws adequate_coarse adequate_fine x) l = pairedCoordinateMap (coarseLawCoordinates x l) := by
  simp only [pairedLawCoordinates,coarseLawCoordinates,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply]
  exact (congrArg (pairedBlockCoordinates l) (pairedM.lawH1Family_natural laws adequate_coarse adequate_fine x l)).trans (paired_block_map l _)
/-- 面あり全実Law J00。 -/
theorem law_defect : blockDefect (M.generatedComparisonH1Map laws adequate_coarse adequate_fine) = (0,0) := by
  classical
  rw [lawH1Defect_subset_sum Nc Nf laws adequate_coarse M adequate_fine]
  have h (l : LawValueLabel laws) := defect (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l)
  simp only [h,Finset.sum_const,Finset.card_univ,labels_card]
  decide
/-- mなし全実Law J02、二つのkを保持。 -/
theorem paired_law_defect : blockDefect (pairedM.generatedComparisonH1Map laws adequate_coarse adequate_fine) = (0,2) := by
  classical
  rw [lawH1Defect_subset_sum Nc pairedNf laws adequate_coarse pairedM adequate_fine]
  have h (l : LawValueLabel laws) := paired_defect (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l)
  simp only [h,Finset.sum_const,Finset.card_univ,labels_card]
  decide
/-- 元Law producerの同J00。 -/
theorem primitive_law_J : primitiveLawDiagnostic M laws adequate_coarse = (0,0) :=
  (primitiveLawDiagnostic_eq_blockDefect M laws adequate_coarse).trans law_defect
/-- mなし原Law producerの同J02。 -/
theorem paired_primitive_law_J : primitiveLawDiagnostic pairedM laws adequate_coarse = (0,2) :=
  (primitiveLawDiagnostic_eq_blockDefect pairedM laws adequate_coarse).trans paired_law_defect
/-- mなし実全Law余核と二labelの同原k period族の両逆。 -/
def pairedLawCokernelCoordinates : ((pairedNf.lawGeneratedComplex laws adequate_fine).H1 ⧸
    LinearMap.range (pairedM.generatedComparisonH1Map laws adequate_coarse adequate_fine)) ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawH1CokernelFamilyEquiv Nc pairedNf laws adequate_coarse pairedM adequate_fine).trans
    (LinearEquiv.piCongrRight fun l => (LinearConjugation.cokernelEquiv _ pairedCoordinateMap
      (coarseBlockCoordinates l) (pairedBlockCoordinates l) (paired_block_map l)).trans coordinateCokernelEquiv)
/-- 同literal Law Rの独立k period二label座標。 -/
def lawRCoordinates : lawR M laws adequate_coarse ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawRFamilyEquiv M laws adequate_coarse).trans (LinearEquiv.piCongrRight fun l =>
    rawRCoordinates (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l))
/-- mなし同literal Law Rの二label全座標。 -/
def pairedLawRCoordinates : lawR pairedM laws adequate_coarse ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawRFamilyEquiv pairedM laws adequate_coarse).trans (LinearEquiv.piCongrRight fun l =>
    pairedRCoordinates (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l))
/-- 面あり元Law R次元2。 -/
theorem law_R_dimension : Module.finrank ℚ (lawR M laws adequate_coarse) = 2 := by
  rw [lawRCoordinates.finrank_eq]
  simp only [Module.finrank_pi,labels_card]
/-- mなし元Law R次元2。 -/
theorem paired_law_R_dimension : Module.finrank ℚ (lawR pairedM laws adequate_coarse) = 2 := by
  rw [pairedLawRCoordinates.finrank_eq]
  simp only [Module.finrank_pi,labels_card]
/-- 元P H²の二label原二面period座標。 -/
def lawPH2Coordinates := (lawPushforwardHomologyEquiv M laws adequate_coarse 2).trans
  (LinearEquiv.piCongrRight fun l => pH2Coordinates (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l))
/-- 全元・全labelの原標準Law τは独立k periodを同二面periodへ送る。 -/
theorem law_tau_coordinates (x : lawR M laws adequate_coarse) (l : LawValueLabel laws) :
    lawPH2Coordinates (lawConnectingTau M laws adequate_coarse x) l = lawRCoordinates x l := by
  change pH2Coordinates _ _ (lawPushforwardHomologyEquiv M laws adequate_coarse 2 (lawConnectingTau M laws adequate_coarse x) l) = _
  rw [lawConnectingTau_component,tau_period]
  rfl
/-- 元Law τは全単射、供給されたrankでなく各実射から生成。 -/
theorem law_tau_bijective : Function.Bijective (lawConnectingTau M laws adequate_coarse) := by
  constructor
  · intro x y hh
    apply lawRCoordinates.injective
    funext l
    rw [← law_tau_coordinates x l,← law_tau_coordinates y l,hh]
  · intro z
    refine ⟨lawRCoordinates.symm (lawPH2Coordinates z),?_⟩
    exact lawPH2Coordinates.injective (by funext l; rw [law_tau_coordinates,LinearEquiv.apply_symm_apply])
/-- 元Law τ全像rank2。 -/
theorem law_tau_rank : Module.finrank ℚ (LinearMap.range (lawConnectingTau M laws adequate_coarse)) = 2 := by
  rw [LinearMap.range_eq_top.mpr law_tau_bijective.2]
  have hd : Module.finrank ℚ ((zeroExtension (lawPushforwardComplex M laws adequate_coarse)).homology (2 : ℤ)) = 2 := by
    rw [lawPH2Coordinates.finrank_eq]
    simp only [Module.finrank_pi,labels_card]
  exact Submodule.topEquiv.finrank_eq.trans hd
/-- 同原Law κは各原forestから零。 -/
theorem law_kappa_zero : lawKappa M laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x; funext l
  rw [lawKappa_apply,kappa_zero,LinearMap.zero_apply]; rfl
/-- 同原Law κ*は各原forestから零。 -/
theorem law_kappaStar_zero : lawKappaStar M laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x; funext l
  rw [lawKappaStar_apply,kappaStar_zero,LinearMap.zero_apply]; rfl
/-- mなし同原Law κ零。 -/
theorem paired_law_kappa_zero : lawKappa pairedM laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x; funext l
  rw [lawKappa_apply,paired_kappa_zero,LinearMap.zero_apply]; rfl
/-- mなし同原Law κ*零。 -/
theorem paired_law_kappaStar_zero : lawKappaStar pairedM laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x; funext l
  rw [lawKappaStar_apply,paired_kappaStar_zero,LinearMap.zero_apply]; rfl
/-- mなし実Law τ零、同標準δ族から生成。 -/
theorem paired_law_tau_zero : lawConnectingTau pairedM laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x
  apply (lawPushforwardHomologyEquiv pairedM laws adequate_coarse 2).injective
  funext l
  rw [lawConnectingTau_component,paired_tau_zero]
  simp only [LinearMap.zero_apply,map_zero,Pi.zero_apply]
/-- mなし実Law τrank零。 -/
theorem paired_law_tau_rank : Module.finrank ℚ (LinearMap.range (lawConnectingTau pairedM laws adequate_coarse)) = 0 := by
  rw [paired_law_tau_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- 原Law k代表、元z/betaを二labelで保持。 -/
def lawRK : lawR M laws adequate_coarse := (lawRFamilyEquiv M laws adequate_coarse).symm
  (fun l => rK (labelValueFiber laws qc adequate_coarse l))
/-- 原Law k代表の独立periodは各1。 -/
theorem lawRK_period (l : LawValueLabel laws) : lawRCoordinates lawRK l = 1 := by
  simp only [lawRCoordinates,lawRK,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.piCongrRight_apply]
  exact rawRPeriod_rK _ _
/-- 元Law τは元k代表を両label二面period1へ送る。 -/
theorem law_tau_RK_period (l : LawValueLabel laws) : lawPH2Coordinates (lawConnectingTau M laws adequate_coarse lawRK) l = 1 := by
  rw [law_tau_coordinates,lawRK_period]
/-- 元Law k代表は非零。 -/
theorem lawRK_nonzero : lawRK ≠ 0 := by
  intro hh
  have he := congrArg (fun z => lawRCoordinates z (label false)) hh
  dsimp only at he
  rw [lawRK_period,map_zero] at he
  exact one_ne_zero he
/-- 原二labelの非零h粗類。 -/
def coarseLawH := coarseLawCoordinates.symm (fun _ => 1)
/-- 元面あり細h類。 -/
def fineLawH := fineLawCoordinates.symm (fun _ => 1)
/-- 元mなし細h類。 -/
def pairedLawH := pairedLawCoordinates.symm (fun _ => ![1,0])
/-- 元mなし細k類。 -/
def pairedLawK := pairedLawCoordinates.symm (fun _ => ![0,1])
/-- 元Law hは面ありでも保存される。 -/
theorem law_h_preserved : M.generatedComparisonH1Map laws adequate_coarse adequate_fine coarseLawH = fineLawH := by
  apply fineLawCoordinates.injective; funext l
  rw [law_map]
  simp only [coarseLawH,fineLawH,LinearEquiv.apply_symm_apply]
/-- 元Law hはmなしでも保存される。 -/
theorem paired_law_h_preserved : pairedM.generatedComparisonH1Map laws adequate_coarse adequate_fine coarseLawH = pairedLawH := by
  apply pairedLawCoordinates.injective; funext l
  rw [paired_law_map]
  simp only [coarseLawH,pairedLawH,LinearEquiv.apply_symm_apply]
  rfl
/-- 原粗二label h類は非零。 -/
theorem coarse_law_h_nonzero : coarseLawH ≠ 0 := by
  intro hh
  have he := congrArg coarseLawCoordinates hh
  rw [coarseLawH,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero (congrFun he (label false))
/-- 同原面あり細h類は非零。 -/
theorem fine_law_h_nonzero : fineLawH ≠ 0 := by
  intro hh
  have he := congrArg fineLawCoordinates hh
  rw [fineLawH,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero (congrFun he (label false))
/-- 同原mなし細h類は非零。 -/
theorem paired_law_h_nonzero : pairedLawH ≠ 0 := by
  intro hh
  have he := congrArg pairedLawCoordinates hh
  rw [pairedLawH,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero (congrFun (congrFun he (label false)) 0)
/-- mなし同実全余核座標は各元k値を読む。 -/
theorem pairedLawCokernelCoordinates_mk (x : (pairedNf.lawGeneratedComplex laws adequate_fine).H1) (l : LawValueLabel laws) :
    pairedLawCokernelCoordinates ((LinearMap.range (pairedM.generatedComparisonH1Map laws adequate_coarse adequate_fine)).mkQ x) l = pairedLawCoordinates x l 1 := by
  simp only [pairedLawCokernelCoordinates,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply,FaceRelationSubdivision.lawH1CokernelFamilyEquiv_mk]
  rfl
/-- 原mなしLaw k余核類は二labelともperiod1。 -/
theorem pairedLawK_period (l : LawValueLabel laws) :
    pairedLawCokernelCoordinates ((LinearMap.range (pairedM.generatedComparisonH1Map laws adequate_coarse adequate_fine)).mkQ pairedLawK) l = 1 := by
  rw [pairedLawCokernelCoordinates_mk]
  simp only [pairedLawK,LinearEquiv.apply_symm_apply]
  rfl
/-- 元mなしLaw k余核類は非零。 -/
theorem pairedLawK_nonzero : (LinearMap.range (pairedM.generatedComparisonH1Map laws adequate_coarse adequate_fine)).mkQ pairedLawK ≠ 0 := by
  intro hh
  have he := congrArg (fun z => pairedLawCokernelCoordinates z (label false)) hh
  dsimp only at he
  rw [pairedLawK_period,map_zero] at he
  exact one_ne_zero he
/-- 元Law G133相殺は零、rank2のτと区別。 -/
theorem law_cancellation_zero : DefectSequence.cancellation (lawUnitH1 M laws adequate_coarse) (lawEvaluationH1 M laws adequate_coarse) = 0 :=
  lawCoefficientCancellation_zero M laws adequate_coarse
/-- mなし元Law G133相殺も零。 -/
theorem paired_law_cancellation_zero : DefectSequence.cancellation (lawUnitH1 pairedM laws adequate_coarse) (lawEvaluationH1 pairedM laws adequate_coarse) = 0 :=
  lawCoefficientCancellation_zero pairedM laws adequate_coarse

/-- 元成分η全単射から元Lawη全単射を生成する族API。 -/
theorem lawUnit_bijective_of_components (N' : TargetSupportedNerve qf)
    (M' : IncidenceSupportedComparison qc qf coarser Nc N')
    (hu : ∀ A : Set Bool, Function.Bijective (unitH1 M' A)) :
    Function.Bijective (lawUnitH1 M' laws adequate_coarse) := by
  classical
  let g := FiniteLinearFamily.map (fun l : LawValueLabel laws => unitH1 M' (labelValueFiber laws qc adequate_coarse l))
  have hg : Function.Bijective g := by
    constructor
    · intro x y hh
      funext l
      exact (hu _).1 (congrFun hh l)
    · intro y
      choose x hx using fun l : LawValueLabel laws => (hu (labelValueFiber laws qc adequate_coarse l)).2 (y l)
      exact ⟨x,funext hx⟩
  apply (LinearConjugation.bijective_iff (lawUnitH1 M' laws adequate_coarse) g
    (lawCoarseHomologyEquiv (Nc := Nc) laws adequate_coarse 1)
    (lawPushforwardHomologyEquiv M' laws adequate_coarse 1) ?_).mpr hg
  intro x
  funext l
  exact lawUnit_homology_component M' laws adequate_coarse 1 x l
/-- 面あり元Law ηH¹は全単射。 -/
theorem law_unit_bijective : Function.Bijective (lawUnitH1 M laws adequate_coarse) :=
  lawUnit_bijective_of_components Nf M unit_bijective
/-- mなし元Law ηH¹も全単射。 -/
theorem paired_law_unit_bijective : Function.Bijective (lawUnitH1 pairedM laws adequate_coarse) :=
  lawUnit_bijective_of_components pairedNf pairedM allA_paired_unit_bijective
/-- 面あり元Law aの実欠損00。 -/
theorem law_unit_defect : blockDefect (lawUnitH1 M laws adequate_coarse) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr law_unit_bijective
/-- mなし元Law aの実欠損00。 -/
theorem paired_law_unit_defect : blockDefect (lawUnitH1 pairedM laws adequate_coarse) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr paired_law_unit_bijective
/-- 元Law κ*全像rank零。 -/
theorem law_kappaStar_rank : Module.finrank ℚ (LinearMap.range (lawKappaStar M laws adequate_coarse)) = 0 := by
  rw [law_kappaStar_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- mなし元Law κ*全像rank零。 -/
theorem paired_law_kappaStar_rank : Module.finrank ℚ (LinearMap.range (lawKappaStar pairedM laws adequate_coarse)) = 0 := by
  rw [paired_law_kappaStar_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- 同Law H¹Qのliteral R経由の二元k座標。 -/
def lawQCoordinates := (lawRestrictionHomologyREquiv M laws adequate_coarse).trans lawRCoordinates
/-- mなし同Law H¹Qも二元k座標と両逆。 -/
def pairedLawQCoordinates := (lawRestrictionHomologyREquiv pairedM laws adequate_coarse).trans pairedLawRCoordinates
/-- 独立Law総錐H¹と同じ原二面period二label族の両逆。 -/
def lawTotalConeH1Coordinates : (lawTotalCone M laws adequate_coarse).homology (1 : ℤ) ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  ((HomologicalComplex.homologyMapIso (lawTotalConeFamilyIso M laws adequate_coarse) 1).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ 1)).trans
      (LinearEquiv.piCongrRight fun l => totalConeH1Coordinates (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l))
/-- 元Law総錐H¹次元2。 -/
theorem law_totalConeH1_dimension : Module.finrank ℚ ((lawTotalCone M laws adequate_coarse).homology (1 : ℤ)) = 2 := by
  rw [lawTotalConeH1Coordinates.finrank_eq]
  simp only [Module.finrank_pi,labels_card]
/-- mなし元Law P H²は原各成分零から零。 -/
theorem pairedLawPH2_subsingleton : Subsingleton ((zeroExtension (lawPushforwardComplex pairedM laws adequate_coarse)).homology (2 : ℤ)) := by
  letI : ∀ l : LawValueLabel laws, Subsingleton ((zeroExtension (pushforwardComplex pairedM (labelValueFiber laws qc adequate_coarse l))).homology (2 : ℤ)) :=
    fun l => pairedPH2_subsingleton _ (labelValueFiber_nonempty laws qc adequate_coarse l)
  exact (lawPushforwardHomologyEquiv pairedM laws adequate_coarse 2).toEquiv.subsingleton_congr.mpr inferInstance

/-- 二元Law発生labelの原Phi Betti和。 -/
theorem law_phi_dimension_sum :
    letI := Fintype.ofFinite (LawValueLabel laws)
    ∑ l : LawValueLabel laws, (letI := Fintype.ofFinite (Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l));
      ∑ c : Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l),
        Module.finrank ℚ (phiComplex M (labelValueFiber laws qc adequate_coarse l) c).H1) = 2 := by
  classical
  letI := Fintype.ofFinite (LawValueLabel laws)
  simp only [phi_dimension_sum _ (labelValueFiber_nonempty laws qc adequate_coarse _),
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact (Fintype.card_congr labelEquiv).trans (by decide)
/-- mなしも同じ二元Law原Phi Betti和。 -/
theorem paired_law_phi_dimension_sum :
    letI := Fintype.ofFinite (LawValueLabel laws)
    ∑ l : LawValueLabel laws, (letI := Fintype.ofFinite (Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l));
      ∑ c : Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l),
        Module.finrank ℚ (phiComplex pairedM (labelValueFiber laws qc adequate_coarse l) c).H1) = 2 := by
  classical
  letI := Fintype.ofFinite (LawValueLabel laws)
  simp only [paired_phi_dimension_sum _ (labelValueFiber_nonempty laws qc adequate_coarse _),
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact (Fintype.card_congr labelEquiv).trans (by decide)
/-- 元Law H¹Q次元は同literal Rの二発生成分。 -/
theorem law_Q_dimension : Module.finrank ℚ ((zeroExtension (lawRestrictionComplex M laws adequate_coarse)).homology (1 : ℤ)) = 2 := by
  rw [lawQCoordinates.finrank_eq]
  simp only [Module.finrank_pi,labels_card]
/-- mなし元Law H¹Qも同じ二原発生成分。 -/
theorem paired_law_Q_dimension : Module.finrank ℚ ((zeroExtension (lawRestrictionComplex pairedM laws adequate_coarse)).homology (1 : ℤ)) = 2 := by
  rw [pairedLawQCoordinates.finrank_eq]
  simp only [Module.finrank_pi,labels_card]
/-- 原面ありLaw全rank行、同元二射・literal R・標準τ。 -/
theorem law_full_rank_table :
    blockDefect (lawUnitH1 M laws adequate_coarse) = (0,0) ∧
    Module.finrank ℚ (LinearMap.range (lawKappaStar M laws adequate_coarse)) = 0 ∧
    Module.finrank ℚ (lawR M laws adequate_coarse) = 2 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau M laws adequate_coarse)) = 2 ∧
    primitiveLawDiagnostic M laws adequate_coarse = (0,0) :=
  ⟨law_unit_defect,law_kappaStar_rank,law_R_dimension,law_tau_rank,primitive_law_J⟩
/-- 原mなしLaw全rank行、同二発生labelを保持。 -/
theorem paired_law_full_rank_table :
    blockDefect (lawUnitH1 pairedM laws adequate_coarse) = (0,0) ∧
    Module.finrank ℚ (LinearMap.range (lawKappaStar pairedM laws adequate_coarse)) = 0 ∧
    Module.finrank ℚ (lawR pairedM laws adequate_coarse) = 2 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau pairedM laws adequate_coarse)) = 0 ∧
    primitiveLawDiagnostic pairedM laws adequate_coarse = (0,2) :=
  ⟨paired_law_unit_defect,paired_law_kappaStar_rank,paired_law_R_dimension,paired_law_tau_rank,paired_primitive_law_J⟩

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fineBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.block_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_block_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fineLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.primitive_law_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_primitive_law_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawCokernelCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lawRCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawRCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lawPH2Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_tau_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_tau_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lawRK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lawRK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_tau_RK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lawRK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarseLawH
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fineLawH
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawH
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_h_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_h_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.coarse_law_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.fine_law_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawCokernelCoordinates_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_cancellation_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_cancellation_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lawUnit_bijective_of_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lawQCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawQCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lawTotalConeH1Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_totalConeH1_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLawPH2_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_Q_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_Q_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.law_full_rank_table
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_law_full_rank_table
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rawRCoordinates.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
