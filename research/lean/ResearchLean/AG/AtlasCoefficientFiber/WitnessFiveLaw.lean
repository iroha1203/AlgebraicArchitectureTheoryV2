import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveDiagnostics
import ResearchLean.AG.AtlasCoefficientFiber.LawFiberSequence
import ResearchLean.AG.AtlasCoefficientFiber.LawHomologyCoordinates
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonFiberDiagnostics

/-!
# G-135 W5：二発生labelの同原Law比較

## Implementation notes

同台の二labelを保持し、実族自然性によりη/ε/u/κ/τを各原射へ接続する。
同台を一成分へ商化する手法は指定Lawの重複度を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 同原Law block粗H¹のe/h全座標。 -/
def coarseBlockCoordinates (l : LawValueLabel laws) :
    (Nc.lawValueBlockComplex laws adequate_coarse l).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
    (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l).h1Equiv.trans coarseNamedCoordinates
/-- 同原Law block細H¹のe/h全座標。 -/
def fineBlockCoordinates (l : LawValueLabel laws) :
    (Nf.lawValueBlockComplex laws adequate_fine l).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullBlockNamedEquivalence Nf laws adequate_fine (fun _ => rfl)
    (fullSupport_edge Nf (fun _ => rfl)) (fullSupport_face Nf (fun _ => rfl)) l).h1Equiv.trans fineNamedCoordinates
/-- 同実Law block比較は全元e/h恒等。 -/
theorem block_map (l : LawValueLabel laws) (x : (Nc.lawValueBlockComplex laws adequate_coarse l).H1) :
    fineBlockCoordinates l ((M.generatedBlockComparisonHom laws adequate_coarse adequate_fine l).h1Map x) =
      coarseBlockCoordinates l x := by
  have hs := incidenceNamedHom_square M laws adequate_coarse adequate_fine
    (fun _ => rfl) (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl))
    (fun _ => rfl) (fullSupport_edge Nf (fun _ => rfl)) (fullSupport_face Nf (fun _ => rfl)) l
  have hn := fun z => congrArg (fun f => f.f1 z) hs
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
      (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l)
    (fullBlockNamedEquivalence Nf laws adequate_fine (fun _ => rfl)
      (fullSupport_edge Nf (fun _ => rfl)) (fullSupport_face Nf (fun _ => rfl)) l)
    (M.generatedBlockComparisonHom laws adequate_coarse adequate_fine l) (incidenceNamedHom M) hn x
  exact (congrArg fineNamedCoordinates hh).trans (named_map _)

/-- 同実全Law H¹比較の核余核は二labelで00。 -/
theorem law_defect : blockDefect (M.generatedComparisonH1Map laws adequate_coarse adequate_fine) = (0,0) := by
  classical
  rw [lawH1Defect_subset_sum Nc Nf laws adequate_coarse M adequate_fine]
  have hf (l : LawValueLabel laws) := WitnessFive.defect (labelValueFiber laws qc adequate_coarse l)
  simp only [hf,Finset.sum_const_zero]
/-- 同Law producerは同実00。 -/
theorem primitive_law_J : primitiveLawDiagnostic M laws adequate_coarse = (0,0) :=
  (primitiveLawDiagnostic_eq_blockDefect M laws adequate_coarse).trans law_defect
/-- 同粗Lawの全原e/h座標族。 -/
def coarseLawCoordinates := (lawH1FamilyEquiv Nc laws adequate_coarse).trans
  (LinearEquiv.piCongrRight coarseBlockCoordinates)
/-- 同細Lawの全原e/h座標族。 -/
def fineLawCoordinates := (lawH1FamilyEquiv Nf laws adequate_fine).trans
  (LinearEquiv.piCongrRight fineBlockCoordinates)
/-- 同実uの全label・全e/h値は恒等。 -/
theorem law_map (x : (Nc.lawGeneratedComplex laws adequate_coarse).H1) (l : LawValueLabel laws) :
    fineLawCoordinates (M.generatedComparisonH1Map laws adequate_coarse adequate_fine x) l = coarseLawCoordinates x l := by
  simp only [fineLawCoordinates,coarseLawCoordinates,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply]
  exact (congrArg (fineBlockCoordinates l) (M.lawH1Family_natural laws adequate_coarse adequate_fine x l)).trans (block_map l _)
/-- 各発生labelに元粗e/h単独1類を置く。 -/
def coarseLawLoop (i : Fin 2) := coarseLawCoordinates.symm (fun _ => Pi.single i 1)
/-- 各発生labelに元細e/h単独1類を独立に置く。 -/
def fineLawLoop (i : Fin 2) := fineLawCoordinates.symm (fun _ => Pi.single i 1)
/-- 同実Law射は原e/hの両方を保存する。 -/
theorem law_loop_preserved (i : Fin 2) : M.generatedComparisonH1Map laws adequate_coarse adequate_fine (coarseLawLoop i) = fineLawLoop i := by
  apply fineLawCoordinates.injective; funext l
  rw [law_map]
  simp only [coarseLawLoop,fineLawLoop,LinearEquiv.apply_symm_apply]
/-- 元粗Law e/hは発生labelの値1により非零。 -/
theorem coarse_law_loop_nonzero (i : Fin 2) : coarseLawLoop i ≠ 0 := by
  classical
  intro hh
  have he := congrArg (fun z => coarseLawCoordinates z (label false) i) hh
  change coarseLawCoordinates (coarseLawLoop i) (label false) i = coarseLawCoordinates 0 (label false) i at he
  rw [coarseLawLoop,LinearEquiv.apply_symm_apply,Pi.single_eq_same,map_zero] at he
  exact one_ne_zero he
/-- 元細Law e/hも発生labelの値1により非零。 -/
theorem fine_law_loop_nonzero (i : Fin 2) : fineLawLoop i ≠ 0 := by
  classical
  intro hh
  have he := congrArg (fun z => fineLawCoordinates z (label false) i) hh
  change fineLawCoordinates (fineLawLoop i) (label false) i = fineLawCoordinates 0 (label false) i at he
  rw [fineLawLoop,LinearEquiv.apply_symm_apply,Pi.single_eq_same,map_zero] at he
  exact one_ne_zero he
/-- 同Lawのηは実族自然性と各原η同型から単射かつ全射。 -/
theorem law_unit_bijective : Function.Bijective (lawUnitH1 M laws adequate_coarse) := by
  classical
  let g := FiniteLinearFamily.map (fun l : LawValueLabel laws => unitH1 M (labelValueFiber laws qc adequate_coarse l))
  have hg : Function.Bijective g := by
    constructor
    · intro x y hh
      funext l
      apply (unit_bijective (labelValueFiber laws qc adequate_coarse l)).1
      exact congrFun hh l
    · intro y
      choose x hx using fun l : LawValueLabel laws => (unit_bijective (labelValueFiber laws qc adequate_coarse l)).2 (y l)
      exact ⟨x,funext hx⟩
  apply (LinearConjugation.bijective_iff (lawUnitH1 M laws adequate_coarse) g
    (lawCoarseHomologyEquiv (Nc := Nc) laws adequate_coarse 1)
    (lawPushforwardHomologyEquiv M laws adequate_coarse 1) ?_).mpr hg
  intro x
  funext l
  exact lawUnit_homology_component M laws adequate_coarse 1 x l
/-- 同Law原a=ηH¹の核余核は00。 -/
theorem law_unit_defect : blockDefect (lawUnitH1 M laws adequate_coarse) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr law_unit_bijective


/-- 同実Law κは各原κの両逆族。 -/
def lawKappaEquiv := LinearEquiv.piCongrRight (fun l : LawValueLabel laws => kappaEquiv (labelValueFiber laws qc adequate_coarse l))
/-- 同Law κ両逆の実射はliteral lawκ。 -/
theorem lawKappaEquiv_toLinearMap : lawKappaEquiv.toLinearMap = lawKappa M laws adequate_coarse := rfl
/-- 同実Law κ*は各原κ*の両逆族。 -/
def lawKappaStarEquiv := LinearEquiv.piCongrRight (fun l : LawValueLabel laws => kappaStarEquiv (labelValueFiber laws qc adequate_coarse l))
/-- 同Law κ*両逆はliteral lawκ*の実写像を保持。 -/
theorem lawKappaStarEquiv_toLinearMap : lawKappaStarEquiv.toLinearMap = lawKappaStar M laws adequate_coarse := by
  apply LinearMap.ext; intro x; funext l
  exact congrArg (fun f => f (x l)) (kappaStarEquiv_toLinearMap _)
/-- 同literal Law Rは実κ*単射性から零。 -/
theorem law_R_zero : lawR M laws adequate_coarse = ⊥ := by
  change LinearMap.ker (lawKappaStar M laws adequate_coarse) = ⊥
  rw [← lawKappaStarEquiv_toLinearMap]
  exact LinearMap.ker_eq_bot.mpr lawKappaStarEquiv.injective
/-- 同literal Law Rの零空間性。 -/
theorem law_R_subsingleton : Subsingleton (lawR M laws adequate_coarse) := by rw [law_R_zero]; infer_instance
/-- 同Law Rの次元零。 -/
theorem law_R_dimension : Module.finrank ℚ (lawR M laws adequate_coarse) = 0 := by
  letI := law_R_subsingleton
  exact Module.finrank_zero_of_subsingleton
/-- 同標準Law τは元τ族の零射。 -/
theorem law_tau_zero : lawConnectingTau M laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x
  apply (lawPushforwardHomologyEquiv M laws adequate_coarse 2).injective
  funext l
  rw [lawConnectingTau_component,tau_zero]
  simp only [LinearMap.zero_apply,map_zero,Pi.zero_apply]
/-- 同Law τのrank零。 -/
theorem law_tau_rank : Module.finrank ℚ (LinearMap.range (lawConnectingTau M laws adequate_coarse)) = 0 := by
  rw [law_tau_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- 二labelの同原全Φ空間の両逆座標。 -/
def lawWholePhiCoordinates := LinearEquiv.piCongrRight (fun l : LawValueLabel laws =>
  wholePhiCoordinates (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l))
/-- 二labelの全Φ H¹の次元は2。 -/
theorem law_wholePhi_dimension : Module.finrank ℚ
    ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l)) →
      (phiComplex M (labelValueFiber laws qc adequate_coarse l) c).H1) = 2 := by
  rw [lawWholePhiCoordinates.finrank_eq]
  exact (Module.finrank_fintype_fun_eq_card (R := ℚ) (η := LawValueLabel laws)).trans labels_card
/-- 実二labelの同κ*像のrankは2。 -/
theorem law_kappaStar_rank : Module.finrank ℚ (LinearMap.range (lawKappaStar M laws adequate_coarse)) = 2 := by
  have he := LinearEquiv.ofInjective (lawKappaStar M laws adequate_coarse)
    (by rw [← lawKappaStarEquiv_toLinearMap]; exact lawKappaStarEquiv.injective)
  exact he.finrank_eq.symm.trans law_wholePhi_dimension
/-- 同原Law m閉路族、実κから独立の原セル値1。 -/
def lawMCycle := fun l : LawValueLabel laws => mCycle (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l)
/-- 同原Law k chain類族、実κから独立。 -/
def lawPhiK := fun l : LawValueLabel laws => phiK (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l)
/-- 同実Law κは全label・全chartで原mを原kへ送る。 -/
theorem law_kappa_m (l : LawValueLabel laws) (c : Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l)) :
    lawKappa M laws adequate_coarse lawMCycle l c = lawPhiK l c := by
  rw [lawKappa_apply]
  exact kappa_m _ _ c

/-- 実二発生labelで同原Phi Betti和を合計すると2。 -/
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


/-- 同実Law εのH¹射は原literalR零から可逆。 -/
theorem law_evaluation_bijective : Function.Bijective (lawEvaluationH1 M laws adequate_coarse) := by
  constructor
  · exact lawEvaluationH1_injective M laws adequate_coarse
  · intro y
    apply (lawFiveTerm_exact_at_fineH1 M laws adequate_coarse y).mp
    letI := law_R_subsingleton
    exact Subsingleton.elim _ _
/-- 同原Law P H²は各原P H²零の実族同型から零。 -/
theorem law_pH2_subsingleton : Subsingleton ((zeroExtension (lawPushforwardComplex M laws adequate_coarse)).homology (2:ℤ)) := by
  letI : (l : LawValueLabel laws) → Subsingleton ((zeroExtension (pushforwardComplex M (labelValueFiber laws qc adequate_coarse l))).homology (2:ℤ)) :=
    fun l => pH2_subsingleton _
  exact (lawPushforwardHomologyEquiv M laws adequate_coarse 2).toEquiv.subsingleton_congr.mpr inferInstance
/-- 同二labelの原k dual族。 -/
def lawWholePhiK := fun l : LawValueLabel laws => wholePhiK (labelValueFiber laws qc adequate_coarse l)
/-- 同二labelのk dual族の全periodは1。 -/
theorem lawWholePhiK_period (l : LawValueLabel laws) : lawWholePhiCoordinates lawWholePhiK l = 1 :=
  wholePhiK_period _ _
/-- 同二labelのk dual族は元Φ商で非零。 -/
theorem lawWholePhiK_nonzero : lawWholePhiK ≠ 0 := by
  intro hh
  have he := congrArg (fun z => lawWholePhiCoordinates z (label false)) hh
  change lawWholePhiCoordinates lawWholePhiK (label false) = lawWholePhiCoordinates 0 (label false) at he
  rw [lawWholePhiK_period,map_zero] at he
  exact one_ne_zero he
/-- 同実Law κ*は各原m閉路上のk period1を保持。 -/
theorem law_kappaStar_m_period (l : LawValueLabel laws) : lawKappaStar M laws adequate_coarse lawWholePhiK l (lawMCycle l) = 1 := by
  rw [lawKappaStar_apply]
  exact kappaStar_m_period _ _
/-- 同全Lawでも全Φを入れた隣接完全列は構成できない。 -/
theorem law_wholePhi_sequence_not_exact
    (g : (zeroExtension (Nf.lawGeneratedComplex laws adequate_fine)).homology (1:ℤ) →ₗ[ℚ]
      ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l)) →
        (phiComplex M (labelValueFiber laws qc adequate_coarse l) c).H1))
    (t : ((l : LawValueLabel laws) → (c : Nc.ChartInTargetSubset (labelValueFiber laws qc adequate_coarse l)) →
        (phiComplex M (labelValueFiber laws qc adequate_coarse l) c).H1) →ₗ[ℚ]
      (zeroExtension (lawPushforwardComplex M laws adequate_coarse)).homology (2:ℤ)) :
    ¬ (Function.Exact (lawEvaluationH1 M laws adequate_coarse) g ∧ Function.Exact g t) := by
  rintro ⟨hg,ht⟩
  have hg0 (x) : g x = 0 := by
    obtain ⟨z,rfl⟩ := law_evaluation_bijective.2 x
    exact hg.apply_apply_eq_zero z
  letI := law_pH2_subsingleton
  have hy : t lawWholePhiK = 0 := Subsingleton.elim _ _
  obtain ⟨x,hx⟩ := (ht lawWholePhiK).mp hy
  exact lawWholePhiK_nonzero (hx.symm.trans (hg0 x))

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.block_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.primitive_law_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseLawLoop
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineLawLoop
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_loop_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarse_law_loop_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_law_loop_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawKappaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawKappaEquiv_toLinearMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawKappaStarEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawKappaStarEquiv_toLinearMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_R_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawWholePhiCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_wholePhi_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawMCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawPhiK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_kappa_m
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_evaluation_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_pH2_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawWholePhiK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawWholePhiK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lawWholePhiK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_kappaStar_m_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.law_wholePhi_sequence_not_exact
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
