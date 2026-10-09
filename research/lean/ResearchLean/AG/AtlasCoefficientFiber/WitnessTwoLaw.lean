import ResearchLean.AG.AtlasCoefficientFiber.WitnessTwoFiber
import ResearchLean.AG.AtlasCoefficientFiber.LawFiberSequence
import ResearchLean.AG.AtlasCoefficientFiber.LawHomologyCoordinates
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonFiberDiagnostics

/-!
# G-135 W2：同じ実Law二成分のpure fiber欠損

## Implementation notes

二つの発生labelを保ち、同原商・同射のfamily自然性と両逆を使う。
元発生labelの族同型を使い、同台labelを商化する方法は二成分の重複度を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessTwo
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 同原Law block粗H¹のh全座標。 -/
def coarseBlockCoordinates (l : LawValueLabel laws) :
    (Nc.lawValueBlockComplex laws adequate_coarse l).H1 ≃ₗ[ℚ] (Fin 1 → ℚ) :=
  (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
    (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l).h1Equiv.trans coarseNamedCoordinates
/-- 同原Law block細H¹のh,k全座標。 -/
def fineBlockCoordinates (l : LawValueLabel laws) :
    (Nf.lawValueBlockComplex laws adequate_fine l).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullBlockNamedEquivalence Nf laws adequate_fine (fun _ => rfl)
    (fullSupport_edge Nf (fun _ => rfl)) (fullSupport_face Nf (fun _ => rfl)) l).h1Equiv.trans fineNamedCoordinates
/-- 同実Law block比較は全元x→(x,0)。 -/
theorem block_map (l : LawValueLabel laws) (x : (Nc.lawValueBlockComplex laws adequate_coarse l).H1) :
    fineBlockCoordinates l ((M.generatedBlockComparisonHom laws adequate_coarse adequate_fine l).h1Map x) =
      coordinateMap (coarseBlockCoordinates l x) := by
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
/-- 同実全Law余核と二発生labelのk値族の全商両逆。 -/
def lawCokernelEquiv : ((Nf.lawGeneratedComplex laws adequate_fine).H1 ⧸
    LinearMap.range (M.generatedComparisonH1Map laws adequate_coarse adequate_fine)) ≃ₗ[ℚ]
    (LawValueLabel laws → ℚ) :=
  (lawH1CokernelFamilyEquiv Nc Nf laws adequate_coarse M adequate_fine).trans
    (LinearEquiv.piCongrRight fun l =>
      (LinearConjugation.cokernelEquiv _ coordinateMap (coarseBlockCoordinates l) (fineBlockCoordinates l)
        (block_map l)).trans coordinateCokernelEquiv)
/-- 同実全Law欠損は二元発生成分の和02。 -/
theorem law_defect : blockDefect (M.generatedComparisonH1Map laws adequate_coarse adequate_fine) = (0,2) := by
  classical
  rw [lawH1Defect_subset_sum Nc Nf laws adequate_coarse M adequate_fine]
  have h (l : LawValueLabel laws) := defect (labelValueFiber laws qc adequate_coarse l)
    (labelValueFiber_nonempty laws qc adequate_coarse l)
  simp only [h,Finset.sum_const,Finset.card_univ,labels_card]
  decide
/-- 原Law producerも同実02。 -/
theorem primitive_law_J : primitiveLawDiagnostic M laws adequate_coarse = (0,2) :=
  (primitiveLawDiagnostic_eq_blockDefect M laws adequate_coarse).trans law_defect
/-- 全Law核は零、実同射の次元式。 -/
theorem law_kernel_dimension : Module.finrank ℚ (LinearMap.ker
    (M.generatedComparisonH1Map laws adequate_coarse adequate_fine)) = 0 :=
  congrArg Prod.fst law_defect
/-- 全Law余核は二発生成分分の2。 -/
theorem law_cokernel_dimension : Module.finrank ℚ ((Nf.lawGeneratedComplex laws adequate_fine).H1 ⧸
    LinearMap.range (M.generatedComparisonH1Map laws adequate_coarse adequate_fine)) = 2 :=
  congrArg Prod.snd law_defect
/-- 同literal Law Rと元二成分k値の全両逆。 -/
def lawRCoordinates : lawR M laws adequate_coarse ≃ₗ[ℚ] (LawValueLabel laws → ℚ) :=
  (lawRFamilyEquiv M laws adequate_coarse).trans (LinearEquiv.piCongrRight fun l =>
    rCoordinates (labelValueFiber laws qc adequate_coarse l) (labelValueFiber_nonempty laws qc adequate_coarse l))
/-- 同Law Rは二成分の2。 -/
theorem law_R_dimension : Module.finrank ℚ (lawR M laws adequate_coarse) = 2 := by
  rw [lawRCoordinates.finrank_eq]
  simp only [Module.finrank_pi,labels_card]
/-- 同Law κ*は各原射が零であることから零。 -/
theorem law_kappaStar_zero : lawKappaStar M laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x; funext l
  rw [lawKappaStar_apply,kappaStar_zero,LinearMap.zero_apply]
  rfl
/-- 同Law κ*のrank零。 -/
theorem law_kappaStar_rank : Module.finrank ℚ (LinearMap.range (lawKappaStar M laws adequate_coarse)) = 0 := by
  rw [law_kappaStar_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- 同実SESのLaw τは同じ原τ族の零射。 -/
theorem law_tau_zero : lawConnectingTau M laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x
  apply (lawPushforwardHomologyEquiv M laws adequate_coarse 2).injective
  funext l
  rw [lawConnectingTau_component,tau_zero]
  simp only [LinearMap.zero_apply,map_zero,Pi.zero_apply]
/-- 同Law τ rank零。 -/
theorem law_tau_rank : Module.finrank ℚ (LinearMap.range (lawConnectingTau M laws adequate_coarse)) = 0 := by
  rw [law_tau_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- 同実全Law粗H¹の二発生label h全座標。 -/
def coarseLawCoordinates := (lawH1FamilyEquiv Nc laws adequate_coarse).trans
  (LinearEquiv.piCongrRight coarseBlockCoordinates)
/-- 同実全Law細H¹の二発生label h,k全座標。 -/
def fineLawCoordinates := (lawH1FamilyEquiv Nf laws adequate_fine).trans
  (LinearEquiv.piCongrRight fineBlockCoordinates)
/-- 同全Law射は全元・全labelで元h/k式を持つ。 -/
theorem law_map (x : (Nc.lawGeneratedComplex laws adequate_coarse).H1) (l : LawValueLabel laws) :
    fineLawCoordinates (M.generatedComparisonH1Map laws adequate_coarse adequate_fine x) l =
      coordinateMap (coarseLawCoordinates x l) := by
  simp only [fineLawCoordinates,coarseLawCoordinates,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply]
  exact (congrArg (fineBlockCoordinates l) (M.lawH1Family_natural laws adequate_coarse adequate_fine x l)).trans
    (block_map l _)
/-- 全Law元h類、両発生labelで同じ原値1。 -/
def coarseLawH := coarseLawCoordinates.symm (fun _ => ![1])
/-- 同細h類、k値0。 -/
def fineLawH := fineLawCoordinates.symm (fun _ => ![1,0])
/-- 同細k類、h値0。 -/
def fineLawK := fineLawCoordinates.symm (fun _ => ![0,1])
/-- 同実全Law射はh非零類を保つ。 -/
theorem law_h_preserved : M.generatedComparisonH1Map laws adequate_coarse adequate_fine coarseLawH = fineLawH := by
  apply fineLawCoordinates.injective; funext l
  rw [law_map]
  simp only [coarseLawH,fineLawH,LinearEquiv.apply_symm_apply]
  rfl
/-- 同原粗Law h類は非零。 -/
theorem coarse_law_h_nonzero : coarseLawH ≠ 0 := by
  intro h; have he := congrArg coarseLawCoordinates h
  rw [coarseLawH,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero (congrFun (congrFun he (label false)) 0)
/-- 同原細Law h類も非零。 -/
theorem fine_law_h_nonzero : fineLawH ≠ 0 := by
  intro h; have he := congrArg fineLawCoordinates h
  rw [fineLawH,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero (congrFun (congrFun he (label false)) 0)
/-- 原Rの両k類、期待rankではなく原fiber代表族から生成。 -/
def lawRK : lawR M laws adequate_coarse := (lawRFamilyEquiv M laws adequate_coarse).symm
  (fun l => rK (labelValueFiber laws qc adequate_coarse l))
/-- 同原R代表は全発生labelでk period1。 -/
theorem lawRK_period (l : LawValueLabel laws) : lawRCoordinates lawRK l = 1 := by
  simp only [lawRCoordinates,lawRK,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.piCongrRight_apply]
  exact rK_period _ _

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

/-- 同実全Law余核座標は原細代表の各k値を読む。 -/
theorem lawCokernelEquiv_mk (x : (Nf.lawGeneratedComplex laws adequate_fine).H1) (l : LawValueLabel laws) :
    lawCokernelEquiv ((LinearMap.range (M.generatedComparisonH1Map laws adequate_coarse adequate_fine)).mkQ x) l =
      fineLawCoordinates x l 1 := by
  simp only [lawCokernelEquiv,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply,
    FaceRelationSubdivision.lawH1CokernelFamilyEquiv_mk]
  rfl
/-- 原二labelのk単独1の同実余核periodは各1。 -/
theorem lawK_cokernel_period (l : LawValueLabel laws) :
    lawCokernelEquiv ((LinearMap.range (M.generatedComparisonH1Map laws adequate_coarse adequate_fine)).mkQ fineLawK) l = 1 := by
  rw [lawCokernelEquiv_mk]
  simp only [fineLawK,LinearEquiv.apply_symm_apply]
  rfl
/-- 同原Law k余核類は非零。 -/
theorem lawK_cokernel_nonzero :
    (LinearMap.range (M.generatedComparisonH1Map laws adequate_coarse adequate_fine)).mkQ fineLawK ≠ 0 := by
  intro h
  have hh := congrArg (fun z => lawCokernelEquiv z (label false)) h
  dsimp only at hh
  rw [lawK_cokernel_period,map_zero] at hh
  exact one_ne_zero hh
/-- 同原Law R代表も非零。 -/
theorem lawRK_nonzero : lawRK ≠ 0 := by
  intro h
  have hh := congrArg (fun z => lawRCoordinates z (label false)) h
  dsimp only at hh
  rw [lawRK_period,map_zero] at hh
  exact one_ne_zero hh


/-- 同全Law κも原混在面なしから零。 -/
theorem law_kappa_zero : lawKappa M laws adequate_coarse = 0 := by
  apply LinearMap.ext; intro x; funext l
  rw [lawKappa_apply,kappa_zero,LinearMap.zero_apply]
  rfl
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

end AAT.AG.AtlasCoefficientFiber.WitnessTwo
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.block_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lawCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.primitive_law_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_kernel_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_cokernel_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lawRCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseLawH
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineLawH
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineLawK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_h_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarse_law_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fine_law_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lawRK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lawRK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lawCokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lawK_cokernel_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lawK_cokernel_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lawRK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.law_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.rCoordinates.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessTwo
