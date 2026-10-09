import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneDiagnostics
import ResearchLean.AG.AtlasCoefficientFiber.LawFiberSequence
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonFiberDiagnostics

/-!
# G-135 W1：同じ実Law比較の二発生label

## Implementation notes

原始Lawから生成した各blockを全三次数で原始名付き表へ移し、同じ比較正方形を使う。
全Lawは実分解を通じて元二labelを保つ。二labelの同じ全台を統合しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 各元labelの実粗block H¹と元e,h全座標。 -/
def coarseBlockCoordinates (l : LawValueLabel laws) :
    (Nc.lawValueBlockComplex laws adequate_coarse l).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
    (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l).h1Equiv.trans
    coarseNamedCoordinates

/-- 各元labelの実W1a細block H¹と元h全座標。 -/
def aBlockCoordinates (l : LawValueLabel laws) :
    (Na.lawValueBlockComplex laws adequate_fine l).H1 ≃ₗ[ℚ] (Fin 1 → ℚ) :=
  (fullBlockNamedEquivalence Na laws adequate_fine (fun _ => rfl)
    (fullSupport_edge Na (fun _ => rfl)) (fullSupport_face Na (fun _ => rfl)) l).h1Equiv.trans
    aNamedCoordinates

/-- 各元labelの実W1b細block H¹と元e₀,e₁,h全座標。 -/
def bBlockCoordinates (l : LawValueLabel laws) :
    (Nb.lawValueBlockComplex laws adequate_fine l).H1 ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  (fullBlockNamedEquivalence Nb laws adequate_fine (fun _ => rfl)
    (fullSupport_edge Nb (fun _ => rfl)) (fullSupport_face Nb (fun _ => rfl)) l).h1Equiv.trans
    bNamedCoordinates

/-- 同じ実W1a block比較は全元labelで原始座標式を持つ。 -/
theorem a_block_map (l : LawValueLabel laws)
    (x : (Nc.lawValueBlockComplex laws adequate_coarse l).H1) :
    aBlockCoordinates l ((Ma.generatedBlockComparisonHom laws adequate_coarse adequate_fine l).h1Map x) =
      aMap (coarseBlockCoordinates l x) := by
  have hs := incidenceNamedHom_square Ma laws adequate_coarse adequate_fine
    (fun _ => rfl) (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl))
    (fun _ => rfl) (fullSupport_edge Na (fun _ => rfl)) (fullSupport_face Na (fun _ => rfl)) l
  have hn := fun z => congrArg (fun f => f.f1 z) hs
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
      (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l)
    (fullBlockNamedEquivalence Na laws adequate_fine (fun _ => rfl)
      (fullSupport_edge Na (fun _ => rfl)) (fullSupport_face Na (fun _ => rfl)) l)
    (Ma.generatedBlockComparisonHom laws adequate_coarse adequate_fine l) (incidenceNamedHom Ma) hn x
  exact (congrArg aNamedCoordinates hh).trans (a_named_map _)

/-- 同じ実W1b block比較は全元labelで原始座標式を持つ。 -/
theorem b_block_map (l : LawValueLabel laws)
    (x : (Nc.lawValueBlockComplex laws adequate_coarse l).H1) :
    bBlockCoordinates l ((Mb.generatedBlockComparisonHom laws adequate_coarse adequate_fine l).h1Map x) =
      bMap (coarseBlockCoordinates l x) := by
  have hs := incidenceNamedHom_square Mb laws adequate_coarse adequate_fine
    (fun _ => rfl) (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl))
    (fun _ => rfl) (fullSupport_edge Nb (fun _ => rfl)) (fullSupport_face Nb (fun _ => rfl)) l
  have hn := fun z => congrArg (fun f => f.f1 z) hs
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullBlockNamedEquivalence Nc laws adequate_coarse (fun _ => rfl)
      (fullSupport_edge Nc (fun _ => rfl)) (fullSupport_face Nc (fun _ => rfl)) l)
    (fullBlockNamedEquivalence Nb laws adequate_fine (fun _ => rfl)
      (fullSupport_edge Nb (fun _ => rfl)) (fullSupport_face Nb (fun _ => rfl)) l)
    (Mb.generatedBlockComparisonHom laws adequate_coarse adequate_fine l) (incidenceNamedHom Mb) hn x
  exact (congrArg bNamedCoordinates hh).trans (b_named_map _)

/-- 同じ実W1a全Law核は、元二labelのe period族。 -/
def aLawKernelEquiv : LinearMap.ker (Ma.generatedComparisonH1Map laws adequate_coarse adequate_fine) ≃ₗ[ℚ]
    (LawValueLabel laws → ℚ) :=
  (lawH1KernelFamilyEquiv Nc Na laws adequate_coarse Ma adequate_fine).trans
    (LinearEquiv.piCongrRight fun l =>
      (LinearConjugation.kernelEquiv _ aMap (coarseBlockCoordinates l) (aBlockCoordinates l)
        (a_block_map l)).trans aMapKernelEquiv)

/-- 同じ実W1b全Law余核は、元二labelのe₁−e₀ period族。 -/
def bLawCokernelEquiv : ((Nb.lawGeneratedComplex laws adequate_fine).H1 ⧸
    LinearMap.range (Mb.generatedComparisonH1Map laws adequate_coarse adequate_fine)) ≃ₗ[ℚ]
    (LawValueLabel laws → ℚ) :=
  (lawH1CokernelFamilyEquiv Nc Nb laws adequate_coarse Mb adequate_fine).trans
    (LinearEquiv.piCongrRight fun l =>
      (LinearConjugation.cokernelEquiv _ bMap (coarseBlockCoordinates l) (bBlockCoordinates l)
        (b_block_map l)).trans bMapCokernelEquiv)

/-- 元二labelの同じ実全Law削除欠損は(2,0)。 -/
theorem a_law_defect : blockDefect (Ma.generatedComparisonH1Map laws adequate_coarse adequate_fine) = (2,0) := by
  classical
  rw [lawH1Defect_subset_sum Nc Na laws adequate_coarse Ma adequate_fine]
  have h (l : LawValueLabel laws) := a_defect (labelValueFiber laws qc adequate_coarse l)
    (labelValueFiber_nonempty laws qc adequate_coarse l)
  simp only [h,Finset.sum_const,Finset.card_univ,labels_card]
  decide

/-- 元二labelの同じ実全Law重複欠損は(0,2)。 -/
theorem b_law_defect : blockDefect (Mb.generatedComparisonH1Map laws adequate_coarse adequate_fine) = (0,2) := by
  classical
  rw [lawH1Defect_subset_sum Nc Nb laws adequate_coarse Mb adequate_fine]
  have h (l : LawValueLabel laws) := b_defect (labelValueFiber laws qc adequate_coarse l)
    (labelValueFiber_nonempty laws qc adequate_coarse l)
  simp only [h,Finset.sum_const,Finset.card_univ,labels_card]
  decide

/-- 同じ原始行列Law producerを実全Law削除欠損へ戻す。 -/
theorem a_primitive_law_J : primitiveLawDiagnostic Ma laws adequate_coarse = (2,0) :=
  (primitiveLawDiagnostic_eq_blockDefect Ma laws adequate_coarse).trans a_law_defect

/-- 同じ原始行列Law producerを実全Law重複欠損へ戻す。 -/
theorem b_primitive_law_J : primitiveLawDiagnostic Mb laws adequate_coarse = (0,2) :=
  (primitiveLawDiagnostic_eq_blockDefect Mb laws adequate_coarse).trans b_law_defect

/-- W1a全Lawのliteral Rも元二labelの零族である。 -/
theorem a_law_R_zero : Subsingleton (lawR Ma laws adequate_coarse) := by
  letI (l : LawValueLabel laws) := MappedCells.R_subsingleton Ma
    (labelValueFiber laws qc adequate_coarse l) Ma_all_mapped
  exact (lawRFamilyEquiv Ma laws adequate_coarse).toEquiv.subsingleton_congr.mpr inferInstance

/-- W1a全Lawの同じtransgressionは零射。 -/
theorem a_law_tau_zero : lawConnectingTau Ma laws adequate_coarse = 0 := by
  letI := a_law_R_zero
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0,map_zero,LinearMap.zero_apply]

/-- W1a実全LawのR次元とτ rankの指定零値。 -/
theorem a_law_R_tau_dimensions : Module.finrank ℚ (lawR Ma laws adequate_coarse) = 0 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau Ma laws adequate_coarse)) = 0 := by
  letI := a_law_R_zero
  constructor
  · exact Module.finrank_zero_of_subsingleton
  · rw [a_law_tau_zero,LinearMap.range_zero]
    exact Module.finrank_zero_of_subsingleton

/-- W1b全Lawのliteral Rも元二labelの零族である。 -/
theorem b_law_R_zero : Subsingleton (lawR Mb laws adequate_coarse) := by
  letI (l : LawValueLabel laws) := MappedCells.R_subsingleton Mb
    (labelValueFiber laws qc adequate_coarse l) Mb_all_mapped
  exact (lawRFamilyEquiv Mb laws adequate_coarse).toEquiv.subsingleton_congr.mpr inferInstance

/-- W1b全Lawの同じtransgressionは零射。 -/
theorem b_law_tau_zero : lawConnectingTau Mb laws adequate_coarse = 0 := by
  letI := b_law_R_zero
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0,map_zero,LinearMap.zero_apply]

/-- W1b実全LawのR次元とτ rankの指定零値。 -/
theorem b_law_R_tau_dimensions : Module.finrank ℚ (lawR Mb laws adequate_coarse) = 0 ∧
    Module.finrank ℚ (LinearMap.range (lawConnectingTau Mb laws adequate_coarse)) = 0 := by
  letI := b_law_R_zero
  constructor
  · exact Module.finrank_zero_of_subsingleton
  · rw [b_law_tau_zero,LinearMap.range_zero]
    exact Module.finrank_zero_of_subsingleton


/-- 実全Lawの粗H¹を元二labelのe,h全座標へ移す。 -/
def coarseLawCoordinates := (lawH1FamilyEquiv Nc laws adequate_coarse).trans
  (LinearEquiv.piCongrRight coarseBlockCoordinates)
/-- 実全LawのW1a細H¹を元二labelのh全座標へ移す。 -/
def aLawCoordinates := (lawH1FamilyEquiv Na laws adequate_fine).trans
  (LinearEquiv.piCongrRight aBlockCoordinates)
/-- 実全LawのW1b細H¹を元二labelの二eとh全座標へ移す。 -/
def bLawCoordinates := (lawH1FamilyEquiv Nb laws adequate_fine).trans
  (LinearEquiv.piCongrRight bBlockCoordinates)

/-- 同じ実全Law比較は各元labelで同じ原始式を持つ。 -/
theorem a_law_map (x : (Nc.lawGeneratedComplex laws adequate_coarse).H1) (l : LawValueLabel laws) :
    aLawCoordinates ((Ma.generatedComparisonH1Map laws adequate_coarse adequate_fine) x) l =
      aMap (coarseLawCoordinates x l) := by
  simp only [aLawCoordinates,coarseLawCoordinates,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply]
  exact (congrArg (aBlockCoordinates l) (Ma.lawH1Family_natural laws adequate_coarse adequate_fine x l)).trans
    (a_block_map l _)

/-- 同じ実全Law比較は各元labelで同じ原始式を持つ。 -/
theorem b_law_map (x : (Nc.lawGeneratedComplex laws adequate_coarse).H1) (l : LawValueLabel laws) :
    bLawCoordinates ((Mb.generatedComparisonH1Map laws adequate_coarse adequate_fine) x) l =
      bMap (coarseLawCoordinates x l) := by
  simp only [bLawCoordinates,coarseLawCoordinates,LinearEquiv.trans_apply,LinearEquiv.piCongrRight_apply]
  exact (congrArg (bBlockCoordinates l) (Mb.lawH1Family_natural laws adequate_coarse adequate_fine x l)).trans
    (b_block_map l _)

/-- 全Lawの指定h単独類は元二labelの原h値を読む。 -/
def coarseLawH := coarseLawCoordinates.symm (fun _ => ![0,1])
/-- 全Law W1aの同じ指定h単独類。 -/
def aLawH := aLawCoordinates.symm (fun _ => ![1])
/-- 全Law W1bの同じ指定h単独類。 -/
def bLawH := bLawCoordinates.symm (fun _ => ![0,0,1])

/-- 同じ実全Law削除比較は二labelのh類を同時に保つ。 -/
theorem a_law_h_preserved : Ma.generatedComparisonH1Map laws adequate_coarse adequate_fine coarseLawH = aLawH := by
  apply aLawCoordinates.injective
  funext l
  rw [a_law_map]
  simp only [coarseLawH,aLawH,LinearEquiv.apply_symm_apply]
  funext e
  fin_cases e
  rfl
/-- 同じ実全Law重複比較は二labelのh類を同時に保つ。 -/
theorem b_law_h_preserved : Mb.generatedComparisonH1Map laws adequate_coarse adequate_fine coarseLawH = bLawH := by
  apply bLawCoordinates.injective
  funext l
  rw [b_law_map]
  simp only [coarseLawH,bLawH,LinearEquiv.apply_symm_apply]
  rfl
/-- 元粗Law h類は両発生labelでperiod1、従って非零。 -/
theorem coarse_law_h_nonzero : coarseLawH ≠ 0 := by
  intro h
  have he := congrArg coarseLawCoordinates h
  rw [coarseLawH,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero (congrFun (congrFun he (label false)) 1)
/-- W1aの同じ元細Law h類も非零。 -/
theorem a_law_h_nonzero : aLawH ≠ 0 := by
  intro h
  have he := congrArg aLawCoordinates h
  rw [aLawH,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero (congrFun (congrFun he (label false)) 0)
/-- W1bの同じ元細Law h類も非零。 -/
theorem b_law_h_nonzero : bLawH ≠ 0 := by
  intro h
  have he := congrArg bLawCoordinates h
  rw [bLawH,LinearEquiv.apply_symm_apply,map_zero] at he
  exact one_ne_zero (congrFun (congrFun he (label false)) 2)

end AAT.AG.AtlasCoefficientFiber.WitnessOne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bBlockCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_block_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_block_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aLawKernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bLawCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_law_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_law_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_primitive_law_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_primitive_law_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_law_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_law_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_law_R_tau_dimensions
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_law_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_law_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_law_R_tau_dimensions
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bLawCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_law_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_law_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseLawH
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aLawH
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bLawH
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_law_h_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_law_h_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_law_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_law_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_law_h_nonzero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessOne
