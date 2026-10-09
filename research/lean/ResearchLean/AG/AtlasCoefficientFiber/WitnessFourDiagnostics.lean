import ResearchLean.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration
import ResearchLean.AG.AtlasCoefficientFiber.LawDefectDiagnostics
import ResearchLean.AG.FaceRelationSubdivision.WitnessOneDiagnostics

/-!
# W4：原係数欠損と同じ実三角形診断

Implementation notes: literal R零から原εのH¹両逆を生成する。その同じ座標で
原ηの全元射をk/additional periodへ移し、実P余核を計算する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
open FaceRelationSubdivision.WitnessOne (N plus minus qc qf coarser rPlus rMinus)

/-- literal R零なら同じ実Jは原係数aの欠損だけとなる。 -/
theorem defect_eq_unit_of_R_zero {Source : Type} {qc qf : Reading Source} {h : qc.CoarserThan qf}
    {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
    (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)
    (hR : Subsingleton (R M A)) : blockDefect (M.aSubnerveComparisonHom A).h1Map = blockDefect (unitH1 M A) := by
  letI := hR
  apply Prod.ext
  · rw [coefficient_kernel_dimension, blockDefect_kernel_dimension]
  · rw [coefficient_cokernel_sum, blockDefect_cokernel_dimension]
    have hker : Module.finrank ℚ (LinearMap.ker (connectingTau M A)) = 0 := Module.finrank_zero_of_subsingleton
    rw [hker, add_zero]

/-- 原plus ηのH¹写像は局所原成分から全Aで同型。 -/
theorem plus_unit_bijective (A : Set Bool) : Function.Bijective (unitH1 rPlus A) :=
  unitH1_bijective_of_local rPlus A (WitnessFourPhi.plus_components A)
    (WitnessFourCoefficients.plus_gamma_components A) (fun F => isEmptyElim F.1)
/-- 同じ原plus係数欠損は全Aで(0,0)。 -/
theorem plus_unit_defect (A : Set Bool) : blockDefect (unitH1 rPlus A) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (plus_unit_bijective A)
/-- 同じ独立plus比較Jは原係数欠損とR零から(0,0)。 -/
theorem plus_defect (A : Set Bool) : blockDefect (rPlus.aSubnerveComparisonHom A).h1Map = (0,0) :=
  (defect_eq_unit_of_R_zero rPlus A (WitnessFourTriangle.plus_R_zero A)).trans (plus_unit_defect A)

/-- 原minus εのH¹両逆を同じ五項完全列とΦ零から生成する。 -/
def minusEvaluationEquiv (A : Set Bool) :
    (zeroExtension (pushforwardComplex rMinus A)).homology (1 : ℤ) ≃ₗ[ℚ]
      (zeroExtension (minus.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A))).homology (1 : ℤ) :=
  LinearEquiv.ofBijective (evaluationH1 rMinus A) ⟨evaluationH1_injective rMinus A,
    (evaluationH1_surjective_iff rMinus A).mpr
      (connectingTau_injective_of_phiH1_zero rMinus A (WitnessFourTriangle.minus_phiH1_zero A))⟩
/-- 原minus ε座標の順値は同じ標準評価射。 -/
theorem minusEvaluationEquiv_apply (A : Set Bool) (x) : minusEvaluationEquiv A x = evaluationH1 rMinus A x := rfl
/-- 原粗標準H¹の同じk period座標。 -/
def coarseCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (zeroExtension (N.targetSubsetComplex A)).homology (1 : ℤ) ≃ₗ[ℚ] ℚ :=
  (oldH1Equiv _).symm.trans (FaceRelationSubdivision.WitnessOne.oldSubsetPeriod A hA)
/-- 原minus細標準H¹の同じ二period座標。 -/
def minusFineCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (zeroExtension (minus.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A))).homology (1 : ℤ) ≃ₗ[ℚ] (ℚ × ℚ) :=
  (oldH1Equiv _).symm.trans (FaceRelationSubdivision.WitnessOne.minusSubsetPeriod A hA)
/-- 原minus P標準H¹を同じε両逆の二periodへ移す。 -/
def minusPCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (zeroExtension (pushforwardComplex rMinus A)).homology (1 : ℤ) ≃ₗ[ℚ] (ℚ × ℚ) :=
  (minusEvaluationEquiv A).trans (minusFineCoordinates A hA)

/-- 同じ原独立Tの旧商座標は同じ旧実subset写像。 -/
theorem minus_direct_old (A : Set Bool) (x) :
    (oldH1Equiv _).symm (directH1 rMinus A x) =
      (rMinus.aSubnerveComparisonHom A).h1Map ((oldH1Equiv _).symm x) := by
  apply (oldH1Equiv _).injective
  rw [LinearEquiv.apply_symm_apply, oldH1Equiv_natural, LinearEquiv.apply_symm_apply]
  rfl
/-- 原minus ηの全元射は同じk保存と追加period零になる。 -/
theorem minus_unit_coordinates (A : Set Bool) (hA : A.Nonempty) (x) :
    minusPCoordinates A hA (unitH1 rMinus A x) = (coarseCoordinates A hA x, 0) := by
  have hf : evaluationH1 rMinus A (unitH1 rMinus A x) = directH1 rMinus A x :=
    (congrArg (fun f => f x) (directH1_factor rMinus A)).symm
  change FaceRelationSubdivision.WitnessOne.minusSubsetPeriod A hA
    ((oldH1Equiv _).symm (evaluationH1 rMinus A (unitH1 rMinus A x))) = _
  rw [hf]
  exact (congrArg (FaceRelationSubdivision.WitnessOne.minusSubsetPeriod A hA)
    (minus_direct_old A x)).trans (FaceRelationSubdivision.WitnessOne.minus_subset_injection A hA _)

/-- 同じ原minus aは単射。 -/
theorem minus_unit_injective (A : Set Bool) (hA : A.Nonempty) : Function.Injective (unitH1 rMinus A) := by
  intro x y hxy
  apply (coarseCoordinates A hA).injective
  have hh := congrArg (minusPCoordinates A hA) hxy
  exact congrArg Prod.fst ((minus_unit_coordinates A hA x).symm.trans
    (hh.trans (minus_unit_coordinates A hA y)))
/-- 同じ原P上のa余核を追加periodへ両方向同定する。 -/
def minusUnitCokernelEquiv (A : Set Bool) (hA : A.Nonempty) :
    ((zeroExtension (pushforwardComplex rMinus A)).homology (1 : ℤ) ⧸ LinearMap.range (unitH1 rMinus A)) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv (unitH1 rMinus A) FaceRelationSubdivision.WitnessOne.periodInjection
    (coarseCoordinates A hA) (minusPCoordinates A hA) (minus_unit_coordinates A hA)).trans
      FaceRelationSubdivision.WitnessOne.injectionCokernel
/-- 非空Aの原minus係数欠損は同じ実商から(0,1)。 -/
theorem minus_unit_defect (A : Set Bool) (hA : A.Nonempty) : blockDefect (unitH1 rMinus A) = (0,1) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension]
    letI : Subsingleton (LinearMap.ker (unitH1 rMinus A)) := by
      rw [LinearMap.ker_eq_bot.mpr (minus_unit_injective A hA)]
      infer_instance
    exact Module.finrank_zero_of_subsingleton
  · rw [blockDefect_cokernel_dimension, (minusUnitCokernelEquiv A hA).finrank_eq]
    exact Module.finrank_self ℚ
/-- 同じ独立minus比較Jは原係数(0,1)とliteral R零から(0,1)。 -/
theorem minus_defect (A : Set Bool) (hA : A.Nonempty) : blockDefect (rMinus.aSubnerveComparisonHom A).h1Map = (0,1) :=
  (defect_eq_unit_of_R_zero rMinus A (WitnessFourTriangle.minus_R_zero A)).trans (minus_unit_defect A hA)

/-- 同じG134の一ラベルplus実診断と係数・fiber計算値の一致。 -/
theorem plus_block_agrees (l : LawValueLabel FaceRelationSubdivision.WitnessOne.laws) :
    blockDefect (FaceRelationSubdivision.WitnessOne.plusBlockHom l).h1Map = (0,0) :=
  FaceRelationSubdivision.WitnessOne.plus_block_defect l
/-- 同じG134の一ラベルminus実診断と係数・fiber計算値の一致。 -/
theorem minus_block_agrees (l : LawValueLabel FaceRelationSubdivision.WitnessOne.laws) :
    blockDefect (FaceRelationSubdivision.WitnessOne.minusBlockHom l).h1Map = (0,1) :=
  FaceRelationSubdivision.WitnessOne.minus_block_defect l

/-- 空Aの同じ原minus独立比較はG134の零cochain同定となる。 -/
theorem minus_empty_defect : blockDefect (rMinus.aSubnerveComparisonHom ∅).h1Map = (0,0) := by
  change blockDefect (FaceRelationSubdivision.WitnessOne.minusSubsetHom ∅).h1Map = (0,0)
  rw [FaceRelationSubdivision.WitnessOne.minus_empty_identity]
  exact (blockDefect_eq_zero_iff_bijective _).mpr
    (FaceRelationSubdivision.WitnessOne.emptySubsetEquiv minus).toHom_h1Map_bijective
/-- 空Aの原minus係数欠損も同じR零と実比較から零。 -/
theorem minus_empty_unit_defect : blockDefect (unitH1 rMinus ∅) = (0,0) :=
  (defect_eq_unit_of_R_zero rMinus ∅ (WitnessFourTriangle.minus_R_zero ∅)).symm.trans minus_empty_defect
/-- 同じ全Aのminus診断は空台0、非空台一追加period。 -/
theorem allA_minus_defect (A : Set Bool) : blockDefect (rMinus.aSubnerveComparisonHom A).h1Map =
    @ite (ℕ × ℕ) (A = ∅) (Classical.propDecidable _) (0,0) (0,1) := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_neg (Set.nonempty_iff_ne_empty.mp hA)]
    exact minus_defect A hA
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [if_pos rfl]
    exact minus_empty_defect

/-- 原ε座標で原a余核の代表値は同じ追加periodとなる。 -/
theorem minusUnitCokernelEquiv_mk (A : Set Bool) (hA : A.Nonempty) (x) :
    minusUnitCokernelEquiv A hA ((LinearMap.range (unitH1 rMinus A)).mkQ x) =
      (minusPCoordinates A hA x).2 := rfl
/-- 同じ原G134 e₂だけ1の閉cochain類を実fine標準商へ移す。 -/
def minusExtraClass (A : Set Bool) (hA : A.Nonempty) :=
  oldH1Equiv _ ((FaceRelationSubdivision.WitnessOne.minusSubsetEquiv A hA).h1Equiv.symm
    ((LinearMap.range (namedComplex minus).boundaryToCycles).mkQ
      (FaceRelationSubdivision.WitnessOne.minusSection (0,1))))
/-- 原追加fine類の同じ二periodは(0,1)。 -/
theorem minus_extra_period (A : Set Bool) (hA : A.Nonempty) :
    minusFineCoordinates A hA (minusExtraClass A hA) = (0,1) := by
  change FaceRelationSubdivision.WitnessOne.minusSubsetPeriod A hA
    ((oldH1Equiv (minus.targetSubsetComplex (FaceRelationSubdivision.WitnessOne.fineSubset A))).symm
      (minusExtraClass A hA)) = (0,1)
  dsimp only [minusExtraClass]
  rw [LinearEquiv.symm_apply_apply]
  dsimp only [FaceRelationSubdivision.WitnessOne.minusSubsetPeriod, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply, FaceRelationSubdivision.WitnessOne.minusH1Period_mk,
    FaceRelationSubdivision.WitnessOne.minusPeriod_section]
/-- 元fine追加代表を同じ原ε両逆で実P商へ移す。 -/
def minusPExtraClass (A : Set Bool) (hA : A.Nonempty) :=
  (minusEvaluationEquiv A).symm (minusExtraClass A hA)
/-- 元P追加類を実a余核で読む値は同じ1。 -/
theorem minus_extra_cokernel_period (A : Set Bool) (hA : A.Nonempty) :
    minusUnitCokernelEquiv A hA ((LinearMap.range (unitH1 rMinus A)).mkQ (minusPExtraClass A hA)) = 1 := by
  rw [minusUnitCokernelEquiv_mk]
  change (minusFineCoordinates A hA (minusEvaluationEquiv A ((minusEvaluationEquiv A).symm (minusExtraClass A hA)))).2 = 1
  rw [LinearEquiv.apply_symm_apply, minus_extra_period]
/-- 元P追加類は実a余核で非零、H¹保存不能の具体証拠。 -/
theorem minus_extra_cokernel_nonzero (A : Set Bool) (hA : A.Nonempty) :
    (LinearMap.range (unitH1 rMinus A)).mkQ (minusPExtraClass A hA) ≠ 0 := by
  intro hh
  have he := congrArg (minusUnitCokernelEquiv A hA) hh
  rw [minus_extra_cokernel_period, map_zero] at he
  exact one_ne_zero he
/-- 元kだけ1の原粗標準類。 -/
def oldLoopClass (A : Set Bool) (hA : A.Nonempty) :=
  oldH1Equiv _ ((FaceRelationSubdivision.WitnessOne.oldSubsetEquiv A hA).h1Equiv.symm
    ((LinearMap.range (namedComplex N).boundaryToCycles).mkQ
      (FaceRelationSubdivision.WitnessOne.oldLoopOnly 1)))
/-- 同じ原k類のperiodは1。 -/
theorem old_loop_period (A : Set Bool) (hA : A.Nonempty) :
    coarseCoordinates A hA (oldLoopClass A hA) = 1 := by
  dsimp only [coarseCoordinates, oldLoopClass, LinearEquiv.trans_apply,
    FaceRelationSubdivision.WitnessOne.oldSubsetPeriod]
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
    FaceRelationSubdivision.WitnessOne.oldH1Period_mk,
    FaceRelationSubdivision.WitnessOne.oldPeriod_loop]
/-- 原ηが保存する同じk類は原Pでも非零。 -/
theorem minus_mapped_loop_nonzero (A : Set Bool) (hA : A.Nonempty) :
    unitH1 rMinus A (oldLoopClass A hA) ≠ 0 := by
  intro hh
  have hp := minus_unit_coordinates A hA (oldLoopClass A hA)
  rw [hh,map_zero,old_loop_period] at hp
  exact one_ne_zero (congrArg Prod.fst hp).symm

end AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.defect_eq_unit_of_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.plus_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.plus_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.plus_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minusEvaluationEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minusEvaluationEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.coarseCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minusFineCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minusPCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_direct_old
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_unit_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_unit_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minusUnitCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.plus_block_agrees
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_block_agrees
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_empty_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_empty_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.allA_minus_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minusUnitCokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minusExtraClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_extra_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minusPExtraClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_extra_cokernel_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_extra_cokernel_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.oldLoopClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.old_loop_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics.minus_mapped_loop_nonzero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourDiagnostics
