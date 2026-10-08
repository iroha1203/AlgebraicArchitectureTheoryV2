import ResearchLean.AG.AtlasCoefficientFiber.PositivePreservation
import ResearchLean.AG.AtlasCoefficientFiber.DefectDiagnostics
import ResearchLean.AG.AtlasCoefficientFiber.LawHomologyCoordinates
import ResearchLean.AG.AtlasCoefficientFiber.LawCoefficientCones
import ResearchLean.AG.AtlasCoefficientFiber.LawSupportFamilyHomology

/-!
# 原始保存操作の同じ原a・literal R・τ

Implementation notes: 全Aの同じ旧J零から原aの同型とτ核零を導く。
原Law aは同じラベル別aの可逆座標から生成し、literal Law Rの直接族座標で
τ単射を照合する。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
namespace AAT.AG.AtlasCoefficientFiber.PositiveOperationPath
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (path : PositiveOperationPath qc Nc qf Nf)

/-- 全Aの同じ原aの両方向同型を元零診断から生成する。 -/
def unitEquiv (A : Set qc.Target) :
    (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ) ≃ₗ[ℚ]
      (zeroExtension (pushforwardComplex path.comparison A)).homology (1 : ℤ) :=
  unitH1EquivOfZeroDefect path.comparison A (path.subsetDefect_zero A)
/-- 同型の順写像は同じ原a。 -/
theorem unitEquiv_apply (A : Set qc.Target) (x) :
    path.unitEquiv A x = unitH1 path.comparison A x :=
  unitH1EquivOfZeroDefect_apply path.comparison A (path.subsetDefect_zero A) x
/-- 元aで戻すと生成同型の逆座標は元を回復する。 -/
theorem unitEquiv_symm_apply (A : Set qc.Target) (y) :
    unitH1 path.comparison A ((path.unitEquiv A).symm y) = y := by
  rw [← path.unitEquiv_apply, LinearEquiv.apply_symm_apply]
/-- 原aの値から戻す逆方向も同じ元を回復する。 -/
theorem unitEquiv_apply_symm (A : Set qc.Target) (x) :
    (path.unitEquiv A).symm (unitH1 path.comparison A x) = x := by
  rw [← path.unitEquiv_apply, LinearEquiv.symm_apply_apply]
/-- 同じ実τは全Aで単射。 -/
theorem tau_injective (A : Set qc.Target) : Function.Injective (connectingTau path.comparison A) :=
  ((coefficient_zeroDefect_iff path.comparison A).mp (path.subsetDefect_zero A)).2
/-- 全Aの原τの核は同じliteral R内で零。 -/
theorem tauKernel_eq_bot (A : Set qc.Target) : LinearMap.ker (connectingTau path.comparison A) = ⊥ :=
  tauKernel_eq_bot_of_zeroDefect path.comparison A (path.subsetDefect_zero A)
/-- 原η・ε・独立uの同じ三錐にあるtotal錐は全整数次数で零。 -/
theorem totalCone_isZero (A : Set qc.Target) (n : ℤ) :
    IsZero ((totalCone path.comparison A).homology n) := path.subsetCone_isZero A n

variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 元Law aの逆座標を同じ全ラベル原aの両逆から生成する。 -/
def lawUnitEquiv : (zeroExtension (Nc.lawGeneratedComplex laws ha)).homology (1 : ℤ) ≃ₗ[ℚ]
    (zeroExtension (lawPushforwardComplex path.comparison laws ha)).homology (1 : ℤ) :=
  (lawCoarseHomologyEquiv (Nc := Nc) laws ha 1).trans
    ((LinearEquiv.piCongrRight (fun l : LawValueLabel laws =>
      path.unitEquiv (labelValueFiber laws qc ha l))).trans
      (lawPushforwardHomologyEquiv path.comparison laws ha 1).symm)
/-- 原Law可逆座標の順写像は同じ元Law a。 -/
theorem lawUnitEquiv_apply (x) : path.lawUnitEquiv laws ha x = lawUnitH1 path.comparison laws ha x := by
  apply (lawPushforwardHomologyEquiv path.comparison laws ha 1).injective
  funext l
  dsimp only [lawUnitEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  rw [LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.piCongrRight_apply, path.unitEquiv_apply, unitH1_eq_standard]
  exact (lawUnit_homology_component path.comparison laws ha 1 x l).symm
/-- 同じ原Law aへ戻す逆座標は元を回復する。 -/
theorem lawUnitEquiv_symm_apply (y) :
    lawUnitH1 path.comparison laws ha ((path.lawUnitEquiv laws ha).symm y) = y := by
  rw [← path.lawUnitEquiv_apply, LinearEquiv.apply_symm_apply]
/-- 原Law aから逆に戻すと同じ粗Law元を回復する。 -/
theorem lawUnitEquiv_apply_symm (x) :
    (path.lawUnitEquiv laws ha).symm (lawUnitH1 path.comparison laws ha x) = x := by
  rw [← path.lawUnitEquiv_apply, LinearEquiv.symm_apply_apply]

/-- 原Lawのliteral Rにあるτは全元で単射。 -/
theorem lawTau_injective : Function.Injective (lawConnectingTau path.comparison laws ha) := by
  intro x y hxy
  apply (lawRFamilyEquiv path.comparison laws ha).injective
  funext l
  apply path.tau_injective (labelValueFiber laws qc ha l)
  have hl := congrArg (fun p => lawPushforwardHomologyEquiv path.comparison laws ha 2 p l) hxy
  dsimp only at hl
  rw [lawConnectingTau_component, lawConnectingTau_component] at hl
  exact hl
/-- 同じ原Law τの核はliteral Law R内で零。 -/
theorem lawTauKernel_eq_bot : LinearMap.ker (lawConnectingTau path.comparison laws ha) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (path.lawTau_injective laws ha)
/-- 同じ原Law三錐のtotal錐は全次数で零。 -/
theorem lawTotalCone_isZero (n : ℤ) : IsZero ((lawTotalCone path.comparison laws ha).homology n) :=
  path.lawCone_isZero laws ha n

/-- ラベル別任意台族の同じ原aを集める両方向座標。重複labelを保持する。 -/
def supportUnitEquiv (A : LawValueLabel laws → Set qc.Target) :
    ((l : LawValueLabel laws) → (zeroExtension (Nc.targetSubsetComplex (A l))).homology (1 : ℤ)) ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (zeroExtension (pushforwardComplex path.comparison (A l))).homology (1 : ℤ)) :=
  LinearEquiv.piCongrRight (fun l => path.unitEquiv (A l))
omit [Fintype Source] in
/-- 任意部分台族の可逆座標も同じ原aの各値である。 -/
theorem supportUnitEquiv_apply (A : LawValueLabel laws → Set qc.Target) (x) (l) :
    path.supportUnitEquiv laws A x l = unitH1 path.comparison (A l) (x l) :=
  path.unitEquiv_apply (A l) (x l)

/-- 任意ラベル別台族の同じ原τを元literal R族上へ集める。 -/
def supportTau (A : LawValueLabel laws → Set qc.Target) :
    ((l : LawValueLabel laws) → R path.comparison (A l)) →ₗ[ℚ]
      ((l : LawValueLabel laws) → (zeroExtension (pushforwardComplex path.comparison (A l))).homology (2 : ℤ)) :=
  LinearMap.pi (fun l => (connectingTau path.comparison (A l)).comp (LinearMap.proj l))
omit [Fintype Source] in
/-- 族τの各値は同じ原τ。 -/
theorem supportTau_apply (A : LawValueLabel laws → Set qc.Target) (x) (l) :
    path.supportTau laws A x l = connectingTau path.comparison (A l) (x l) := rfl
omit [Fintype Source] in
/-- 全ラベル別台族の原τは同じliteral R族で単射。 -/
theorem supportTau_injective (A : LawValueLabel laws → Set qc.Target) :
    Function.Injective (path.supportTau laws A) := by
  intro x y hxy
  funext l
  apply path.tau_injective (A l)
  exact congrFun hxy l

/-- 原台族SESで生成したnative tauの可逆座標は同じ全値。 -/
theorem supportTau_native (A : LawValueLabel laws → Set qc.Target) (x) :
    path.supportTau laws A x = FiniteComplexFamily.homologyEquiv
      (fun l => zeroExtension (pushforwardComplex path.comparison (A l))) 2
      (supportFamilyTau path.comparison laws (A := A) x) := by
  funext l
  rw [path.supportTau_apply, supportFamilyTau_component]

/-- 同じ原部分台族SESのnative tauもliteral R族上で単射。 -/
theorem supportFamilyTau_injective (A : LawValueLabel laws → Set qc.Target) :
    Function.Injective (supportFamilyTau path.comparison laws (A := A)) := by
  intro x y hxy
  apply path.supportTau_injective laws A
  rw [path.supportTau_native, path.supportTau_native, hxy]

end AAT.AG.AtlasCoefficientFiber.PositiveOperationPath
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.unitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.unitEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.unitEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.unitEquiv_apply_symm
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.tau_injective
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.tauKernel_eq_bot
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.totalCone_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawUnitEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawUnitEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawUnitEquiv_apply_symm
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawTau_injective
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawTauKernel_eq_bot
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawTotalCone_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.supportUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.supportUnitEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.supportTau
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.supportTau_apply
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.supportTau_injective
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.supportTau_native
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.supportFamilyTau_injective
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.PositiveOperationPath
