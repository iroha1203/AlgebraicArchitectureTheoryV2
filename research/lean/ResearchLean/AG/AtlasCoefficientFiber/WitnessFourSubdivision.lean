import ResearchLean.AG.AtlasCoefficientFiber.SubdivisionCoefficients
import ResearchLean.AG.AtlasCoefficientFiber.SubdivisionFiber
import ResearchLean.AG.AtlasCoefficientFiber.PositiveCoefficientPreservation
import ResearchLean.AG.FaceRelationSubdivision.WitnessTwoDiagnostics

/-!
# W4：G134の同じ三つの部分台分割と原順像

Implementation notes: G134のCase/old/edge/fine/comparisonをそのまま使う。
原局所係数からηの全次数同型を構成し、同じ原r/s/hへ原独立比較を接続する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open FaceRelationSubdivision.WitnessTwo (Case old edge fine comparison contraction)

/-- 同じ原G134入力の単一正操作列。 -/
def path (i : Case) : PositiveOperationPath ConnectedFaceWitness.q (old i) ConnectedFaceWitness.q (fine i) :=
  PositiveOperationPath.single (.subdivision (old i) (edge i))
/-- 元Pの入力比較は同じG134の原collapseそのもの。 -/
theorem path_comparison (i : Case) : (path i).comparison = comparison i :=
  PositiveOperationPath.single_comparison _

/-- 同じW2a/b/cの全Φ・Γ・Λから原ηの両逆を生成する。 -/
def etaEquiv (i : Case) (A : Set Bool) : ThreeCochainComplex.CochainEquiv
    ((old i).targetSubsetComplex A) (pushforwardComplex (comparison i) A) :=
  SubdivisionCoefficients.etaEquiv (old i) (edge i) A
/-- 全三成分の同型順射は同じ原η。 -/
theorem etaEquiv_toHom (i : Case) (A : Set Bool) :
    (etaEquiv i A).toHom = unitHom (comparison i) A := rfl
/-- 原Pから原粗cochainへの全三次数座標は実η逆である。 -/
def pOriginalEquiv (i : Case) (A : Set Bool) : ThreeCochainComplex.CochainEquiv
    (pushforwardComplex (comparison i) A) ((old i).targetSubsetComplex A) := (etaEquiv i A).symm
/-- 原ηと生成P座標の全三成分の可換式。 -/
theorem eta_square (i : Case) (A : Set Bool) :
    cochainComp (unitHom (comparison i) A) (pOriginalEquiv i A).toHom =
      cochainId ((old i).targetSubsetComplex A) := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro z
  · change (etaEquiv i A).e0.symm ((etaEquiv i A).e0 z) = z
    exact LinearEquiv.symm_apply_apply _ z
  · change (etaEquiv i A).e1.symm ((etaEquiv i A).e1 z) = z
    exact LinearEquiv.symm_apply_apply _ z
  · change (etaEquiv i A).e2.symm ((etaEquiv i A).e2 z) = z
    exact LinearEquiv.symm_apply_apply _ z

/-- 原全Φは同じcまたは点から実H¹零。 -/
theorem phiH1_zero (i : Case) (A : Set Bool) (c : (old i).ChartInTargetSubset A) :
    Subsingleton (phiComplex (comparison i) A c).H1 :=
  SubdivisionFiber.phiH1_zero (old i) (edge i) A c
/-- 原κの同じ全値は零。 -/
theorem kappa_zero (i : Case) (A : Set Bool) : kappa (comparison i) A = 0 :=
  SubdivisionFiber.kappa_zero (old i) (edge i) A
/-- 原κ*の同じ全値は零。 -/
theorem kappaStar_zero (i : Case) (A : Set Bool) : kappaStar (comparison i) A = 0 :=
  SubdivisionFiber.kappaStar_zero (old i) (edge i) A
/-- 同じliteral Rの零性は全Aを保持する。 -/
theorem R_zero (i : Case) (A : Set Bool) : Subsingleton (R (comparison i) A) :=
  SubdivisionFiber.R_zero (old i) (edge i) A
/-- 同じ原標準τは全Aで零。 -/
theorem tau_zero (i : Case) (A : Set Bool) : connectingTau (comparison i) A = 0 :=
  SubdivisionFiber.tau_zero (old i) (edge i) A

/-- 原ηの実H¹比較は局所原係数から全Aで同型。 -/
theorem unit_bijective (i : Case) (A : Set Bool) : Function.Bijective (unitH1 (comparison i) A) :=
  unitH1_bijective_of_local (comparison i) A
    (SubdivisionCoefficients.phi_components (old i) (edge i) A)
    (SubdivisionCoefficients.gamma_components (old i) (edge i) A)
    (SubdivisionCoefficients.lambda_single (old i) (edge i) A)
/-- 原独立比較の同じJは係数・fiberの必要十分条件から零。 -/
theorem defect_zero (i : Case) (A : Set Bool) : blockDefect ((comparison i).aSubnerveComparisonHom A).h1Map = (0,0) :=
  (coefficient_zeroDefect_iff (comparison i) A).mpr ⟨unit_bijective i A,
    connectingTau_injective_of_phiH1_zero (comparison i) A (phiH1_zero i A)⟩
/-- 同じ原τの核はliteral R内で零。 -/
theorem tauKernel_zero (i : Case) (A : Set Bool) : LinearMap.ker (connectingTau (comparison i) A) = ⊥ :=
  tauKernel_eq_bot_of_zeroDefect (comparison i) A (defect_zero i A)
/-- 同じ原独立uとG134のr/s/hから、総錐は全整数次数で零。 -/
theorem totalCone_zero (i : Case) (A : Set Bool) (n : ℤ) :
    IsZero ((totalCone (comparison i) A).homology n) := by
  have hh := (path i).totalCone_isZero A n
  rw [path_comparison] at hh
  exact hh

/-- 同じ元G134収縮rは同じ原Pを介した独立uへ接続する。 -/
theorem contraction_factorization (i : Case) (A : Set Bool) :
    (contraction i A).rHom = (comparison i).targetSubsetComparisonHom A A
      (IncidenceSupportedComparison.selfSubsetMapsTo (q := ConnectedFaceWitness.q) A) :=
  FaceRelationSubdivision.WitnessTwo.subset_comparison i A
/-- 同じr/sの三次数往復と全h補正は元G134定理の同じ選択出力。 -/
theorem contraction_rs (i : Case) (A : Set Bool) :
    ((EdgeSubdivision.r0 (old i) (edge i)).selected A).comp ((EdgeSubdivision.s0 (old i) (edge i)).selected A) = LinearMap.id ∧
    ((EdgeSubdivision.r1 (old i) (edge i)).selected A).comp ((EdgeSubdivision.s1 (old i) (edge i)).selected A) = LinearMap.id ∧
    ((EdgeSubdivision.r2 (old i) (edge i)).selected A).comp ((EdgeSubdivision.s2 (old i) (edge i)).selected A) = LinearMap.id :=
  FaceRelationSubdivision.WitnessTwo.rs_all i A

/-- 同じ非定数Lawの原aは元全labelの両方向同型。 -/
def lawUnitEquiv (i : Case) :
    (zeroExtension ((old i).lawGeneratedComplex ConnectedFaceWitness.laws ConnectedFaceWitness.adequate)).homology (1 : ℤ) ≃ₗ[ℚ]
      (zeroExtension (lawPushforwardComplex (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate)).homology (1 : ℤ) := by
  rw [← path_comparison]
  exact (path i).lawUnitEquiv ConnectedFaceWitness.laws ConnectedFaceWitness.adequate
/-- 同じ原Law total錐は元ラベルを保って全次数零。 -/
theorem lawTotalCone_zero (i : Case) (n : ℤ) :
    IsZero ((lawTotalCone (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate).homology n) := by
  have hh := (path i).lawTotalCone_isZero ConnectedFaceWitness.laws ConnectedFaceWitness.adequate n
  rw [path_comparison] at hh
  exact hh

/-- 同じ原P粗座標におけるεは独立に生成したG134原比較となる。 -/
theorem epsilon_square (i : Case) (A : Set Bool) :
    cochainComp (pOriginalEquiv i A).toHom ((comparison i).aSubnerveComparisonHom A) =
      evaluationHom (comparison i) A := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro z
  · have hh := congrArg (fun f => f.f0 ((etaEquiv i A).e0.symm z))
      (aSubnerveComparisonHom_factorization (comparison i) A)
    change ((comparison i).aSubnerveComparisonHom A).f0 ((etaEquiv i A).e0.symm z) =
      (evaluationHom (comparison i) A).f0 ((etaEquiv i A).e0 ((etaEquiv i A).e0.symm z)) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
  · have hh := congrArg (fun f => f.f1 ((etaEquiv i A).e1.symm z))
      (aSubnerveComparisonHom_factorization (comparison i) A)
    change ((comparison i).aSubnerveComparisonHom A).f1 ((etaEquiv i A).e1.symm z) =
      (evaluationHom (comparison i) A).f1 ((etaEquiv i A).e1 ((etaEquiv i A).e1.symm z)) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
  · have hh := congrArg (fun f => f.f2 ((etaEquiv i A).e2.symm z))
      (aSubnerveComparisonHom_factorization (comparison i) A)
    change ((comparison i).aSubnerveComparisonHom A).f2 ((etaEquiv i A).e2.symm z) =
      (evaluationHom (comparison i) A).f2 ((etaEquiv i A).e2 ((etaEquiv i A).e2.symm z)) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
/-- 同じ元Law aの全単射は原正操作列の元a両逆から得る。 -/
theorem law_unit_bijective (i : Case) :
    Function.Bijective (lawUnitH1 (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate) := by
  have he : ((path i).lawUnitEquiv ConnectedFaceWitness.laws ConnectedFaceWitness.adequate).toLinearMap =
      lawUnitH1 (path i).comparison ConnectedFaceWitness.laws ConnectedFaceWitness.adequate :=
    LinearMap.ext ((path i).lawUnitEquiv_apply ConnectedFaceWitness.laws ConnectedFaceWitness.adequate)
  have hb := ((path i).lawUnitEquiv ConnectedFaceWitness.laws ConnectedFaceWitness.adequate).bijective
  change Function.Bijective ((path i).lawUnitEquiv ConnectedFaceWitness.laws ConnectedFaceWitness.adequate).toLinearMap at hb
  rw [he, path_comparison] at hb
  exact hb
/-- 原二Law係数欠損は同じ原aから零。 -/
theorem law_unit_defect (i : Case) :
    blockDefect (lawUnitH1 (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (law_unit_bijective i)
/-- 同じ原二Law literal Rは零。 -/
theorem law_R_zero (i : Case) : Subsingleton (lawR (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate) := by
  letI (l : LawValueLabel ConnectedFaceWitness.laws) := R_zero i
    (labelValueFiber ConnectedFaceWitness.laws ConnectedFaceWitness.q ConnectedFaceWitness.adequate l)
  exact (lawRFamilyEquiv (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate).toEquiv.subsingleton
/-- 同じ原二Law標準τは零。 -/
theorem law_tau_zero (i : Case) : lawConnectingTau (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate = 0 := by
  letI := law_R_zero i
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
/-- 同じ原二Law κは原全labelのκ零から零。 -/
theorem law_kappa_zero (i : Case) : lawKappa (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate = 0 := by
  apply LinearMap.ext
  intro x
  funext l
  rw [lawKappa_apply, kappa_zero, LinearMap.zero_apply]
  rfl
/-- 同じ原二Law κ*は原全labelのκ*零から零。 -/
theorem law_kappaStar_zero (i : Case) : lawKappaStar (comparison i) ConnectedFaceWitness.laws ConnectedFaceWitness.adequate = 0 := by
  apply LinearMap.ext
  intro x
  funext l
  rw [lawKappaStar_apply, kappaStar_zero, LinearMap.zero_apply]
  rfl
/-- 同じ原有限和の全三次数h補正も元G134そのもの。 -/
theorem contraction_sr_h (i : Case) (A : Set Bool) :
    ((EdgeSubdivision.s0 (old i) (edge i)).selected A).comp ((EdgeSubdivision.r0 (old i) (edge i)).selected A)+
      (chainD1 (fine i) A).comp ((EdgeSubdivision.h0 (old i) (edge i)).selected A)=LinearMap.id ∧
    ((EdgeSubdivision.s1 (old i) (edge i)).selected A).comp ((EdgeSubdivision.r1 (old i) (edge i)).selected A)+
      (chainD2 (fine i) A).comp ((EdgeSubdivision.h1 (old i) (edge i)).selected A)+
      ((EdgeSubdivision.h0 (old i) (edge i)).selected A).comp (chainD1 (fine i) A)=LinearMap.id ∧
    ((EdgeSubdivision.s2 (old i) (edge i)).selected A).comp ((EdgeSubdivision.r2 (old i) (edge i)).selected A)+
      ((EdgeSubdivision.h1 (old i) (edge i)).selected A).comp (chainD2 (fine i) A)=LinearMap.id :=
  FaceRelationSubdivision.WitnessTwo.sr_h_all i A

end AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.path
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.path_comparison
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.etaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.etaEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.pOriginalEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.eta_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.phiH1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.defect_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.tauKernel_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.totalCone_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.contraction_factorization
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.contraction_rs
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.lawUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.lawTotalCone_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.epsilon_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.law_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.law_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.law_R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.law_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.law_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.law_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision.contraction_sr_h
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourSubdivision
