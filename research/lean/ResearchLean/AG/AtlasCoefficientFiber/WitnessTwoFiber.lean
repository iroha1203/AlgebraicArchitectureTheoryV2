import ResearchLean.AG.AtlasCoefficientFiber.WitnessTwoComparison
import ResearchLean.AG.AtlasCoefficientFiber.WitnessTwoCoefficients
import ResearchLean.AG.AtlasCoefficientFiber.PurePreservation

/-!
# G-135 W2：同原fiber、R、k代表とpure非保存

## Implementation notes

κとτの零性は原混在面なしから導く。原Rの全商座標はpure定理の両逆で生成する。
pure同定は原mixed空を証明した後だけに用い、一般混在Rを全Phiと定義する方法は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessTwo
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 原Φ辺はk一本と両逆対応、hは原none条件から排除。 -/
def phiEdgeEquiv (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiEdge M A c ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact {
    toFun _ := 0
    invFun _ := ⟨fullSelected Nf.edgeSupport (fullSupport_edge Nf (fun _ => rfl))
      _ (fine_nonempty A hA) 1, rfl,by apply Subtype.ext; exact Subsingleton.elim _ _⟩
    left_inv e := by
      apply Subtype.ext; apply Subtype.ext
      rcases e with ⟨⟨e,hs⟩,he,hc⟩
      fin_cases e
      · simp [M] at he
      · rfl
    right_inv _ := Subsingleton.elim _ _ }
/-- 元Φ微分零は同じloopの二端点差。 -/
theorem phi_d0_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).d0 = 0 := by
  letI := phiChart_subsingleton A c
  apply LinearMap.ext; intro z; funext e
  change phiD0 M A c z e = 0
  rw [phiD0_apply M A c z e,Subsingleton.elim (phiEndpoint M A e true) (phiEndpoint M A e false)]
  exact sub_self _
/-- 元Φ第二微分零は指定面なし。 -/
theorem phi_d1_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).d1 = 0 := by
  apply LinearMap.ext; intro z; funext f; exact Fin.elim0 f.1.1
/-- 元Φ全H¹商と原k値ℚの両逆。 -/
def phiCoordinates (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).H1 ≃ₗ[ℚ] ℚ :=
  (zeroDifferentialH1Equiv _ (phi_d0_zero A c) (phi_d1_zero A c)).trans
    ((LinearEquiv.piCongrLeft' ℚ (fun _ : PhiEdge M A c => ℚ) (phiEdgeEquiv A c)).trans
      (LinearEquiv.funUnique (Fin 1) ℚ ℚ))
/-- 原Φ Betti数は同k全商で1。 -/
theorem phi_dimension (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Module.finrank ℚ (phiComplex M A c).H1 = 1 := (phiCoordinates A c).finrank_eq.trans (Module.finrank_self ℚ)
/-- 非空Aの同原粗chartは一つ。 -/
def coarseChartEquiv (A : Set Bool) (hA : A.Nonempty) : Nc.ChartInTargetSubset A ≃ Fin 1 where
  toFun c := c.1
  invFun i := fullSelected Nc.chartSupport (fun _ => rfl) A hA i
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
/-- 全実ΦのBetti和は非空Aで1。 -/
theorem phi_dimension_sum (A : Set Bool) (hA : A.Nonempty) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 = 1 := by
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  simp only [phi_dimension,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact Fintype.card_congr (coarseChartEquiv A hA)
/-- 原混在面なしから原κは零。 -/
theorem kappa_zero (A : Set Bool) : kappa M A = 0 := by
  letI := mixed_empty A
  exact kappa_zero_of_mixed_isEmpty (Source := WitnessCommon.Source) (qc := qc) (qf := qf)
    (h := coarser) (Nc := Nc) (Nf := Nf) A M
/-- 同じ原κ*も零、全Phiからの実射。 -/
theorem kappaStar_zero (A : Set Bool) : kappaStar M A = 0 := by
  letI := mixed_empty A
  exact pure_kappaStar_zero M A
/-- 原κ*rank零。 -/
theorem kappaStar_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (kappaStar M A)) = 0 := by
  rw [kappaStar_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- 原Rは原mixed空の下で全Phiの同じ値に対応する。 -/
def rFamilyEquiv (A : Set Bool) : R M A ≃ₗ[ℚ] ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) := by
  letI := mixed_empty A
  exact pureFiberREquiv M A
/-- 原Rと同k値ℚの全商両逆。 -/
def rCoordinates (A : Set Bool) (hA : A.Nonempty) : R M A ≃ₗ[ℚ] ℚ :=
  (rFamilyEquiv A).trans ((LinearEquiv.piCongrRight (phiCoordinates A)).trans
    ((fullSelectedCochain Nc.chartSupport (fun _ => rfl) A hA).trans (LinearEquiv.funUnique (Fin 1) ℚ ℚ)))
/-- 原R次元は同じkの1。 -/
theorem r_dimension (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ (R M A) = 1 :=
  (rCoordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- 原τは同じ標準連結射の零射。 -/
theorem tau_zero (A : Set Bool) : connectingTau M A = 0 := by
  letI := mixed_empty A
  exact connectingTau_zero_of_mixed_isEmpty (Source := WitnessCommon.Source) (qc := qc) (qf := qf)
    (h := coarser) (Nc := Nc) (Nf := Nf) A M
/-- 原τrank零。 -/
theorem tau_rank (A : Set Bool) : Module.finrank ℚ (LinearMap.range (connectingTau M A)) = 0 := by
  rw [tau_zero,LinearMap.range_zero]
  exact Module.finrank_zero_of_subsingleton
/-- k上1の原fiber cocycle。 -/
def phiKCycle (A : Set Bool) (c : Nc.ChartInTargetSubset A) : LinearMap.ker (phiComplex M A c).d1 :=
  ⟨fun _ => 1,by funext f; exact Fin.elim0 f.1.1⟩
/-- 同cocycleの原H¹商類。 -/
def phiKClass (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).H1 :=
  (LinearMap.range (phiComplex M A c).boundaryToCycles).mkQ (phiKCycle A c)
/-- 元k fiber類の同periodは1。 -/
theorem phiK_period (A : Set Bool) (c : Nc.ChartInTargetSubset A) : phiCoordinates A c (phiKClass A c) = 1 := rfl
/-- 元fiber類は非零。 -/
theorem phiK_nonzero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : phiKClass A c ≠ 0 := by
  intro h; have hh := congrArg (phiCoordinates A c) h
  rw [phiK_period,map_zero] at hh
  exact one_ne_zero hh
/-- 同k原fiber類からliteral Rの元を生成する。 -/
def rK (A : Set Bool) : R M A := (rFamilyEquiv A).symm (phiKClass A)
/-- Rの生成元も同k period1。 -/
theorem rK_period (A : Set Bool) (hA : A.Nonempty) : rCoordinates A hA (rK A) = 1 := by
  simp only [rCoordinates,rK,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  rfl
/-- 同Rは非零。 -/
theorem rK_nonzero (A : Set Bool) (hA : A.Nonempty) : rK A ≠ 0 := by
  intro h; have hh := congrArg (rCoordinates A hA) h
  rw [rK_period,map_zero] at hh
  exact one_ne_zero hh
/-- 粗hの元subset cocycle。 -/
def coarseCycle (A : Set Bool) (z : Fin 1 → ℚ) : LinearMap.ker (Nc.targetSubsetComplex A).d1 :=
  ⟨fun e => z e.1,by funext f; exact Fin.elim0 f.1⟩
/-- 細h,kの元subset cocycle。 -/
def fineCycle (A : Set Bool) (z : Fin 2 → ℚ) :
    LinearMap.ker (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).d1 :=
  ⟨fun e => z e.1,by funext f; exact Fin.elim0 f.1⟩
/-- 原粗cycleの原商類。 -/
def coarseClass (A : Set Bool) (z : Fin 1 → ℚ) : (Nc.targetSubsetComplex A).H1 :=
  (LinearMap.range (Nc.targetSubsetComplex A).boundaryToCycles).mkQ (coarseCycle A z)
/-- 原細cycleの原商類。 -/
def fineClass (A : Set Bool) (z : Fin 2 → ℚ) :
    (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 :=
  (LinearMap.range (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).boundaryToCycles).mkQ (fineCycle A z)
/-- 元粗代表の全座標。 -/
theorem coarseClass_coordinates (A : Set Bool) (hA : A.Nonempty) (z) : coarseCoordinates A hA (coarseClass A z) = z := rfl
/-- 元細代表の全座標。 -/
theorem fineClass_coordinates (A : Set Bool) (hA : A.Nonempty) (z) : fineCoordinates A hA (fineClass A z) = z := rfl
/-- 同原h類は実uで保存する。 -/
theorem h_preserved (A : Set Bool) (hA : A.Nonempty) :
    (M.aSubnerveComparisonHom A).h1Map (coarseClass A ![1]) = fineClass A ![1,0] := by
  apply (fineCoordinates A hA).injective
  rw [subset_map,coarseClass_coordinates,fineClass_coordinates]
  rfl
/-- 原粗h類は非零。 -/
theorem coarse_h_nonzero (A : Set Bool) (hA : A.Nonempty) : coarseClass A ![1] ≠ 0 := by
  intro h; have hh := congrArg (fun x => coarseCoordinates A hA x 0) h
  change coarseCoordinates A hA (coarseClass A ![1]) 0 = coarseCoordinates A hA 0 0 at hh
  rw [coarseClass_coordinates,map_zero] at hh
  exact one_ne_zero hh
/-- 原細h類も非零。 -/
theorem fine_h_nonzero (A : Set Bool) (hA : A.Nonempty) : fineClass A ![1,0] ≠ 0 := by
  intro h; have hh := congrArg (fun x => fineCoordinates A hA x 0) h
  change fineCoordinates A hA (fineClass A ![1,0]) 0 = fineCoordinates A hA 0 0 at hh
  rw [fineClass_coordinates,map_zero] at hh
  exact one_ne_zero hh
/-- k単独1は同実余核のperiod1。 -/
theorem k_cokernel_period (A : Set Bool) (hA : A.Nonempty) :
    cokernelEquiv A hA ((LinearMap.range (M.aSubnerveComparisonHom A).h1Map).mkQ (fineClass A ![0,1])) = 1 := rfl
/-- 同実余核類は非零。 -/
theorem k_cokernel_nonzero (A : Set Bool) (hA : A.Nonempty) :
    (LinearMap.range (M.aSubnerveComparisonHom A).h1Map).mkQ (fineClass A ![0,1]) ≠ 0 := by
  intro h; have hh := congrArg (cokernelEquiv A hA) h
  rw [k_cokernel_period,map_zero] at hh
  exact one_ne_zero hh
/-- 同指定pure例は新C3primeの原Φ H¹零に違反する。 -/
theorem C3prime_failure (A : Set Bool) (hA : A.Nonempty) :
    ¬ ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1 := by
  intro hz
  let c := (coarseChartEquiv A hA).symm 0
  letI := hz c
  exact phiK_nonzero A c (Subsingleton.elim _ _)
/-- 同pure例の実比較は非保存、同原J01による。 -/
theorem nonpreservation (A : Set Bool) (hA : A.Nonempty) :
    blockDefect (M.aSubnerveComparisonHom A).h1Map ≠ (0,0) := by
  rw [defect A hA]
  exact by decide

/-- k単独1の同じ細cochainが原Φ代表を与える。 -/
theorem k_cochain_fiber (A : Set Bool) (c : Nc.ChartInTargetSubset A) (e : PhiEdge M A c) :
    (fineCycle A ![0,1]).val e.1 = (phiKCycle A c).val e := by
  rcases e with ⟨⟨e,hs⟩,he,hc⟩
  fin_cases e
  · simp [M] at he
  · rfl
/-- 空Aの元Rは全Phi添字も空なので零。 -/
theorem empty_R_subsingleton : Subsingleton (R M ∅) := by
  letI : IsEmpty (Nc.ChartInTargetSubset ∅) := ⟨fun c => by
    obtain ⟨t,ht,ha⟩ := c.2; exact ha⟩
  infer_instance
/-- 同原Rの空A次元は零。 -/
theorem empty_R_dimension : Module.finrank ℚ (R M ∅) = 0 := by
  letI := empty_R_subsingleton
  exact Module.finrank_zero_of_subsingleton
/-- 全Aの同原R次元、空Aを保持。 -/
theorem allA_R_dimension (A : Set Bool) :
    Module.finrank ℚ (R M A) = @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact r_dimension A hA
  · have ha := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [if_neg Set.not_nonempty_empty]; exact empty_R_dimension


/-- 同原H¹Qをliteral R経由でk値へ全両逆同定する。 -/
def qCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (zeroExtension (restrictionComplex M A)).homology (1 : ℤ) ≃ₗ[ℚ] ℚ :=
  (restrictionStandardHomologyREquiv M A).trans (rCoordinates A hA)
/-- 同原H¹Qも非空Aで1。 -/
theorem q_dimension (A : Set Bool) (hA : A.Nonempty) :
    Module.finrank ℚ ((zeroExtension (restrictionComplex M A)).homology (1 : ℤ)) = 1 :=
  (qCoordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- 全AのPhi Betti和は同非空/空行の1/0。 -/
theorem allA_phi_dimension_sum (A : Set Bool) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 =
      @ite ℕ A.Nonempty (Classical.propDecidable _) 1 0 := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact phi_dimension_sum A hA
  · have ha := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    letI : IsEmpty (Nc.ChartInTargetSubset ∅) := ⟨fun c => by
      obtain ⟨t,ht,ha⟩ := c.2; exact ha⟩
    rw [if_neg Set.not_nonempty_empty]
    exact Finset.sum_of_isEmpty _


/-- k単独1の同じ原細H¹類を、実五項列の制限射で原Rへ送る。 -/
def kFiberClass (A : Set Bool) : R M A := fiberRestrictionH1 M A
  (oldH1Equiv (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A))
    (fineClass A ![0,1]))
/-- 同cochainの実fiber類は非零。η可逆と同実余核非零から原完全性で検出する。 -/
theorem kFiberClass_nonzero (A : Set Bool) (hA : A.Nonempty) : kFiberClass A ≠ 0 := by
  intro hz
  obtain ⟨p,hp⟩ := (fiveTerm_exact_at_fineH1 M A _).mp hz
  obtain ⟨c,hc⟩ := (unit_bijective A).2 p
  let co := (oldH1Equiv (Nc.targetSubsetComplex A)).symm c
  have hm : directH1 M A c = oldH1Equiv
      (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)) (fineClass A ![0,1]) := by
    rw [directH1_factor,LinearMap.comp_apply,hc]
    exact hp
  have he := directH1_old M A co
  change directH1 M A ((oldH1Equiv (Nc.targetSubsetComplex A))
    ((oldH1Equiv (Nc.targetSubsetComplex A)).symm c)) = _ at he
  rw [LinearEquiv.apply_symm_apply] at he
  have ho := (oldH1Equiv (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A))).injective
    (he.symm.trans hm)
  apply k_cokernel_nonzero A hA
  rw [← ho]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨co,rfl⟩

end AAT.AG.AtlasCoefficientFiber.WitnessTwo
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phiEdgeEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phi_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phi_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phiCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phi_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseChartEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.kappaStar_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.rFamilyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.rCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.r_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phiKCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phiKClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phiK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phiK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.rK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.rK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.rK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseClass_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineClass_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.h_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarse_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fine_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.k_cokernel_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.k_cokernel_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.C3prime_failure
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.nonpreservation
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.k_cochain_fiber
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.empty_R_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.empty_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.allA_R_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.qCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.q_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.allA_phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.kFiberClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.kFiberClass_nonzero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessTwo
