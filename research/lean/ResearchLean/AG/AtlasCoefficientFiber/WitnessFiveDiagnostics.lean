import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveRepresentatives
import Mathlib.Algebra.Exact

/-!
# G-135 W5：指定e/h代表と全Φを使う列の反証

## Implementation notes

正しいεが可逆でP H²が零という同じ生成比較に対し、全Φ項を置いた任意の二射の
完全性を反証する。単なる次元差の観測を反証の代替にはしない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 原Pの次数2は粗面なしのη両逆から零。 -/
theorem pC2_subsingleton (A : Set Bool) : Subsingleton (pushforwardComplex M A).C2 := by
  letI : IsEmpty (Nc.FaceInTargetSubset A) := ⟨fun f => Empty.elim f.1⟩
  have hc : Subsingleton (Nc.targetSubsetComplex A).C2 := by
    change Subsingleton (Nc.FaceInTargetSubset A → ℚ)
    infer_instance
  exact (etaEquiv A).e2.toEquiv.subsingleton_congr.mp hc
/-- 原P標準H²も全Aで零。 -/
theorem pH2_subsingleton (A : Set Bool) : Subsingleton ((zeroExtension (pushforwardComplex M A)).homology (2:ℤ)) := by
  letI := pC2_subsingleton A
  exact (oldH2Equiv (pushforwardComplex M A)).toEquiv.subsingleton_congr.mp inferInstance
/-- 全Φの非零k類を元εと零P H²の間へ入れる任意の二射は完全にならない。 -/
theorem wholePhi_sequence_not_exact (A : Set Bool) (hA : A.Nonempty)
    (g : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A))).homology (1:ℤ) →ₗ[ℚ]
      ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1))
    (t : ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) →ₗ[ℚ]
      (zeroExtension (pushforwardComplex M A)).homology (2:ℤ)) :
    ¬ (Function.Exact (evaluationH1 M A) g ∧ Function.Exact g t) := by
  rintro ⟨hg,ht⟩
  have hg0 (x) : g x = 0 := by
    obtain ⟨z,rfl⟩ := (evaluation_bijective A).2 x
    exact hg.apply_apply_eq_zero z
  letI := pH2_subsingleton A
  have hy : t (wholePhiK A) = 0 := Subsingleton.elim _ _
  obtain ⟨x,hx⟩ := (ht (wholePhiK A)).mp hy
  exact wholePhiK_nonzero A hA (hx.symm.trans (hg0 x))
/-- 指定粗e/hの単独1原閉cochain。 -/
def coarseLoopCycle (i : Fin 2) : LinearMap.ker (namedComplex Nc).d1 :=
  ⟨Pi.single i 1,by rw [LinearMap.mem_ker,coarse_d1_zero]; rfl⟩
/-- 指定粗e/hの原商類。 -/
def coarseNamedLoop (i : Fin 2) : (namedComplex Nc).H1 := Submodule.Quotient.mk (coarseLoopCycle i)
/-- 指定細e/hの単独1、原k値0の閉cochain。 -/
def fineLoopCycle (i : Fin 2) : LinearMap.ker (namedComplex Nf).d1 :=
  ⟨![(Pi.single i (1:ℚ) : Fin 2 → ℚ) 0,(Pi.single i (1:ℚ) : Fin 2 → ℚ) 1,0],(fine_cycle_iff _).mpr rfl⟩
/-- 指定細e/hの原商類。 -/
def fineNamedLoop (i : Fin 2) : (namedComplex Nf).H1 := (LinearMap.range (namedComplex Nf).boundaryToCycles).mkQ (fineLoopCycle i)
/-- 原粗代表のe/h全periodは単独1。 -/
theorem coarseNamedLoop_period (i : Fin 2) : coarseNamedCoordinates (coarseNamedLoop i) = Pi.single i 1 := rfl
/-- 原細代表のe/h全periodも単独1。 -/
theorem fineNamedLoop_period (i : Fin 2) : fineNamedCoordinates (fineNamedLoop i) = Pi.single i 1 := by
  rw [fineNamedLoop,fineNamedCoordinates_mk]
  funext j; fin_cases j <;> rfl
/-- 元全支持から指定粗e/h原代表を移す。 -/
def coarseLoop (A : Set Bool) (hA : A.Nonempty) (i : Fin 2) :=
  (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).h1Equiv.symm (coarseNamedLoop i)
/-- 元全支持から指定細e/h原代表を独立に移す。 -/
def fineLoop (A : Set Bool) (hA : A.Nonempty) (i : Fin 2) :=
  (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).h1Equiv.symm (fineNamedLoop i)
/-- 原粗subset代表の全period。 -/
theorem coarseLoop_period (A : Set Bool) (hA : A.Nonempty) (i : Fin 2) :
    coarseCoordinates A hA (coarseLoop A hA i) = Pi.single i 1 := by
  rw [coarseCoordinates_apply,coarseLoop,LinearEquiv.apply_symm_apply,coarseNamedLoop_period]
/-- 原細subset代表の全period。 -/
theorem fineLoop_period (A : Set Bool) (hA : A.Nonempty) (i : Fin 2) :
    fineCoordinates A hA (fineLoop A hA i) = Pi.single i 1 := by
  rw [fineCoordinates_apply,fineLoop,LinearEquiv.apply_symm_apply,fineNamedLoop_period]
/-- 同実uは指定e/hの双方を元単独1代表へ送る。 -/
theorem loop_preserved (A : Set Bool) (hA : A.Nonempty) (i : Fin 2) :
    (M.aSubnerveComparisonHom A).h1Map (coarseLoop A hA i) = fineLoop A hA i := by
  apply (fineCoordinates A hA).injective
  rw [subset_map,coarseLoop_period,fineLoop_period]
/-- 同粗e/h類は双方非零。 -/
theorem coarseLoop_nonzero (A : Set Bool) (hA : A.Nonempty) (i : Fin 2) : coarseLoop A hA i ≠ 0 := by
  classical
  intro hh
  have he := congrArg (fun z => coarseCoordinates A hA z i) hh
  change coarseCoordinates A hA (coarseLoop A hA i) i = coarseCoordinates A hA 0 i at he
  rw [coarseLoop_period,Pi.single_eq_same,map_zero] at he
  exact one_ne_zero he
/-- 同細e/h類も双方非零。 -/
theorem fineLoop_nonzero (A : Set Bool) (hA : A.Nonempty) (i : Fin 2) : fineLoop A hA i ≠ 0 := by
  classical
  intro hh
  have he := congrArg (fun z => fineCoordinates A hA z i) hh
  change fineCoordinates A hA (fineLoop A hA i) i = fineCoordinates A hA 0 i at he
  rw [fineLoop_period,Pi.single_eq_same,map_zero] at he
  exact one_ne_zero he
/-- 標準H¹の同原Tも指定e/hを保存する。 -/
theorem standard_loop_preserved (A : Set Bool) (hA : A.Nonempty) (i : Fin 2) :
    directH1 M A (oldH1Equiv _ (coarseLoop A hA i)) = oldH1Equiv _ (fineLoop A hA i) := by
  rw [directH1_old,loop_preserved]

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.pC2_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.pH2_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.wholePhi_sequence_not_exact
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseLoopCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseNamedLoop
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineLoopCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineNamedLoop
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseNamedLoop_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineNamedLoop_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseLoop
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineLoop
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseLoop_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineLoop_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.loop_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseLoop_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineLoop_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.standard_loop_preserved
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
