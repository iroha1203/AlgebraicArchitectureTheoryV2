import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveRepresentatives

/-!
# G-135 W5：原Φ chain商と原混在閉路の全両逆

## Implementation notes

実微分の核と像を両方向に計算する。対合が非零であることだけを全商の
両逆の代替にはしない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 原Φ chainのaは同端点差で零。 -/
theorem phiBoundary1_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : phiBoundary1 M A c = 0 := by
  letI := phiChart_subsingleton A c
  apply Finsupp.lhom_ext; intro e r
  rw [phiBoundary1_single,Subsingleton.elim (phiEndpoint M A e true) (phiEndpoint M A e false),sub_self,smul_zero]
  rfl
/-- 原Φ chainのV像は面なしから零。 -/
theorem phiBoundaryToCycles_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : phiBoundaryToCycles M A c = 0 := by
  letI := phiFace_empty A c
  apply LinearMap.ext; intro x
  rw [Subsingleton.elim x 0,map_zero]; rfl
/-- 原Φ H1全商から原k chain値Qへの両逆。 -/
def phiHomologyCoordinates (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiHomology M A c ≃ₗ[ℚ] ℚ := by
  let v := (LinearMap.ker (phiBoundary1 M A c)).subtype
  have hk : LinearMap.ker v = LinearMap.range (phiBoundaryToCycles M A c) := by
    have hv : LinearMap.ker v = ⊥ := LinearMap.ker_eq_bot.mpr Subtype.val_injective
    rw [hv,phiBoundaryToCycles_zero,LinearMap.range_zero]
  have hs : Function.Surjective v := by
    intro z
    exact ⟨⟨z,by rw [LinearMap.mem_ker,phiBoundary1_zero]; rfl⟩,rfl⟩
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (v.quotKerEquivOfSurjective hs)).trans
    ((Finsupp.domLCongr (phiEdgeEquiv A c)).trans
      ((Finsupp.linearEquivFunOnFinite ℚ ℚ Unit).trans (LinearEquiv.funUnique Unit ℚ ℚ)))
/-- 同原Φ chain商の次元は1。 -/
theorem phiHomology_dimension (A : Set Bool) (c : Nc.ChartInTargetSubset A) : Module.finrank ℚ (PhiHomology M A c) = 1 :=
  (phiHomologyCoordinates A c).finrank_eq.trans (Module.finrank_self ℚ)
/-- 非空支持では原混在面は同m一つ。 -/
def mixedFaceEquiv (A : Set Bool) (hA : A.Nonempty) : MixedFace M A ≃ Unit where
  toFun _ := ()
  invFun _ := mixedM A hA
  left_inv _ := by apply Subtype.ext; apply Subtype.ext; exact Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
/-- 同原kerB全体とm chain値Qの両逆。 -/
def mixedCycleCoordinates (A : Set Bool) (hA : A.Nonempty) : mixedCycles M A ≃ₗ[ℚ] ℚ := by
  let v := (LinearMap.ker (mixedHorizontalBoundary M A)).subtype
  have hv : Function.Bijective v := by
    constructor
    · exact Subtype.val_injective
    · intro z
      exact ⟨⟨z,by rw [LinearMap.mem_ker,mixedHorizontalBoundary_zero]; rfl⟩,rfl⟩
  exact (LinearEquiv.ofBijective v hv).trans
    ((Finsupp.domLCongr (mixedFaceEquiv A hA)).trans
      ((Finsupp.linearEquivFunOnFinite ℚ ℚ Unit).trans (LinearEquiv.funUnique Unit ℚ ℚ)))
/-- 同原混在閉路全体の次元は1。 -/
theorem mixedCycle_dimension (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ (mixedCycles M A) = 1 :=
  (mixedCycleCoordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- e上の同原Γ incidence核の次元は1。 -/
theorem gammaCycle_dimension (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (he : e.1 = 0) :
    Module.finrank ℚ (LinearMap.ker (gammaBoundary M A e)) = 1 :=
  (gammaCycleCoordinates A e he).finrank_eq.trans (Module.finrank_self ℚ)

/-- 原Φ chain商の公開評価は同k辺の元chain係数。 -/
theorem phiHomologyCoordinates_mk (A : Set Bool) (c : Nc.ChartInTargetSubset A) (z : phiCycles M A c) :
    phiHomologyCoordinates A c (Submodule.Quotient.mk z) = z.1 ((phiEdgeEquiv A c).symm ()) := rfl
/-- 指定原k chain類の同全商periodは1。 -/
theorem phiK_period (A : Set Bool) (hA : A.Nonempty) (c : Nc.ChartInTargetSubset A) :
    phiHomologyCoordinates A c (phiK A hA c) = 1 := by
  classical
  rw [phiK_eq_mk,phiHomologyCoordinates_mk,phiVerticalCyclesEquiv_val,kCycle_val,phiChainEquiv1_single]
  apply if_pos
  apply Subtype.ext
  exact ((edgeMap_none_iff _).mp ((phiEdgeEquiv A c).symm ()).2.1).symm
/-- 原混在閉路全商座標の公開評価は同m係数。 -/
theorem mixedCycleCoordinates_apply (A : Set Bool) (hA : A.Nonempty) (z : mixedCycles M A) :
    mixedCycleCoordinates A hA z = z.1 (mixedM A hA) := rfl
/-- 指定原m閉路の同全商periodは1。 -/
theorem mCycle_period (A : Set Bool) (hA : A.Nonempty) : mixedCycleCoordinates A hA (mCycle A hA) = 1 := by
  classical
  rw [mixedCycleCoordinates_apply,mCycle_val]
  exact Finsupp.single_eq_same

/-- 原m非零閉路により非空W5はforest特殊化に属さない。 -/
theorem not_gammaForest (A : Set Bool) (hA : A.Nonempty) : ¬ GammaForest M A := by
  intro hf
  exact mCycle_nonzero A hA (mixedCycle_eq_zero M A hf (mCycle A hA))

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiBoundary1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiBoundaryToCycles_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiHomologyCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiHomology_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedFaceEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedCycleCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedCycle_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gammaCycle_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiHomologyCoordinates_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedCycleCoordinates_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mCycle_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.not_gammaForest
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
