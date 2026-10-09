import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeComparison
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeCoefficients
import ResearchLean.AG.AtlasCoefficientFiber.GammaForest
import ResearchLean.AG.AtlasCoefficientFiber.PurePreservation

/-!
# G-135 W3：原mのforestとliteral R

## Implementation notes

mの異なる二端点からforestを証明し、元Rの両逆を原Phi H¹へ接続する。
Phiのk loopを消す商は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 全Aで原混在面名はmだけ。 -/
theorem mixed_name (A : Set Bool) (f : MixedFace M A) : f.1.1 = 2 :=
  (faceMap_none_iff f.1.1).mp f.2.1
/-- 全Aの原mixed集合は高々一面。空Aも含む。 -/
theorem mixed_subsingleton (A : Set Bool) : Subsingleton (MixedFace M A) := by
  constructor
  intro f g
  apply Subtype.ext; apply Subtype.ext
  exact (mixed_name A f).trans (mixed_name A g).symm
/-- mの原Γ始点a1と終点a0は異名である。 -/
theorem mixed_endpoints_ne (A : Set Bool) (f : MixedFace M A) :
    mixedGraphSource M A f ≠ mixedGraphTarget M A f := by
  intro he
  have hv := congrArg (fun e : HorizontalEdge M A => e.1.1) he
  have ht := mixedGraphTarget_val_left M A f (by rw [mixed_name A f]; rfl)
  have ht' := congrArg Subtype.val ht
  change Nf.nerve.faceEdge1 f.1.1 = (mixedGraphTarget M A f).1.1 at hv
  rw [ht'] at hv
  change Nf.nerve.faceEdge1 f.1.1 = Nf.nerve.faceEdge2 f.1.1 at hv
  rw [mixed_name A f] at hv
  exact (by decide : (1 : Fin 6) ≠ 0) hv
/-- 原m一辺の全有限部分グラフleaf条件。 -/
theorem gamma_forest (A : Set Bool) : GammaForest M A := by
  letI := mixed_subsingleton A
  exact namedForest_of_subsingleton _ _ (mixed_endpoints_ne A)
/-- 原Bの全核が零、期待rankを入力しない。 -/
theorem B_kernel (A : Set Bool) : LinearMap.ker (mixedHorizontalBoundary M A) = ⊥ :=
  mixedHorizontalBoundary_ker_eq_bot M A (gamma_forest A)
/-- 原κは同じ混在閉路零性から零。 -/
theorem kappa_zero (A : Set Bool) : kappa M A = 0 := kappa_eq_zero_of_forest M A (gamma_forest A)
/-- 原κ*も零。 -/
theorem kappaStar_zero (A : Set Bool) : kappaStar M A = 0 := kappaStar_eq_zero_of_forest M A (gamma_forest A)
/-- 元Rと全原Phi H¹の両逆、原κ核を保持。 -/
def rFamilyEquiv (A : Set Bool) : R M A ≃ₗ[ℚ] ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) :=
  forestFiberREquiv M A (gamma_forest A)

/-- 全Aでmなし原mixed集合は空。 -/
theorem paired_mixed_empty (A : Set Bool) : IsEmpty (MixedFace pairedM A) where
  false f := by cases f.2.1
/-- mなし原κは原mixed空から零。 -/
theorem paired_kappa_zero (A : Set Bool) : kappa pairedM A = 0 := by
  letI := paired_mixed_empty A
  exact kappa_zero_of_mixed_isEmpty (Source := WitnessCommon.Source) (qc := qc) (qf := qf)
    (h := coarser) (Nc := Nc) (Nf := pairedNf) A pairedM
/-- mなし原κ*も零。 -/
theorem paired_kappaStar_zero (A : Set Bool) : kappaStar pairedM A = 0 := by
  letI := paired_mixed_empty A
  exact pure_kappaStar_zero pairedM A
/-- mなし原τは同じ標準連結射の零写像。 -/
theorem paired_tau_zero (A : Set Bool) : connectingTau pairedM A = 0 := by
  letI := paired_mixed_empty A
  exact connectingTau_zero_of_mixed_isEmpty (Source := WitnessCommon.Source) (qc := qc) (qf := qf)
    (h := coarser) (Nc := Nc) (Nf := pairedNf) A pairedM
/-- mなし原Rから同じ全Phiへの両逆。 -/
def pairedRFamilyEquiv (A : Set Bool) : R pairedM A ≃ₗ[ℚ] ((c : Nc.ChartInTargetSubset A) → (phiComplex pairedM A c).H1) := by
  letI := paired_mixed_empty A
  exact pureFiberREquiv pairedM A

/-- 非空Aの指定x chart。 -/
def xChart (A : Set Bool) (hA : A.Nonempty) : Nc.ChartInTargetSubset A := fullSelected Nc.chartSupport (fun _ => rfl) A hA 0
/-- 元x Phi辺集合はk一本と両逆。 -/
def phiEdgeXEquiv (A : Set Bool) (hA : A.Nonempty) : PhiEdge M A (xChart A hA) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨fullSelected Nf.edgeSupport (fullSupport_edge Nf (fun _ => rfl)) _ (fine_nonempty A hA) 5,rfl,rfl⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; exact ((edgeMap_none_iff e.1.1).mp e.2.1).symm
  right_inv _ := Subsingleton.elim _ _
/-- 元y/z Phi辺集合は空、原carrier条件による。 -/
theorem phiEdge_other_empty (A : Set Bool) (c : Nc.ChartInTargetSubset A) (hc : c.1 ≠ 0) : IsEmpty (PhiEdge M A c) where
  false e := by
    have he := (edgeMap_none_iff e.1.1).mp e.2.1
    have hh := congrArg Subtype.val e.2.2
    change Nf.nerve.edgeLeft e.1.1 = c.1 at hh
    rw [he] at hh
    exact hc hh.symm
/-- 原Phi d0は同chartの二端点差から零。 -/
theorem phi_d0_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).d0 = 0 := by
  letI := phiChart_subsingleton A c
  apply LinearMap.ext; intro z; funext e
  change phiD0 M A c z e = 0
  rw [phiD0_apply,Subsingleton.elim (phiEndpoint M A e true) (phiEndpoint M A e false)]
  exact sub_self _
/-- 原Phi d1零は原mixed mが垂直面ではないことによる。 -/
theorem phi_d1_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).d1 = 0 := by
  apply LinearMap.ext; intro z; funext f
  exact False.elim ((phiFace_empty A c).false f)
/-- 元x Phi H¹の全商両逆k座標。 -/
def phiXCoordinates (A : Set Bool) (hA : A.Nonempty) : (phiComplex M A (xChart A hA)).H1 ≃ₗ[ℚ] ℚ :=
  (zeroDifferentialH1Equiv _ (phi_d0_zero A _) (phi_d1_zero A _)).trans
    ((LinearEquiv.piCongrLeft' ℚ (fun _ : PhiEdge M A (xChart A hA) => ℚ) (phiEdgeXEquiv A hA)).trans
      (LinearEquiv.funUnique (Fin 1) ℚ ℚ))
/-- 原y/z Phi全H¹は零。 -/
theorem phi_other_subsingleton (A : Set Bool) (c : Nc.ChartInTargetSubset A) (hc : c.1 ≠ 0) :
    Subsingleton (phiComplex M A c).H1 := by
  letI := phiEdge_other_empty A c hc
  letI : Subsingleton (phiComplex M A c).C1 := by
    change Subsingleton (PhiEdge M A c → ℚ); infer_instance
  exact (zeroDifferentialH1Equiv _ (phi_d0_zero A c) (phi_d1_zero A c)).toEquiv.subsingleton_congr.mpr inferInstance
/-- 全原Phi族からxの実k periodを取る線形写像。 -/
def phiFamilyPeriod (A : Set Bool) (hA : A.Nonempty) :
    ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) →ₗ[ℚ] ℚ :=
  (phiXCoordinates A hA).toLinearMap.comp (LinearMap.proj (xChart A hA))
/-- 同期した全原Phi族のperiodは両方向全単射。 -/
theorem phiFamilyPeriod_bijective (A : Set Bool) (hA : A.Nonempty) : Function.Bijective (phiFamilyPeriod A hA) := by
  classical
  constructor
  · intro z w hh
    funext c
    by_cases hc : c.1 = 0
    · have he : c = xChart A hA := Subtype.ext hc
      subst c
      exact (phiXCoordinates A hA).injective hh
    · letI := phi_other_subsingleton A c hc
      exact Subsingleton.elim _ _
  · intro q
    let z : (c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1 := fun c =>
      if he : c = xChart A hA then he.symm ▸ (phiXCoordinates A hA).symm q else 0
    refine ⟨z,?_⟩
    change phiXCoordinates A hA (z (xChart A hA)) = q
    simp [z]
/-- 原Rの全商両逆はxの実k period。 -/
def rCoordinates (A : Set Bool) (hA : A.Nonempty) : R M A ≃ₗ[ℚ] ℚ :=
  (rFamilyEquiv A).trans (LinearEquiv.ofBijective (phiFamilyPeriod A hA) (phiFamilyPeriod_bijective A hA))
/-- literal Rの次元1。 -/
theorem r_dimension (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ (R M A) = 1 :=
  (rCoordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- 指定Qの標準H¹をliteral R経由で元k座標へ同定。 -/
def qCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (zeroExtension (restrictionComplex M A)).homology (1 : ℤ) ≃ₗ[ℚ] ℚ :=
  (restrictionStandardHomologyREquiv M A).trans (rCoordinates A hA)

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.mixed_name
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.mixed_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.mixed_endpoints_ne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.gamma_forest
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.B_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rFamilyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_mixed_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedRFamilyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.xChart
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phiEdgeXEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phiEdge_other_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phi_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phi_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phiXCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phi_other_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phiFamilyPeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phiFamilyPeriod_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.r_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.qCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.xChart.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
