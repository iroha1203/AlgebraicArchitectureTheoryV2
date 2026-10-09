import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveKappa
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveGeneration

/-!
# G-135 W5：原mとkの代表およびΦ全空間

## Implementation notes

代表は原セルの値1から生成する。κの逆像を代表として定義すると指定mの評価を
失うため、m/kを先に独立構成してから実κと対合を計算する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 同非空支持の唯一粗chart。 -/
def coarseChart (A : Set Bool) (hA : A.Nonempty) : Nc.ChartInTargetSubset A :=
  fullSelected Nc.chartSupport (fun _ => rfl) A hA ()
/-- 同非空支持の原k、期待κ値から独立。 -/
def verticalK (A : Set Bool) (hA : A.Nonempty) : VerticalEdge M A :=
  ⟨fullSelected Nf.edgeSupport (fullSupport_edge Nf (fun _ => rfl)) _ (fine_nonempty A hA) 2,edgeMap_k⟩
/-- 同非空支持の原m、期待κの逆から独立。 -/
def mixedM (A : Set Bool) (hA : A.Nonempty) : MixedFace M A :=
  ⟨fullSelected Nf.faceSupport (fullSupport_face Nf (fun _ => rfl)) _ (fine_nonempty A hA) (),
    faceMap_apply _,0,by rw [fine_faceEdge1,edgeMap_e]⟩
/-- 原mの垂直位置0は同原k。 -/
theorem mixedM_vertical (A : Set Bool) (hA : A.Nonempty) : mixedToVertical A (mixedM A hA) = verticalK A hA := by
  apply Subtype.ext; apply Subtype.ext
  change Nf.nerve.faceEdge0 () = 2
  exact fine_faceEdge0 ()
/-- 原mの値1の実B閉路。 -/
def mCycle (A : Set Bool) (hA : A.Nonempty) : mixedCycles M A :=
  ⟨Finsupp.single (mixedM A hA) 1,by rw [LinearMap.mem_ker,mixedHorizontalBoundary_zero]; rfl⟩
/-- 原kの値1の実a閉路。 -/
def kCycle (A : Set Bool) (hA : A.Nonempty) : verticalCycles M A :=
  ⟨Finsupp.single (verticalK A hA) 1,by rw [LinearMap.mem_ker,verticalEdgeBoundary_zero]; rfl⟩
/-- 原m閉路のD像は原k閉路と全chain一致。 -/
theorem mCycle_vertical (A : Set Bool) (hA : A.Nonempty) : mixedCycleToVertical M A (mCycle A hA) = kCycle A hA := by
  apply Subtype.ext
  rw [mixedCycleToVertical_val]
  change mixedVerticalBoundary M A (Finsupp.single (mixedM A hA) 1) = Finsupp.single (verticalK A hA) 1
  rw [mixedVerticalBoundary_single,mixedM_vertical]
/-- κと独立に同原k chainから生成する各Φ homology類。 -/
def phiK (A : Set Bool) (hA : A.Nonempty) (c : Nc.ChartInTargetSubset A) : PhiHomology M A c :=
  Submodule.Quotient.mk (phiVerticalCyclesEquiv M A (kCycle A hA) c)
/-- 実κ[m]=[k]、同原m/kの全Φ成分での等号。 -/
theorem kappa_m (A : Set Bool) (hA : A.Nonempty) (c : Nc.ChartInTargetSubset A) :
    kappa M A (mCycle A hA) c = phiK A hA c := by
  rw [kappa_apply_component,mCycle_vertical]; rfl
/-- 指定m閉路は実自由chainの値1により非零。 -/
theorem mCycle_nonzero (A : Set Bool) (hA : A.Nonempty) : mCycle A hA ≠ 0 := by
  classical
  intro hh
  have he := congrArg (fun y : mixedCycles M A => y.1 (mixedM A hA)) hh
  change (Finsupp.single (mixedM A hA) (1:ℚ)) (mixedM A hA) = 0 at he
  rw [Finsupp.single_eq_same] at he
  exact one_ne_zero he
/-- 同κの全Φ像も非零。 -/
theorem kappa_m_nonzero (A : Set Bool) (hA : A.Nonempty) : kappa M A (mCycle A hA) ≠ 0 := by
  intro hh
  exact mCycle_nonzero A hA ((kappaEquiv A).injective (hh.trans (map_zero _).symm))
/-- 元Φのkだけ1の閉cochain。 -/
def phiKCocycle (A : Set Bool) (c : Nc.ChartInTargetSubset A) : LinearMap.ker (phiComplex M A c).d1 :=
  ⟨fun _ => 1,by rw [LinearMap.mem_ker,phi_d1_zero]; rfl⟩
/-- 同k cochainの原Φ商類。 -/
def phiKDual (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).H1 :=
  Submodule.Quotient.mk (phiKCocycle A c)
/-- 同k dual類の全商座標は1。 -/
theorem phiKDual_period (A : Set Bool) (c : Nc.ChartInTargetSubset A) : phiH1Coordinates A c (phiKDual A c) = 1 := by
  change phiH1Coordinates A c ((LinearMap.range (phiComplex M A c).boundaryToCycles).mkQ (phiKCocycle A c)) = 1
  rw [phiH1Coordinates_mk]; rfl
/-- 原k dual類は同Φ商で非零。 -/
theorem phiKDual_nonzero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : phiKDual A c ≠ 0 := by
  intro hh
  have he := congrArg (phiH1Coordinates A c) hh
  rw [phiKDual_period,map_zero] at he
  exact one_ne_zero he
/-- 同kのchain/cocycle対合は1、κ像の具体的非零性。 -/
theorem phiK_pairing (A : Set Bool) (hA : A.Nonempty) (c : Nc.ChartInTargetSubset A) :
    phiHomologyDualEquiv M A c (phiKDual A c) (phiK A hA c) = 1 := by
  classical
  rw [phiK,phiKDual,phiHomologyDualEquiv_mk]
  change freeDualEquiv _ (fun _ => 1) (phiChainEquiv1 M A (Finsupp.single (verticalK A hA) 1) c) = 1
  let e := (phiEdgeEquiv A c).symm ()
  have he : verticalK A hA = (⟨e.1,e.2.1⟩ : VerticalEdge M A) := by
    apply Subtype.ext; apply Subtype.ext
    exact ((edgeMap_none_iff _).mp e.2.1).symm
  rw [he,phiChainEquiv1_single_same,freeDualEquiv_single,one_mul]
/-- 同原k chain類は各Φ成分でも非零。 -/
theorem phiK_nonzero (A : Set Bool) (hA : A.Nonempty) (c : Nc.ChartInTargetSubset A) : phiK A hA c ≠ 0 := by
  intro hh
  have he := phiK_pairing A hA c
  rw [hh,map_zero] at he
  exact one_ne_zero he.symm
/-- 元全Φ H¹とQの全両逆。 -/
def wholePhiCoordinates (A : Set Bool) (hA : A.Nonempty) :
    ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) ≃ₗ[ℚ] ℚ := by
  letI : Unique (Nc.ChartInTargetSubset A) :=
    ⟨⟨coarseChart A hA⟩,fun _ => Subtype.ext (Subsingleton.elim _ _)⟩
  exact (LinearEquiv.piCongrRight (phiH1Coordinates A)).trans
    (LinearEquiv.funUnique (Nc.ChartInTargetSubset A) ℚ ℚ)
/-- 元全Φ H¹は非空支持で1。 -/
theorem wholePhi_dimension (A : Set Bool) (hA : A.Nonempty) :
    Module.finrank ℚ ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) = 1 :=
  (wholePhiCoordinates A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- 元全Φの指定k dual族。 -/
def wholePhiK (A : Set Bool) : (c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1 := phiKDual A
/-- 同全Φ族のk periodは1。 -/
theorem wholePhiK_period (A : Set Bool) (hA : A.Nonempty) : wholePhiCoordinates A hA (wholePhiK A) = 1 :=
  phiKDual_period A (coarseChart A hA)
/-- 同全Φ族は非空支持で非零。 -/
theorem wholePhiK_nonzero (A : Set Bool) (hA : A.Nonempty) : wholePhiK A ≠ 0 := by
  intro hh
  have he := congrArg (wholePhiCoordinates A hA) hh
  rw [wholePhiK_period,map_zero] at he
  exact one_ne_zero he

/-- 同原粗chartの有限cardは非空支持で1。 -/
theorem chart_card (A : Set Bool) (hA : A.Nonempty) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A); Fintype.card (Nc.ChartInTargetSubset A) = 1 := by
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  exact Fintype.card_eq_one_iff.mpr ⟨coarseChart A hA,fun c => Subtype.ext (Subsingleton.elim _ _)⟩
/-- 同原Φ全Betti和は非空支持で1。 -/
theorem phi_dimension_sum (A : Set Bool) (hA : A.Nonempty) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    ∑ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 = 1 := by
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  simp only [phiH1_dimension,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,chart_card A hA]
  norm_num
/-- 同実κ*は原k cochainを原m閉路上1へ送る。 -/
theorem kappaStar_m_period (A : Set Bool) (hA : A.Nonempty) : kappaStar M A (wholePhiK A) (mCycle A hA) = 1 := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  rw [kappaStar_apply,allPhiHomologyDualEquiv_apply]
  simp only [wholePhiK,kappa_m,phiK_pairing,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,chart_card A hA]
  norm_num

/-- 同原m閉路の公開chain値。 -/
theorem mCycle_val (A : Set Bool) (hA : A.Nonempty) : (mCycle A hA).1 = Finsupp.single (mixedM A hA) 1 := rfl
/-- 同原k閉路の公開chain値。 -/
theorem kCycle_val (A : Set Bool) (hA : A.Nonempty) : (kCycle A hA).1 = Finsupp.single (verticalK A hA) 1 := rfl
/-- 同原k類の公開商代表。 -/
theorem phiK_eq_mk (A : Set Bool) (hA : A.Nonempty) (c : Nc.ChartInTargetSubset A) :
    phiK A hA c = Submodule.Quotient.mk (phiVerticalCyclesEquiv M A (kCycle A hA) c) := rfl

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseChart
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.verticalK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedM
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedM_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mCycle_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kappa_m
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mCycle_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kappa_m_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiKCocycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiKDual
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiKDual_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiKDual_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiK_pairing
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.wholePhiCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.wholePhi_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.wholePhiK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.wholePhiK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.wholePhiK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.chart_card
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phi_dimension_sum
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kappaStar_m_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mCycle.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiK.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mCycle_val
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.kCycle_val
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiK_eq_mk
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
