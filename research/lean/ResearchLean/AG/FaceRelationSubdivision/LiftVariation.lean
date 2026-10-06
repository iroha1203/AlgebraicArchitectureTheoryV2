import ResearchLean.AG.FaceRelationSubdivision.SubsetContraction

/-!
# 支持された二次補正によるsectionの変更

## Implementation notes

一般bridgeのtとr2t=0は方向入力。両操作では原始有限和から生成して放電する。
抽象同型による置換は指定された道との接続を隠すため採らない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable {Ac : Set qc.Target} {Af : Set qf.Target}
namespace SubsetChainContraction
variable (C : SubsetChainContraction Nc Nf Ac Af)
variable (t : K1 Nc Ac →ₗ[ℚ] K2 Nf Af) (ht : C.r2.comp t = 0)

/-- 指定したs'=s+∂t+t∂とh1'=h1-tr1から同じrの収縮を生成する。 -/
def varyLift : SubsetChainContraction Nc Nf Ac Af where
  r0 := C.r0
  r1 := C.r1
  r2 := C.r2
  s0 := C.s0
  s1 := C.s1 + (chainD2 Nf Af).comp t
  s2 := C.s2 + t.comp (chainD2 Nc Ac)
  h0 := C.h0
  h1 := C.h1 - t.comp C.r1
  r_comm01 := C.r_comm01
  r_comm12 := C.r_comm12
  s_comm01 := by
    rw [LinearMap.comp_add, ← LinearMap.comp_assoc, chainD1_comp_chainD2,
      LinearMap.zero_comp, add_zero]
    exact C.s_comm01
  s_comm12 := by
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc]
    rw [C.s_comm12]
  rs0 := C.rs0
  rs1 := by
    rw [LinearMap.comp_add, ← LinearMap.comp_assoc, ← C.r_comm12,
      LinearMap.comp_assoc, ht, LinearMap.comp_zero, add_zero]
    exact C.rs1
  rs2 := by
    rw [LinearMap.comp_add, ← LinearMap.comp_assoc, ht, LinearMap.zero_comp, add_zero]
    exact C.rs2
  sr_h0 := C.sr_h0
  sr_h1 := by
    rw [LinearMap.add_comp, LinearMap.comp_sub, LinearMap.comp_assoc]
    convert C.sr_h1 using 1; abel
  sr_h2 := by
    rw [LinearMap.add_comp, LinearMap.sub_comp, LinearMap.comp_assoc,
      LinearMap.comp_assoc, ← C.r_comm12]
    convert C.sr_h2 using 1; abel

/-- 頂点sectionは元と同じ。 -/
@[simp] theorem varyLift_s0 : (C.varyLift t ht).s0 = C.s0 := rfl
/-- 辺sectionの補正式。 -/
@[simp] theorem varyLift_s1 : (C.varyLift t ht).s1 = C.s1 + (chainD2 Nf Af).comp t := rfl
/-- 面sectionの補正式。 -/
@[simp] theorem varyLift_s2 : (C.varyLift t ht).s2 = C.s2 + t.comp (chainD2 Nc Ac) := rfl
/-- 頂点ホモトピーは元と同じ。 -/
@[simp] theorem varyLift_h0 : (C.varyLift t ht).h0 = C.h0 := rfl
/-- 辺ホモトピーの補正式。 -/
@[simp] theorem varyLift_h1 : (C.varyLift t ht).h1 = C.h1 - t.comp C.r1 := rfl
/-- 変更後のr0は元と同じ。 -/
@[simp] theorem varyLift_r0 : (C.varyLift t ht).r0 = C.r0 := rfl
/-- 変更後のr1は元と同じ。 -/
@[simp] theorem varyLift_r1 : (C.varyLift t ht).r1 = C.r1 := rfl
/-- 変更後のr2は元と同じ。 -/
@[simp] theorem varyLift_r2 : (C.varyLift t ht).r2 = C.r2 := rfl
/-- 収縮の実比較は全三次数で元と同じ。 -/
@[simp] theorem varyLift_rHom : (C.varyLift t ht).rHom = C.rHom := by
  apply cochain_ext
  · rw [rHom_f0, rHom_f0, varyLift_r0]
  · rw [rHom_f1, rHom_f1, varyLift_r1]
  · rw [rHom_f2, rHom_f2, varyLift_r2]

/-- sectionの実双対次数0は同じ。 -/
@[simp] theorem varyLift_sHom_f0 : (C.varyLift t ht).sHom.f0 = C.sHom.f0 := by
  rw [sHom_f0, sHom_f0, varyLift_s0]
/-- sectionの実双対次数1は同じtの補正。 -/
theorem varyLift_sHom_f1 (z : Nf.EdgeInTargetSubset Af → ℚ) :
    (C.varyLift t ht).sHom.f1 z = dualCellMap t (Nf.targetSubsetD1 Af z) + dualCellMap C.s1 z := by
  rw [sHom_f1, varyLift_s1, dualCellMap_add, dualCellMap_comp, dualCellMap_chainD2]
  exact add_comm (dualCellMap C.s1 z) (dualCellMap t (Nf.targetSubsetD1 Af z))

/-- sectionの実双対次数2も同じtの補正。 -/
theorem varyLift_sHom_f2 (z : Nf.FaceInTargetSubset Af → ℚ) :
    (C.varyLift t ht).sHom.f2 z = Nc.targetSubsetD1 Ac (dualCellMap t z) + dualCellMap C.s2 z := by
  rw [sHom_f2, varyLift_s2, dualCellMap_add, dualCellMap_comp, dualCellMap_chainD2]
  exact add_comm (dualCellMap C.s2 z) (Nc.targetSubsetD1 Ac (dualCellMap t z))

/-- 同じ実section Homを結ぶ標準ホモトピー。 -/
def liftHomotopy : Homotopy (zeroExtensionMap (C.varyLift t ht).sHom)
    (zeroExtensionMap C.sHom) :=
  threeHomotopy _ _ 0 (dualCellMap t)
    (by intro x; simp only [varyLift_sHom_f0, LinearMap.zero_apply, zero_add])
    (by intro x; simpa only [sHom_f1, LinearMap.zero_apply, map_zero, add_zero] using C.varyLift_sHom_f1 t ht x)
    (by intro x; simpa only [sHom_f2] using C.varyLift_sHom_f2 t ht x)

/-- 指定section変更は全標準homologyの読み戻しを保つ。 -/
theorem varyLift_homologyMap (n : ℤ) :
    HomologicalComplex.homologyMap (zeroExtensionMap (C.varyLift t ht).sHom) n =
      HomologicalComplex.homologyMap (zeroExtensionMap C.sHom) n :=
  (C.liftHomotopy t ht).homologyMap_eq n

/-- 同じ読み戻しを既存H1商の同じh1Mapへ戻す。 -/
theorem varyLift_h1Map : (C.varyLift t ht).sHom.h1Map = C.sHom.h1Map := by
  have h := C.varyLift_homologyMap t ht 1
  have hn := oldH1Iso_natural (C.varyLift t ht).sHom
  rw [h, oldH1Iso_natural] at hn
  have hm := (cancel_mono (oldH1Iso (Nc.targetSubsetComplex Ac)).hom).mp hn
  exact (ModuleCat.hom_ext_iff.mp hm).symm

/-- cocycleのh0補正は同じr*s代表へ着地する。 -/
theorem cocycle_normalize (z : Nf.EdgeInTargetSubset Af → ℚ)
    (hz : Nf.targetSubsetD1 Af z = 0) :
    z - Nf.targetSubsetD0 Af (dualCellMap C.h0 z) = C.rHom.f1 (C.sHom.f1 z) := by
  have h := C.cochain_correction1 z
  rw [hz, map_zero, zero_add] at h
  rw [rHom_f1, sHom_f1]
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

/-- cocycleの同じr*s読み戻し代表は既存H1商で元と一致する。 -/
theorem cocycle_readback_class (z : LinearMap.ker (Nf.targetSubsetComplex Af).d1) :
    C.rHom.h1Map (C.sHom.h1Map
      ((LinearMap.range (Nf.targetSubsetComplex Af).boundaryToCycles).mkQ z)) =
      (LinearMap.range (Nf.targetSubsetComplex Af).boundaryToCycles).mkQ z := by
  rw [ThreeCochainComplex.Hom.h1Map_mk, ThreeCochainComplex.Hom.h1Map_mk]
  apply (Submodule.Quotient.eq _).2
  refine ⟨-dualCellMap C.h0 z.1, ?_⟩
  apply Subtype.ext
  simp only [ThreeCochainComplex.boundaryToCycles_apply, Submodule.coe_sub,
    ThreeCochainComplex.Hom.cyclesMap_apply]
  have h := C.cocycle_normalize z.1 z.2
  change (Nf.targetSubsetComplex Af).d0 (-dualCellMap C.h0 z.1) =
    C.rHom.f1 (C.sHom.f1 z.1) - z.1
  rw [Nf.targetSubsetComplex_d0 Af]
  rw [map_neg]
  funext a
  have hp := congrFun h a
  change z.1 a - Nf.targetSubsetD0 Af (dualCellMap C.h0 z.1) a =
    C.rHom.f1 (C.sHom.f1 z.1) a at hp
  change -Nf.targetSubsetD0 Af (dualCellMap C.h0 z.1) a =
    C.rHom.f1 (C.sHom.f1 z.1) a - z.1 a
  linarith

end SubsetChainContraction
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
