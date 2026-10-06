import ResearchLean.AG.FaceRelationSubdivision.ChainDualMap
import Formal.Util.AssertStandardAxioms

/-!
# 入力から生成された支持chain収縮の標準双対

## Implementation notes

このrecordは基本変形の入力ではなく、セル表から計算されたr/s/hと証明の出力である。
一般bridgeではその具体式を方向仮定として使用し、各基本変形constructorで全fieldを
原始データから放電する。標準HomotopyEquivをfieldから受け取る案は同じ射との接続を
隠すため採らず、双対生成・三項補正式を通して標準recordを構成する。
-/

noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable (Nc : TargetSupportedNerve qc) (Nf : TargetSupportedNerve qf)
variable (Ac : Set qc.Target) (Af : Set qf.Target)

/-- 原始構成から得た支持chain収縮の出力。操作の原始入力条件ではない。 -/
structure SubsetChainContraction where
  r0 : K0 Nf Af →ₗ[ℚ] K0 Nc Ac
  r1 : K1 Nf Af →ₗ[ℚ] K1 Nc Ac
  r2 : K2 Nf Af →ₗ[ℚ] K2 Nc Ac
  s0 : K0 Nc Ac →ₗ[ℚ] K0 Nf Af
  s1 : K1 Nc Ac →ₗ[ℚ] K1 Nf Af
  s2 : K2 Nc Ac →ₗ[ℚ] K2 Nf Af
  h0 : K0 Nf Af →ₗ[ℚ] K1 Nf Af
  h1 : K1 Nf Af →ₗ[ℚ] K2 Nf Af
  r_comm01 : (chainD1 Nc Ac).comp r1 = r0.comp (chainD1 Nf Af)
  r_comm12 : (chainD2 Nc Ac).comp r2 = r1.comp (chainD2 Nf Af)
  s_comm01 : (chainD1 Nf Af).comp s1 = s0.comp (chainD1 Nc Ac)
  s_comm12 : (chainD2 Nf Af).comp s2 = s1.comp (chainD2 Nc Ac)
  rs0 : r0.comp s0 = LinearMap.id
  rs1 : r1.comp s1 = LinearMap.id
  rs2 : r2.comp s2 = LinearMap.id
  sr_h0 : s0.comp r0 + (chainD1 Nf Af).comp h0 = LinearMap.id
  sr_h1 : s1.comp r1 + (chainD2 Nf Af).comp h1 + h0.comp (chainD1 Nf Af) = LinearMap.id
  sr_h2 : s2.comp r2 + h1.comp (chainD2 Nf Af) = LinearMap.id

namespace SubsetChainContraction
variable {Nc Nf Ac Af}
variable (C : SubsetChainContraction Nc Nf Ac Af)

/-- 生成された同じrの実subset cochain Hom。 -/
def rHom : ThreeCochainComplex.Hom (Nc.targetSubsetComplex Ac) (Nf.targetSubsetComplex Af) :=
  dualSubsetHom Ac Af C.r0 C.r1 C.r2 C.r_comm01 C.r_comm12

/-- 生成された同じsの実subset cochain Hom。 -/
def sHom : ThreeCochainComplex.Hom (Nf.targetSubsetComplex Af) (Nc.targetSubsetComplex Ac) :=
  dualSubsetHom Af Ac C.s0 C.s1 C.s2 C.s_comm01 C.s_comm12

/-- 同じr/sの実cochain往復は旧複体上で恒等。 -/
theorem cochain_rs : cochainComp C.rHom C.sHom = cochainId (Nc.targetSubsetComplex Ac) := by
  apply cochain_ext
  · change (dualCellMap C.s0).comp (dualCellMap C.r0) = LinearMap.id
    rw [← dualCellMap_comp, C.rs0, dualCellMap_identity]
  · change (dualCellMap C.s1).comp (dualCellMap C.r1) = LinearMap.id
    rw [← dualCellMap_comp, C.rs1, dualCellMap_identity]
  · change (dualCellMap C.s2).comp (dualCellMap C.r2) = LinearMap.id
    rw [← dualCellMap_comp, C.rs2, dualCellMap_identity]

/-- 頂点の原始chain補正式を同じcochain有限和へ双対化する。 -/
theorem cochain_correction0 (z : Nf.ChartInTargetSubset Af → ℚ) :
    z = dualCellMap C.h0 (Nf.targetSubsetD0 Af z) +
      dualCellMap C.r0 (dualCellMap C.s0 z) := by
  apply (freeDualEquiv _).injective
  apply LinearMap.ext
  intro x
  change freeDualEquiv _ z x = freeDualEquiv _
    (dualCellMap C.h0 (Nf.targetSubsetD0 Af z) + dualCellMap C.r0 (dualCellMap C.s0 z)) x
  rw [map_add, LinearMap.add_apply, dualCellMap_dual, ← chainD1_dual, dualCellMap_dual, dualCellMap_dual]
  have h : freeDualEquiv _ z (C.s0 (C.r0 x) + chainD1 Nf Af (C.h0 x)) =
      freeDualEquiv _ z x := congrArg (freeDualEquiv _ z) (LinearMap.congr_fun C.sr_h0 x)
  rw [map_add] at h
  exact h.symm.trans (add_comm _ _)

/-- 辺の原始chain補正式を同じcochain有限和へ双対化する。 -/
theorem cochain_correction1 (z : Nf.EdgeInTargetSubset Af → ℚ) :
    z = dualCellMap C.h1 (Nf.targetSubsetD1 Af z) +
      Nf.targetSubsetD0 Af (dualCellMap C.h0 z) +
      dualCellMap C.r1 (dualCellMap C.s1 z) := by
  apply (freeDualEquiv _).injective
  apply LinearMap.ext
  intro x
  change freeDualEquiv _ z x = freeDualEquiv _
    (dualCellMap C.h1 (Nf.targetSubsetD1 Af z) +
      Nf.targetSubsetD0 Af (dualCellMap C.h0 z) + dualCellMap C.r1 (dualCellMap C.s1 z)) x
  rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, dualCellMap_dual, ← chainD2_dual, ← chainD1_dual,
    dualCellMap_dual, dualCellMap_dual, dualCellMap_dual]
  have h : freeDualEquiv _ z (C.s1 (C.r1 x) + chainD2 Nf Af (C.h1 x) + C.h0 (chainD1 Nf Af x)) =
      freeDualEquiv _ z x := congrArg (freeDualEquiv _ z) (LinearMap.congr_fun C.sr_h1 x)
  rw [map_add, map_add] at h
  rw [← h]
  abel

/-- 面の原始chain補正式を同じcochain有限和へ双対化する。 -/
theorem cochain_correction2 (z : Nf.FaceInTargetSubset Af → ℚ) :
    z = Nf.targetSubsetD1 Af (dualCellMap C.h1 z) +
      dualCellMap C.r2 (dualCellMap C.s2 z) := by
  apply (freeDualEquiv _).injective
  apply LinearMap.ext
  intro x
  change freeDualEquiv _ z x = freeDualEquiv _
    (Nf.targetSubsetD1 Af (dualCellMap C.h1 z) + dualCellMap C.r2 (dualCellMap C.s2 z)) x
  rw [map_add, LinearMap.add_apply, ← chainD2_dual, dualCellMap_dual, dualCellMap_dual, dualCellMap_dual]
  have h : freeDualEquiv _ z (C.s2 (C.r2 x) + C.h1 (chainD2 Nf Af x)) =
      freeDualEquiv _ z x := congrArg (freeDualEquiv _ z) (LinearMap.congr_fun C.sr_h2 x)
  rw [map_add] at h
  exact h.symm.trans (add_comm _ _)

/-- 原始r/s/hの出力から標準零延長の同じ二射によるhomotopy同値を生成する。 -/
def cochainHomotopyEquiv : HomotopyEquiv
    (zeroExtension (Nc.targetSubsetComplex Ac)) (zeroExtension (Nf.targetSubsetComplex Af)) where
  hom := zeroExtensionMap C.rHom
  inv := zeroExtensionMap C.sHom
  homotopyHomInvId := Homotopy.ofEq (by
    rw [← zeroExtensionMap_comp, C.cochain_rs, zeroExtensionMap_id])
  homotopyInvHomId := by
    simpa only [zeroExtensionMap_comp, zeroExtensionMap_id] using
      (threeHomotopy (cochainId (Nf.targetSubsetComplex Af)) (cochainComp C.sHom C.rHom)
        (dualCellMap C.h0) (dualCellMap C.h1)
        C.cochain_correction0 C.cochain_correction1 C.cochain_correction2).symm


/-- 生成された標準同値の順方向は同じ実rHomの零延長。 -/
@[simp] theorem cochainHomotopyEquiv_hom : C.cochainHomotopyEquiv.hom = zeroExtensionMap C.rHom := rfl

/-- 生成された標準同値の逆方向は同じ実sHomの零延長。 -/
@[simp] theorem cochainHomotopyEquiv_inv : C.cochainHomotopyEquiv.inv = zeroExtensionMap C.sHom := rfl

/-- 同じ生成r/sから全次数の標準homology同型を得る。特に次数0/1/2を含む。 -/
def homologyIso (n : ℤ) :
    (zeroExtension (Nc.targetSubsetComplex Ac)).homology n ≅
      (zeroExtension (Nf.targetSubsetComplex Af)).homology n :=
  C.cochainHomotopyEquiv.toHomologyIso n

/-- 全次数の同型の順方向は同じrの実homology map。 -/
@[simp] theorem homologyIso_hom (n : ℤ) :
    (C.homologyIso n).hom = HomologicalComplex.homologyMap (zeroExtensionMap C.rHom) n := rfl

/-- 標準次数1同型を既存H1商へ読み戻す。商を新しく定義しない。 -/
def oldH1ComparisonIso : ModuleCat.of ℚ (Nc.targetSubsetComplex Ac).H1 ≅
    ModuleCat.of ℚ (Nf.targetSubsetComplex Af).H1 :=
  oldH1Iso (Nc.targetSubsetComplex Ac) ≪≫ C.homologyIso 1 ≪≫ (oldH1Iso (Nf.targetSubsetComplex Af)).symm

/-- 既存商上の同型も、同じ実rHom.h1Mapそのものである。 -/
theorem oldH1ComparisonIso_hom : C.oldH1ComparisonIso.hom = ModuleCat.ofHom C.rHom.h1Map := by
  change ((oldH1Iso (Nc.targetSubsetComplex Ac)).hom ≫
    HomologicalComplex.homologyMap (zeroExtensionMap C.rHom) 1) ≫
      (oldH1Iso (Nf.targetSubsetComplex Af)).inv = _
  rw [oldH1Iso_natural]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SubsetChainContraction
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
