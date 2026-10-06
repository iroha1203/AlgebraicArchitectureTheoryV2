import ResearchLean.AG.FaceRelationSubdivision.PrimitiveCellDeletion
import ResearchLean.AG.FaceRelationSubdivision.TriangleGeometry
import Formal.Util.AssertStandardAxioms

/-!
# 同じreadingの支持表示の両方向

## Implementation notes

逆は元の名前全単射の逆として生成し、逆incidenceと台等式を順方向から証明する。
新しい診断同型を仮定しない。任意Aで同じreadingの因子を恒等へ正規化して、
前cycleの同じ選択基底射を型の等号transportとともに再利用する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}

/-- 同じreadingの全射因子は恒等関数。 -/
theorem self_factor_eq_id : comparisonFactor q q (Reading.coarserThan_refl q) = id :=
  funext TriangleAddition.self_factor
/-- 同じreadingのcanonical逆像は元の支持部分集合。 -/
theorem self_preimage (A : Set q.Target) :
    comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A = A := by
  ext t
  rw [Set.mem_preimage, TriangleAddition.self_factor]

/-- 型族の引数を等号transportした三次数の線形同型も、同じ微分正方形を保つ。 -/
theorem linearEquiv_square_cast {I : Type u} {X0 X1 : I → Type u}
    [∀ i, AddCommGroup (X0 i)] [∀ i, Module ℚ (X0 i)]
    [∀ i, AddCommGroup (X1 i)] [∀ i, Module ℚ (X1 i)]
    {Y0 Y1 : Type u} [AddCommGroup Y0] [Module ℚ Y0]
    [AddCommGroup Y1] [Module ℚ Y1]
    {a b : I} (hab : a = b) (e0 : X0 a ≃ₗ[ℚ] Y0) (e1 : X1 a ≃ₗ[ℚ] Y1)
    (dx : ∀ i, X1 i →ₗ[ℚ] X0 i) (dy : Y1 →ₗ[ℚ] Y0)
    (hc : dy.comp e1.toLinearMap = e0.toLinearMap.comp (dx a)) :
    dy.comp (Eq.mp (congrArg (fun i => X1 i ≃ₗ[ℚ] Y1) hab) e1).toLinearMap =
      (Eq.mp (congrArg (fun i => X0 i ≃ₗ[ℚ] Y0) hab) e0).toLinearMap.comp (dx b) := by
  cases hab
  exact hc

/-- 型族のdomainだけの等号transportは、同じ生成線形射との等号を保つ。 -/
theorem linearEquiv_cast_eq {I : Type u} {X : I → Type u}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℚ (X i)]
    {Y : Type u} [AddCommGroup Y] [Module ℚ Y]
    {a b : I} (hab : a = b) (P : I → Prop) (ha : P a) (hb : P b)
    (e : X a ≃ₗ[ℚ] Y) (f : ∀ i, P i → X i →ₗ[ℚ] Y)
    (he : e.toLinearMap = f a ha) :
    (Eq.mp (congrArg (fun i => X i ≃ₗ[ℚ] Y) hab) e).toLinearMap = f b hb := by
  cases hab
  exact he

namespace CellPresentationEquiv
variable {N M : TargetSupportedNerve.{u, u} q}
variable (E : CellPresentationEquiv q q (Reading.coarserThan_refl q) N M)

/-- 同じreadingの表示同型の逆を、名前の逆と原始等式から生成する。 -/
def symmSelf : CellPresentationEquiv q q (Reading.coarserThan_refl q) M N where
  chartEquiv := E.chartEquiv.symm
  edgeEquiv := E.edgeEquiv.symm
  faceEquiv := E.faceEquiv.symm
  edge_left := by
    intro a
    apply E.chartEquiv.injective
    simpa using (E.edge_left (E.edgeEquiv.symm a)).symm
  edge_right := by
    intro a
    apply E.chartEquiv.injective
    simpa using (E.edge_right (E.edgeEquiv.symm a)).symm
  face_edge0 := by
    intro F
    apply E.edgeEquiv.injective
    simpa using (E.face_edge0 (E.faceEquiv.symm F)).symm
  face_edge1 := by
    intro F
    apply E.edgeEquiv.injective
    simpa using (E.face_edge1 (E.faceEquiv.symm F)).symm
  face_edge2 := by
    intro F
    apply E.edgeEquiv.injective
    simpa using (E.face_edge2 (E.faceEquiv.symm F)).symm
  chartSupport_eq := by
    intro v
    have h := E.chartSupport_eq (E.chartEquiv.symm v)
    simpa only [self_factor_eq_id, Set.preimage_id, Equiv.apply_symm_apply] using h.symm

/-- 生成した逆表示のchart計算成分は元の逆全単射。 -/
@[simp] theorem symmSelf_chart : E.symmSelf.chartEquiv = E.chartEquiv.symm := rfl
/-- 生成した逆表示のedge計算成分。 -/
@[simp] theorem symmSelf_edge : E.symmSelf.edgeEquiv = E.edgeEquiv.symm := rfl
/-- 生成した逆表示のface計算成分。 -/
@[simp] theorem symmSelf_face : E.symmSelf.faceEquiv = E.faceEquiv.symm := rfl

/-- 任意Aの同じreading上のdegree0基底同型。 -/
def sameR0 (A : Set q.Target) : K0 M A ≃ₗ[ℚ] K0 N A := by
  exact Eq.mp (congrArg (fun S => K0 M S ≃ₗ[ℚ] K0 N A) (self_preimage A)) (E.r0 A)
/-- 任意Aのdegree1基底同型。 -/
def sameR1 (A : Set q.Target) : K1 M A ≃ₗ[ℚ] K1 N A := by
  exact Eq.mp (congrArg (fun S => K1 M S ≃ₗ[ℚ] K1 N A) (self_preimage A)) (E.r1 A)
/-- 任意Aのdegree2基底同型。 -/
def sameR2 (A : Set q.Target) : K2 M A ≃ₗ[ℚ] K2 N A := by
  exact Eq.mp (congrArg (fun S => K2 M S ≃ₗ[ℚ] K2 N A) (self_preimage A)) (E.r2 A)

/-- 同じreadingのrはdegree1微分と可換。 -/
theorem sameR_comm01 (A : Set q.Target) :
    (chainD1 N A).comp (E.sameR1 A).toLinearMap =
      (E.sameR0 A).toLinearMap.comp (chainD1 M A) := by
  exact linearEquiv_square_cast (self_preimage A) (E.r0 A) (E.r1 A)
    (chainD1 M) (chainD1 N A) (E.r_comm01 A)
/-- 同じreadingのrはdegree2微分と可換。 -/
theorem sameR_comm12 (A : Set q.Target) :
    (chainD2 N A).comp (E.sameR2 A).toLinearMap =
      (E.sameR1 A).toLinearMap.comp (chainD2 M A) := by
  exact linearEquiv_square_cast (self_preimage A) (E.r1 A) (E.r2 A)
    (chainD2 M) (chainD2 N A) (E.r_comm12 A)

/-- 同じ選択集合へ正規化した表示同型の収縮出力。 -/
def sameContraction (A : Set q.Target) : SubsetChainContraction N M A A := by
  simpa only [self_preimage] using E.chainContraction A

/-- 正規化したdegree0射も新比較クラスの同じ生成射である。 -/
theorem sameR0_eq_generated (A : Set q.Target) : (E.sameR0 A).toLinearMap =
    E.comparison.supportedChainMap0 A A (IncidenceSupportedComparison.selfSubsetMapsTo A) := by
  exact linearEquiv_cast_eq (self_preimage A)
    (fun B => ∀ t, t ∈ B → comparisonFactor q q (Reading.coarserThan_refl q) t ∈ A)
    (subsetMapsTo A) (IncidenceSupportedComparison.selfSubsetMapsTo A) (E.r0 A)
    (fun B hB => E.comparison.supportedChainMap0 A B hB) (E.r0_eq_generated A)
/-- 正規化したdegree1射の新比較クラスへの接続。 -/
theorem sameR1_eq_generated (A : Set q.Target) : (E.sameR1 A).toLinearMap =
    E.comparison.supportedChainMap1 A A (IncidenceSupportedComparison.selfSubsetMapsTo A) := by
  exact linearEquiv_cast_eq (self_preimage A)
    (fun B => ∀ t, t ∈ B → comparisonFactor q q (Reading.coarserThan_refl q) t ∈ A)
    (subsetMapsTo A) (IncidenceSupportedComparison.selfSubsetMapsTo A) (E.r1 A)
    (fun B hB => E.comparison.supportedChainMap1 A B hB) (E.r1_eq_generated A)
/-- 正規化したdegree2射の新比較クラスへの接続。 -/
theorem sameR2_eq_generated (A : Set q.Target) : (E.sameR2 A).toLinearMap =
    E.comparison.supportedChainMap2 A A (IncidenceSupportedComparison.selfSubsetMapsTo A) := by
  exact linearEquiv_cast_eq (self_preimage A)
    (fun B => ∀ t, t ∈ B → comparisonFactor q q (Reading.coarserThan_refl q) t ∈ A)
    (subsetMapsTo A) (IncidenceSupportedComparison.selfSubsetMapsTo A) (E.r2 A)
    (fun B hB => E.comparison.supportedChainMap2 A B hB) (E.r2_eq_generated A)

/-- 表示の逆を生成したdegree0射は、同じ基底同型の逆そのものである。 -/
theorem sameR0_symmSelf (A : Set q.Target) :
    (E.symmSelf.sameR0 A).toLinearMap = (E.sameR0 A).symm.toLinearMap := by
  have hinv : (E.sameR0 A).toLinearMap.comp (E.symmSelf.sameR0 A).toLinearMap = LinearMap.id := by
    rw [E.sameR0_eq_generated, E.symmSelf.sameR0_eq_generated]
    apply Finsupp.lhom_ext
    intro v a
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [IncidenceSupportedComparison.supportedChainMap0_single,
      Finsupp.smul_single, smul_eq_mul, mul_one,
      IncidenceSupportedComparison.supportedChainMap0_single,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    apply Subtype.ext
    change E.chartEquiv (E.chartEquiv.symm v.1) = v.1
    exact E.chartEquiv.apply_symm_apply v.1
  apply LinearMap.ext
  intro x
  apply (E.sameR0 A).injective
  have hx := LinearMap.congr_fun hinv x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    LinearEquiv.apply_symm_apply] using hx

/-- 表示の逆を生成したdegree1射は、同じ基底同型の逆そのものである。 -/
theorem sameR1_symmSelf (A : Set q.Target) :
    (E.symmSelf.sameR1 A).toLinearMap = (E.sameR1 A).symm.toLinearMap := by
  have hinv : (E.sameR1 A).toLinearMap.comp (E.symmSelf.sameR1 A).toLinearMap = LinearMap.id := by
    rw [E.sameR1_eq_generated, E.symmSelf.sameR1_eq_generated]
    apply Finsupp.lhom_ext
    intro v a
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [IncidenceSupportedComparison.supportedChainMap1_single,
      E.symmSelf.comparison.targetSubsetEdgeMapOption_eq_some A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A) v (E.edgeEquiv.symm v.1) rfl,
      rationalOptionCell_some, Finsupp.smul_single, smul_eq_mul, mul_one,
      IncidenceSupportedComparison.supportedChainMap1_single,
      E.comparison.targetSubsetEdgeMapOption_eq_some A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A) _ _ rfl,
      rationalOptionCell_some, Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    apply Subtype.ext
    change E.edgeEquiv (E.edgeEquiv.symm v.1) = v.1
    exact E.edgeEquiv.apply_symm_apply v.1
  apply LinearMap.ext
  intro x
  apply (E.sameR1 A).injective
  have hx := LinearMap.congr_fun hinv x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    LinearEquiv.apply_symm_apply] using hx

/-- 表示の逆を生成したdegree2射は、同じ基底同型の逆そのものである。 -/
theorem sameR2_symmSelf (A : Set q.Target) :
    (E.symmSelf.sameR2 A).toLinearMap = (E.sameR2 A).symm.toLinearMap := by
  have hinv : (E.sameR2 A).toLinearMap.comp (E.symmSelf.sameR2 A).toLinearMap = LinearMap.id := by
    rw [E.sameR2_eq_generated, E.symmSelf.sameR2_eq_generated]
    apply Finsupp.lhom_ext
    intro v a
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [IncidenceSupportedComparison.supportedChainMap2_single,
      E.symmSelf.comparison.targetSubsetFaceMapOption_eq_some A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A) v (E.faceEquiv.symm v.1) rfl,
      rationalOptionCell_some, Finsupp.smul_single, smul_eq_mul, mul_one,
      IncidenceSupportedComparison.supportedChainMap2_single,
      E.comparison.targetSubsetFaceMapOption_eq_some A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A) _ _ rfl,
      rationalOptionCell_some, Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    apply Subtype.ext
    change E.faceEquiv (E.faceEquiv.symm v.1) = v.1
    exact E.faceEquiv.apply_symm_apply v.1
  apply LinearMap.ext
  intro x
  apply (E.sameR2 A).injective
  have hx := LinearMap.congr_fun hinv x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    LinearEquiv.apply_symm_apply] using hx

/-- 同じreadingへ正規化した実subset cochain Hom。 -/
def sameHom (A : Set q.Target) := dualSubsetHom A A
  (E.sameR0 A).toLinearMap (E.sameR1 A).toLinearMap (E.sameR2 A).toLinearMap
  (E.sameR_comm01 A) (E.sameR_comm12 A)

/-- 原始表示から独立生成した射と、正規化した双対射の三成分が一致する。 -/
theorem sameHom_eq_generated (A : Set q.Target) : E.sameHom A =
    E.comparison.targetSubsetComparisonHom A A (IncidenceSupportedComparison.selfSubsetMapsTo A) := by
  apply AtlasDefectComposition.cochain_ext
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (E.sameR0 A).toLinearMap z) x =
      freeDualEquiv _ (E.comparison.targetSubsetPullback0 A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A) z) x
    rw [dualCellMap_dual, E.sameR0_eq_generated, E.comparison.supportedChainMap0_dual]
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (E.sameR1 A).toLinearMap z) x =
      freeDualEquiv _ (E.comparison.targetSubsetPullback1 A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A) z) x
    rw [dualCellMap_dual, E.sameR1_eq_generated, E.comparison.supportedChainMap1_dual]
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (E.sameR2 A).toLinearMap z) x =
      freeDualEquiv _ (E.comparison.targetSubsetPullback2 A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A) z) x
    rw [dualCellMap_dual, E.sameR2_eq_generated, E.comparison.supportedChainMap2_dual]

/-- 同じ表示の逆基底双対は、原始逆表示から生成した実Homに一致する。 -/
theorem inverseDual_eq_symmSelf (A : Set q.Target) :
    dualSubsetHom A A (E.sameR0 A).symm.toLinearMap (E.sameR1 A).symm.toLinearMap
      (E.sameR2 A).symm.toLinearMap
      (inverse_comm (E.sameR0 A) (E.sameR1 A) _ _ (E.sameR_comm01 A))
      (inverse_comm (E.sameR1 A) (E.sameR2 A) _ _ (E.sameR_comm12 A)) =
    E.symmSelf.sameHom A := by
  apply AtlasDefectComposition.cochain_ext
  · change dualCellMap (E.sameR0 A).symm.toLinearMap =
      dualCellMap (E.symmSelf.sameR0 A).toLinearMap
    rw [E.sameR0_symmSelf]
  · change dualCellMap (E.sameR1 A).symm.toLinearMap =
      dualCellMap (E.symmSelf.sameR1 A).toLinearMap
    rw [E.sameR1_symmSelf]
  · change dualCellMap (E.sameR2 A).symm.toLinearMap =
      dualCellMap (E.symmSelf.sameR2 A).toLinearMap
    rw [E.sameR2_symmSelf]

end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
