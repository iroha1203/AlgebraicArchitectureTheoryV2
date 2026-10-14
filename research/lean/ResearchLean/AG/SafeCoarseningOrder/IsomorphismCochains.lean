import ResearchLean.AG.SafeCoarseningOrder.SafetyInstances
import Mathlib.LinearAlgebra.Pi

/-!
# 原始同型から生成する支持複体の同型

S/T/Vの全原始同型から選択セルを輸送し、元の実d0/d1を保つ全三次数同型を生成する。
比較の同型性を入力fieldに置かず、q/辺/支持の保存から構成する。
## Implementation notes

選択セルの全単射にmathlibの非依存関数再添字同型を適用する。既存の実複体を
保ち、H¹同型やrankを原始同型のfieldへ加えない。微分は公開評価APIで照合する。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase
variable {S T V S' T' V' : Type} [Fintype V] [Fintype V']
variable {M : PrimitiveInput S T V} {N : PrimitiveInput S' T' V'}
namespace PrimitiveIso
variable (a : PrimitiveIso M N) (A : Set T')
/-- target逆像に属する元chartと輸送先chartの全単射。 -/
def subsetChartEquiv : M.supported.ChartInTargetSubset (a.target ⁻¹' A) ≃
    N.supported.ChartInTargetSubset A where
  toFun v := ⟨a.chart v.1, by
    obtain ⟨t,ht,hA⟩ := v.2
    exact ⟨a.target t, (a.support_iff _ _).mp ht,hA⟩⟩
  invFun v := ⟨a.chart.symm v.1, by
    obtain ⟨t,ht,hA⟩ := v.2
    refine ⟨a.target.symm t,(a.symm.support_iff _ _).mp ht,?_⟩
    simpa only [Set.mem_preimage,Equiv.apply_symm_apply] using hA⟩
  left_inv v := Subtype.ext (a.chart.symm_apply_apply v.1)
  right_inv v := Subtype.ext (a.chart.apply_symm_apply v.1)
/-- 原始有向辺のK1台は同型によるtarget輸送と両方向に一致。 -/
theorem edge_support_iff (e : M.Edge) (t : T) :
    t ∈ M.supported.edgeSupport e ↔ a.target t ∈ N.supported.edgeSupport (a.edgeEquiv e) := by
  rw [M.mem_edgeSupport,N.mem_edgeSupport]
  exact and_congr (a.support_iff _ _) (a.support_iff _ _)
/-- 同じ辺台に属する元有向辺と輸送先辺の全単射。 -/
def subsetEdgeEquiv : M.supported.EdgeInTargetSubset (a.target ⁻¹' A) ≃
    N.supported.EdgeInTargetSubset A where
  toFun e := ⟨a.edgeEquiv e.1, by
    obtain ⟨t,ht,hA⟩ := e.2
    exact ⟨a.target t,(a.edge_support_iff _ _).mp ht,hA⟩⟩
  invFun e := ⟨a.edgeEquiv.symm e.1, by
    obtain ⟨t,ht,hA⟩ := e.2
    refine ⟨a.target.symm t,(a.symm.edge_support_iff _ _).mp ht,?_⟩
    simpa only [Set.mem_preimage,Equiv.apply_symm_apply] using hA⟩
  left_inv e := Subtype.ext (a.edgeEquiv.symm_apply_apply e.1)
  right_inv e := Subtype.ext (a.edgeEquiv.apply_symm_apply e.1)
/-- 両側の空面型の一意な全単射。 -/
def subsetFaceEquiv : M.supported.FaceInTargetSubset (a.target ⁻¹' A) ≃
    N.supported.FaceInTargetSubset A where
  toFun f := f.1.elim
  invFun f := f.1.elim
  left_inv f := f.1.elim
  right_inv f := f.1.elim
/-- 原始同型が生成する実支持複体の全三次数同型。 -/
def subsetCochainEquiv : ThreeCochainComplex.CochainEquiv
    (M.supported.targetSubsetComplex (a.target ⁻¹' A)) (N.supported.targetSubsetComplex A) where
  e0 := LinearEquiv.funCongrLeft ℚ ℚ (a.subsetChartEquiv A).symm
  e1 := LinearEquiv.funCongrLeft ℚ ℚ (a.subsetEdgeEquiv A).symm
  e2 := LinearEquiv.funCongrLeft ℚ ℚ (a.subsetFaceEquiv A).symm
  comm0 x := by
    funext e
    change (M.supported.targetSubsetComplex (a.target ⁻¹' A)).d0 x
      ((a.subsetEdgeEquiv A).symm e) =
      (N.supported.targetSubsetComplex A).d0
        (LinearEquiv.funCongrLeft ℚ ℚ (a.subsetChartEquiv A).symm x) e
    rw [M.supported.targetSubsetComplex_d0_apply,
      N.supported.targetSubsetComplex_d0_apply]
    rfl
  comm1 x := by
    funext f
    exact f.1.elim

/-- 逆生成Homの次数0評価。恒等商・比較図式が同じ再添字を使うためのAPI。 -/
theorem subsetCochainEquiv_symm_f0_apply (x : (N.supported.targetSubsetComplex A).C0)
    (v : M.supported.ChartInTargetSubset (a.target ⁻¹' A)) :
    (a.subsetCochainEquiv A).symm.toHom.f0 x v = x (a.subsetChartEquiv A v) := rfl
/-- 逆生成Homの次数1評価。元の有向辺を同じ原始同型で輸送する。 -/
theorem subsetCochainEquiv_symm_f1_apply (x : (N.supported.targetSubsetComplex A).C1)
    (e : M.supported.EdgeInTargetSubset (a.target ⁻¹' A)) :
    (a.subsetCochainEquiv A).symm.toHom.f1 x e = x (a.subsetEdgeEquiv A e) := rfl
/-- 逆生成Homの次数2評価。空面を同じ原始同型で輸送する。 -/
theorem subsetCochainEquiv_symm_f2_apply (x : (N.supported.targetSubsetComplex A).C2)
    (f : M.supported.FaceInTargetSubset (a.target ⁻¹' A)) :
    (a.subsetCochainEquiv A).symm.toHom.f2 x f = x (a.subsetFaceEquiv A f) := rfl

end PrimitiveIso
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
