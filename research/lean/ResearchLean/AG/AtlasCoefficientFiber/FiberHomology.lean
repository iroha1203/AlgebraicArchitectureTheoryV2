import ResearchLean.AG.AtlasCoefficientFiber.FiberChains
import ResearchLean.AG.AtlasCoefficientFiber.Kappa
import ResearchLean.AG.AtlasCoefficientFiber.ChainHomologyDual
import ResearchLean.AG.AtlasCoefficientFiber.DegenerateHomology
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# G-135 B §1：全原Φの一次homologyとκ

元の垂直chain分類は両微分に可換であり、閉路・実微分像・商へ降りる。
有限直積は設計の有限直和表示である。

## Implementation notes

原chainの両方向同型をkerと実微分像へ制限し、mathlibのquotientPiを使う。
Φのhomologyを入力fieldにする案は原垂直homologyとの両方向接続を失うため採用しない。
κ余核の型推論ではnative Piの加法群/module instanceを先に固定し、
同じ原Φ商のinstance探索を再開しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 各原Φのchain閉路部分空間。 -/
abbrev phiCycles (c : Nc.ChartInTargetSubset A) := LinearMap.ker (phiBoundary1 M A c)

/-- 各原Φのchain第二微分の閉路への実制限。 -/
def phiBoundaryToCycles (c : Nc.ChartInTargetSubset A) :
    (PhiFace M A c →₀ ℚ) →ₗ[ℚ] phiCycles M A c :=
  chainBoundaryToCycles (phiBoundary1 M A c) (phiBoundary2 M A c)
    (phiBoundary1_comp_phiBoundary2 M A c)

/-- 各原Φの一次chain homology。 -/
abbrev PhiHomology (c : Nc.ChartInTargetSubset A) :=
  phiCycles M A c ⧸ LinearMap.range (phiBoundaryToCycles M A c)

/-- 原垂直閉路と全Φ閉路の両方向同定。 -/
def phiVerticalCyclesEquiv : verticalCycles M A ≃ₗ[ℚ]
    (c : Nc.ChartInTargetSubset A) → phiCycles M A c where
  toFun z c := ⟨phiChainEquiv1 M A z.1 c, by
    change phiBoundary1 M A c (phiChainEquiv1 M A z.1 c) = 0
    rw [← phiChainEquiv_comm1, show verticalEdgeBoundary M A z.1 = 0 from z.2]
    simp⟩
  invFun y := ⟨(phiChainEquiv1 M A).symm (fun c => (y c).1), by
    apply (phiChainEquiv0 M A).injective
    funext c
    rw [phiChainEquiv_comm1]
    simp only [LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply]
    exact (y c).2⟩
  left_inv z := by
    apply Subtype.ext
    exact (phiChainEquiv1 M A).symm_apply_apply z.1
  right_inv y := by
    funext c
    apply Subtype.ext
    exact congrFun ((phiChainEquiv1 M A).apply_symm_apply (fun c => (y c).1)) c
  map_add' x y := by
    funext c
    apply Subtype.ext
    exact congrFun ((phiChainEquiv1 M A).map_add x.1 y.1) c
  map_smul' r x := by
    funext c
    apply Subtype.ext
    exact congrFun ((phiChainEquiv1 M A).map_smul r x.1) c

/-- 閉路同定は同じ原係数分類の値を読む。 -/
@[simp] theorem phiVerticalCyclesEquiv_val (z : verticalCycles M A) (c : Nc.ChartInTargetSubset A) :
    (phiVerticalCyclesEquiv M A z c).1 = phiChainEquiv1 M A z.1 c := rfl

/-- 元Vの微分像は全原Φの微分像の直積へ全て、ちょうど移る。 -/
theorem phiVerticalCyclesEquiv_range :
    (LinearMap.range (verticalBoundaryToCycles M A)).map
      (phiVerticalCyclesEquiv M A).toLinearMap =
    Submodule.pi Set.univ (fun c => LinearMap.range (phiBoundaryToCycles M A c)) := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    intro c _
    refine ⟨phiChainEquiv2 M A x c, ?_⟩
    apply Subtype.ext
    exact (phiChainEquiv_comm2 M A x c).symm
  · intro hy
    have hx : ∀ c, ∃ x, phiBoundaryToCycles M A c x = y c := fun c => hy c (Set.mem_univ c)
    choose x hx using hx
    let t := (phiChainEquiv2 M A).symm x
    refine ⟨verticalBoundaryToCycles M A t, ⟨t, rfl⟩, ?_⟩
    funext c
    apply Subtype.ext
    change phiChainEquiv1 M A (verticalBoundary M A t) c = (y c).1
    rw [phiChainEquiv_comm2]
    have ht : phiChainEquiv2 M A t = x := (phiChainEquiv2 M A).apply_symm_apply x
    rw [ht]
    exact congrArg Subtype.val (hx c)

/-- 全原垂直homologyと全Φ一次homologyの有限直和表示の両方向同型。 -/
def verticalHomologyPhiEquiv : VerticalHomology M A ≃ₗ[ℚ]
    (c : Nc.ChartInTargetSubset A) → PhiHomology M A c := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  exact (Submodule.Quotient.equiv _ _ (phiVerticalCyclesEquiv M A)
    (phiVerticalCyclesEquiv_range M A)).trans (Submodule.quotientPi _)

/-- 全Φ homologyの同定は各閉路代表の実fiber類を返す。 -/
@[simp] theorem verticalHomologyPhiEquiv_mk (z : verticalCycles M A) (c : Nc.ChartInTargetSubset A) :
    verticalHomologyPhiEquiv M A (Submodule.Quotient.mk z) c =
      Submodule.Quotient.mk (phiVerticalCyclesEquiv M A z c) := rfl

/-- 設計のκは同じ原Dyの類を全Φ表示へ送る。 -/
def kappa : mixedCycles M A →ₗ[ℚ]
    ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) :=
  (verticalHomologyPhiEquiv M A).toLinearMap.comp (rawKappa M A)

/-- κの代表は原D行列の同じ閉路であり、任意の中間写像ではない。 -/
@[simp] theorem kappa_apply (y : mixedCycles M A) :
    kappa M A y = verticalHomologyPhiEquiv M A (Submodule.Quotient.mk (mixedCycleToVertical M A y)) := rfl

/-- κの各Φ成分は同じDyをそのfiberへ制限した閉路の類。 -/
@[simp] theorem kappa_apply_component (y : mixedCycles M A) (c : Nc.ChartInTargetSubset A) :
    kappa M A y c = Submodule.Quotient.mk
      (phiVerticalCyclesEquiv M A (mixedCycleToVertical M A y) c) := rfl

/-- 原κ像は、全Φ表示の同じκ像へちょうど移る。 -/
theorem kappa_range : (LinearMap.range (rawKappa M A)).map
    (verticalHomologyPhiEquiv M A).toLinearMap = LinearMap.range (kappa M A) := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨rawKappa M A y, ⟨y, rfl⟩, rfl⟩

/-- 全Φ homologyのnative Pi加法群instanceを型推論のため局所固定する。 -/
local instance allPhiHomologyAddCommGroup :
    AddCommGroup ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) := inferInstance

/-- 全Φ homologyのnative Pi module instanceを型推論のため局所固定する。 -/
local instance allPhiHomologyModule :
    Module ℚ ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) := inferInstance

/-- 全Φ表示の実κ像によるnative商。原混在関係だけを商にする。 -/
abbrev KappaCokernel :=
  ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) ⧸ LinearMap.range (kappa M A)

/-- 原垂直表示と全Φ表示での、同じκ余核の両方向同型。 -/
def kappaCokernelCoordinateEquiv :
    (VerticalHomology M A ⧸ LinearMap.range (rawKappa M A)) ≃ₗ[ℚ]
      KappaCokernel M A :=
  Submodule.Quotient.equiv (R := ℚ) (LinearMap.range (rawKappa M A))
    (LinearMap.range (kappa M A)) (verticalHomologyPhiEquiv M A) (kappa_range M A)

/-- κ余核の座標同型は、同じ全Φ homology代表を商へ送る。 -/
@[simp] theorem kappaCokernelCoordinateEquiv_mk (z : VerticalHomology M A) :
    kappaCokernelCoordinateEquiv M A (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (verticalHomologyPhiEquiv M A z) := rfl

/-- 全Φ表示で定義した実κ余核と、同じ指定Lの一次homologyとの両方向同型。 -/
def kappaCokernelHomologyEquiv :
    KappaCokernel M A ≃ₗ[ℚ]
      DegenerateHomology M A :=
  (kappaCokernelCoordinateEquiv M A).symm.trans (rawKappaCokernelHomologyEquiv M A)

/-- 設計の全Φ κの余核を、同じ指定Lの標準H₁へ両方向に同定。 -/
def kappaCokernelStandardEquiv :
    KappaCokernel M A ≃ₗ[ℚ]
      (degenerateChain M A).homology (1 : ℤ) :=
  (kappaCokernelCoordinateEquiv M A).symm.trans (rawKappaCokernelStandardEquiv M A)

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.phiCycles
#print axioms AAT.AG.AtlasCoefficientFiber.phiBoundaryToCycles
#print axioms AAT.AG.AtlasCoefficientFiber.PhiHomology
#print axioms AAT.AG.AtlasCoefficientFiber.phiVerticalCyclesEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.phiVerticalCyclesEquiv_val
#print axioms AAT.AG.AtlasCoefficientFiber.phiVerticalCyclesEquiv_range
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyPhiEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.verticalHomologyPhiEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.kappa
#print axioms AAT.AG.AtlasCoefficientFiber.kappa_apply
#print axioms AAT.AG.AtlasCoefficientFiber.kappa_apply_component
#print axioms AAT.AG.AtlasCoefficientFiber.kappa_range
#print axioms AAT.AG.AtlasCoefficientFiber.allPhiHomologyAddCommGroup
#print axioms AAT.AG.AtlasCoefficientFiber.allPhiHomologyModule
#print axioms AAT.AG.AtlasCoefficientFiber.KappaCokernel
#print axioms AAT.AG.AtlasCoefficientFiber.kappaCokernelCoordinateEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.kappaCokernelCoordinateEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.kappaCokernelHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.kappaCokernelStandardEquiv
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
