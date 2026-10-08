import ResearchLean.AG.AtlasCoefficientFiber.RawBlocks
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# G-135 B §1：混在面の原始fiber適合

κの入力は実Bの核、出力は実垂直chainの一次homology。
Dyが閉路であることはaD+bB=0から導く。Φへの同定は別の構成義務として残す。

## Implementation notes

κは原Dyをker aへ制限して実V像で商にする。第二同型定理でcokerκを
V像とD(ker B)の和による商へ接続する。任意の関係空間を入力にする案は
同じ原B/Dへの生成経路を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原始垂直微分aの閉路部分空間。 -/
abbrev verticalCycles := LinearMap.ker (verticalEdgeBoundary M A)

/-- 垂直面微分Vを閉路へ余域制限した実写像。 -/
def verticalBoundaryToCycles : (VerticalFace M A →₀ ℚ) →ₗ[ℚ] verticalCycles M A :=
  (verticalBoundary M A).codRestrict _ (fun x =>
    LinearMap.congr_fun (verticalEdgeBoundary_comp_verticalBoundary M A) x)

/-- 実垂直微分の閉路への値。 -/
@[simp] theorem verticalBoundaryToCycles_val (x : VerticalFace M A →₀ ℚ) :
    (verticalBoundaryToCycles M A x).1 = verticalBoundary M A x := rfl

/-- 元のaとVによる垂直一次homology。 -/
abbrev VerticalHomology := verticalCycles M A ⧸ LinearMap.range (verticalBoundaryToCycles M A)

/-- 混在面の実水平incidence Bの閉路部分空間。 -/
abbrev mixedCycles := LinearMap.ker (mixedHorizontalBoundary M A)

/-- 混在関係の閉路に残る垂直成分Dyはa閉路になる。 -/
theorem mixedCycle_vertical_closed (y : mixedCycles M A) :
    verticalEdgeBoundary M A (mixedVerticalBoundary M A y.1) = 0 := by
  have hh := LinearMap.congr_fun (mixedBoundary_square M A) y.1
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hh
  rw [show mixedHorizontalBoundary M A y.1 = 0 from y.2, map_zero, add_zero] at hh
  exact hh

/-- 実Dのker Bへの定義域制限とker aへの余域制限。 -/
def mixedCycleToVertical : mixedCycles M A →ₗ[ℚ] verticalCycles M A :=
  ((mixedVerticalBoundary M A).comp (mixedCycles M A).subtype).codRestrict _
    (mixedCycle_vertical_closed M A)

/-- この写像の代表は同じ原始行列のDy。 -/
@[simp] theorem mixedCycleToVertical_val (y : mixedCycles M A) :
    (mixedCycleToVertical M A y).1 = mixedVerticalBoundary M A y.1 := rfl

/-- 原始混在面からのκ。値はDyの垂直homology類。 -/
def rawKappa : mixedCycles M A →ₗ[ℚ] VerticalHomology M A :=
  (LinearMap.range (verticalBoundaryToCycles M A)).mkQ.comp (mixedCycleToVertical M A)

/-- κの評価は供給された証明書でなく実Dyの商類。 -/
@[simp] theorem rawKappa_apply (y : mixedCycles M A) :
    rawKappa M A y = Submodule.Quotient.mk (mixedCycleToVertical M A y) := rfl

/-- κ類が零であることはDyが原垂直面微分の像に属することと同値。 -/
theorem rawKappa_eq_zero_iff (y : mixedCycles M A) :
    rawKappa M A y = 0 ↔
      ∃ x : VerticalFace M A →₀ ℚ, verticalBoundary M A x = mixedVerticalBoundary M A y.1 := by
  rw [rawKappa_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- 垂直面微分と混在閉路微分が張る、指定商の実関係部分空間。 -/
def verticalRelations : Submodule ℚ (verticalCycles M A) :=
  LinearMap.range (verticalBoundaryToCycles M A) ⊔ LinearMap.range (mixedCycleToVertical M A)

/-- 関係部分空間への所属はVx+Dyの実代表と同値。 -/
theorem mem_verticalRelations (z : verticalCycles M A) :
    z ∈ verticalRelations M A ↔ ∃ (x : VerticalFace M A →₀ ℚ) (y : mixedCycles M A),
      verticalBoundary M A x + mixedVerticalBoundary M A y.1 = z.1 := by
  constructor
  · intro hz
    obtain ⟨v, ⟨x, hx⟩, w, ⟨y, hy⟩, he⟩ := Submodule.mem_sup.mp hz
    exact ⟨x, y, by
      have hh := congrArg Subtype.val he
      simpa only [← hx, ← hy, Submodule.coe_add, verticalBoundaryToCycles_val,
        mixedCycleToVertical_val] using hh⟩
  · rintro ⟨x, y, hz⟩
    exact Submodule.mem_sup.mpr ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, Subtype.ext hz⟩

/-- κの像は同じ混在閉路微分の商像である。 -/
theorem rawKappa_range : LinearMap.range (rawKappa M A) =
    (LinearMap.range (mixedCycleToVertical M A)).map
      (LinearMap.range (verticalBoundaryToCycles M A)).mkQ := by
  rw [rawKappa, LinearMap.range_comp]

/-- 二段の商は設計のker a/(im V+D ker B)そのもの。 -/
def rawKappaCokernelEquiv :
    (VerticalHomology M A ⧸ LinearMap.range (rawKappa M A)) ≃ₗ[ℚ]
      (verticalCycles M A ⧸ verticalRelations M A) :=
  (Submodule.quotEquivOfEq _ _ (rawKappa_range M A)).trans
    (Submodule.quotientQuotientEquivQuotientSup _ _)

/-- 二段商の同定は同じ垂直閉路の類を保つ。 -/
@[simp] theorem rawKappaCokernelEquiv_mk (z : verticalCycles M A) :
    rawKappaCokernelEquiv M A
      (Submodule.Quotient.mk (Submodule.Quotient.mk z)) = Submodule.Quotient.mk z := by
  simp only [rawKappaCokernelEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.quotientQuotientEquivQuotientSup, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.verticalCycles
#print axioms AAT.AG.AtlasCoefficientFiber.verticalBoundaryToCycles
#print axioms AAT.AG.AtlasCoefficientFiber.verticalBoundaryToCycles_val
#print axioms AAT.AG.AtlasCoefficientFiber.VerticalHomology
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCycles
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCycle_vertical_closed
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCycleToVertical
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCycleToVertical_val
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappa
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappa_apply
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappa_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRelations
#print axioms AAT.AG.AtlasCoefficientFiber.mem_verticalRelations
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappa_range
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappaCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappaCokernelEquiv_mk
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
