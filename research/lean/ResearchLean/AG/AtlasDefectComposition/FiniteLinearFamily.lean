import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Formal.Util.AssertStandardAxioms
/-! # 有限線形族の実核・実像・実余核

Implementation notes: 実核は元の各成分、実余核は実像による商の代表元で同定する。有限族の関数表示は重複を保持する有限直和表示であり、添字の集合圧縮を行わない。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.FiniteLinearFamily
universe v w
variable {J : Type v} {A B : J → Type w}
variable [∀ j, AddCommGroup (A j)] [∀ j, Module ℚ (A j)]
variable [∀ j, AddCommGroup (B j)] [∀ j, Module ℚ (B j)]
variable (f : ∀ j, A j →ₗ[ℚ] B j)
/-- 各成分の実写像から作る族写像。 -/
def map : ((j : J) → A j) →ₗ[ℚ] ((j : J) → B j) :=
  LinearMap.pi fun j => (f j).comp (LinearMap.proj j)
/-- Dの族写像mapのAPI補題。同じ添字の実写像へ評価を正規化する。 -/
@[simp] theorem map_apply (x : (j : J) → A j) (j : J) : map f x j = f j (x j) := rfl
/-- 族写像の核を各実核の族へ同定する。 -/
def kernelEquiv : LinearMap.ker (map f) ≃ₗ[ℚ] ((j : J) → LinearMap.ker (f j)) where
  toFun x j := ⟨x.val j,congrFun x.property j⟩
  invFun x := ⟨fun j => (x j).val,funext fun j => (x j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- Dの実核族同型kernelEquivのAPI補題。核の元の同じ成分値を保持する。 -/
@[simp] theorem kernelEquiv_val (x : LinearMap.ker (map f)) (j : J) :
    (kernelEquiv f x j).val = x.val j := rfl
/-- 像の族等号は、成分ごとの実前像を同時に選ぶことで成立する。 -/
theorem range_eq : LinearMap.range (map f) =
    Submodule.pi Set.univ (fun j => LinearMap.range (f j)) := by
  classical
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    intro j _
    exact ⟨y j,rfl⟩
  · intro hx
    have hy : ∀ j, ∃ y, f j y = x j := fun j => hx j (Set.mem_univ j)
    choose y hy using hy
    exact ⟨y,funext hy⟩
/-- 族写像の実像を、各実像の族へ元を保って同定する。 -/
def rangeEquiv : LinearMap.range (map f) ≃ₗ[ℚ] ((j : J) → LinearMap.range (f j)) where
  toFun x j := ⟨x.val j,by
    have hx : x.val ∈ Submodule.pi Set.univ (fun j => LinearMap.range (f j)) := by
      rw [← range_eq];exact x.property
    exact hx j (Set.mem_univ j)⟩
  invFun x := ⟨fun j => (x j).val,by
    rw [range_eq]
    intro j _
    exact (x j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- Dの実像族同型rangeEquivのAPI補題。像の元の同じ成分値を保持する。 -/
@[simp] theorem rangeEquiv_val (x : LinearMap.range (map f)) (j : J) :
    (rangeEquiv f x j).val = x.val j := rfl
variable [Fintype J]
/-- 族写像の余核を、同じ全添字の実余核族へ同定する。 -/
def cokernelEquiv : (((j : J) → B j) ⧸ LinearMap.range (map f)) ≃ₗ[ℚ]
    ((j : J) → B j ⧸ LinearMap.range (f j)) := by
  classical
  exact (Submodule.quotEquivOfEq _ _ (range_eq f)).trans
    (Submodule.quotientPi (fun j => LinearMap.range (f j)))
/-- 実商代表元の同定は同じ添字の実商代表元を読む。 -/
@[simp] theorem cokernelEquiv_mk (x : (j : J) → B j) (j : J) :
    cokernelEquiv f ((LinearMap.range (map f)).mkQ x) j =
      (LinearMap.range (f j)).mkQ (x j) := by
  classical
  rfl
end AAT.AG.AtlasDefectComposition.FiniteLinearFamily
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.FiniteLinearFamily
