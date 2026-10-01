import ResearchLean.AG.RelativeRepairComposition.NamedColumnSum
import ResearchLean.AG.RelativeRepairComposition.LinearInterface

/-!
# Selected named columns in the same always-column cokernel

The native quotient map is applied to the actual right-hand side and every
full candidate column. Quotient feasibility is equivalent to the original
equation, in both directions, before any section or solution is selected.
-/
namespace AAT.AG.RelativeRepairComposition.CokernelNamed
attribute [local instance] Classical.propDecidable
universe uk ux ue uy uv
variable {k : Type uk} [Field k] {X : Type ux} [AddCommGroup X] [Module k X]
variable {E : Type ue} [Fintype E] {Y : E → Type uy}
variable [∀ e, AddCommGroup (Y e)] [∀ e, Module k (Y e)]
variable {V : Type uv} [AddCommGroup V] [Module k V]
variable (D : X →ₗ[k] V) (C : ∀ e, Y e →ₗ[k] V)

/-- Each whole original named column followed by the same always-column quotient. -/
def column (e : E) : Y e →ₗ[k] (V ⧸ LinearMap.range D) :=
  (LinearInterface.q D).comp (C e)

/-- The same quotient commutes with the full selected original column sum. -/
theorem quotient_sum (S : Set E) (y : ∀ e : S, Y e.1) :
    LinearInterface.q D (NamedDual.sumSelected C S y) =
      NamedDual.sumSelected (column D C) S y :=
  NamedDual.map_sumSelected C (LinearInterface.q D) S y

/-- Feasibility in the cokernel is precisely solvability of the original split equation. -/
theorem mem_iff_equation (r : V) (S : Set E) :
    LinearInterface.q D r ∈ NamedDual.ranges (column D C) S ↔
      ∃ (x : X) (y : ∀ e : S, Y e.1), D x + NamedDual.sumSelected C S y = r := by
  classical
  rw [NamedDual.mem_ranges_iff_sum]
  constructor
  · rintro ⟨y,hy⟩
    have hq : LinearInterface.q D r = LinearInterface.q D (NamedDual.sumSelected C S y) :=
      (quotient_sum D C S y).trans hy |>.symm
    have hm : r - NamedDual.sumSelected C S y ∈ LinearMap.range D :=
      (Submodule.Quotient.eq (LinearMap.range D)).mp hq
    obtain ⟨x,hx⟩ := hm
    exact ⟨x,y,eq_sub_iff_add_eq.mp hx⟩
  · rintro ⟨x,y,hxy⟩
    refine ⟨y,?_⟩
    rw [← quotient_sum]
    have hq := congrArg (LinearInterface.q D) hxy
    have hd : LinearInterface.q D (D x) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range D)).mpr ⟨x,rfl⟩
    rw [map_add,hd,zero_add] at hq
    exact hq

/-- The all-range dual criterion applies to the same original split equation. -/
theorem equation_iff_hits (r : V) (S : Set E) :
    (∃ (x : X) (y : ∀ e : S, Y e.1), D x + NamedDual.sumSelected C S y = r) ↔
      NamedDual.Hits (column D C) (LinearInterface.q D r) S :=
  (mem_iff_equation D C r S).symm.trans
    (NamedDual.mem_ranges_iff_hits (column D C) (LinearInterface.q D r) S)

end AAT.AG.RelativeRepairComposition.CokernelNamed
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
