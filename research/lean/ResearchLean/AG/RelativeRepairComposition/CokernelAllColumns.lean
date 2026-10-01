import ResearchLean.AG.RelativeRepairComposition.CokernelNamedRanges
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The same always quotient followed by all candidate columns

The full candidate image is derived from the original named finite sum. The
second quotient preserves every original representative under the third
isomorphism theorem, rather than identifying only vanishing conditions.
-/
namespace AAT.AG.RelativeRepairComposition.CokernelNamed
attribute [local instance] Classical.propDecidable
universe uk ux ue uy uv
variable {k : Type uk} [Field k] {X : Type ux} [AddCommGroup X] [Module k X]
variable {E : Type ue} [Fintype E] {Y : E → Type uy}
variable [∀ e, AddCommGroup (Y e)] [∀ e, Module k (Y e)]
variable {V : Type uv} [AddCommGroup V] [Module k V]
variable (D : X →ₗ[k] V) (C : ∀ e, Y e →ₗ[k] V)

/-- The whole original finite candidate map. -/
noncomputable def fullMap : (∀ e, Y e) →ₗ[k] V := by
  classical
  exact LinearMap.lsum k Y k C

/-- Summing every selected original name reconstructs the same full candidate map. -/
theorem sum_univ (y : ∀ e, Y e) :
    NamedDual.sumSelected C Set.univ (fun e => y e.1) = fullMap C y := by
  have h := LinearMap.congr_fun (NamedDual.sum_extend C Set.univ) (fun e => y e.1)
  change fullMap C (NamedDual.extendSelected (k := k) Set.univ (fun e => y e.1)) = _ at h
  rw [NamedDual.extend_read (k := k) Set.univ y (by intro e he; exact (he trivial).elim)] at h
  exact h.symm

/-- The all-candidate range is precisely the full original candidate image in the always quotient. -/
theorem all_ranges_eq : NamedDual.ranges (column D C) Set.univ =
    (LinearMap.range (fullMap C)).map (LinearInterface.q D) := by
  classical
  ext o
  rw [NamedDual.mem_ranges_iff_sum,Submodule.mem_map]
  constructor
  · rintro ⟨y,hy⟩
    let all := NamedDual.extendSelected (k := k) Set.univ y
    have h := LinearMap.congr_fun (NamedDual.sum_extend C Set.univ) y
    change fullMap C all = NamedDual.sumSelected C Set.univ y at h
    refine ⟨fullMap C all,⟨all,rfl⟩,?_⟩
    rw [h,quotient_sum]
    exact hy
  · rintro ⟨v,⟨y,rfl⟩,hy⟩
    refine ⟨fun e => y e.1,?_⟩
    rw [← quotient_sum,sum_univ]
    exact hy

/-- The full second quotient is the original face space modulo all original columns. -/
noncomputable def secondQuotient :
    ((V ⧸ LinearMap.range D) ⧸ NamedDual.ranges (column D C) Set.univ) ≃ₗ[k]
      V ⧸ (LinearMap.range D ⊔ LinearMap.range (fullMap C)) :=
  (Submodule.quotEquivOfEq _ _ (all_ranges_eq D C)).trans
    (Submodule.quotientQuotientEquivQuotientSup (LinearMap.range D) (LinearMap.range (fullMap C)))

/-- The complete second quotient maps the very same original representative. -/
theorem secondQuotient_value (v : V) :
    secondQuotient D C ((NamedDual.ranges (column D C) Set.univ).mkQ (LinearInterface.q D v)) =
      (LinearMap.range D ⊔ LinearMap.range (fullMap C)).mkQ v := by
  rw [secondQuotient,LinearEquiv.trans_apply]
  simp only [Submodule.mkQ_apply]
  rw [Submodule.quotEquivOfEq_mk]
  rfl

end AAT.AG.RelativeRepairComposition.CokernelNamed
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
