import ResearchLean.AG.RelativeRepairComposition.CokernelNamedRanges
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# G-131 A: the full cokernel for every selected original range

## Implementation notes

The selected domain keeps the whole coefficient at each original allowed name.
The third isomorphism theorem is applied to this selected map, so no all-column
quotient is silently substituted for an arbitrary range. Both quotient maps
retain the same original face representative.
-/

namespace AAT.AG.RepairObservationDuality.SelectedCokernel
open RelativeRepairComposition
universe uk ux ue uy uw
variable {k : Type uk} [Field k] {X : Type ux} [AddCommGroup X] [Module k X]
variable {E : Type ue} [Fintype E] {Y : E → Type uy}
variable [∀ e, AddCommGroup (Y e)] [∀ e, Module k (Y e)]
variable {W : Type uw} [AddCommGroup W] [Module k W]
variable (D₀ : X →ₗ[k] W) (C : ∀ e, Y e →ₗ[k] W)

/-- A's permitted correction map combines the always columns and precisely S's
whole original named coefficients. -/
noncomputable def differential (S : Set E) : (X × (∀ e : S, Y e.1)) →ₗ[k] W :=
  D₀.coprod (NamedDual.sumSelected C S)

/-- The selected correction map computes the original split equation literally. -/
theorem differential_apply (S : Set E) (h : X × (∀ e : S, Y e.1)) :
    differential D₀ C S h = D₀ h.1 + NamedDual.sumSelected C S h.2 := rfl

/-- A's native image is the always image plus the full selected candidate image. -/
theorem range_differential (S : Set E) :
    LinearMap.range (differential D₀ C S) =
      LinearMap.range D₀ ⊔ LinearMap.range (NamedDual.sumSelected C S) :=
  LinearMap.range_coprod D₀ (NamedDual.sumSelected C S)

/-- The original split equation is the same single full correction equation. -/
theorem equation_iff (S : Set E) (r : W) :
    (∃ x y, D₀ x + NamedDual.sumSelected C S y = r) ↔
      ∃ h, differential D₀ C S h = r := by
  constructor
  · rintro ⟨x, y, he⟩
    exact ⟨(x, y), (differential_apply D₀ C S (x, y)).trans he⟩
  · rintro ⟨h, he⟩
    exact ⟨h.1, h.2, (differential_apply D₀ C S h).symm.trans he⟩

/-- A's exact permitted equation is solvable precisely at zero of its native cokernel. -/
theorem equation_iff_zero (S : Set E) (r : W) :
    (∃ h, differential D₀ C S h = r) ↔
      (LinearMap.range (differential D₀ C S)).mkQ r = 0 :=
  (Submodule.Quotient.mk_eq_zero (LinearMap.range (differential D₀ C S))).symm

/-- The selected original quotient-column range is the selected full image
followed by the always quotient. This equality includes arbitrary S. -/
theorem selected_ranges_eq (S : Set E) :
    NamedDual.ranges (CokernelNamed.column D₀ C) S =
      (LinearMap.range (NamedDual.sumSelected C S)).map (LinearInterface.q D₀) := by
  ext o
  rw [NamedDual.mem_ranges_iff_sum, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨NamedDual.sumSelected C S y, ⟨y, rfl⟩,
      (CokernelNamed.quotient_sum D₀ C S y).trans hy⟩
  · rintro ⟨v, ⟨y, rfl⟩, hy⟩
    exact ⟨y, (CokernelNamed.quotient_sum D₀ C S y).symm.trans hy⟩

/-- The same residual obstruction quotient maps to the native cokernel of D_S,
using the selected original map and its complete image. -/
noncomputable def residualToNative (S : Set E) :
    ((W ⧸ LinearMap.range D₀) ⧸ NamedDual.ranges (CokernelNamed.column D₀ C) S) ≃ₗ[k]
      W ⧸ LinearMap.range (differential D₀ C S) :=
  ((Submodule.quotEquivOfEq _ _ (selected_ranges_eq D₀ C S)).trans
    (Submodule.quotientQuotientEquivQuotientSup (LinearMap.range D₀)
      (LinearMap.range (NamedDual.sumSelected C S)))).trans
    (Submodule.quotEquivOfEq _ _ (range_differential D₀ C S).symm)

/-- The forward quotient comparison preserves the very same original face value. -/
theorem residualToNative_value (S : Set E) (r : W) :
    residualToNative D₀ C S
      ((NamedDual.ranges (CokernelNamed.column D₀ C) S).mkQ (LinearInterface.q D₀ r)) =
      (LinearMap.range (differential D₀ C S)).mkQ r := by
  rw [residualToNative, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  simp only [Submodule.mkQ_apply]
  rw [Submodule.quotEquivOfEq_mk]
  change (Submodule.quotEquivOfEq _ _ (range_differential D₀ C S).symm)
    ((LinearMap.range D₀ ⊔ LinearMap.range (NamedDual.sumSelected C S)).mkQ r) = _
  exact Submodule.quotEquivOfEq_mk _ _ _ _

/-- A's required cokernel-to-residual quotient is the inverse of the full comparison. -/
noncomputable def nativeToResidual (S : Set E) :
    (W ⧸ LinearMap.range (differential D₀ C S)) ≃ₗ[k]
      ((W ⧸ LinearMap.range D₀) ⧸ NamedDual.ranges (CokernelNamed.column D₀ C) S) :=
  (residualToNative D₀ C S).symm

/-- The required orientation also sends q_S r to q₀ r modulo the same R_S. -/
theorem nativeToResidual_value (S : Set E) (r : W) :
    nativeToResidual D₀ C S ((LinearMap.range (differential D₀ C S)).mkQ r) =
      (NamedDual.ranges (CokernelNamed.column D₀ C) S).mkQ (LinearInterface.q D₀ r) :=
  (LinearEquiv.symm_apply_eq (residualToNative D₀ C S)).mpr
    (residualToNative_value D₀ C S r).symm

end AAT.AG.RepairObservationDuality.SelectedCokernel

namespace AAT.AG.RepairObservationDuality.SelectedCokernel
open RelativeRepairComposition
variable (k : Type*) [Field k]

/-- The same nonzero field and original column distinguish empty from full
permission: a missing primitive column cannot be silently inserted. -/
theorem empty_full_differ :
    (LinearMap.range (differential (0 : k →ₗ[k] k)
      (fun _ : Unit => LinearMap.id) ∅)).mkQ (1 : k) ≠ 0 ∧
    (LinearMap.range (differential (0 : k →ₗ[k] k)
      (fun _ : Unit => LinearMap.id) Set.univ)).mkQ (1 : k) = 0 := by
  classical
  constructor
  · intro hz
    obtain ⟨h, hh⟩ := (equation_iff_zero (0 : k →ₗ[k] k)
      (fun _ : Unit => LinearMap.id) ∅ 1).mpr hz
    rw [differential_apply, NamedDual.sumSelected_apply] at hh
    simp at hh
  · apply (equation_iff_zero (0 : k →ₗ[k] k)
      (fun _ : Unit => LinearMap.id) Set.univ 1).mp
    apply (equation_iff (0 : k →ₗ[k] k) (fun _ : Unit => LinearMap.id) Set.univ 1).mp
    apply (CokernelNamed.mem_iff_equation (0 : k →ₗ[k] k)
      (fun _ : Unit => LinearMap.id) 1 Set.univ).mp
    exact NamedDual.range_le (CokernelNamed.column (0 : k →ₗ[k] k)
      (fun _ : Unit => LinearMap.id)) Set.univ () (Set.mem_univ ()) ⟨1, rfl⟩

end AAT.AG.RepairObservationDuality.SelectedCokernel
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.SelectedCokernel
