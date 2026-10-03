import ResearchLean.AG.RepairObservationDuality.SelectedCokernel
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# G-131 D: the same named dual witness on the residual quotient

## Implementation notes

The G-130 witness lives on the always-column quotient and annihilates the
selected full columns. The canonical quotient-dual inverse descends that
very functional, preserving its value. The selected native comparison
then keeps the same original face representative. Selecting a fresh native
separator alone would lose the original named support of the witness.
-/

namespace AAT.AG.RepairObservationDuality.ResidualDualWitness
open RelativeRepairComposition
variable {k X W E : Type*} [Field k]
variable [AddCommGroup X] [Module k X] [AddCommGroup W] [Module k W]
variable [Fintype E] {Y : E → Type*}
variable [∀ e, AddCommGroup (Y e)] [∀ e, Module k (Y e)]
variable (D₀ : X →ₗ[k] W) (C : ∀ e, Y e →ₗ[k] W)
local notation "col" => CokernelNamed.column D₀ C

/-- D's quotient-dual descent uses the original G-130 witness and its proved column annihilation. -/
noncomputable def residual (S : Set E) (phi : Module.Dual k (W ⧸ LinearMap.range D₀))
    (hphi : ∀ e ∈ S, phi.comp (col e) = 0) :
    Module.Dual k ((W ⧸ LinearMap.range D₀) ⧸ NamedDual.ranges col S) :=
  (Submodule.dualQuotEquivDualAnnihilator (NamedDual.ranges col S)).symm
    ⟨phi, (NamedDual.annihilates_iff col S phi).mpr hphi⟩

omit [Fintype E] in
/-- D's residual dual returns exactly the value of the same always-quotient witness. -/
theorem residual_value (S : Set E) (phi : Module.Dual k (W ⧸ LinearMap.range D₀))
    (hphi : ∀ e ∈ S, phi.comp (col e) = 0) (o : W ⧸ LinearMap.range D₀) :
    residual D₀ C S phi hphi ((NamedDual.ranges col S).mkQ o) = phi o :=
  Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk _ _ o

/-- D's identical witness on the native selected cokernel follows the representative-preserving comparison. -/
noncomputable def native (S : Set E) (phi : Module.Dual k (W ⧸ LinearMap.range D₀))
    (hphi : ∀ e ∈ S, phi.comp (col e) = 0) :
    Module.Dual k (W ⧸ LinearMap.range (SelectedCokernel.differential D₀ C S)) :=
  (residual D₀ C S phi hphi).comp (SelectedCokernel.nativeToResidual D₀ C S).toLinearMap

/-- D's native dual evaluates the original RHS with exactly its G-130 dual value. -/
theorem native_value (S : Set E) (phi : Module.Dual k (W ⧸ LinearMap.range D₀))
    (hphi : ∀ e ∈ S, phi.comp (col e) = 0) (r : W) :
    native D₀ C S phi hphi
      ((LinearMap.range (SelectedCokernel.differential D₀ C S)).mkQ r) =
        phi (LinearInterface.q D₀ r) := by
  rw [native, LinearMap.comp_apply, LinearEquiv.coe_coe, SelectedCokernel.nativeToResidual_value,
    residual_value]

/-- D's original candidate direction has nonzero witness composite exactly when it changes the residual value. -/
theorem candidate_changes_iff (S : Set E) (phi : Module.Dual k (W ⧸ LinearMap.range D₀))
    (hphi : ∀ e ∈ S, phi.comp (col e) = 0) (e : E) :
    e ∈ NamedDual.support col phi ↔ ∃ y : Y e,
      native D₀ C S phi hphi
        ((LinearMap.range (SelectedCokernel.differential D₀ C S)).mkQ (C e y)) ≠ 0 := by
  rw [NamedDual.mem_support]
  simp only [native_value]
  constructor
  · intro hn
    by_contra he
    apply hn
    ext y
    exact not_not.mp (fun h => he ⟨y,h⟩)
  · rintro ⟨y,hy⟩ hz
    exact hy (LinearMap.congr_fun hz y)

/-- D's original candidate support exactly records changes of the same residual value at any RHS. -/
theorem candidate_change_value_iff (S : Set E) (phi : Module.Dual k (W ⧸ LinearMap.range D₀))
    (hphi : ∀ e ∈ S, phi.comp (col e) = 0) (e : E) (r : W) :
    e ∈ NamedDual.support col phi ↔ ∃ y : Y e,
      native D₀ C S phi hphi
        ((LinearMap.range (SelectedCokernel.differential D₀ C S)).mkQ (r + C e y)) ≠
      native D₀ C S phi hphi
        ((LinearMap.range (SelectedCokernel.differential D₀ C S)).mkQ r) := by
  rw [candidate_changes_iff D₀ C S phi hphi e]
  simp only [map_add, ne_eq, add_eq_left]

/-- D's failure separator is generated from the independent original selected equation and preserves its nonzero value. -/
theorem failure (S : Set E) (r : W)
    (hn : ¬ ∃ h, SelectedCokernel.differential D₀ C S h = r) :
    ∃ (phi : Module.Dual k (W ⧸ LinearMap.range D₀))
      (hp : ∀ e ∈ S, phi.comp (col e) = 0),
      native D₀ C S phi hp
        ((LinearMap.range (SelectedCokernel.differential D₀ C S)).mkQ r) ≠ 0 := by
  have hr : LinearInterface.q D₀ r ∉ NamedDual.ranges col S := by
    intro hm
    exact hn ((SelectedCokernel.equation_iff D₀ C S r).mp
      ((CokernelNamed.mem_iff_equation D₀ C r S).mp hm))
  obtain ⟨phi,hv,hp⟩ := NamedDual.failure_witness col (LinearInterface.q D₀ r) S hr
  refine ⟨phi,hp,?_⟩
  rw [native_value]
  exact hv

end AAT.AG.RepairObservationDuality.ResidualDualWitness
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.ResidualDualWitness
