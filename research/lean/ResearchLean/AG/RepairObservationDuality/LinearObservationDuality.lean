import ResearchLean.AG.RepairObservationDuality.QueryOptimum
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# G-131 B: the dual of the same primitive observation

The observation is Cycle 2's table on the original indices. Its annihilator
is computed from the span of those evaluations, rather than supplied as data.
The quotient dual and the residual image retain their original representatives.
Finite dimensionality is used only for the double annihilator in the dual.

## Implementation notes

A supplied dual basis would hide the span obligation. Computing the span
and using the canonical quotient maps keeps the original representatives.

-/

namespace AAT.AG.RepairObservationDuality.LinearObservationDuality

variable {k V T W J : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [AddCommGroup T] [Module k T]
variable [AddCommGroup W] [Module k W]

/-- B's observation predicate factors kernel membership exactly under kernel inclusion. -/
theorem predicate_iff (O : V →ₗ[k] T) (R : Submodule k V) :
    (∃ p : T → Prop, ∀ n, p (O n) ↔ n ∈ R) ↔ LinearMap.ker O ≤ R := by
  constructor
  · rintro ⟨p, hp⟩ n hn
    have hzero := (hp 0).mpr R.zero_mem
    rw [map_zero] at hzero
    exact (hp n).mp (hn ▸ hzero)
  · intro hk
    refine ⟨fun t => ∃ r ∈ R, O r = t, ?_⟩
    intro n
    constructor
    · rintro ⟨r, hr, he⟩
      have hd : n - r ∈ LinearMap.ker O := by
        change O (n - r) = 0
        rw [map_sub, he, sub_self]
      have hn := R.add_mem (hk hd) hr
      simpa only [sub_add_cancel] using hn
    · intro hn
      exact ⟨n, hn, rfl⟩

/-- B's factorization can return an actual Boolean indicator of the same repair kernel. -/
theorem decision_iff (O : V →ₗ[k] T) (R : Submodule k V) :
    (∃ f : T → Bool, ∀ n, f (O n) = true ↔ n ∈ R) ↔ LinearMap.ker O ≤ R := by
  classical
  constructor
  · rintro ⟨f,hf⟩
    exact (predicate_iff O R).mp ⟨fun t => f t = true,hf⟩
  · intro hk
    obtain ⟨p,hp⟩ := (predicate_iff O R).mpr hk
    refine ⟨fun t => decide (p t), ?_⟩
    intro n
    simpa only [decide_eq_true_eq] using hp n

/-- B's span contains precisely the original evaluations indexed by the chosen set. -/
def evaluationSpan (lam : J → V →ₗ[k] k) (points : Finset J) :
    Submodule k (Module.Dual k V) :=
  Submodule.span k (Set.range fun j : points => lam j.1)

/-- The span's common zero space is the kernel of the identical primitive table. -/
theorem span_coannihilator (lam : J → V →ₗ[k] k) (points : Finset J) :
    (evaluationSpan lam points).dualCoannihilator =
      LinearMap.ker (observation lam points) := by
  ext n
  change n ∈ (Submodule.span k (Set.range fun j : points => lam j.1)).dualCoannihilator ↔ _
  rw [← SetLike.mem_coe, Submodule.coe_dualCoannihilator_span]
  change (∀ f ∈ Set.range (fun j : points => lam j.1), f n = 0) ↔ _
  rw [mem_ker_observation]
  constructor
  · intro hz j hj
    exact hz (lam j) ⟨⟨j, hj⟩, rfl⟩
  · rintro hz f ⟨j, rfl⟩
    exact hz j.1 j.2

/-- B's observation annihilator is the primitive evaluation span; no span premise is supplied. -/
theorem observation_annihilator [FiniteDimensional k V]
    (lam : J → V →ₗ[k] k) (points : Finset J) :
    (LinearMap.ker (observation lam points)).dualAnnihilator =
      evaluationSpan lam points := by
  rw [← span_coannihilator]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq

/-- B's kernel sufficient-set condition and its stated dual condition are equivalent. -/
theorem kernel_iff_dual [FiniteDimensional k V] (lam : J → V →ₗ[k] k)
    (points : Finset J) (R : Submodule k V) :
    LinearMap.ker (observation lam points) ≤ R ↔
      R.dualAnnihilator ≤ evaluationSpan lam points := by
  rw [← observation_annihilator]
  exact Subspace.dualAnnihilator_le_dualAnnihilator_iff.symm

/-- B's observation predicate, kernel inclusion, and evaluation span have the same strength. -/
theorem predicate_iff_dual [FiniteDimensional k V] (lam : J → V →ₗ[k] k)
    (points : Finset J) (R : Submodule k V) :
    (∃ p : (points → k) → Prop, ∀ n, p (observation lam points n) ↔ n ∈ R) ↔
      R.dualAnnihilator ≤ evaluationSpan lam points := by
  rw [predicate_iff, kernel_iff_dual]

/-- B's quotient dual is canonically the annihilator of the same repair kernel. -/
noncomputable def quotientDual (R : Submodule k V) :
    Module.Dual k (V ⧸ R) ≃ₗ[k] R.dualAnnihilator :=
  Submodule.dualQuotEquivDualAnnihilator R

/-- The canonical quotient-dual map preserves evaluation on every original representative. -/
theorem quotientDual_apply (R : Submodule k V) (f : Module.Dual k (V ⧸ R)) (n : V) :
    (quotientDual R f).1 n = f (R.mkQ n) := rfl

/-- The inverse quotient-dual map preserves the same representative evaluation. -/
theorem quotientDual_symm_apply (R : Submodule k V) (f : R.dualAnnihilator) (n : V) :
    (quotientDual R).symm f (R.mkQ n) = f.1 n :=
  Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk R f n

/-- B's effective input quotient is the image of the very same residual obstruction map. -/
noncomputable def quotientImage (Q : V →ₗ[k] W) :
    (V ⧸ LinearMap.ker Q) ≃ₗ[k] LinearMap.range Q := Q.quotKerEquivRange

/-- The residual image inclusion maps each quotient representative to its original obstruction. -/
theorem quotientImage_apply (Q : V →ₗ[k] W) (n : V) :
    (quotientImage Q ((LinearMap.ker Q).mkQ n)).1 = Q n :=
  Q.quotKerEquivRange_apply_mk n

/-- The inverse residual-image map recovers the same input quotient representative. -/
theorem quotientImage_symm_apply (Q : V →ₗ[k] W) (n : V) :
    (quotientImage Q).symm ⟨Q n, LinearMap.mem_range_self Q n⟩ =
      (LinearMap.ker Q).mkQ n :=
  Q.quotKerEquivRange_symm_apply_image n (LinearMap.mem_range_self Q n)

end AAT.AG.RepairObservationDuality.LinearObservationDuality
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.LinearObservationDuality
