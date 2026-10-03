import ResearchLean.AG.RepairObservationDuality.LinearObservationDuality
import ResearchLean.AG.RepairObservationDuality.FiberSufficiency

/-!
# G-131 D: acquiring the same dual value on a known information fiber

## Implementation notes

The value is a fixed affine linear evaluation. Its factorization is built
from actual observational fibers; an arbitrary selected functional is not
assumed obtainable. Restriction to the unknown kernel removes the known
constant. Choice establishes the factorization criterion; the finite
executable plan replacing choice is a subsequent construction.
-/

namespace AAT.AG.RepairObservationDuality.DualValueAcquisition
variable {k V I J T H W : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [AddCommGroup I] [Module k I]
variable [AddCommGroup T] [Module k T] [AddCommGroup H] [Module k H]
variable [AddCommGroup W] [Module k W]

/-- D's same affine value can be obtained from an observation exactly when equal observed inputs have equal values. -/
theorem acquisition_iff (L : V →ₗ[k] I) (s : I) (O : V →ₗ[k] T)
    (mu : V →ₗ[k] k) (c : k) {w : V} (hw : w ∈ informationFiber L s) :
    (∃ f : T → k, ∀ v ∈ informationFiber L s, f (O v) = c + mu v) ↔
      LinearMap.ker L ⊓ LinearMap.ker O ≤ LinearMap.ker mu := by
  classical
  constructor
  · rintro ⟨f,hf⟩ n hn
    have hwn := add_mem_fiber L s hw hn.1
    have ho : O (w + n) = O w := by rw [map_add, hn.2, add_zero]
    have he : c + mu (w + n) = c + mu w :=
      (hf (w + n) hwn).symm.trans ((congrArg f ho).trans (hf w hw))
    rw [map_add, ← add_assoc] at he
    exact add_left_cancel (he.trans (add_zero (c + mu w)).symm)
  · intro hk
    let has : T → Prop := fun t => ∃ v ∈ informationFiber L s, O v = t
    let chosen : ∀ t, has t → V := fun _ ht => Classical.choose ht
    refine ⟨fun t => if ht : has t then c + mu (chosen t ht) else 0, ?_⟩
    intro v hv
    have ht : has (O v) := ⟨v,hv,rfl⟩
    simp only [dif_pos ht]
    have hp := Classical.choose_spec ht
    have hn : chosen (O v) ht - v ∈ LinearMap.ker L ⊓ LinearMap.ker O :=
      ⟨mem_fiber_sub L s hp.1 hv, by
        change O (chosen (O v) ht - v) = 0
        rw [map_sub, hp.2, sub_self]⟩
    have hzero : mu (chosen (O v) ht - v) = 0 := hk hn
    rw [map_sub] at hzero
    have he : mu (chosen (O v) ht) = mu v := sub_eq_zero.mp hzero
    exact congrArg (fun a => c + a) he

/-- D's information-kernel restriction converts the original intersection condition to a dual annihilator. -/
theorem restriction_iff (L : V →ₗ[k] I) (lam : J → V →ₗ[k] k)
    (points : Finset J) (mu : V →ₗ[k] k) :
    mu.comp (LinearMap.ker L).subtype ∈
      (LinearMap.ker (observation (fun j => (lam j).comp (LinearMap.ker L).subtype) points)).dualAnnihilator ↔
      LinearMap.ker L ⊓ LinearMap.ker (observation lam points) ≤ LinearMap.ker mu := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hz n hn
    let z : LinearMap.ker L := ⟨n,hn.1⟩
    have ho : z ∈ LinearMap.ker
        (observation (fun j => (lam j).comp (LinearMap.ker L).subtype) points) := by
      apply (mem_ker_observation _ points z).mpr
      intro j hj
      exact (mem_ker_observation lam points n).mp hn.2 j hj
    exact hz z ho
  · intro hk z hz
    have ho : (z : V) ∈ LinearMap.ker (observation lam points) := by
      apply (mem_ker_observation lam points (z : V)).mpr
      intro j hj
      exact (mem_ker_observation _ points z).mp hz j hj
    exact hk ⟨z.2,ho⟩

/-- D's value acquisition is precisely membership of the restricted dual in the specified primitive span. -/
theorem acquisition_iff_span [FiniteDimensional k V] (L : V →ₗ[k] I) (s : I)
    (lam : J → V →ₗ[k] k) (points : Finset J) (mu : V →ₗ[k] k) (c : k)
    {w : V} (hw : w ∈ informationFiber L s) :
    (∃ f : (points → k) → k, ∀ v ∈ informationFiber L s,
      f (observation lam points v) = c + mu v) ↔
      mu.comp (LinearMap.ker L).subtype ∈
        LinearObservationDuality.evaluationSpan
          (fun j => (lam j).comp (LinearMap.ker L).subtype) points := by
  rw [acquisition_iff L s _ mu c hw]
  have hr := restriction_iff L lam points mu
  rw [LinearObservationDuality.observation_annihilator] at hr
  exact hr.symm

/-- D's pulled-back residual evaluation is the same affine expression, retaining its known constant. -/
theorem residual_value_affine (D : H →ₗ[k] W) (B : V →ₗ[k] W) (b₀ : W)
    (ell : Module.Dual k (W ⧸ LinearMap.range D)) (v : V) :
    ell ((LinearMap.range D).mkQ (b₀ + B v)) =
      ell ((LinearMap.range D).mkQ b₀) +
        (ell.comp ((LinearMap.range D).mkQ.comp B)) v := by
  rw [map_add, map_add]
  rfl

/-- D's specified residual value is obtainable exactly under its actual restricted pullback-span condition. -/
theorem residual_acquisition_iff [FiniteDimensional k V]
    (D : H →ₗ[k] W) (B : V →ₗ[k] W) (b₀ : W)
    (ell : Module.Dual k (W ⧸ LinearMap.range D))
    (L : V →ₗ[k] I) (s : I) (lam : J → V →ₗ[k] k) (points : Finset J)
    {w : V} (hw : w ∈ informationFiber L s) :
    (∃ f : (points → k) → k, ∀ v ∈ informationFiber L s,
      f (observation lam points v) = ell ((LinearMap.range D).mkQ (b₀ + B v))) ↔
      (ell.comp ((LinearMap.range D).mkQ.comp B)).comp (LinearMap.ker L).subtype ∈
        LinearObservationDuality.evaluationSpan
          (fun j => (lam j).comp (LinearMap.ker L).subtype) points := by
  simp only [residual_value_affine]
  exact acquisition_iff_span L s lam points _ _ hw

end AAT.AG.RepairObservationDuality.DualValueAcquisition
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.DualValueAcquisition
