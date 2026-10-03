import ResearchLean.AG.RepairObservationDuality.DualValueAcquisition

/-!
# G-131 D: retained and notified values in the updated information fiber

## Implementation notes

The first map records values still known after the update. The second map
records the newly notified values. Their product defines the exact new
fiber and unknown kernel. Including stale, unreceived values as rows would
change the information available to the next query plan.
-/

namespace AAT.AG.RepairObservationDuality.KnownValueUpdates
variable {k V I T J : Type*} [Field k]
variable [AddCommGroup V] [Module k V] [AddCommGroup I] [Module k I]
variable [AddCommGroup T] [Module k T]

/-- D's update keeps the retained information and the received notification as separate components. -/
def information (retained : V →ₗ[k] I) (notified : V →ₗ[k] T) : V →ₗ[k] I × T :=
  retained.prod notified

/-- Updated information reads exactly the two specified values. -/
theorem information_apply (retained : V →ₗ[k] I) (notified : V →ₗ[k] T) (v : V) :
    information retained notified v = (retained v, notified v) := rfl

/-- D's unknown directions are precisely the directions invisible to both retained and notified values. -/
theorem information_ker (retained : V →ₗ[k] I) (notified : V →ₗ[k] T) :
    LinearMap.ker (information retained notified) = LinearMap.ker retained ⊓ LinearMap.ker notified := by
  ext n
  change (retained n, notified n) = (0,0) ↔ retained n = 0 ∧ notified n = 0
  simp only [Prod.mk.injEq]

/-- The updated fiber contains every input satisfying the exact retained and notified values. -/
theorem fiber_iff (retained : V →ₗ[k] I) (notified : V →ₗ[k] T) (s : I) (t : T) (v : V) :
    v ∈ informationFiber (information retained notified) (s,t) ↔
      retained v = s ∧ notified v = t := by
  rw [mem_informationFiber, information_apply]
  simp only [Prod.mk.injEq]

/-- D's same affine dual value uses the new unknown directions after retained values and actual notifications. -/
theorem acquisition_after_update_iff [FiniteDimensional k V]
    (retained : V →ₗ[k] I) (notified : V →ₗ[k] T) (s : I) (t : T)
    (lam : J → V →ₗ[k] k) (points : Finset J) (mu : V →ₗ[k] k) (c : k)
    {w : V} (hw : retained w = s) (hn : notified w = t) :
    (∃ f : (points → k) → k, ∀ v,
      retained v = s → notified v = t → f (observation lam points v) = c + mu v) ↔
      mu.comp (LinearMap.ker (information retained notified)).subtype ∈
        LinearObservationDuality.evaluationSpan
          (fun j => (lam j).comp (LinearMap.ker (information retained notified)).subtype) points := by
  have he := DualValueAcquisition.acquisition_iff_span (information retained notified) (s,t)
    lam points mu c ((fiber_iff retained notified s t w).mpr ⟨hw,hn⟩)
  simpa only [fiber_iff, and_imp] using he

end AAT.AG.RepairObservationDuality.KnownValueUpdates
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.KnownValueUpdates
