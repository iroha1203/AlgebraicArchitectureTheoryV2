import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Coset.Basic

/-!
# Observation kernels and comparison information

The general group-theoretic core of G-120(A).  A subgroup membership predicate
factors through an observation homomorphism exactly when it contains the
observation kernel.  The same kernel describes the saturated compatible set,
the fibers over compatible points, and the pointed left-coset obstruction.
-/

open scoped Pointwise

namespace AAT.AG.ComparisonInformationLoss

universe u v

variable {Q : Type u} {R : Type v} [Group Q] [Group R]

/-- The part of the observation kernel that is compatible, viewed inside the
kernel itself.  No normality assumption is imposed. -/
def compatibleKernel (O : Q →* R) (Gamma : Subgroup Q) : Subgroup O.ker :=
  Subgroup.comap O.ker.subtype Gamma

@[simp]
theorem mem_compatibleKernel_iff (O : Q →* R) (Gamma : Subgroup Q) (k : O.ker) :
    k ∈ compatibleKernel O Gamma ↔ (k : Q) ∈ Gamma :=
  Iff.rfl

/-- Membership in `Gamma` is determined by the observation precisely when the
observation kernel is contained in `Gamma`. -/
theorem exists_observation_predicate_iff_ker_le (O : Q →* R) (Gamma : Subgroup Q) :
    (∃ h : R → Prop, ∀ q : Q, q ∈ Gamma ↔ h (O q)) ↔ O.ker ≤ Gamma := by
  constructor
  · rintro ⟨h, hh⟩ k hk
    have h_one : h 1 := by simpa using (hh 1).mp Gamma.one_mem
    exact (hh k).mpr (by simpa [MonoidHom.mem_ker.mp hk] using h_one)
  · intro hker
    refine ⟨fun r => ∃ q : Q, q ∈ Gamma ∧ O q = r, fun q => ?_⟩
    constructor
    · intro hq
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q', hq', hobs⟩
      have hk : q'⁻¹ * q ∈ O.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hobs, inv_mul_cancel]
      have hrel : q'⁻¹ * q ∈ Gamma := hker hk
      have : q = q' * (q'⁻¹ * q) := by simp
      rw [this]
      exact Gamma.mul_mem hq' hrel

/-- The saturation of a subgroup by an observation is its join with the
observation kernel. -/
theorem preimage_image_eq_sup_ker (O : Q →* R) (Gamma : Subgroup Q) :
    O ⁻¹' (O '' (Gamma : Set Q)) = (Gamma ⊔ O.ker : Subgroup Q) := by
  ext q
  constructor
  · rintro ⟨g, hg, hOg⟩
    have hk : g⁻¹ * q ∈ O.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hOg, inv_mul_cancel]
    have : q = g * (g⁻¹ * q) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hg hk
  · intro hq
    rw [Subgroup.mul_normal Gamma O.ker] at hq
    rcases hq with ⟨g, hg, k, hk, rfl⟩
    refine ⟨g, hg, ?_⟩
    simp [MonoidHom.mem_ker.mp hk]

/-- Set-theoretically, the saturated compatible set is the product of the
compatible subgroup and the (normal) observation kernel. -/
theorem preimage_image_eq_mul_ker (O : Q →* R) (Gamma : Subgroup Q) :
    O ⁻¹' (O '' (Gamma : Set Q)) = (Gamma : Set Q) * (O.ker : Set Q) := by
  rw [preimage_image_eq_sup_ker, Subgroup.mul_normal]

/-- The observation fiber over `gamma` is its left coset by the kernel. -/
theorem observation_fiber_eq_leftCoset (O : Q →* R) (gamma : Q) :
    O ⁻¹' ({O gamma} : Set R) = gamma • (O.ker : Set Q) := by
  ext q
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_smul_set_iff_inv_smul_mem]
  change O q = O gamma ↔ gamma⁻¹ * q ∈ O.ker
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  constructor
  · intro h
    rw [h, inv_mul_cancel]
  · intro h
    calc
      O q = O gamma * ((O gamma)⁻¹ * O q) := by simp
      _ = O gamma := by rw [h]; simp

/-- Intersecting a compatible observation fiber with `Gamma` leaves the left
coset by the compatible part of the kernel. -/
theorem observation_fiber_inter_eq_leftCoset (O : Q →* R) (Gamma : Subgroup Q)
    {gamma : Q} (hgamma : gamma ∈ Gamma) :
    O ⁻¹' ({O gamma} : Set R) ∩ (Gamma : Set Q) =
      gamma • ((O.ker ⊓ Gamma : Subgroup Q) : Set Q) := by
  ext q
  rw [observation_fiber_eq_leftCoset]
  simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · rintro ⟨hk, hq⟩
    exact ⟨hk, Gamma.mul_mem (Gamma.inv_mem hgamma) hq⟩
  · rintro ⟨hk, hcompat⟩
    refine ⟨hk, ?_⟩
    have : q = gamma * (gamma⁻¹ * q) := by simp
    rw [this]
    exact Gamma.mul_mem hgamma hcompat

/-- Moving within an observation fiber preserves compatibility exactly at the
basepoint coset of the compatible kernel. -/
theorem mul_mem_iff_kernel_coset_basepoint (O : Q →* R) (Gamma : Subgroup Q)
    {gamma : Q} (hgamma : gamma ∈ Gamma) (k : O.ker) :
    gamma * (k : Q) ∈ Gamma ↔
      (QuotientGroup.mk k : O.ker ⧸ compatibleKernel O Gamma) = QuotientGroup.mk 1 := by
  rw [QuotientGroup.eq]
  simpa using (Gamma.mul_mem_cancel_left hgamma)

/-- The pointed left-coset obstruction is a singleton exactly when the
observation kernel is contained in the compatible subgroup. -/
theorem subsingleton_kernel_quotient_iff_ker_le (O : Q →* R) (Gamma : Subgroup Q) :
    Subsingleton (O.ker ⧸ compatibleKernel O Gamma) ↔ O.ker ≤ Gamma := by
  constructor
  · intro h k hk
    letI := h
    have hq : (QuotientGroup.mk (⟨k, hk⟩ : O.ker) :
        O.ker ⧸ compatibleKernel O Gamma) = QuotientGroup.mk 1 := Subsingleton.elim _ _
    rw [QuotientGroup.eq] at hq
    simpa using hq
  · intro hle
    refine ⟨fun x y => ?_⟩
    refine QuotientGroup.induction_on x (fun a => ?_)
    refine QuotientGroup.induction_on y (fun b => ?_)
    apply QuotientGroup.eq.mpr
    exact hle (O.ker.mul_mem (O.ker.inv_mem a.property) b.property)

/-- The pointed obstruction is a singleton exactly when compatible membership
is decidable from the observation alone. -/
theorem subsingleton_kernel_quotient_iff_exists_observation_predicate
    (O : Q →* R) (Gamma : Subgroup Q) :
    Subsingleton (O.ker ⧸ compatibleKernel O Gamma) ↔
      ∃ h : R → Prop, ∀ q : Q, q ∈ Gamma ↔ h (O q) := by
  rw [subsingleton_kernel_quotient_iff_ker_le, exists_observation_predicate_iff_ker_le]

end AAT.AG.ComparisonInformationLoss
