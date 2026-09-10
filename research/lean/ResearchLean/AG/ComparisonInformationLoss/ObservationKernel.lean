import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Coset.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Observation kernels and comparison information

The general group-theoretic core of G-120(A).  A subgroup membership predicate
factors through an observation homomorphism exactly when it contains the
observation kernel.  The same kernel describes the saturated compatible set,
the fibers over compatible points, and the pointed left-coset obstruction.

Implementation notes: `compatibleKernel` is a subgroup of `O.ker`, rather
than the ambient intersection `O.ker ⊓ Gamma` in `Q`, because G-120(A) asks
for the left-coset type `K/L` with `K` as its ambient group.  The ambient
intersection remains the convenient set-level presentation for compatible
fibers.  A quotient group was rejected because G-120(A) does not assume that
`L` is normal in `K`.
-/

open scoped Pointwise

namespace AAT.AG.ComparisonInformationLoss

universe u v

variable {Q : Type u} {R : Type v} [Group Q] [Group R]

/-- G-120(A)'s data definition of `L = K ∩ Gamma`, represented as a subgroup
of `K = O.ker` so that its general left-coset type can be formed.  The inputs
are precisely the arbitrary observation homomorphism and compatible subgroup
from the fixed target; no normality assumption is imposed. -/
def compatibleKernel (O : Q →* R) (Gamma : Subgroup Q) : Subgroup O.ker :=
  Subgroup.comap O.ker.subtype Gamma

/-- API normalization for G-120(A)'s compatible kernel: membership in the
subgroup of `O.ker` simplifies to membership of the underlying element in
`Gamma`.  The `@[simp]` direction hides the `comap` representation downstream. -/
@[simp]
theorem mem_compatibleKernel_iff (O : Q →* R) (Gamma : Subgroup Q) (k : O.ker) :
    k ∈ compatibleKernel O Gamma ↔ (k : Q) ∈ Gamma :=
  Iff.rfl

/-- G-120(A)'s first main criterion: for arbitrary groups, observation
homomorphism, and compatible subgroup, membership is determined by some
predicate on observations precisely when the observation kernel is contained
in the subgroup.  No surjectivity premise is added. -/
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

/-- G-120(A)'s saturation formula in subgroup form.  For the fixed arbitrary
`O` and `Gamma`, the preimage of the observed image is the join with `O.ker`;
this API lemma supplies the subgroup whose carrier is the required set product. -/
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

/-- G-120(A)'s set-level saturation formula.  It exposes the requested order
`Gamma * ker(O)` and derives its subgroup presentation from the automatic
normality of the homomorphism kernel. -/
theorem preimage_image_eq_mul_ker (O : Q →* R) (Gamma : Subgroup Q) :
    O ⁻¹' (O '' (Gamma : Set Q)) = (Gamma : Set Q) * (O.ker : Set Q) := by
  rw [preimage_image_eq_sup_ker, Subgroup.mul_normal]

/-- G-120(A)'s observation-fiber theorem for an arbitrary `gamma`: equality
of observed values is exactly membership in the left coset `gamma * ker(O)`.
It is the fiber API used by the compatible-fiber result below. -/
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

/-- G-120(A)'s compatible-fiber theorem.  The fixed-target premise
`hgamma : gamma ∈ Gamma` is used to identify the intersection of the
observation fiber with `Gamma` as the left coset by `ker(O) ∩ Gamma`. -/
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

/-- G-120(A)'s basepoint criterion.  For the fixed-target inputs
`hgamma : gamma ∈ Gamma` and `k : ker(O)`, the change `gamma * k` remains
compatible exactly when the left-coset class of `k` is the basepoint class. -/
theorem mul_mem_iff_kernel_coset_basepoint (O : Q →* R) (Gamma : Subgroup Q)
    {gamma : Q} (hgamma : gamma ∈ Gamma) (k : O.ker) :
    gamma * (k : Q) ∈ Gamma ↔
      (QuotientGroup.mk k : O.ker ⧸ compatibleKernel O Gamma) = QuotientGroup.mk 1 := by
  rw [QuotientGroup.eq]
  simpa using (Gamma.mul_mem_cancel_left hgamma)

/-- G-120(A)'s first singleton criterion for the pointed left-coset set
`ker(O) / compatibleKernel O Gamma`.  Its arbitrary group/homomorphism/subgroup
inputs are those of the fixed target, and it requires no normality of the
denominator subgroup. -/
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

/-- G-120(A)'s final Cycle 1 equivalence: the pointed obstruction is a
singleton exactly when compatible membership is determined by a predicate on
the observation alone.  This is a propositional factorization statement, not
a computational decidability claim. -/
theorem subsingleton_kernel_quotient_iff_exists_observation_predicate
    (O : Q →* R) (Gamma : Subgroup Q) :
    Subsingleton (O.ker ⧸ compatibleKernel O Gamma) ↔
      ∃ h : R → Prop, ∀ q : Q, q ∈ Gamma ↔ h (O q) := by
  rw [subsingleton_kernel_quotient_iff_ker_le, exists_observation_predicate_iff_ker_le]

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss

end AAT.AG.ComparisonInformationLoss
