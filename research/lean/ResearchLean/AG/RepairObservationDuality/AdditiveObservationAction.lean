import ResearchLean.AG.RepairObservationDuality.QueryOptimum
import ResearchLean.AG.MinimalCompatibilityObservations.PointObservation

/-!
# G-131 B: the additive action behind primitive observations

Every point has an original primitive index and a known scalar offset. The
action adds exactly that primitive evaluation. All points, including nonzero
offsets and repeated indices, are admitted by the G-128 model. Passing to a
finite set of indices removes duplicate fixed observations, never run steps.

## Implementation notes

The multiplicative type tag permits direct use of G-128 without altering
the input additive group. Restricting points to offset zero would omit the
arbitrary-point procedure obligation; the action therefore includes every offset.

-/

namespace AAT.AG.RepairObservationDuality.AdditiveObservationAction
open MinimalCompatibilityObservations

variable {k V J : Type*} [Field k] [AddCommGroup V] [Module k V]
variable (lam : J → V →ₗ[k] k)

/-- B's action of the input additive group on every indexed scalar point. -/
def action : MulAction (Multiplicative V) (J × k) where
  smul n p := (p.1, p.2 + lam p.1 n.toAdd)
  one_smul p := by
    change (p.1, p.2 + lam p.1 0) = p
    simp
  mul_smul n m p := by
    change (p.1, p.2 + lam p.1 (n.toAdd + m.toAdd)) =
      (p.1, (p.2 + lam p.1 m.toAdd) + lam p.1 n.toAdd)
    simp only [map_add]
    congr 1
    abel


/-- B's action returns the actual primitive value added to the point's known offset. -/
theorem action_apply (n : V) (j : J) (a : k) :
    letI := action lam;
    (Multiplicative.ofAdd n) • (j, a) = (j, a + lam j n) := rfl

/-- A point is fixed precisely when its original primitive evaluation vanishes. -/
theorem fixed_iff (n : Multiplicative V) (p : J × k) :
    letI := action lam;
    n • p = p ↔ lam p.1 n.toAdd = 0 := by
  letI := action lam
  change (p.1, p.2 + lam p.1 n.toAdd) = p ↔ _
  rcases p with ⟨j, a⟩
  simp

/-- B's compatible subgroup is the same repair kernel, with only the group notation changed. -/
def compatible (R : Submodule k V) : Subgroup (Multiplicative V) :=
  R.toAddSubgroup.toSubgroup

/-- Compatibility uses the original vector membership with no additional condition. -/
theorem mem_compatible (R : Submodule k V) (n : Multiplicative V) :
    n ∈ compatible R ↔ n.toAdd ∈ R := Iff.rfl

variable [DecidableEq J]

/-- B's fixed observation set retains each distinct original index. -/
def indices (points : Finset (J × k)) : Finset J := points.image Prod.fst

/-- G-128's exact point stabilizer is the kernel of the same original-index table. -/
theorem stabilizer_iff (points : Finset (J × k)) (n : Multiplicative V) :
    letI := action lam;
    n ∈ pointStabilizer points ↔
      n.toAdd ∈ LinearMap.ker (observation lam (indices points)) := by
  letI := action lam
  rw [mem_pointStabilizer_iff, mem_ker_observation]
  constructor
  · intro hn j hj
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hj
    subst j
    exact (fixed_iff lam n p).mp (hn p hp)
  · intro hn p hp
    exact (fixed_iff lam n p).mpr (hn p.1 (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

/-- G-128 sufficient points and primitive kernel inclusion are the same condition. -/
theorem sufficient_iff (R : Submodule k V) (points : Finset (J × k)) :
    letI := action lam;
    Sufficient (compatible R) points ↔
      LinearMap.ker (observation lam (indices points)) ≤ R := by
  letI := action lam
  constructor
  · intro hs n hn
    exact hs ((stabilizer_iff lam points (Multiplicative.ofAdd n)).mpr hn)
  · intro hs n hn
    exact hs ((stabilizer_iff lam points n).mp hn)

/-- G-128's observation predicate is the same primitive kernel predicate on arbitrary offsets. -/
theorem predicate_iff (R : Submodule k V) (points : Finset (J × k)) :
    letI := action lam;
    (∃ p : (points → J × k) → Prop,
      ∀ n : Multiplicative V, p (observe points n) ↔ n.toAdd ∈ R) ↔
      LinearMap.ker (observation lam (indices points)) ≤ R := by
  letI := action lam
  exact (exists_predicate_iff_sufficient (compatible R) points).trans
    (sufficient_iff lam R points)

omit [DecidableEq J] in
/-- Reading a G-128 response and subtracting the known offset recovers the primitive value. -/
theorem observe_decode (points : Finset (J × k)) (n : Multiplicative V) (p : points) :
    letI := action lam;
    (observe points n p).2 - p.1.2 = lam p.1.1 n.toAdd := by
  letI := action lam
  change p.1.2 + lam p.1.1 n.toAdd - p.1.2 = _
  abel

/-- B's canonical point plan chooses offset zero for each original primitive index. -/
def zeroPoints (points : Finset J) : Finset (J × k) :=
  points.map ⟨fun j => (j, 0), fun _ _ he => congrArg Prod.fst he⟩

/-- The zero-offset plan retains exactly its original indices. -/
theorem indices_zeroPoints (points : Finset J) : indices (zeroPoints (k := k) points) = points := by
  ext j
  simp [indices, zeroPoints]

omit [DecidableEq J] in
/-- Every primitive in the zero-offset plan is one point, preserving its exact finite cost. -/
theorem card_zeroPoints (points : Finset J) : (zeroPoints (k := k) points).card = points.card :=
  Finset.card_map _

omit [Field k] in
/-- Multiple fixed points with the same index cannot improve the number of distinct primitives. -/
theorem card_indices_le (points : Finset (J × k)) : (indices points).card ≤ points.card :=
  Finset.card_image_le

/-- B's G-128 minimum equals the primitive minimum on the full input space, including infinity. -/
theorem minimum_eq (R : Submodule k V) :
    letI := action lam;
    minObservations (X := J × k) (compatible R) =
      minimum lam (0 : V →ₗ[k] k) R := by
  letI := action lam
  apply le_antisymm
  · change _ ≤ ⨅ p : {p : Finset J // SufficientSet lam (0 : V →ₗ[k] k) R p}, _
    apply le_iInf
    intro p
    have hp : LinearMap.ker (observation lam p.1) ≤ R := by
      simpa only [sufficientSet_zero_iff] using p.2
    have hs := (sufficient_iff lam R (zeroPoints p.1)).mpr (by
      rw [indices_zeroPoints]; exact hp)
    simpa only [card_zeroPoints] using minObservations_le (compatible R) (zeroPoints p.1) hs
  · change _ ≤ ⨅ p : {p : Finset (J × k) // Sufficient (compatible R) p}, _
    apply le_iInf
    intro p
    have hp : SufficientSet lam (0 : V →ₗ[k] k) R (indices p.1) := by
      simpa only [sufficientSet_zero_iff] using
        (sufficient_iff lam R p.1).mp p.2
    exact (minimum_le_card lam (0 : V →ₗ[k] k) R (indices p.1) hp).trans
      (by exact_mod_cast card_indices_le p.1)

end AAT.AG.RepairObservationDuality.AdditiveObservationAction
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.AdditiveObservationAction
