import ResearchLean.AG.RelativeRepairComposition.W1PermissionClassification
import ResearchLean.AG.RelativeRepairComposition.W1NativeLabels

/-!
# W1 identity-holonomy comparison on the unchanged input

## Implementation notes

Only the original linear component of a changes. Both authored a occurrences,
all six original names, the full affine groups and the same masks remain.
The private h contributes 2h and eliminates the empty-range obstruction.
The complete actual repairs, rather than a selected family, are counted.
-/
namespace AAT.AG.RelativeRepairComposition.W1IdentityClassification
open CategoryTheory TransportCoherence AbelianLiftingObstruction
open W1AffineInput W1Regions W1ActualRepairs W1PermissionClassification W1NativeLabels

/-- Multiplication by two is its own inverse in the specified whole F3 kernel. -/
theorem twice_twice (a : ZMod 3) : 2 * (2 * a) = a := by
  rw [← mul_assoc, show (2 : ZMod 3) * 2 = 1 by decide, one_mul]

/-- The forbidden-c equation fixes the entire private correction to 2d, rather than restricting its kernel in advance. -/
theorem twice_eq_iff (h d : ZMod 3) : 2 * h = d ↔ h = 2 * d := by
  constructor
  · intro he
    have hh := congrArg (fun a : ZMod 3 => 2 * a) he
    simpa only [twice_twice] using hh
  · intro he
    rw [he, twice_twice]

/-- All identity-linear corrections retain full h,z subject only to the original candidate masks. -/
def IdentityChoices (S : Set (EdgeName (K := geometry))) (d : ZMod 3) :=
  {q : (ZMod 3) × (ZMod 3) //
    (name edgeB ∉ S → q.2 = 0) ∧ (name edgeC ∉ S → d - 2 * q.1 = 0)}

/-- The unchanged authored words recover u and v from the full identity-linear h,z choices in both directions. -/
noncomputable def identityParametersEquiv (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    {p : Parameters // Equations false x y p ∧ Allowed S p} ≃ IdentityChoices S (y - x) where
  toFun p := ⟨(p.1.h, p.1.z), p.2.2.1, fun hc => by
    have hv := (identity_equations_iff x y p.1).mp p.2.1
    have hz := p.2.2.2 hc
    linear_combination hz - hv.2⟩
  invFun q := ⟨⟨x - q.1.2, q.1.1, q.1.2, y - x - 2 * q.1.1⟩,
    (identity_equations_iff x y _).mpr ⟨rfl, by ring⟩, q.2⟩
  left_inv p := by
    apply Subtype.ext
    have hp := (identity_equations_iff x y p.1).mp p.2.1
    rcases p with ⟨⟨u, h, z, v⟩, he, ha⟩
    change Parameters.mk (x - z) h z (y - x - 2 * h) = Parameters.mk u h z v
    have hu : x - z = u := hp.1.symm
    have hv : y - x - 2 * h = v := by linear_combination -hp.2
    rw [hu, hv]
  right_inv _ := Subtype.ext rfl

/-- The whole independent actual identity-linear repair set corresponds to all h,z choices with the same original masks. -/
noncomputable def identityActualEquiv (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    RealRepairs false x y S ≃ IdentityChoices S (y - x) :=
  (actualParametersEquiv false x y S).trans (identityParametersEquiv x y S)

/-- With no candidates, the same identity-linear input has one entire actual repair, with h=2d and z=v=0. -/
noncomputable def identityEmptyChoiceEquiv (d : ZMod 3) : IdentityChoices ∅ d ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(2 * d, 0), by simp [twice_twice]⟩
  left_inv q := by
    apply Subtype.ext
    have hz := q.2.1 (by simp)
    have hh := q.2.2 (by simp)
    exact Prod.ext ((twice_eq_iff q.1.1 d).mp (sub_eq_zero.mp hh).symm).symm hz.symm
  right_inv q := by cases q; rfl

/-- Allowing only b leaves every candidate z and forces the whole private h=2d. -/
noncomputable def identityBChoiceEquiv (d : ZMod 3) :
    IdentityChoices {name edgeB} d ≃ ZMod 3 where
  toFun q := q.1.2
  invFun z := ⟨(2 * d, z), by simp [twice_twice, geometry, name, edgeB, edgeC]⟩
  left_inv q := by
    apply Subtype.ext
    have hh := q.2.2 (by simp [geometry, name, edgeB, edgeC])
    exact Prod.ext ((twice_eq_iff q.1.1 d).mp (sub_eq_zero.mp hh).symm).symm rfl
  right_inv _ := rfl

/-- Allowing only c leaves the whole private h and forces the original b correction to zero. -/
noncomputable def identityCChoiceEquiv (d : ZMod 3) :
    IdentityChoices {name edgeC} d ≃ ZMod 3 where
  toFun q := q.1.1
  invFun h := ⟨(h, 0), by simp [geometry, name, edgeB, edgeC]⟩
  left_inv q := by
    apply Subtype.ext
    exact Prod.ext rfl (q.2.1 (by simp [geometry, name, edgeB, edgeC])).symm
  right_inv _ := rfl

/-- Both original candidate names permit every full h,z pair on the same identity-linear input. -/
noncomputable def identityFullChoiceEquiv (d : ZMod 3) :
    IdentityChoices candidates d ≃ (ZMod 3) × (ZMod 3) where
  toFun := Subtype.val
  invFun q := ⟨q, by simp [candidates]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full actual empty-range repair count is one for every original x,y. -/
theorem identity_empty_card (x y : ZMod 3) : Nat.card (RealRepairs false x y ∅) = 1 := by
  rw [Nat.card_congr ((identityActualEquiv x y ∅).trans (identityEmptyChoiceEquiv (y - x)))]
  exact Nat.card_unique

/-- The full actual b-only repair count is three on the unchanged original permissions. -/
theorem identity_b_card (x y : ZMod 3) : Nat.card (RealRepairs false x y {name edgeB}) = 3 := by
  rw [Nat.card_congr ((identityActualEquiv x y _).trans (identityBChoiceEquiv (y - x))),
    Nat.card_eq_fintype_card, ZMod.card]

/-- The full actual c-only repair count is three on the unchanged original permissions. -/
theorem identity_c_card (x y : ZMod 3) : Nat.card (RealRepairs false x y {name edgeC}) = 3 := by
  rw [Nat.card_congr ((identityActualEquiv x y _).trans (identityCChoiceEquiv (y - x))),
    Nat.card_eq_fintype_card, ZMod.card]

/-- The full actual both-candidate repair count is nine, keeping every private h. -/
theorem identity_full_card (x y : ZMod 3) : Nat.card (RealRepairs false x y candidates) = 9 := by
  rw [Nat.card_congr ((identityActualEquiv x y candidates).trans (identityFullChoiceEquiv (y - x))),
    Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

/-- The entire native identity-linear isomorphism classes have the specified four counts, and all their automorphisms are identities. -/
theorem identity_class_counts (x y : ZMod 3) :
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory false x y ∅))) = 1 ∧
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory false x y {name edgeB}))) = 3 ∧
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory false x y {name edgeC}))) = 3 ∧
    Nat.card (Quotient (isIsomorphicSetoid (NativeCategory false x y candidates))) = 9 := by
  simp only [class_card_eq_actual_card, identity_empty_card, identity_b_card, identity_c_card,
    identity_full_card, and_self]

end AAT.AG.RelativeRepairComposition.W1IdentityClassification
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1IdentityClassification
