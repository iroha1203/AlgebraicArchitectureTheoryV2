import ResearchLean.AG.RelativeRepairComposition.W1ActualRepairs
import Mathlib.Tactic.LinearCombination

/-!
# W1 permission classification from both original authored Laws

## Implementation notes

The coordinate types below are consequences of the independent actual repair
equivalence. They retain the whole private h and the same two original candidate
names for every S. Characteristic three changes the transported negative b
coefficient to the common obstruction column. The identity-linear comparison
retains the same geometry and masks, but its two a occurrences contribute 2h.
-/
namespace AAT.AG.RelativeRepairComposition.W1PermissionClassification
open TransportCoherence AbelianLiftingObstruction
open W1AffineInput W1AuthoredOperations W1Regions W1ActualRepairs

/-- In the specified field, the negative transported b correction contributes the same quotient column as c. -/
theorem negative_equations_iff (x y : ZMod 3) (p : Parameters) :
    Equations true x y p ↔ p.u = x - p.z ∧ p.z + p.v = y - x := by
  constructor
  · intro he
    have hsecond := he.2
    change p.u - p.z + p.v = y at hsecond
    have hthree : (3 : ZMod 3) * p.z = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul]
    constructor
    · linear_combination he.1
    · linear_combination hsecond - he.1 + hthree
  · rintro ⟨hu, hv⟩
    constructor
    · linear_combination hu
    · change p.u - p.z + p.v = y
      have hthree : (3 : ZMod 3) * p.z = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_mul]
      linear_combination hu + hv - hthree

/-- Identity holonomy changes only the derived a column and makes the always-only correction possible. -/
theorem identity_equations_iff (x y : ZMod 3) (p : Parameters) :
    Equations false x y p ↔ p.u = x - p.z ∧ 2 * p.h + p.v = y - x := by
  constructor
  · intro he
    have hsecond := he.2
    change p.u + 2 * p.h + p.z + p.v = y at hsecond
    constructor
    · linear_combination he.1
    · linear_combination hsecond - he.1
  · rintro ⟨hu, hv⟩
    constructor
    · linear_combination hu
    · change p.u + 2 * p.h + p.z + p.v = y
      linear_combination hu + hv

/-- All negative-holonomy repairs retain arbitrary h,z, restricted only by the original two forbidden-candidate masks. -/
def NegativeChoices (S : Set (EdgeName (K := geometry))) (d : ZMod 3) :=
  {q : (ZMod 3) × (ZMod 3) //
    (name edgeB ∉ S → q.2 = 0) ∧ (name edgeC ∉ S → d - q.2 = 0)}

/-- The two derived Laws reconstruct u and v while preserving the entire h,z parameter set. -/
noncomputable def negativeParametersEquiv (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    {p : Parameters // Equations true x y p ∧ Allowed S p} ≃ NegativeChoices S (y - x) where
  toFun p := ⟨(p.1.h, p.1.z), p.2.2.1, fun hc => by
    have hv := (negative_equations_iff x y p.1).mp p.2.1
    have hz := p.2.2.2 hc
    linear_combination hz - hv.2⟩
  invFun q := ⟨⟨x - q.1.2, q.1.1, q.1.2, y - x - q.1.2⟩,
    (negative_equations_iff x y _).mpr ⟨rfl, by ring⟩, q.2⟩
  left_inv p := by
    apply Subtype.ext
    have hp := (negative_equations_iff x y p.1).mp p.2.1
    rcases p with ⟨⟨u, h, z, v⟩, he, ha⟩
    change Parameters.mk (x - z) h z (y - x - z) = Parameters.mk u h z v
    have hu : x - z = u := hp.1.symm
    have hv : y - x - z = v := by linear_combination -hp.2
    rw [hu, hv]
  right_inv q := Subtype.ext rfl

/-- Full independent actual repairs are exactly the unrestricted private h and derived allowed candidate choice, for every S and every x,y. -/
noncomputable def negativeActualEquiv (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    RealRepairs true x y S ≃ NegativeChoices S (y - x) :=
  (actualParametersEquiv true x y S).trans (negativeParametersEquiv x y S)

/-- The native full-kernel original repair family has the same full negative-holonomy classification. -/
noncomputable def negativeNativeEquiv (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    SupportedRepair (originalTower true x y) (fixedEdges S) ≃ NegativeChoices S (y - x) :=
  (nativeParametersEquiv true x y S).trans (negativeParametersEquiv x y S)

/-- The empty permission set forces both original candidate values to zero and succeeds exactly at zero obstruction. -/
theorem negative_empty_exists_iff (x y : ZMod 3) :
    Nonempty (RealRepairs true x y ∅) ↔ y - x = 0 := by
  rw [Equiv.nonempty_congr (negativeActualEquiv x y ∅)]
  constructor
  · rintro ⟨⟨⟨h, z⟩, hb, hc⟩⟩
    have hz := hb (by simp)
    have hv := hc (by simp)
    change z = 0 at hz
    change y - x - z = 0 at hv
    simpa only [hz, sub_zero] using hv
  · intro hd
    exact ⟨⟨(0, 0), by simp [hd]⟩⟩

/-- Every d has an actual repair when only the original b is permitted. -/
theorem negative_b_exists (x y : ZMod 3) :
    Nonempty (RealRepairs true x y {name edgeB}) := by
  apply (negativeActualEquiv x y _).symm.nonempty_congr.mp
  exact ⟨⟨(0, y - x), by simp [name, edgeB, edgeC, geometry]⟩⟩

/-- Every d has an actual repair when only the original c is permitted. -/
theorem negative_c_exists (x y : ZMod 3) :
    Nonempty (RealRepairs true x y {name edgeC}) := by
  apply (negativeActualEquiv x y _).symm.nonempty_congr.mp
  exact ⟨⟨(0, 0), by simp [name, edgeB, edgeC, geometry]⟩⟩

/-- Allowing both original candidates retains every pair of private h and candidate b correction z. -/
noncomputable def negativeFullEquiv (x y : ZMod 3) :
    RealRepairs true x y candidates ≃ (ZMod 3) × (ZMod 3) :=
  (negativeActualEquiv x y candidates).trans {
    toFun := Subtype.val
    invFun q := ⟨q, by simp [candidates]⟩
    left_inv _ := rfl
    right_inv _ := rfl }

/-- The same original geometry with identity a always admits an actual repair with no candidate correction. -/
theorem identity_empty_exists (x y : ZMod 3) :
    Nonempty (RealRepairs false x y ∅) := by
  have he : Equations false x y ⟨x, 2 * (y - x), 0, 0⟩ :=
    (identity_equations_iff x y _).mpr ⟨by simp, by
      change 2 * (2 * (y - x)) + 0 = y - x
      rw [← mul_assoc, show (2 : ZMod 3) * 2 = 1 by decide, one_mul, add_zero]⟩
  exact ⟨actualRepair false x y ∅ _ he (by simp [Allowed])⟩

/-- A concrete zero-obstruction instance satisfies both derived equations and the empty mask. -/
theorem zero_instance : Equations true 0 0 ⟨0, 0, 0, 0⟩ ∧ Allowed ∅ ⟨0, 0, 0, 0⟩ := by
  simp [Equations, Allowed]

/-- The same no-candidate parameters fail the original second Law at the specified nonzero update. -/
theorem nonzero_equations_fail : ¬ Equations true 0 1 ⟨0, 0, 0, 0⟩ := by
  simp [Equations]

/-- A nonzero correction of forbidden original b fails its literal permission mask. -/
theorem forbidden_b_fail : ¬ Allowed ∅ ⟨0, 0, 1, 0⟩ := by
  simp [Allowed]

end AAT.AG.RelativeRepairComposition.W1PermissionClassification
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1PermissionClassification
