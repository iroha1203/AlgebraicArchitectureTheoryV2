import Formal.SHIGURE.Part1.CoordinateRings
import Formal.SHIGURE.Part2.CopyingCoalgebra

/-!
# Coefficient charts of support profiles

Definition 4.5 and the point calculation underlying Theorem 4.6.

## Implementation notes

The profile assigns a finite set of allowed outputs to each source.
A chart uses the existing `PolynomialPresentation` for idempotence,
orthogonality and the row sum. Extending the coordinates by zero gives the
comparison with the finite rows of Theorem 4.3.

A dedicated quotient would repeat the existing universal assignment
equivalence. The named Law families let that equivalence handle the quotient
while recording which equations impose idempotence, orthogonality and the sum.
-/

open MvPolynomial
open scoped BigOperators

noncomputable section

namespace SHIGURE.Copying

universe u

/-- The finite set of allowed output states for each input in Definition 4.5. -/
abbrev SupportProfile (X Y : Type u) := X → Finset Y

namespace SupportProfile

variable {X Y : Type u} (F : SupportProfile X Y)

/-- The variables of the chart in Definition 4.5. -/
abbrev Coordinate := (x : X) × (F x : Type u)

/-- The three families of equations of the profile chart in Definition 4.5.
The sum of an empty row is the empty sum. -/
inductive ChartLaw where
  | idempotent (v : F.Coordinate)
  | orthogonal (x : X) (y z : F x) (hne : y ≠ z)
  | complete (x : X)

variable (k : Type u) [CommRing k]

/-- The coordinates and equations of the affine chart of Definition 4.5. -/
def presentation : PolynomialPresentation.{u, u} k where
  Variable := F.Coordinate
  Law := F.ChartLaw
  left
    | .idempotent v => MvPolynomial.X v * MvPolynomial.X v
    | .orthogonal x y z _ => MvPolynomial.X ⟨x, y⟩ * MvPolynomial.X ⟨x, z⟩
    | .complete x => ∑ y : F x, MvPolynomial.X ⟨x, y⟩
  right
    | .idempotent v => MvPolynomial.X v
    | .orthogonal _ _ _ _ => 0
    | .complete _ => 1

variable {k} {R : Type u} [CommRing R] [Algebra k R]

/-- A row family has profile `F` if every coefficient outside its prescribed finite set is zero. -/
abbrev RowsAt (R : Type u) [CommRing R] :=
  {a : CopyRows R X Y // ∀ x, (a.val x).support ⊆ F x}

/-- The coefficient row formed by adding zeros to chart coordinates outside the profile. -/
def rowOfValues (v : F.Coordinate → R) (x : X) : CopyCoalgebra R Y := by
  classical
  refine Finsupp.onFinset (F x) (fun y => if hy : y ∈ F x then v ⟨x, ⟨y, hy⟩⟩ else 0) ?_
  intro y hy
  by_contra hn
  exact hy (dif_neg hn)

/-- Simplify the allowed coefficients of a chart row to the value of their coordinate. -/
@[simp]
theorem rowOfValues_apply_mem (v : F.Coordinate → R) (x : X) (y : F x) :
    F.rowOfValues v x y.val = v ⟨x, y⟩ := by
  classical
  exact dif_pos y.property

/-- Simplify the disallowed coefficients of a chart row to zero. -/
@[simp]
theorem rowOfValues_apply_notMem (v : F.Coordinate → R) (x : X) (y : Y)
    (h : y ∉ F x) : F.rowOfValues v x y = 0 := by
  classical
  exact dif_neg h

/-- The zero extension of the coordinates is supported in the designated finite set. -/
theorem support_rowOfValues (v : F.Coordinate → R) (x : X) :
    (F.rowOfValues v x).support ⊆ F x :=
  Finsupp.support_onFinset_subset

/-- The sum of the zero-extended row is the finite sum of the chart coordinates. -/
theorem rowOfValues_sum (v : F.Coordinate → R) (x : X) :
    (F.rowOfValues v x).sum (fun _ r => r) = ∑ y : F x, v ⟨x, y⟩ := by
  classical
  rw [Finsupp.sum_of_support_subset _ (F.support_rowOfValues v x) _ (fun _ _ => rfl)]
  rw [← Finset.sum_coe_sort]
  simp

/-- The chart conditions imply equation (4.1) for each zero-extended row. -/
theorem isCopyRow_rowOfAssignment (a : (F.presentation k).Assignment R) (x : X) :
    IsCopyRow (F.rowOfValues a.value x) := by
  classical
  refine ⟨fun y => ?_, fun y z hyz => ?_, ?_⟩
  · by_cases hy : y ∈ F x
    · rw [F.rowOfValues_apply_mem a.value x ⟨y, hy⟩]
      simpa [presentation, IsIdempotentElem] using a.holds (.idempotent ⟨x, ⟨y, hy⟩⟩)
    · rw [F.rowOfValues_apply_notMem a.value x y hy]
      exact IsIdempotentElem.zero
  · change F.rowOfValues a.value x y * F.rowOfValues a.value x z = 0
    by_cases hy : y ∈ F x
    · by_cases hz : z ∈ F x
      · rw [F.rowOfValues_apply_mem a.value x ⟨y, hy⟩,
          F.rowOfValues_apply_mem a.value x ⟨z, hz⟩]
        simpa [presentation] using
          a.holds (.orthogonal x ⟨y, hy⟩ ⟨z, hz⟩ (fun h => hyz (congrArg Subtype.val h)))
      · rw [F.rowOfValues_apply_notMem a.value x z hz, mul_zero]
    · rw [F.rowOfValues_apply_notMem a.value x y hy, zero_mul]
  · rw [F.rowOfValues_sum]
    simpa [presentation] using a.holds (.complete x)

/-- A family of rows with the profile defines an assignment in the coordinate chart. -/
def assignmentOfRows (a : F.RowsAt R) : (F.presentation k).Assignment R where
  value v := a.val.val v.1 v.2.val
  holds
    | .idempotent v => by
        simpa [presentation, IsIdempotentElem] using (a.val.property v.1).1 v.2.val
    | .orthogonal x y z hne => by
        simpa [presentation] using (a.val.property x).2.1 (fun h => hne (Subtype.ext h))
    | .complete x => by
        have h := (a.val.property x).2.2
        rw [Finsupp.sum_of_support_subset _ (a.property x) _ (fun _ _ => rfl),
          ← Finset.sum_coe_sort] at h
        simpa [presentation] using h

/-- Zero extension and restriction of coefficients identify the chart assignments and the
rows with prescribed finite profile. -/
def assignmentRowsEquiv : (F.presentation k).Assignment R ≃ F.RowsAt R where
  toFun a := ⟨⟨F.rowOfValues a.value, F.isCopyRow_rowOfAssignment a⟩, F.support_rowOfValues _⟩
  invFun := F.assignmentOfRows
  left_inv a := PolynomialPresentation.Assignment.ext fun ⟨x, y⟩ => F.rowOfValues_apply_mem a.value x y
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    apply Finsupp.ext
    intro y
    classical
    by_cases hy : y ∈ F x
    · exact F.rowOfValues_apply_mem (F.assignmentOfRows (k := k) a).value x ⟨y, hy⟩
    · rw [show F.rowOfValues (F.assignmentOfRows (k := k) a).value x y = 0
        from F.rowOfValues_apply_notMem _ x y hy]
      exact (Finsupp.notMem_support_iff.mp fun h => hy (a.property x h)).symm

end SupportProfile

end SHIGURE.Copying
