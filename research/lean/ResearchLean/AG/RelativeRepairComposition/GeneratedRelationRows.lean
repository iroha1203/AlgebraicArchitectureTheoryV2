import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteRectangularImage

/-!
# Independent public equations generated from the actual public output

## Implementation notes

Generated pivot coordinates of the full public image give independent rows.
Their number is bounded by the number of original public coordinates. For
each consistent affine right-hand side these same rows present the relation.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteElimination
open Module
universe uk un
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {m n : Type un} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (M : Matrix m n k) (enumK : Enumeration k) (enumM : Enumeration m) (enumN : Enumeration n)

/-- The generated public-output coordinates use the whole original matrix range. -/
def publicImageCoordinates : (n → k) →ₗ[k] (RectangularActive M enumK enumM enumN → k) :=
  (rectangularImageEquivalence M enumK enumM enumN).toLinearMap.comp (Matrix.toLin' M).rangeRestrict

/-- Every generated image coordinate is reached by original public variables. -/
theorem public_image_coordinates_surjective : Function.Surjective (publicImageCoordinates M enumK enumM enumN) :=
  (rectangularImageEquivalence M enumK enumM enumN).surjective.comp
    (Matrix.toLin' M).surjective_rangeRestrict

/-- Generated coordinates distinguish exactly the original public output values. -/
theorem public_image_coordinates_eq_iff (z z' : n → k) :
    publicImageCoordinates M enumK enumM enumN z = publicImageCoordinates M enumK enumM enumN z' ↔
      Matrix.toLin' M z = Matrix.toLin' M z' := by
  change (rectangularImageEquivalence M enumK enumM enumN) _ =
    (rectangularImageEquivalence M enumK enumM enumN) _ ↔ _
  rw [(rectangularImageEquivalence M enumK enumM enumN).injective.eq_iff]
  exact Subtype.ext_iff

/-- A row is the generated pivot-coordinate functional on the original public variables. -/
def publicRow (i : RectangularActive M enumK enumM enumN) : Module.Dual k (n → k) :=
  (LinearMap.proj i).comp (publicImageCoordinates M enumK enumM enumN)

/-- The complete generated public equation rows are linearly independent. -/
theorem public_rows_independent : LinearIndependent k (publicRow M enumK enumM enumN) := by
  have hh := (Pi.basisFun k (RectangularActive M enumK enumM enumN)).dualBasis.linearIndependent.map_injOn
    (publicImageCoordinates M enumK enumM enumN).dualMap
    (LinearMap.dualMap_injective_of_surjective (public_image_coordinates_surjective M enumK enumM enumN)).injOn
  convert hh using 1
  funext i
  ext z
  simp [publicRow]

/-- Generated rows read exactly their effective pivot coordinates. -/
theorem public_row_value (i : RectangularActive M enumK enumM enumN) (z : n → k) :
    publicRow M enumK enumM enumN i z = publicImageCoordinates M enumK enumM enumN z i := by
  rfl

/-- The number of independent equations is at most the original public dimension. -/
theorem public_row_count : Fintype.card (RectangularActive M enumK enumM enumN) ≤ Fintype.card n := by
  rw [← Module.finrank_eq_card_basis (rectangularBasis M enumK enumM enumN)]
  simpa only [Module.finrank_fintype_fun_eq_card] using (Matrix.toLin' M).finrank_range_le

/-- Every consistent affine relation is presented by the same independent generated rows. -/
theorem public_affine_relation (r : m → k) (z₀ : n → k) (hr : Matrix.toLin' M z₀ = r) (z : n → k) :
    Matrix.toLin' M z = r ↔ ∀ i,
      publicRow M enumK enumM enumN i z = publicRow M enumK enumM enumN i z₀ := by
  rw [← hr,← public_image_coordinates_eq_iff M enumK enumM enumN z z₀]
  simp only [public_row_value,funext_iff]

end AAT.AG.RelativeRepairComposition.FiniteElimination

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
