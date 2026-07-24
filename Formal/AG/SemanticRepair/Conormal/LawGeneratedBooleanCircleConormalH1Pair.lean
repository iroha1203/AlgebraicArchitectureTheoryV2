import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleSquareZeroH1
import Formal.Util.AssertStandardAxioms

/-!
# Fixed Boolean-circle conormal H1 pair

The idempotent and square-zero law cores share the same site, selected cover,
ambient ring, and restriction operation.  The idempotent raw conormal is zero
sectionwise, so its canonical sheafification coefficient and every generated
H1 class are zero.  The square-zero coefficient carries the concrete nonzero
class from Cycle 23.  No vanishing or nonvanishing conclusion is accepted as
input data.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedBooleanCircleConormalH1Pair

open CategoryTheory
open AAT.AG
open LawGeneratedBooleanCircleSite
open LawGeneratedBooleanCircleLawCore
open LawGeneratedBooleanCircleConormalSheafification
open LawGeneratedBooleanCircleSquareZeroH1
open LawGeneratedIdealPowerSequence
open LawGeneratedIdealPowerLiftedSheafification
open LawGeneratedLargeCoefficientCech

/-- The idempotent first sheafified coefficient on the fixed Boolean-circle data. -/
abbrev IdempotentX1 := (sheafifiedShortComplex idempotentCore).X₁.val

/-- Every section of the sheafified idempotent conormal coefficient is zero. -/
theorem idempotentX1_eq_zero (W : site.category)
    (x : IdempotentX1.obj (Opposite.op W)) : x = 0 := by
  rw [← (idempotentRawConormalX1Equiv W).apply_symm_apply x]
  rw [idempotent_conormal_eq_zero W
    ((idempotentRawConormalX1Equiv W).symm x)]
  exact map_zero (idempotentRawConormalX1Equiv W)

/-- Every generated idempotent cochain is the zero cochain. -/
theorem idempotentCochain_eq_zero (n : Nat)
    (c : Cochain geometry IdempotentX1 n) : c = 0 := by
  funext sigma
  exact idempotentX1_eq_zero _ (c sigma)

/-- Every represented idempotent H1 class is the zero class. -/
theorem idempotentH1Class_isZero
    (c : (threeTermComplex geometry IdempotentX1).H1Cocycle) :
    (threeTermComplex geometry IdempotentX1).H1IsZero
      (h1Class geometry IdempotentX1 c) := by
  apply (h1Class_isZero_iff geometry IdempotentX1 c).2
  refine ⟨0, ?_⟩
  rw [idempotentCochain_eq_zero 1 c.1]
  simp

/-- Every idempotent H1 quotient class is zero. -/
theorem idempotentH1_isZero
    (x : H1 geometry IdempotentX1) :
    (threeTermComplex geometry IdempotentX1).H1IsZero x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact idempotentH1Class_isZero c

/-- Fixed D2 pair: idempotent H1 vanishes and square-zero H1 has a nonzero class. -/
theorem conormalH1_zero_nonzero_pair :
    (∀ x : H1 geometry IdempotentX1,
      (threeTermComplex geometry IdempotentX1).H1IsZero x) ∧
    ¬ (threeTermComplex geometry SquareZeroX1).H1IsZero
      (h1Class geometry SquareZeroX1 squareZeroOmegaCocycle) :=
  ⟨idempotentH1_isZero, squareZeroOmegaClass_not_zero⟩

end LawGeneratedBooleanCircleConormalH1Pair
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleConormalH1Pair
