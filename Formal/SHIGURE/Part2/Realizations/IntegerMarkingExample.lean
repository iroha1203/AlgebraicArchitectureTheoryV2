import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The two-generator integer marking in Example 6.6 -/

namespace SHIGURE.RealizationFamilies

open PrimeSpectrum TopologicalSpace

/-- The original integer marking has coordinate row `(2, 3)`. -/
def integerTwoGeneratorMarking : (Fin 2 → ℤ) →ₗ[ℤ] ℤ where
  toFun x := 2 * x 0 + 3 * x 1
  map_add' x y := by
    change 2 * (x 0 + y 0) + 3 * (x 1 + y 1) =
      (2 * x 0 + 3 * x 1) + (2 * y 0 + 3 * y 1)
    ring
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The marking is globally surjective, using the vector `(-x, x)` above `x`. -/
theorem integerTwoGeneratorMarking_surjective : Function.Surjective integerTwoGeneratorMarking := by
  intro x
  refine ⟨![ -x, x ], ?_⟩
  change 2 * (-x) + 3 * x = x
  ring

/-- Neither generating column is itself a global basis. -/
theorem integerTwoGeneratorMarking_no_global_basis (j : Fin 2) :
    ¬ IsUnit (integerTwoGeneratorMarking (Pi.single j 1)) := by
  fin_cases j <;> norm_num [integerTwoGeneratorMarking, Pi.single_apply, Int.isUnit_iff]

/-- The two actual principal opens cover the original integer spectrum. -/
theorem integerTwoGeneratorMarking_cover :
    basicOpen (2 : ℤ) ⊔ basicOpen (3 : ℤ) = ⊤ := by
  apply top_unique
  intro x _
  rw [Opens.mem_sup, mem_basicOpen, mem_basicOpen]
  by_contra h
  have both := not_or.mp h
  have one : (1 : ℤ) ∈ x.asIdeal := by
    have difference := x.asIdeal.sub_mem (not_not.mp both.2) (not_not.mp both.1)
    norm_num at difference
    exact difference
  exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr one)

noncomputable section

variable {S : Type*} [CommRing S] [Algebra ℤ S]

/-- In the first localized basis, the marking row is `(1, 3/2)`. -/
theorem integerTwoGeneratorMarking_normalize_left [IsLocalization.Away (2 : ℤ) S] :
    (fun j => algebraMap ℤ S (![2, 3] j) * IsLocalization.Away.invSelf (S := S) (2 : ℤ)) =
      ![1, algebraMap ℤ S 3 * IsLocalization.Away.invSelf (S := S) (2 : ℤ)] := by
  funext j
  fin_cases j
  · exact IsLocalization.Away.mul_invSelf (S := S) (2 : ℤ)
  · rfl

/-- In the second localized basis, the marking row is `(2/3, 1)`. -/
theorem integerTwoGeneratorMarking_normalize_right [IsLocalization.Away (3 : ℤ) S] :
    (fun j => algebraMap ℤ S (![2, 3] j) * IsLocalization.Away.invSelf (S := S) (3 : ℤ)) =
      ![algebraMap ℤ S 2 * IsLocalization.Away.invSelf (S := S) (3 : ℤ), 1] := by
  funext j
  fin_cases j
  · rfl
  · exact IsLocalization.Away.mul_invSelf (S := S) (3 : ℤ)

/-- On the common localization, the ratios for changing basis are inverse. -/
theorem integerTwoGeneratorMarking_overlap
    [IsLocalization.Away (2 : ℤ) S] [IsLocalization.Away (3 : ℤ) S] :
    (algebraMap ℤ S 2 * IsLocalization.Away.invSelf (S := S) (3 : ℤ)) *
      (algebraMap ℤ S 3 * IsLocalization.Away.invSelf (S := S) (2 : ℤ)) = 1 := by
  calc
    _ = (algebraMap ℤ S 2 * IsLocalization.Away.invSelf (S := S) (2 : ℤ)) *
        (algebraMap ℤ S 3 * IsLocalization.Away.invSelf (S := S) (3 : ℤ)) := by ring
    _ = 1 := by simp only [IsLocalization.Away.mul_invSelf, one_mul]

end

end SHIGURE.RealizationFamilies
