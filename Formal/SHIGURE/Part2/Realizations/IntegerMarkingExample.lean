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

/-- The common open of the two charts is the principal open at six. -/
theorem integerTwoGeneratorMarking_overlap_open :
    basicOpen (2 : ℤ) ⊓ basicOpen (3 : ℤ) = basicOpen (6 : ℤ) :=
  (basicOpen_mul (2 : ℤ) 3).symm

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

private theorem integerTwoGeneratorMarking_overlap_units [IsLocalization.Away (6 : ℤ) S] :
    IsUnit (algebraMap ℤ S 2) ∧ IsUnit (algebraMap ℤ S 3) := by
  apply IsUnit.mul_iff.mp
  rw [← map_mul]
  change IsUnit (algebraMap ℤ S (6 : ℤ))
  exact IsLocalization.Away.algebraMap_isUnit (S := S) (6 : ℤ)

/-- The first chart has its actual restriction map to the localization at six. -/
def integerTwoGeneratorMarking_restrictTwo [IsLocalization.Away (6 : ℤ) S] :
    Localization.Away (2 : ℤ) →+* S :=
  IsLocalization.Away.lift (g := algebraMap ℤ S) (2 : ℤ) integerTwoGeneratorMarking_overlap_units.1

/-- The second chart has its actual restriction map to the localization at six. -/
def integerTwoGeneratorMarking_restrictThree [IsLocalization.Away (6 : ℤ) S] :
    Localization.Away (3 : ℤ) →+* S :=
  IsLocalization.Away.lift (g := algebraMap ℤ S) (3 : ℤ) integerTwoGeneratorMarking_overlap_units.2

/-- The change-of-basis ratios from the two charts are inverse after both are
restricted to the actual overlap, the localization at six. -/
theorem integerTwoGeneratorMarking_overlap [IsLocalization.Away (6 : ℤ) S] :
    integerTwoGeneratorMarking_restrictThree
      (algebraMap ℤ (Localization.Away (3 : ℤ)) 2 * IsLocalization.Away.invSelf (3 : ℤ)) *
    integerTwoGeneratorMarking_restrictTwo
      (algebraMap ℤ (Localization.Away (2 : ℤ)) 3 * IsLocalization.Away.invSelf (2 : ℤ)) = (1 : S) := by
  let u := integerTwoGeneratorMarking_restrictTwo (S := S)
  let v := integerTwoGeneratorMarking_restrictThree (S := S)
  let a := algebraMap ℤ S 2
  let b := algebraMap ℤ S 3
  let i₂ := u (IsLocalization.Away.invSelf (S := Localization.Away (2 : ℤ)) (2 : ℤ))
  let i₃ := v (IsLocalization.Away.invSelf (S := Localization.Away (3 : ℤ)) (3 : ℤ))
  have hu (x : ℤ) : u (algebraMap ℤ _ x) = algebraMap ℤ S x :=
    IsLocalization.Away.lift_eq (2 : ℤ) _ x
  have hv (x : ℤ) : v (algebraMap ℤ _ x) = algebraMap ℤ S x :=
    IsLocalization.Away.lift_eq (3 : ℤ) _ x
  have ha : a * i₂ = 1 := by
    have e := congrArg u (IsLocalization.Away.mul_invSelf (S := Localization.Away (2 : ℤ)) (2 : ℤ))
    rw [map_mul, hu, map_one] at e
    exact e
  have hb : b * i₃ = 1 := by
    have e := congrArg v (IsLocalization.Away.mul_invSelf (S := Localization.Away (3 : ℤ)) (3 : ℤ))
    rw [map_mul, hv, map_one] at e
    exact e
  change v (_ * _) * u (_ * _) = 1
  rw [map_mul v, map_mul u, hv, hu]
  change (a * i₃) * (b * i₂) = 1
  calc
    _ = (a * i₂) * (b * i₃) := by ring
    _ = 1 := by rw [ha, hb, one_mul]

/-- Multiplying the restricted first row by the change of basis gives the
restricted second row on the common localization. -/
theorem integerTwoGeneratorMarking_overlap_rows [IsLocalization.Away (6 : ℤ) S] (j : Fin 2) :
    integerTwoGeneratorMarking_restrictThree (S := S)
      (![algebraMap ℤ (Localization.Away (3 : ℤ)) 2 * IsLocalization.Away.invSelf (3 : ℤ), 1] j) =
    integerTwoGeneratorMarking_restrictThree (S := S)
      (algebraMap ℤ (Localization.Away (3 : ℤ)) 2 * IsLocalization.Away.invSelf (3 : ℤ)) *
    integerTwoGeneratorMarking_restrictTwo (S := S)
      (![1, algebraMap ℤ (Localization.Away (2 : ℤ)) 3 * IsLocalization.Away.invSelf (2 : ℤ)] j) := by
  fin_cases j
  · change _ = _ * integerTwoGeneratorMarking_restrictTwo (S := S) (1 : Localization.Away (2 : ℤ))
    rw [map_one, mul_one]
    rfl
  · change integerTwoGeneratorMarking_restrictThree (S := S) (1 : Localization.Away (3 : ℤ)) = _
    rw [map_one]
    exact (integerTwoGeneratorMarking_overlap (S := S)).symm

end

end SHIGURE.RealizationFamilies
