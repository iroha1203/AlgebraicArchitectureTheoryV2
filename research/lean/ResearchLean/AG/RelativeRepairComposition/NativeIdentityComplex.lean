import ResearchLean.AG.RelativeRepairComposition.NativeProductComplex
import Mathlib.Algebra.Homology.Homotopy

/-!
# The whole identity summand in degrees zero and one

This is the native cochain complex A --id--> A, with zero groups in every
higher degree. The contraction is identity from degree one to degree zero.

## Implementation notes

The input group is retained in full. The contraction is defined on every pair
of degrees and its native homotopy equation is checked at every natural degree.
-/
namespace AAT.AG.RelativeRepairComposition.NativeIdentityComplex
open CategoryTheory Limits
universe u
variable (A : Type u) [AddCommGroup A]

/-- The entire group in degrees zero and one and the zero group in every higher degree. -/
def object : ℕ → AddCommGrpCat.{u}
  | 0 => AddCommGrpCat.of A
  | 1 => AddCommGrpCat.of A
  | _ + 2 => AddCommGrpCat.of PUnit

/-- Identity on the entire input group is the only nonzero differential. -/
def differential : ∀ n, object A n ⟶ object A (n+1)
  | 0 => 𝟙 _
  | _ + 1 => 0

/-- The native full identity cochain complex, zero in all higher degrees. -/
def complex : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (object A) (differential A) (by
    intro n
    cases n <;> simp only [differential,Category.id_comp,Limits.zero_comp])

/-- The native zero-to-one differential is identity on the entire input group. -/
theorem complex_d_zero : (complex A).d 0 1 = 𝟙 _ :=
  CochainComplex.of_d _ _ _ 0

/-- The full zero-to-one differential retains the identity value. -/
theorem d_zero_one : (complex A).d 0 1 = 𝟙 _ := complex_d_zero A

/-- The full contraction is identity from degree one to degree zero, zero on every other pair. -/
def contractionComponent : ∀ i j, (complex A).X i ⟶ (complex A).X j
  | 1,0 => 𝟙 _
  | 0,_ => 0
  | 1,_ + 1 => 0
  | _ + 2,_ => 0

/-- The contraction component vanishes on every pair outside the native cochain homotopy shape. -/
theorem contraction_shape (i j : ℕ) (h : ¬(ComplexShape.up ℕ).Rel j i) :
    contractionComponent A i j = 0 := by
  rcases i with _ | _ | i
  · rfl
  · cases j with
    | zero => exact False.elim (h rfl)
    | succ j => rfl
  · rfl

/-- The whole identity summand is contractible as a native Mathlib complex. -/
def contraction : Homotopy (𝟙 (complex A)) 0 where
  hom := contractionComponent A
  zero := contraction_shape A
  comm n := by
    rw [HomologicalComplex.id_f,HomologicalComplex.zero_f,add_zero,
      dNext_eq (contractionComponent A) (show (ComplexShape.up ℕ).Rel n (n+1) from rfl),
      prevD_nat]
    rcases n with _ | _ | n
    · simp only [contractionComponent,Limits.zero_comp,Category.comp_id,add_zero]
      change 𝟙 (object A 0) = (complex A).d 0 (0+1)
      exact (CochainComplex.of_d (object A) (differential A) _ 0).symm
    · simp only [contractionComponent,Limits.comp_zero,Category.id_comp,zero_add]
      change 𝟙 (object A 1) = (complex A).d 0 (0+1)
      exact (CochainComplex.of_d (object A) (differential A) _ 0).symm
    · simp only [contractionComponent,Limits.comp_zero,Limits.zero_comp,add_zero]
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      cases x
      rfl

/-- Every degree-one element of the complete group is retained by the contraction. -/
theorem contraction_value (a : A) : (contraction A).hom 1 0 a = a := rfl

end AAT.AG.RelativeRepairComposition.NativeIdentityComplex
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeIdentityComplex
