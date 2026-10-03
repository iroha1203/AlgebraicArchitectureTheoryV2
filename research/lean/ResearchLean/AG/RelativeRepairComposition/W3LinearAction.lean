import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Formal.Util.AssertStandardAxioms

/-!
# W3's two specified full linear actions on F3²

Both choices act on the same entire vector space. The shear is the actual
invertible linear map (x,y) ↦ (x+y,y), with inverse (x,y) ↦ (x-y,y).
-/
namespace AAT.AG.RelativeRepairComposition.W3LinearAction

/-- The arithmetic prime-three theorem supplies the specified field. -/
instance primeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The complete specified two-dimensional vector space. -/
abbrev A := Fin 2 → ZMod 3

/-- The original shear and its actual inverse on all vectors. -/
def shear : A ≃ₗ[ZMod 3] A where
  toFun x i := if i = 0 then x 0 + x 1 else x 1
  invFun x i := if i = 0 then x 0 - x 1 else x 1
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv x := by funext i; fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i
    · change (x 0 + y 0) + (x 1 + y 1) = (x 0 + x 1) + (y 0 + y 1)
      abel
    · rfl
  map_smul' c x := by funext i; fin_cases i <;> simp [mul_add]

/-- The first original coordinate is x+y. -/
theorem shear_first (x : A) : shear x 0 = x 0 + x 1 := rfl

/-- The second original coordinate is unchanged. -/
theorem shear_second (x : A) : shear x 1 = x 1 := rfl

/-- Both specified choices use the same vector carrier. -/
def linearAction (sheared : Bool) : A ≃ₗ[ZMod 3] A := if sheared then shear else 1

/-- The comparison choice is the actual identity on every vector. -/
theorem identity_apply (x : A) : linearAction false x = x := rfl

/-- The shear choice evaluates its whole original linear map. -/
theorem shear_apply (x : A) : linearAction true x = shear x := rfl

/-- The shear moves the original second basis vector, so it is not identity. -/
theorem shear_ne_one : shear ≠ (1 : A ≃ₗ[ZMod 3] A) := by
  intro h
  have hx := congrArg (fun f : A ≃ₗ[ZMod 3] A =>
    f (fun i => if i = 0 then 0 else 1) 0) h
  simp [shear] at hx

/-- The actual loop difference is the full vector (-y,0). -/
theorem identity_minus_shear (x : A) :
    x - shear x = fun i => if i = 0 then -x 1 else 0 := by
  funext i
  fin_cases i <;> simp [shear]

/-- The full fixed-vector condition is exactly the vanishing second coordinate. -/
theorem shear_fixed_iff (x : A) : shear x = x ↔ x 1 = 0 := by
  constructor
  · intro h
    have h0 : x 0 + x 1 = x 0 := congrFun h 0
    calc
      x 1 = (x 0 + x 1) - x 0 := by abel
      _ = 0 := by rw [h0, sub_self]
  · intro h
    funext i
    fin_cases i <;> simp [shear, h]

end AAT.AG.RelativeRepairComposition.W3LinearAction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3LinearAction
