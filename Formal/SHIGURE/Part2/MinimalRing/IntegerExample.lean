import Formal.SHIGURE.Part2.MinimalRing.Systems
import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

/-!
# Integer observation that loses injectivity after reduction modulo two

There is one sort, no named operations, identity input, and observation
multiplication by two.  The dual observation is not surjective, and its
actual scalar extension to `ZMod 2` is zero.
-/

namespace SHIGURE.MinimalRing.IntegerExample

open scoped TensorProduct

/-- The observation of the rank-one integer state. -/
def twice : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id

/-- There are no unary operation names in the example. -/
def NoOperation (_ _ : Unit) : Type := Empty

/-- The single input is the identity and there are no operation maps. -/
def system : LinearSystem (R := ℤ) NoOperation (fun _ => ℤ) (fun _ => ℤ) where
  input _ := LinearMap.id
  operation e := nomatch e

/-- The actual observation attached to the unique sort. -/
def observation (_ : Unit) : ℤ →ₗ[ℤ] ℤ := twice

/-- The integer observation is injective. -/
theorem twice_injective : Function.Injective twice := by
  intro x y h
  have h' : 2 * x = 2 * y := by simpa [twice, smul_eq_mul] using h
  omega

/-- Its dual is not surjective: the identity functional has no preimage. -/
theorem twice_dualMap_not_surjective : ¬ Function.Surjective twice.dualMap := by
  intro h
  obtain ⟨φ, hφ⟩ := h (LinearMap.id : Module.Dual ℤ ℤ)
  have hval := LinearMap.congr_fun hφ 1
  have hv : φ (2 : ℤ) = 1 := by simpa [twice, LinearMap.dualMap_apply, smul_eq_mul] using hval
  have hadd : φ (2 : ℤ) = φ 1 + φ 1 := by
    calc
      φ (2 : ℤ) = φ (1 + 1) := by rfl
      _ = φ 1 + φ 1 := map_add φ 1 1
  omega

/-- The actual base change of the observation to `ZMod 2` is the zero map. -/
theorem twice_baseChange_zmod_two : twice.baseChange (ZMod 2) = 0 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  rw [LinearMap.baseChange_tmul, LinearMap.zero_apply]
  change a ⊗ₜ[ℤ] ((2 : ℤ) • x) = 0
  rw [← TensorProduct.smul_tmul]
  have htwo : (2 : ℤ) • a = 0 := by
    rw [two_zsmul, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [htwo, TensorProduct.zero_tmul]

end SHIGURE.MinimalRing.IntegerExample
