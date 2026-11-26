import Mathlib.RingTheory.Flat.Equalizer

/-! # Flat base change and the fixed-vector equalizer

The coaction identities give an inverse to multiplication on the base-changed equalizer.
-/

namespace SHIGURE.CoefficientDescent

open TensorProduct

noncomputable section

universe u

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- The unit inserts the unit coefficient on the left of a vector. -/
def insertUnit : N →ₗ[A] B ⊗[A] N := TensorProduct.mk A B N 1

/-- The counit multiplies the scalar into the vector. -/
def multiply : B ⊗[A] N →ₗ[B] N :=
  AlgebraTensorModule.lift
    { toFun b := (Algebra.lsmul A A N : B →ₐ[A] Module.End A N) b
      map_add' b c := map_add (Algebra.lsmul A A N) b c
      map_smul' b c := by
        ext n
        simp [smul_eq_mul] }

@[simp] theorem multiply_tmul (b : B) (n : N) :
    multiply (A := A) (b ⊗ₜ[A] n) = b • n := rfl

omit [Module B N] [IsScalarTower A B N] in
@[simp] theorem insertUnit_apply (n : N) :
    insertUnit (A := A) (B := B) n = 1 ⊗ₜ[A] n := rfl

/-- An actual coaction with the two identities in (B.3). -/
structure Coaction (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] where
  map : N →ₗ[B] B ⊗[A] N
  counit : ∀ n, multiply (A := A) (map n) = n
  coassoc : ∀ n,
    ((map.restrictScalars A).baseChange B) (map n) =
      ((insertUnit (A := A) (B := B)).baseChange B) (map n)

namespace Coaction

variable (ρ : Coaction A B N)

/-- Vectors for which the coaction is insertion of the unit. -/
def descended : Submodule A N :=
  LinearMap.eqLocus (ρ.map.restrictScalars A) insertUnit

theorem descended_iff (n : N) : n ∈ ρ.descended ↔ ρ.map n = 1 ⊗ₜ[A] n := Iff.rfl

variable [Module.Flat A B]

/-- The coaction takes values in the base-changed equalizer. -/
def intoTensorEqualizer : N →ₗ[B]
    LinearMap.eqLocus ((ρ.map.restrictScalars A).baseChange B)
      ((insertUnit (A := A) (B := B)).baseChange B) :=
  ρ.map.codRestrict _ ρ.coassoc

/-- The inverse of the descent comparison is the coaction read in the equalizer. -/
def fromModule : N →ₗ[B] B ⊗[A] ρ.descended :=
  (LinearMap.tensorEqLocusEquiv B B (ρ.map.restrictScalars A) insertUnit).symm.toLinearMap.comp
    ρ.intoTensorEqualizer

/-- In the original tensor module, the inverse comparison is the coaction. -/
theorem subtype_fromModule (n : N) :
    (ρ.descended.subtype.baseChange B) (ρ.fromModule n) = ρ.map n :=
  LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm B B (ρ.map.restrictScalars A)
    insertUnit (ρ.intoTensorEqualizer n)

/-- The comparison in (B.2) multiplies the coefficient into the underlying fixed vector. -/
def comparison : B ⊗[A] ρ.descended →ₗ[B] N :=
  multiply.comp (ρ.descended.subtype.baseChange B)

omit [Module.Flat A B] in
@[simp] theorem comparison_tmul (b : B) (n : ρ.descended) :
    ρ.comparison (b ⊗ₜ[A] n) = b • (n.val : N) := rfl

theorem comparison_fromModule (n : N) : ρ.comparison (ρ.fromModule n) = n := by
  change multiply (A := A) ((ρ.descended.subtype.baseChange B) (ρ.fromModule n)) = n
  rw [ρ.subtype_fromModule]
  exact ρ.counit n

theorem fromModule_comparison (x : B ⊗[A] ρ.descended) : ρ.fromModule (ρ.comparison x) = x := by
  suffices ρ.fromModule.comp ρ.comparison = LinearMap.id from LinearMap.congr_fun this x
  apply AlgebraTensorModule.ext
  intro b m
  have injective : Function.Injective (ρ.descended.subtype.baseChange B) :=
    Module.Flat.lTensor_preserves_injective_linearMap ρ.descended.subtype ρ.descended.injective_subtype
  apply injective
  change (ρ.descended.subtype.baseChange B) (ρ.fromModule (ρ.comparison (b ⊗ₜ[A] m))) =
    b ⊗ₜ[A] (m.val : N)
  rw [ρ.subtype_fromModule, ρ.comparison_tmul, map_smul, (ρ.descended_iff m.val).1 m.property]
  rw [smul_tmul', smul_eq_mul, mul_one]

/-- The comparison in (B.2) is an isomorphism over the larger coefficient ring. -/
def comparisonEquiv : (B ⊗[A] ρ.descended) ≃ₗ[B] N :=
  LinearEquiv.ofLinear ρ.comparison ρ.fromModule
    (LinearMap.ext ρ.comparison_fromModule) (LinearMap.ext ρ.fromModule_comparison)

end Coaction

end

end SHIGURE.CoefficientDescent
