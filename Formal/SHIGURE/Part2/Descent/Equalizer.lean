import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.RingTheory.Flat.Equalizer

/-! # Flat base change and the fixed-vector equalizer

The coaction identities give an inverse to multiplication on the base-changed equalizer.

## Implementation notes

The two coaction identities are the counit and comultiplication laws
for coalgebras of the extension–restriction comonad. Mathlib proves
`ModuleCat.comonadicExtendScalars` and leaves the passage to geometric
overlap data open. Here the overlap constructs the coaction in
`Datum.toCoaction`, and the explicit tensor equalizer computes the
comparison and its inverse in (B.2). `Coaction.equivCoalgebra` identifies
this concrete representation with the actual mathlib coalgebras on the
same module. Their structure map becomes the coaction, with counit
given by scalar multiplication and comultiplication by unit insertion.
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

/-- Evaluate the multiplication comparison on a pure tensor. -/
@[simp] theorem multiply_tmul (b : B) (n : N) :
    multiply (A := A) (b ⊗ₜ[A] n) = b • n := rfl

omit [Module B N] [IsScalarTower A B N] in
/-- Evaluate the unit insertion on a vector. -/
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

/-- A vector descends exactly when its coaction equals unit insertion. -/
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
/-- The comparison sends a pure tensor to scalar multiplication. -/
@[simp] theorem comparison_tmul (b : B) (n : ρ.descended) :
    ρ.comparison (b ⊗ₜ[A] n) = b • (n.val : N) := rfl

/-- The coaction counit makes the constructed inverse a right inverse. -/
theorem comparison_fromModule (n : N) : ρ.comparison (ρ.fromModule n) = n := by
  change multiply (A := A) ((ρ.descended.subtype.baseChange B) (ρ.fromModule n)) = n
  rw [ρ.subtype_fromModule]
  exact ρ.counit n

/-- Flatness and the fixed-vector condition make the constructed inverse a left inverse. -/
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

open CategoryTheory

noncomputable section
universe u

variable {A B N : Type u} [CommRing A] [CommRing B] [AddCommGroup N] [Module B N]

/-- On a fixed module, the explicit tensor laws are exactly the laws of the coefficient comonad. -/
def Coaction.equivCoalgebra [Algebra A B] [Module A N] [IsScalarTower A B N] :
    Coaction A B N ≃
      { C : Comonad.Coalgebra (ModuleCat.extendRestrictScalarsAdj.{u} (algebraMap A B)).toComonad //
        C.A = ModuleCat.of B N } := by
  let canonical (f : A →+* B) : Type u :=
    letI : Algebra A B := f.toAlgebra
    letI : Module A N := Module.compHom N f
    letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    Coaction A B N

  have restricted : Coaction A B N = canonical (algebraMap A B) := by
    generalize map_eq : algebraMap A B = f
    have algebra_eq : f.toAlgebra = (inferInstance : Algebra A B) := by
      rw [← map_eq]
      exact toAlgebra_algebraMap
    have module_eq : Module.compHom N f = (inferInstance : Module A N) := by
      apply Module.ext'
      intro r n
      change (f r) • n = r • n
      rw [← map_eq]
      exact IsScalarTower.algebraMap_smul B r n
    cases algebra_eq
    cases module_eq
    rfl

  let compare (f : A →+* B) : canonical f ≃
      { C : Comonad.Coalgebra (ModuleCat.extendRestrictScalarsAdj.{u} f).toComonad //
        C.A = ModuleCat.of B N } := by
    letI : Algebra A B := f.toAlgebra
    letI : Module A N := Module.compHom N f
    letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    have counitFormula (z : B ⊗[A] N) :
        ModuleCat.ExtendRestrictScalarsAdj.Counit.map f (Y := ModuleCat.of B N) z =
          multiply (A := A) z := by
      induction z with
      | zero => simp
      | tmul b n => rfl
      | add x y hx hy =>
        rw [map_add, map_add]
        exact congrArg₂ (· + ·) hx hy
    exact
      { toFun := fun ρ => ⟨{
          A := ModuleCat.of B N
          a := ModuleCat.ofHom ρ.map
          counit := by
            apply ModuleCat.hom_ext
            ext n
            exact (counitFormula (ρ.map n)).trans (ρ.counit n)
          coassoc := by
            apply ModuleCat.hom_ext
            ext n
            exact (ρ.coassoc n).symm }, rfl⟩
        invFun := fun ⟨⟨M, a, counit, coassoc⟩, fixed⟩ => by
          change M = ModuleCat.of B N at fixed
          subst M
          exact
            { map := a.hom
              counit := fun n => (counitFormula (a.hom n)).symm.trans (ConcreteCategory.congr_hom counit n)
              coassoc := fun n => (ConcreteCategory.congr_hom coassoc n).symm }
        left_inv := fun ρ => by cases ρ; rfl
        right_inv := fun ⟨⟨M, a, counit, coassoc⟩, fixed⟩ => by
          change M = ModuleCat.of B N at fixed
          subst M
          rfl }
  exact (Equiv.cast restricted).trans (compare (algebraMap A B))

end
end SHIGURE.CoefficientDescent
