import Formal.SHIGURE.Part2.Tensor.CoefficientPoints
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Universal inputs for equations of terms

The first half of Proposition 4.10 uses finite sums of pure tensors as
inputs. A separate indeterminate records each coefficient in those sums.
Terms use typed variables and may use an input more than once.

## Implementation notes

The typed term here uses only total multilinear primitives. A tensor
expression has linear maps between fixed shapes, so its equality transfers
by transport. For a term we instead give each pure summand its own
polynomial variable and use the semilinear state map for its substitution.
-/

open CategoryTheory TensorProduct
open scoped BigOperators TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

/-- Terms whose primitive operations are total multilinear maps. -/
inductive TensorTerm (sig : Signature.{u}) (Γ : List sig.SortType) : sig.SortType → Type u
  | var {s : sig.SortType} : Var Γ s → TensorTerm sig Γ s
  | total (op : sig.Total) :
      (∀ i : TensorPosition (sig.totalArity op).inputs, TensorTerm sig Γ i.1) →
      TensorTerm sig Γ (sig.totalArity op).output
  | quantity (q : sig.Quantity) :
      (∀ i : TensorPosition (sig.quantityArity q).inputs, TensorTerm sig Γ i.1) →
      TensorTerm sig Γ (sig.quantityArity q).output

namespace TensorTerm

variable {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}
variable {R : Type u} [CommRing R]

/-- Evaluate the typed term using actual primitive maps on the input tuple. -/
def eval (A : TensorStructure R sig) (xs : ∀ i : TensorPosition Γ, A.carrier i.1) :
    {s : sig.SortType} → TensorTerm sig Γ s → A.carrier s
  | _, .var i => xs ⟨_, i⟩
  | _, .total op args => A.total op (fun i => (args i).eval A xs)
  | _, .quantity q args => A.quantity q (fun i => (args i).eval A xs)

/-- The structure-preserving maps commute with evaluation of finite terms. -/
theorem eval_hom {A B : TensorStructure R sig} (f : TensorStructure.Hom A B)
    (xs : ∀ i : TensorPosition Γ, A.carrier i.1) (t : TensorTerm sig Γ s) :
    f.onSort s (t.eval A xs) = t.eval B (fun i => f.onSort i.1 (xs i)) := by
  induction t with
  | var i => rfl
  | total op args ih =>
    exact (f.preservesTotal op _).trans (congrArg (B.total op) (funext ih))
  | quantity q args ih =>
    exact (f.preservesQuantity q _).trans (congrArg (B.quantity q) (funext ih))

end TensorTerm

variable {k R S M : Type u} [CommRing k] [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S] [AddCommGroup M] [Module k M]

/-- Evaluation on unit coefficients gives the unit tensor of the original value. -/
theorem TensorTerm.eval_unit {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}
    (A : TensorStructure k sig) (xs : ∀ i : TensorPosition Γ, A.carrier i.1) (t : TensorTerm sig Γ s) :
    t.eval (extendStructure k R A) (fun i => (1 : R) ⊗ₜ[k] xs i) = (1 : R) ⊗ₜ[k] t.eval A xs := by
  induction t with
  | var i => rfl
  | total op args ih =>
    change extendOperation k A.carrier R (A.total op)
      (fun i => (args i).eval (extendStructure k R A) (fun j => (1 : R) ⊗ₜ[k] xs j)) = _
    rw [funext ih, extendOperation_unit]
    rfl
  | quantity q args ih =>
    change extendOperation k A.carrier R (A.quantity q)
      (fun i => (args i).eval (extendStructure k R A) (fun j => (1 : R) ⊗ₜ[k] xs j)) = _
    rw [funext ih, extendOperation_unit]
    rfl

private theorem scalarTower_unit_mapCoefficients (f : R →ₐ[k] S) (z : R ⊗[k] M) :
    letI : Algebra R S := f.toRingHom.toAlgebra
    letI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
    scalarTower (k := k) ((1 : S) ⊗ₜ[R] z) = mapCoefficients f z := by
  letI : Algebra R S := f.toRingHom.toAlgebra
  letI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  change scalarTower (k := k) ((1 : S) ⊗ₜ[R] z) = mapCoefficients f z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    rw [scalarTower_tmul, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- Term evaluation commutes with substitution along each coefficient-algebra homomorphism. -/
theorem TensorTerm.eval_mapCoefficients {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}
    (f : R →ₐ[k] S) (A : TensorStructure k sig)
    (xs : ∀ i : TensorPosition Γ, R ⊗[k] A.carrier i.1) (t : TensorTerm sig Γ s) :
    mapCoefficients f (t.eval (extendStructure k R A) xs) =
      t.eval (extendStructure k S A) (fun i => mapCoefficients f (xs i)) := by
  letI : Algebra R S := f.toRingHom.toAlgebra
  letI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  let e := structureScalarTower (R := R) (S := S) A
  rw [← scalarTower_unit_mapCoefficients f]
  change e.hom.onSort s ((1 : S) ⊗ₜ[R] t.eval (extendStructure k R A) xs) = _
  rw [← t.eval_unit (R := S) (extendStructure k R A) xs, t.eval_hom e.hom]
  exact congrArg (t.eval (extendStructure k S A)) (funext fun i => scalarTower_unit_mapCoefficients f (xs i))

/-- Every scalar-extended element is a finite sum of coefficient-weighted native states. -/
theorem exists_list_tmul_sum (z : R ⊗[k] M) :
    ∃ xs : List (R × M), (xs.map fun x => x.1 ⊗ₜ[k] x.2).sum = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨[], rfl⟩
  | tmul r m => exact ⟨[(r, m)], by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a ++ b, by rw [List.map_append, List.sum_append, ha, hb]⟩

variable {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}

/-- For each native summand, insert a distinct coefficient variable in the
finite input tuple of equation (4.5). -/
def formalInput (A : TensorStructure k sig) (n : TensorPosition Γ → ℕ)
    (m : ∀ i : TensorPosition Γ, Fin (n i) → A.carrier i.1) (i : TensorPosition Γ) :
    MvPolynomial ((j : TensorPosition Γ) × Fin (n j)) k ⊗[k] A.carrier i.1 :=
  ∑ j, MvPolynomial.X ⟨i, j⟩ ⊗ₜ[k] m i j

/-- Equation (4.5) for every finite list of native states is equivalent to equality
after every coefficient extension on arbitrary inputs. -/
theorem universal_term_equation_iff (A : TensorStructure k sig) (t t' : TensorTerm sig Γ s) :
    (∀ (n : TensorPosition Γ → ℕ) (m : ∀ i : TensorPosition Γ, Fin (n i) → A.carrier i.1),
      t.eval (extendStructure k (MvPolynomial ((i : TensorPosition Γ) × Fin (n i)) k) A) (formalInput A n m) -
        t'.eval (extendStructure k (MvPolynomial ((i : TensorPosition Γ) × Fin (n i)) k) A) (formalInput A n m) = 0) ↔
    (∀ (R : Type u) [CommRing R] [Algebra k R] (x : ∀ i : TensorPosition Γ, R ⊗[k] A.carrier i.1),
      t.eval (extendStructure k R A) x = t'.eval (extendStructure k R A) x) := by
  constructor
  · intro hall R _ _ x
    classical
    choose l hl using (fun i => exists_list_tmul_sum (x i))
    let n (i : TensorPosition Γ) := (l i).length
    let m (i : TensorPosition Γ) (j : Fin (n i)) := ((l i).get j).2
    let f : MvPolynomial ((i : TensorPosition Γ) × Fin (n i)) k →ₐ[k] R :=
      MvPolynomial.aeval (fun j => ((l j.1).get j.2).1)
    have hx (i : TensorPosition Γ) : mapCoefficients f (formalInput A n m i) = x i := by
      rw [formalInput, map_sum]
      simp only [mapCoefficients_tmul, f, MvPolynomial.aeval_X]
      rw [← List.sum_ofFn]
      have he := List.map_ofFn (l i).get (fun z => z.1 ⊗ₜ[k] z.2)
      rw [List.ofFn_get] at he
      exact (congrArg List.sum he).symm.trans (hl i)
    have he := congrArg (mapCoefficients f) (sub_eq_zero.mp (hall n m))
    rw [t.eval_mapCoefficients, t'.eval_mapCoefficients, funext hx] at he
    exact he
  · intro hall n m
    exact sub_eq_zero.mpr (hall _ (formalInput A n m))

end SHIGURE.TensorRealization
