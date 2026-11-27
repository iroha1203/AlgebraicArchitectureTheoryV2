import Formal.SHIGURE.Part2.Realizations.TensorCoefficientExtension
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Typed polynomial terms in the tensor realization scheme

## Implementation notes

The syntax uses the original signature and typed argument positions.
Expansion evaluates the original operations on basis vectors and sums
over all basis choices of each finite arity. Working in a free chart
produces a polynomial for each output coordinate. The universal
coefficient algebra then detects every coefficient of the written Law.
-/

namespace SHIGURE.RealizationFamilies

open CategoryTheory MvPolynomial Module SHIGURE.TensorRealization
open scoped TensorProduct

noncomputable section

universe u

/-- Polynomial terms of Definition 6.1 use the same input positions and
operations as the tensor realization. Reusing a variable is allowed. -/
inductive PolynomialTerm (k : Type u) (sig : Signature.{u}) (Γ : List sig.SortType) :
    sig.SortType → Type u
  | var {s} : Var Γ s → PolynomialTerm k sig Γ s
  | total (f : sig.Total) :
      (∀ i : TensorPosition (sig.totalArity f).inputs, PolynomialTerm k sig Γ i.1) →
        PolynomialTerm k sig Γ (sig.totalArity f).output
  | quantity (q : sig.Quantity) :
      (∀ i : TensorPosition (sig.quantityArity q).inputs, PolynomialTerm k sig Γ i.1) →
        PolynomialTerm k sig Γ (sig.quantityArity q).output
  | zero (s) : PolynomialTerm k sig Γ s
  | add {s} : PolynomialTerm k sig Γ s → PolynomialTerm k sig Γ s → PolynomialTerm k sig Γ s
  | smul {s} : k → PolynomialTerm k sig Γ s → PolynomialTerm k sig Γ s

variable {k R : Type u} [CommRing k] [CommRing R] {sig : Signature.{u}} {Γ : List sig.SortType}

namespace PolynomialTerm

/-- Evaluate a polynomial term on the actual multilinear operations. For
a nullary operation the tuple of subterms is empty. -/
def eval (c : k →+* R) (A : TensorStructure R sig)
    (x : ∀ i : TensorPosition Γ, A.carrier i.1) : ∀ {s}, PolynomialTerm k sig Γ s → A.carrier s
  | _, .var i => x ⟨_, i⟩
  | _, .total f args => A.total f (fun i => eval c A x (args i))
  | _, .quantity q args => A.quantity q (fun i => eval c A x (args i))
  | _, .zero _ => 0
  | _, .add a b => eval c A x a + eval c A x b
  | _, .smul a b => c a • eval c A x b

/-- Every tensor structure morphism acts on the value of a term by
acting on the original input tuple. -/
theorem eval_map (c : k →+* R) {A B : TensorStructure R sig} (m : TensorStructure.Hom A B)
    (x : ∀ i : TensorPosition Γ, A.carrier i.1) {s} (t : PolynomialTerm k sig Γ s) :
    m.onSort _ (t.eval c A x) = t.eval c B (fun i => m.onSort i.1 (x i)) := by
  induction t with
  | var i => rfl
  | total f args ih =>
    rw [eval, m.preservesTotal]
    exact congrArg (B.total f) (funext ih)
  | quantity q args ih =>
    rw [eval, m.preservesQuantity]
    exact congrArg (B.quantity q) (funext ih)
  | zero s => exact map_zero (m.onSort s)
  | add a b ha hb => rw [eval, map_add, ha, hb, eval]
  | smul a b hb => rw [eval, LinearMap.map_smul, hb, eval]

end PolynomialTerm

variable (rank : sig.SortType → ℕ)

/-- The independent coordinates of every declared variable on a free chart. -/
abbrev PolynomialInputCoordinates (Γ : List sig.SortType) :=
  Σ i : TensorPosition Γ, Fin (rank i.1)

variable {rank}

open Classical in
/-- The coefficient expansion of a multilinear operation is the sum over
all input basis choices, with one factor from each input argument. -/
def operationPolynomial {I : Type u} {a : Arity sig.SortType} (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s))
    (op : TensorOperation R A.carrier a)
    (inputs : ∀ i : TensorPosition a.inputs, Fin (rank i.1) → MvPolynomial I R)
    (j : Fin (rank a.output)) : MvPolynomial I R :=
  letI : Fintype (TensorPosition a.inputs) := Fintype.ofFinite _
  ∑ index : (∀ i : TensorPosition a.inputs, Fin (rank i.1)),
    C ((basis a.output).repr (op (fun i => (basis i.1) (index i))) j) * ∏ i, inputs i (index i)

/-- Expand a typed term in the independent variables of the input chart. -/
def PolynomialTerm.expand (c : k →+* R) (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) :
    ∀ {s}, PolynomialTerm k sig Γ s → Fin (rank s) → MvPolynomial (PolynomialInputCoordinates rank Γ) R
  | _, .var i, j => X ⟨⟨_, i⟩, j⟩
  | _, .total f args, j =>
    operationPolynomial A basis (A.total f) (fun i => PolynomialTerm.expand c A basis (args i)) j
  | _, .quantity q args, j =>
    operationPolynomial A basis (A.quantity q) (fun i => PolynomialTerm.expand c A basis (args i)) j
  | _, .zero _, _ => 0
  | _, .add a b, j => PolynomialTerm.expand c A basis a j + PolynomialTerm.expand c A basis b j
  | _, .smul a b, j => C (c a) * PolynomialTerm.expand c A basis b j


open Classical in
/-- Expand an actual multilinear value in the given bases. This uses every
finite argument position, including the empty product for a nullary operation. -/
theorem operation_coordinates {a : Arity sig.SortType} (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s))
    (op : TensorOperation R A.carrier a)
    (x : ∀ i : TensorPosition a.inputs, A.carrier i.1) (j : Fin (rank a.output)) :
    letI : Fintype (TensorPosition a.inputs) := Fintype.ofFinite _
    (basis a.output).repr (op x) j =
      ∑ index : (∀ i : TensorPosition a.inputs, Fin (rank i.1)),
        (basis a.output).repr (op (fun i => (basis i.1) (index i))) j *
          ∏ i, (basis i.1).repr (x i) (index i) := by
  classical
  letI : Fintype (TensorPosition a.inputs) := Fintype.ofFinite _
  let coordinate : A.carrier a.output →ₗ[R] R :=
    (Finsupp.lapply j).comp (basis a.output).repr.toLinearMap
  let y (i : TensorPosition a.inputs) (q : Fin (rank i.1)) : A.carrier i.1 :=
    (basis i.1).repr (x i) q • (basis i.1) q
  have basisExpansion : (fun i => ∑ q, y i q) = x := funext fun i => (basis i.1).sum_repr (x i)
  have expanded (index : (i : TensorPosition a.inputs) → Fin (rank i.1)) :
      op (fun i => y i (index i)) =
        (∏ i, (basis i.1).repr (x i) (index i)) • op (fun i => (basis i.1) (index i)) :=
    op.map_smul_univ _ _
  calc
    _ = coordinate (op (fun i => ∑ q, y i q)) := congrArg (fun v => coordinate (op v)) basisExpansion.symm
    _ = coordinate (∑ index : (i : TensorPosition a.inputs) → Fin (rank i.1), op (fun i => y i (index i))) :=
      congrArg coordinate (op.map_sum y)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro index _
      rw [expanded index, LinearMap.map_smul, smul_eq_mul, mul_comm]
      rfl


/-- Substituting the coordinates of actual inputs into the coefficients
of a primitive operation recovers the corresponding output coordinate. -/
theorem operationPolynomial_eval {I : Type u} {a : Arity sig.SortType} (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) (op : TensorOperation R A.carrier a)
    (inputs : ∀ i : TensorPosition a.inputs, Fin (rank i.1) → MvPolynomial I R)
    (x : ∀ i : TensorPosition a.inputs, A.carrier i.1) (values : I → R)
    (coordinates : ∀ i j, aeval values (inputs i j) = (basis i.1).repr (x i) j)
    (j : Fin (rank a.output)) :
    aeval values (operationPolynomial A basis op inputs j) = (basis a.output).repr (op x) j := by
  classical
  rw [operationPolynomial, map_sum, operation_coordinates A basis op x j]
  apply Finset.sum_congr rfl
  intro index _
  rw [map_mul, aeval_C, Algebra.algebraMap_self_apply, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact coordinates i (index i)

/-- Read the actual independent coordinates of the supplied input tuple. -/
def PolynomialTerm.inputValues (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s))
    (x : ∀ i : TensorPosition Γ, A.carrier i.1) :
    PolynomialInputCoordinates rank Γ → R :=
  fun i => (basis i.1.1).repr (x i.1) i.2

/-- Evaluation of the expanded polynomial in the coordinates of the
original tuple agrees with evaluation of the actual typed term. -/
theorem PolynomialTerm.eval_expand (c : k →+* R) (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s))
    (x : ∀ i : TensorPosition Γ, A.carrier i.1) {s} (t : PolynomialTerm k sig Γ s) :
    ∀ j, aeval (PolynomialTerm.inputValues A basis x) (t.expand c A basis j) =
      (basis s).repr (t.eval c A x) j := by
  induction t with
  | var i =>
    intro j
    rw [PolynomialTerm.expand, aeval_X, PolynomialTerm.eval]
    rfl
  | total f args ih =>
    intro j
    rw [PolynomialTerm.expand, PolynomialTerm.eval]
    exact operationPolynomial_eval A basis (A.total f) _ _ _ ih j
  | quantity q args ih =>
    intro j
    rw [PolynomialTerm.expand, PolynomialTerm.eval]
    exact operationPolynomial_eval A basis (A.quantity q) _ _ _ ih j
  | zero s =>
    intro j
    simp only [PolynomialTerm.expand, PolynomialTerm.eval, map_zero, Finsupp.zero_apply]
  | add p q hp hq =>
    intro j
    simp only [PolynomialTerm.expand, PolynomialTerm.eval, map_add, hp j, hq j, Finsupp.add_apply]
  | smul a p hp =>
    intro j
    simp only [PolynomialTerm.expand, PolynomialTerm.eval, map_mul, aeval_C,
      Algebra.algebraMap_self_apply, hp j, map_smul, Finsupp.smul_apply, smul_eq_mul]


section ScalarExtension

variable {S : Type u} [CommRing S] [Algebra R S]

/-- The actual basis in each carrier of the scalar extension of the structure. -/
def extendedBasis (A : TensorStructure R sig) (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) :
    ∀ s, Basis (Fin (rank s)) S ((extendStructure R S A).carrier s) :=
  fun s => (basis s).baseChange S

private theorem operationCoefficient_baseChange {a : Arity sig.SortType} (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) (op : TensorOperation R A.carrier a)
    (idx : ∀ i : TensorPosition a.inputs, Fin (rank i.1)) (j : Fin (rank a.output)) :
    (extendedBasis (S := S) A basis a.output).repr
      (extendOperation R A.carrier S op (fun i => extendedBasis A basis i.1 (idx i))) j =
      algebraMap R S ((basis a.output).repr (op (fun i => basis i.1 (idx i))) j) := by
  let x (i : TensorPosition a.inputs) := basis i.1 (idx i)
  let z : (i : TensorPosition a.inputs) → extendCarriers R A.carrier S i.1 :=
    fun i => (1 : S) ⊗ₜ[R] x i
  have h : (fun i => extendedBasis (S := S) A basis i.1 (idx i)) = z := by
    funext i
    exact Basis.baseChange_apply (S := S) (basis i.1) (idx i)
  rw [h]
  have value := extendOperation_unit R A.carrier S op x
  change extendOperation R A.carrier S op z = _ at value
  rw [value]
  change ((basis a.output).baseChange S).repr ((1 : S) ⊗ₜ[R] op x) j = _
  rw [Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]


/-- Polynomial expansion of the primitive operation commutes with an
arbitrary coefficient extension of the actual multilinear map. -/
theorem operationPolynomial_baseChange {I : Type u} {a : Arity sig.SortType} (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s)) (op : TensorOperation R A.carrier a)
    (inputs : ∀ i : TensorPosition a.inputs, Fin (rank i.1) → MvPolynomial I R)
    (j : Fin (rank a.output)) :
    map (algebraMap R S) (operationPolynomial A basis op inputs j) =
      operationPolynomial (extendStructure R S A) (extendedBasis A basis)
        (extendOperation R A.carrier S op) (fun i q => map (algebraMap R S) (inputs i q)) j := by
  classical
  letI : Fintype (TensorPosition a.inputs) := Fintype.ofFinite _
  simp only [operationPolynomial, map_sum, map_mul, map_C, map_prod]
  apply Finset.sum_congr rfl
  intro idx _
  let monomial := ∏ i, map (algebraMap R S) (inputs i (idx i))
  have coefficient := operationCoefficient_baseChange (S := S) A basis op idx j
  exact congrArg (fun r : S => C r * monomial) coefficient.symm

/-- On the extended bases, every expanded term changes coefficients by
the given ring map, including repeated occurrences of an input variable. -/
theorem PolynomialTerm.expand_baseChange (c : k →+* R) (A : TensorStructure R sig)
    (basis : ∀ s, Basis (Fin (rank s)) R (A.carrier s))
    {s} (t : PolynomialTerm k sig Γ s) :
    ∀ j, map (algebraMap R S) (t.expand c A basis j) =
      t.expand ((algebraMap R S).comp c) (extendStructure R S A) (extendedBasis A basis) j := by
  induction t with
  | var i =>
    intro j
    simp only [PolynomialTerm.expand, map_X]
  | total f args ih =>
    intro j
    rw [PolynomialTerm.expand, PolynomialTerm.expand, operationPolynomial_baseChange]
    change operationPolynomial (extendStructure R S A) (extendedBasis A basis)
        (extendOperation R A.carrier S (A.total f)) (fun i q => map (algebraMap R S)
          ((args i).expand c A basis q)) j =
      operationPolynomial (extendStructure R S A) (extendedBasis A basis)
        (extendOperation R A.carrier S (A.total f)) _ j
    congr 1
    funext i q
    exact ih i q
  | quantity q args ih =>
    intro j
    rw [PolynomialTerm.expand, PolynomialTerm.expand, operationPolynomial_baseChange]
    change operationPolynomial (extendStructure R S A) (extendedBasis A basis)
        (extendOperation R A.carrier S (A.quantity q)) (fun i p => map (algebraMap R S)
          ((args i).expand c A basis p)) j =
      operationPolynomial (extendStructure R S A) (extendedBasis A basis)
        (extendOperation R A.carrier S (A.quantity q)) _ j
    congr 1
    funext i p
    exact ih i p
  | zero s =>
    intro j
    simp only [PolynomialTerm.expand, map_zero]
  | add a b ha hb =>
    intro j
    simp only [PolynomialTerm.expand, map_add, ha j, hb j]
  | smul a b hb =>
    intro j
    simp only [PolynomialTerm.expand, map_mul, map_C, RingHom.comp_apply, hb j]

end ScalarExtension


/-- A polynomial Law compares typed terms with the same input context and output sort. -/
structure PolynomialLaw (k : Type u) (sig : Signature.{u}) (Γ : List sig.SortType)
    (s : sig.SortType) where
  left : PolynomialTerm k sig Γ s
  right : PolynomialTerm k sig Γ s

namespace PolynomialLaw

variable {s : sig.SortType} (l : PolynomialLaw k sig Γ s) (c : k →+* R) (A : TensorStructure R sig)

/-- On an affine test scheme, test a Law on all inputs after every
extension of the test scheme's coefficient ring. -/
def Holds : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S]
    (x : ∀ i : TensorPosition Γ, (extendStructure R S A).carrier i.1),
    l.left.eval ((algebraMap R S).comp c) (extendStructure R S A) x =
      l.right.eval ((algebraMap R S).comp c) (extendStructure R S A) x

/-- The residuals of a written Law in the chosen free coordinates. -/
def residual (basis : ∀ t, Basis (Fin (rank t)) R (A.carrier t)) (j : Fin (rank s)) :
    MvPolynomial (PolynomialInputCoordinates rank Γ) R :=
  l.left.expand c A basis j - l.right.expand c A basis j

variable (basis : ∀ t, Basis (Fin (rank t)) R (A.carrier t))

/-- Evaluating a residual on the coordinates after scalar extension gives
the corresponding coordinate of the difference of the two term values. -/
theorem residual_eval {S : Type u} [CommRing S] [Algebra R S]
    (x : ∀ i : TensorPosition Γ, (extendStructure R S A).carrier i.1) (j : Fin (rank s)) :
    let A' := extendStructure R S A
    let b' := extendedBasis (S := S) A basis
    let c' := (algebraMap R S).comp c
    aeval (PolynomialTerm.inputValues A' b' x) (l.residual c A basis j) =
      (b' s).repr (l.left.eval c' A' x - l.right.eval c' A' x) j := by
  let A' := extendStructure R S A
  let b' := extendedBasis (S := S) A basis
  let c' := (algebraMap R S).comp c
  let vals := PolynomialTerm.inputValues A' b' x
  let p := l.residual c A basis j
  have evalMap : aeval (R := S) vals (map (algebraMap R S) p) = aeval (R := R) vals p := by
    simp only [aeval_eq_eval₂Hom, Algebra.algebraMap_self, eval₂Hom_map_hom, RingHom.id_comp]
  change aeval vals p = _
  rw [← evalMap]
  dsimp only [p, residual]
  rw [map_sub, l.left.expand_baseChange, l.right.expand_baseChange, map_sub,
    l.left.eval_expand c' A' b' x j, l.right.eval_expand c' A' b' x j]
  simp only [map_sub, Finsupp.sub_apply]
  rfl

/-- Universal affine-test semantics is equivalent to vanishing of the
actual expanded residuals, by substituting the universal polynomial tuple. -/
theorem holds_iff_residual_eq_zero :
    l.Holds c A ↔ ∀ j, l.residual c A basis j = 0 := by
  constructor
  · intro h j
    let I := PolynomialInputCoordinates rank Γ
    let S := MvPolynomial I R
    let A' := extendStructure R S A
    let b' := extendedBasis (S := S) A basis
    let x (i : TensorPosition Γ) : A'.carrier i.1 :=
      (b' i.1).equivFun.symm (fun n => X (⟨i, n⟩ : I))
    have vals : PolynomialTerm.inputValues A' b' x = (X : I → S) := by
      funext i
      rcases i with ⟨i, n⟩
      change (b' i.1).repr (x i) n = X ⟨i, n⟩
      rw [← Basis.equivFun_apply]
      exact congrFun ((b' i.1).equivFun.apply_symm_apply _) n
    have result := l.residual_eval c A basis x j
    change aeval (PolynomialTerm.inputValues A' b' x) (l.residual c A basis j) =
      (b' s).repr _ j at result
    rw [vals, aeval_X_left_apply, h S x, sub_self, map_zero, Finsupp.zero_apply] at result
    exact result
  · intro h S _ _ x
    let b' := extendedBasis (S := S) A basis
    apply (b' s).repr.injective
    ext j
    have result := l.residual_eval (S := S) c A basis x j
    change aeval (R := R) (PolynomialTerm.inputValues (extendStructure R S A) b' x)
      (l.residual c A basis j) = (b' s).repr _ j at result
    rw [h j, map_zero, map_sub, Finsupp.sub_apply] at result
    exact sub_eq_zero.mp result.symm

/-- In Definition 6.1 the polynomial Law is equivalent to the vanishing
of every monomial coefficient in every output coordinate. -/
theorem holds_iff_all_monomial_coefficients_zero :
    l.Holds c A ↔ ∀ j m, coeff m (l.residual c A basis j) = 0 := by
  rw [l.holds_iff_residual_eq_zero c A basis]
  constructor
  · intro h j m
    rw [h j, coeff_zero]
  · intro h j
    ext m
    rw [coeff_zero]
    exact h j m

end PolynomialLaw

end

end SHIGURE.RealizationFamilies
