import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Rename
import Formal.Util.AssertStandardAxioms

/-!
# Finite primitive evaluation of polynomial expressions

This closed arithmetic fragment is declared over raw carriers before choosing
an interpretation. Its queries ask for one coefficient image, variable image,
zero, one, sum, or product. Expressions contain no arbitrary functions or
propositions. Evaluation and its finite query support are defined by recursion.
The support theorem compares arbitrary point tables, so no completed ring or
homomorphism is hidden in its assumptions.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentPolynomialExpressions

universe u v w

variable {C : Type u} {k : Type v} {R : Type w}

/-- Finite polynomial data needs only raw carriers and a candidate zero, before any ring is selected. -/
def Sparse (C : Type u) (k : Type v) (z : k) : Type (max u v) :=
  letI : Zero k := ⟨z⟩
  (C →₀ ℕ) →₀ k

/-- Native polynomial data is exactly the sparse value type at the ring's primitive zero. -/
def sparseEquiv [CommSemiring k] : MvPolynomial C k ≃ Sparse C k (0 : k) := Equiv.refl _

/-- Assemble a native polynomial after the single candidate-zero equality is established. -/
def Sparse.toNative [CommSemiring k] {z : k} (hz : z = 0) (p : Sparse C k z) :
    MvPolynomial C k := sparseEquiv.symm (hz ▸ p)

/-- A native polynomial is recovered exactly from its finite sparse value. -/
theorem Sparse.toNative_read [CommSemiring k] (p : MvPolynomial C k) :
    Sparse.toNative rfl (sparseEquiv p) = p := rfl

/-- Re-reading sparse data recovers every coefficient and exponent, after the required zero transport. -/
theorem Sparse.read_toNative [CommSemiring k] {z : k} (hz : z = 0) (p : Sparse C k z) :
    sparseEquiv (Sparse.toNative hz p) = (hz ▸ p) := rfl

/-- The original sparse value survives assembly even when its candidate zero was propositionally identified. -/
theorem Sparse.read_toNative_heq [CommSemiring k] {z : k} (hz : z = 0) (p : Sparse C k z) :
    HEq (sparseEquiv (Sparse.toNative hz p)) p := by
  cases hz
  rfl

/-- The six primitive arithmetic roles, with raw arguments and no chosen interpretation. -/
inductive Query (C : Type u) (k : Type v) (R : Type w) where
  /-- The image of one source coefficient. -/
  | coefficient (a : k)
  /-- The image of one source variable. -/
  | variable (c : C)
  /-- The target zero. -/
  | zero
  /-- The target one. -/
  | one
  /-- A single target addition. -/
  | add (a b : R)
  /-- A single target multiplication. -/
  | mul (a b : R)

/-- Every cell contains one value of the declared raw target carrier. -/
abbrev Table (C : Type u) (k : Type v) (R : Type w) := Query C k R → R

/-- Finite polynomial syntax using only primitive arithmetic and the two named inputs. -/
inductive Expr (C : Type u) (k : Type v) where
  /-- Source coefficient literal, whose image is queried. -/
  | coefficient (a : k)
  /-- Source variable name, whose image is queried. -/
  | variable (c : C)
  /-- Target additive unit. -/
  | zero
  /-- Target multiplicative unit. -/
  | one
  /-- Finite sum of two subexpressions. -/
  | add (a b : Expr C k)
  /-- Finite product of two subexpressions. -/
  | mul (a b : Expr C k)

/-- Closed formulas over one primitive polynomial-evaluation table.  Every
truth-bearing leaf is an exact table cell; no proposition or completed
polynomial equality can be inserted into the syntax. -/
inductive CellFormula (C : Type u) (k : Type v) (R : Type w) where
  | cell (q : Query C k R) (value : R)
  | truth
  | and (left right : CellFormula C k R)

/-- Evaluate a closed formula against a primitive polynomial table. -/
def CellFormula.evaluate (t : Table C k R) : CellFormula C k R → Prop
  | .cell q value => t q = value
  | .truth => True
  | .and left right => left.evaluate t ∧ right.evaluate t

/-- Finite conjunction of polynomial-table cells. -/
def CellFormula.allList {α : Type*} (items : List α)
    (formula : α → CellFormula C k R) : CellFormula C k R :=
  match items with
  | [] => .truth
  | item :: rest => .and (formula item) (CellFormula.allList rest formula)

@[simp] theorem CellFormula.evaluate_allList {α : Type*} (t : Table C k R)
    (items : List α) (formula : α → CellFormula C k R) :
    (CellFormula.allList items formula).evaluate t ↔
      ∀ item ∈ items, (formula item).evaluate t := by
  induction items with
  | nil => simp [CellFormula.allList, CellFormula.evaluate]
  | cons item items ih => simp [CellFormula.allList, CellFormula.evaluate, ih]

/-- Exact polynomial-table queries read by a closed cell formula. -/
noncomputable def CellFormula.support : CellFormula C k R → Finset (Query C k R)
  | .cell q _ => {q}
  | .truth => ∅
  | .and left right => by
      classical
      exact left.support ∪ right.support

/-- Agreement on the named polynomial cells preserves formula evaluation. -/
theorem CellFormula.evaluate_iff_of_support (first second : Table C k R)
    (formula : CellFormula C k R)
    (agree : ∀ q ∈ formula.support, first q = second q) :
    formula.evaluate first ↔ formula.evaluate second := by
  classical
  induction formula with
  | cell q value =>
      change first q = value ↔ second q = value
      rw [agree q (by simp [CellFormula.support])]
  | truth => rfl
  | and left right ihLeft ihRight =>
      exact and_congr
        (ihLeft (fun q hq => agree q (by simp [CellFormula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [CellFormula.support, hq])))

/-- Evaluate through primitive cells; the table need not satisfy any algebraic laws. -/
def evaluate (t : Table C k R) : Expr C k → R
  | .coefficient a => t (.coefficient a)
  | .variable c => t (.variable c)
  | .zero => t .zero
  | .one => t .one
  | .add a b => t (.add (evaluate t a) (evaluate t b))
  | .mul a b => t (.mul (evaluate t a) (evaluate t b))

/-- The final primitive query whose response is the value of an expression.
Its arguments are the recursively evaluated immediate subexpressions. -/
def rootQuery (t : Table C k R) : Expr C k → Query C k R
  | .coefficient a => .coefficient a
  | .variable c => .variable c
  | .zero => .zero
  | .one => .one
  | .add a b => .add (evaluate t a) (evaluate t b)
  | .mul a b => .mul (evaluate t a) (evaluate t b)

theorem evaluate_eq_rootQuery (t : Table C k R) (e : Expr C k) :
    evaluate t e = t (rootQuery t e) := by
  cases e <;> rfl

/-- The finite queries actually needed by an expression, including all intermediate arithmetic. -/
noncomputable def support (t : Table C k R) : Expr C k → Finset (Query C k R)
  | .coefficient a => {.coefficient a}
  | .variable c => {.variable c}
  | .zero => {.zero}
  | .one => {.one}
  | .add a b => by
    classical
    exact insert (.add (evaluate t a) (evaluate t b)) (support t a ∪ support t b)
  | .mul a b => by
    classical
    exact insert (.mul (evaluate t a) (evaluate t b)) (support t a ∪ support t b)

theorem rootQuery_mem_support (t : Table C k R) (e : Expr C k) :
    rootQuery t e ∈ support t e := by
  classical
  cases e <;> simp [rootQuery, support]

/-- One expression equation as a finite table-cell formula.  The first
conjunct fixes every recursively used query, while the last cell requires the
root response to be the expected value. -/
noncomputable def expressionFormula (t : Table C k R) (e : Expr C k)
    (expected : R) : CellFormula C k R :=
  .and
    (CellFormula.allList (support t e).toList (fun q => .cell q (t q)))
    (.cell (rootQuery t e) expected)

@[simp] theorem expressionFormula_evaluate (t : Table C k R) (e : Expr C k)
    (expected : R) :
    (expressionFormula t e expected).evaluate t ↔ evaluate t e = expected := by
  classical
  simp [expressionFormula, CellFormula.evaluate, evaluate_eq_rootQuery]

/-- Agreement on the finite primitive support is sufficient for equality of evaluation. -/
theorem evaluate_eq_of_support (t s : Table C k R) (e : Expr C k)
    (h : ∀ q ∈ support t e, t q = s q) : evaluate t e = evaluate s e := by
  classical
  induction e with
  | coefficient a => exact h (.coefficient a) (by simp [support])
  | «variable» c => exact h (.variable c) (by simp [support])
  | zero => exact h .zero (by simp [support])
  | one => exact h .one (by simp [support])
  | add a b ha hb =>
    have h1 := ha (fun q hq => h q (by simp [support, hq]))
    have h2 := hb (fun q hq => h q (by simp [support, hq]))
    dsimp only [evaluate]
    rw [← h1, ← h2]
    exact h _ (by simp [support])
  | mul a b ha hb =>
    have h1 := ha (fun q hq => h q (by simp [support, hq]))
    have h2 := hb (fun q hq => h q (by simp [support, hq]))
    dsimp only [evaluate]
    rw [← h1, ← h2]
    exact h _ (by simp [support])

/-- The expression formula remains sound on any comparison table satisfying
its exact finite cells.  This is the bridge from the formula syntax to the
recursive `evaluate_eq_of_support` theorem. -/
theorem evaluate_eq_expected_of_expressionFormula (t s : Table C k R)
    (e : Expr C k) (expected : R)
    (h : (expressionFormula t e expected).evaluate s) :
    evaluate s e = expected := by
  classical
  have hcells : ∀ q ∈ support t e, s q = t q := by
    intro q hq
    exact (CellFormula.evaluate_allList s _ _).1 h.1 q
      (by simpa using hq)
  have hagree : ∀ q ∈ support t e, t q = s q :=
    fun q hq => (hcells q hq).symm
  have heval := evaluate_eq_of_support t s e hagree
  have hroot : t (rootQuery t e) = expected :=
    (hagree _ (rootQuery_mem_support t e)).trans h.2
  calc
    evaluate s e = evaluate t e := heval.symm
    _ = t (rootQuery t e) := evaluate_eq_rootQuery t e
    _ = expected := hroot

/-- Powers are finite multiplication expressions, including the exponent-zero unit. -/
def Expr.pow (e : Expr C k) : ℕ → Expr C k
  | 0 => .one
  | n + 1 => .mul (e.pow n) e

/-- A finite sum is syntax, not a precomputed completed polynomial evaluation. -/
def Expr.sum (es : List (Expr C k)) : Expr C k := es.foldr Expr.add .zero

/-- A finite product is syntax with explicit primitive multiplications. -/
def Expr.prod (es : List (Expr C k)) : Expr C k := es.foldr Expr.mul .one

/-- Read native arithmetic and two point maps into the six declared primitive roles. -/
def nativeTable [CommSemiring k] [CommSemiring R] (h : k →+* R) (x : C → R) : Table C k R
  | .coefficient a => h a
  | .variable c => x c
  | .zero => 0
  | .one => 1
  | .add a b => a + b
  | .mul a b => a * b

/-- The recursively constructed power agrees with native exponentiation. -/
theorem evaluate_pow [CommSemiring k] [CommSemiring R] (h : k →+* R) (x : C → R)
    (e : Expr C k) (n : ℕ) :
    evaluate (nativeTable h x) (e.pow n) = (evaluate (nativeTable h x) e) ^ n := by
  induction n with
  | zero => simp [Expr.pow, evaluate, nativeTable]
  | succ n hn =>
    simpa [Expr.pow, evaluate, nativeTable, pow_succ] using
      (congrArg (fun a => a * evaluate (nativeTable h x) e) hn)

/-- A finite sum expression evaluates to the finite sum of its values. -/
theorem evaluate_sum [CommSemiring k] [CommSemiring R] (h : k →+* R) (x : C → R)
    (es : List (Expr C k)) :
    evaluate (nativeTable h x) (Expr.sum es) = (es.map (evaluate (nativeTable h x))).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simpa [Expr.sum, evaluate, nativeTable] using
      (congrArg (fun a => evaluate (nativeTable h x) e + a) ih)

/-- A finite product expression evaluates to the finite product of its values. -/
theorem evaluate_prod [CommSemiring k] [CommSemiring R] (h : k →+* R) (x : C → R)
    (es : List (Expr C k)) :
    evaluate (nativeTable h x) (Expr.prod es) = (es.map (evaluate (nativeTable h x))).prod := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simpa [Expr.prod, evaluate, nativeTable] using
      (congrArg (fun a => evaluate (nativeTable h x) e * a) ih)

/-- Compile one finite exponent vector to multiplication and powers of named variables. -/
noncomputable def monomial (m : C →₀ ℕ) : Expr C k :=
  Expr.prod (m.support.toList.map (fun c => (Expr.variable c).pow (m c)))

/-- Compile the finite canonical support of a native polynomial; the list is derived, not input data. -/
noncomputable def compile [CommSemiring k] (p : MvPolynomial C k) : Expr C k :=
  Expr.sum (p.support.toList.map (fun m => .mul (.coefficient (p.coeff m)) (monomial m)))

/-- The compiled exponent vector has exactly its native monomial evaluation. -/
theorem evaluate_monomial [CommSemiring k] [CommSemiring R] (h : k →+* R) (x : C → R)
    (m : C →₀ ℕ) :
    evaluate (nativeTable h x) (monomial m) = m.prod (fun c n => x c ^ n) := by
  simp [monomial, evaluate_prod, List.map_map, evaluate_pow, evaluate, nativeTable, Finsupp.prod]

/-- Compiled finite syntax evaluates to the full native polynomial algebra map. -/
theorem evaluate_compile [CommSemiring k] [CommSemiring R] (h : k →+* R) (x : C → R)
    (p : MvPolynomial C k) :
    evaluate (nativeTable h x) (compile p) = MvPolynomial.eval₂Hom h x p := by
  rw [compile, evaluate_sum]
  simp only [List.map_map, Function.comp_apply, evaluate, nativeTable, evaluate_monomial,
    Finset.sum_map_toList]
  rfl

/-- Every native polynomial evaluation follows from finitely many coefficient, variable, and arithmetic cells. -/
theorem polynomial_finite_support [CommSemiring k] [CommSemiring R]
    (h : k →+* R) (x : C → R) (p : MvPolynomial C k) :
    ∃ F : Finset (Query C k R), ∀ t : Table C k R,
      (∀ q ∈ F, nativeTable h x q = t q) →
        evaluate t (compile p) = MvPolynomial.eval₂Hom h x p := by
  refine ⟨support (nativeTable h x) (compile p), fun t ht => ?_⟩
  exact (evaluate_eq_of_support _ _ _ ht).symm.trans (evaluate_compile h x p)

/-- Forward coefficient change followed by coordinate rename uses the same finite expression evaluator. -/
theorem evaluate_rename_map [CommSemiring k] [CommSemiring R]
    {D : Type*} (h : k →+* R) (c : C → D) (p : MvPolynomial C k) :
    evaluate (nativeTable (MvPolynomial.C.comp h) (fun x => MvPolynomial.X (c x))) (compile p) =
      MvPolynomial.rename c (MvPolynomial.map h p) := by
  rw [evaluate_compile]
  have he : MvPolynomial.eval₂Hom (MvPolynomial.C.comp h) (fun x => MvPolynomial.X (c x)) =
      (MvPolynomial.rename c).toRingHom.comp (MvPolynomial.map h) := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  exact RingHom.congr_fun he p

end AAT.AG.LocalSemanticReconstruction.IndependentPolynomialExpressions

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentPolynomialExpressions
