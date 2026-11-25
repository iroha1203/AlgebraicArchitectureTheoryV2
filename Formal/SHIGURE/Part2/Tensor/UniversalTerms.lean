import Formal.SHIGURE.Part2.Tensor.CoefficientPoints
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Universal inputs for equations of terms

The first half of Proposition 4.10 uses finite sums of pure tensors as
inputs. A separate indeterminate records each coefficient in those sums.
The terms retain strict bindings and may use an input more than once.

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
inductive TensorTerm (sig : Signature.{u}) : List sig.SortType → sig.SortType → Type u
  | var {Γ : List sig.SortType} {s : sig.SortType} : Var Γ s → TensorTerm sig Γ s
  | total {Γ : List sig.SortType} (op : sig.Total) :
      (∀ i : TensorPosition (sig.totalArity op).inputs, TensorTerm sig Γ i.1) →
      TensorTerm sig Γ (sig.totalArity op).output
  | quantity {Γ : List sig.SortType} (q : sig.Quantity) :
      (∀ i : TensorPosition (sig.quantityArity q).inputs, TensorTerm sig Γ i.1) →
      TensorTerm sig Γ (sig.quantityArity q).output
  | letBind {Γ : List sig.SortType} {s t : sig.SortType} :
      TensorTerm sig Γ s → TensorTerm sig (s :: Γ) t → TensorTerm sig Γ t

namespace TensorTerm

variable {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}
/-- Whether a written Part I term uses only the available total primitives. -/
def usesTotalPrimitives : {Γ : List sig.SortType} → {s : sig.SortType} → Term sig Γ s → Prop
  | _, _, .var _ => True
  | _, _, .app (.total _) args => ∀ i : TensorPosition _, usesTotalPrimitives (args i.2)
  | _, _, .app (.quantity _) args => ∀ i : TensorPosition _, usesTotalPrimitives (args i.2)
  | _, _, .app (.partialOp _) _ => False
  | _, _, .letBind init body => usesTotalPrimitives init ∧ usesTotalPrimitives body

/-- Interpret the total fragment of the existing syntax without removing any bindings. -/
def ofNative : {Γ : List sig.SortType} → {s : sig.SortType} → (t : Term sig Γ s) →
    usesTotalPrimitives t → TensorTerm sig Γ s
  | _, _, .var i, _ => .var i
  | _, _, .app (.total f) args, h => .total f (fun i => ofNative (args i.2) (h i))
  | _, _, .app (.quantity q) args, h => .quantity q (fun i => ofNative (args i.2) (h i))
  | _, _, .app (.partialOp _) _, h => h.elim
  | _, _, .letBind init body, h => .letBind (ofNative init h.1) (ofNative body h.2)

/-- Read the typed tensor term in the original Part I syntax. -/
def toNative : {Γ : List sig.SortType} → {s : sig.SortType} → TensorTerm sig Γ s → Term sig Γ s
  | _, _, .var i => .var i
  | _, _, .total f args => .app (.total f) (fun i => toNative (args ⟨_, i⟩))
  | _, _, .quantity q args => .app (.quantity q) (fun i => toNative (args ⟨_, i⟩))
  | _, _, .letBind init body => .letBind (toNative init) (toNative body)

/-- Each typed tensor term is written using only the native total primitives. -/
theorem toNative_usesTotalPrimitives (t : TensorTerm sig Γ s) : usesTotalPrimitives t.toNative := by
  induction t with
  | var _ => trivial
  | total _ _ ih => exact fun i => ih i
  | quantity _ _ ih => exact fun i => ih i
  | letBind _ _ hi hb => exact ⟨hi, hb⟩

/-- A term headed by a partial operation does not belong to the total fragment. -/
theorem not_usesTotalPrimitives_partial (p : sig.Partial)
    (args : ∀ {r}, Var (sig.partialArity p).inputs r → Term sig Γ r) :
    ¬ usesTotalPrimitives (Term.app (.partialOp p) args) :=
  not_false

/-- Every written total term is recovered verbatim from the tensor syntax. -/
theorem toNative_ofNative (t : Term sig Γ s) (h : usesTotalPrimitives t) :
    (ofNative t h).toNative = t := by
  induction t with
  | var i => rfl
  | app op args ih =>
    cases op with
    | partialOp p => exact h.elim
    | total f =>
      simp only [ofNative, toNative]
      congr 1
      funext j
      funext i
      exact ih i (h ⟨j, i⟩)
    | quantity q =>
      simp only [ofNative, toNative]
      congr 1
      funext j
      funext i
      exact ih i (h ⟨j, i⟩)
  | letBind init body hi hb =>
    simp only [ofNative, toNative, hi h.1, hb h.2]

variable {R : Type u} [CommRing R]

/-- Extend a typed input tuple with its newly bound head value. -/
private def bindInput {X : sig.SortType → Type u} {s : sig.SortType} (x : X s)
    (xs : ∀ i : TensorPosition Γ, X i.1) : ∀ i : TensorPosition (s :: Γ), X i.1
  | ⟨_, .here⟩ => x
  | ⟨_, .there i⟩ => xs ⟨_, i⟩

/-- A family of state maps sends the bound value and every earlier input to their images. -/
private theorem bindInput_map {X Y : sig.SortType → Type u} {s : sig.SortType}
    (f : ∀ s, X s → Y s) (x : X s) (xs : ∀ i : TensorPosition Γ, X i.1) :
    (fun i => f i.1 (bindInput x xs i)) = bindInput (f s x) (fun i => f i.1 (xs i)) := by
  funext i
  obtain ⟨_, i⟩ := i
  cases i <;> rfl

/-- Evaluate the typed term using actual primitive maps and strict binding in the input tuple. -/
def eval (A : TensorStructure R sig) :
    {Γ : List sig.SortType} → (xs : ∀ i : TensorPosition Γ, A.carrier i.1) →
      {s : sig.SortType} → TensorTerm sig Γ s → A.carrier s
  | _, xs, _, .var i => xs ⟨_, i⟩
  | _, xs, _, .total op args => A.total op (fun i => (args i).eval A xs)
  | _, xs, _, .quantity q args => A.quantity q (fun i => (args i).eval A xs)
  | _, xs, _, .letBind init body => body.eval A (bindInput (X := fun s => (A.carrier s : Type u)) (init.eval A xs) xs)

/-- The structure-preserving maps commute with evaluation of finite terms. -/
theorem eval_hom {A B : TensorStructure R sig} (f : TensorStructure.Hom A B)
    (xs : ∀ i : TensorPosition Γ, A.carrier i.1) (t : TensorTerm sig Γ s) :
    f.onSort s (t.eval A xs) = t.eval B (fun i => f.onSort i.1 (xs i)) := by
  induction t with
  | var i => rfl
  | total op args ih =>
    exact (f.preservesTotal op _).trans (congrArg (B.total op) (funext fun i => ih i xs))
  | quantity q args ih =>
    exact (f.preservesQuantity q _).trans (congrArg (B.quantity q) (funext fun i => ih i xs))
  | letBind init body hi hb =>
    simp only [eval]
    rw [hb, bindInput_map (fun s x => f.onSort s x), hi]

/-- For the native evaluation relation, interpret precisely the tensor carrier and total primitives. -/
def nativeStructure (A : TensorStructure R sig) : Structure sig where
  carrier s := A.carrier s
  total f xs := A.total f (fun i => xs.get i.2)
  relation _ := ∅
  partialDomain _ := ∅
  partialValue _ x := False.elim x.property
  quantity q xs := A.quantity q (fun i => xs.get i.2)

/-- The tensor evaluator computes the value of the same written Part I term. -/
theorem native_evaluates (A : TensorStructure R sig) (t : TensorTerm sig Γ s)
    (xs : ∀ i : TensorPosition Γ, A.carrier i.1) :
    t.toNative.Evaluates (nativeStructure A) ⟨fun i => xs ⟨_, i⟩⟩ (t.eval A xs) := by
  induction t with
  | var i => rfl
  | total f args ih =>
    refine ⟨⟨fun i => (args ⟨_, i⟩).eval A xs⟩, ?_, ?_⟩
    · intro r i
      exact ih ⟨r, i⟩ xs
    · exact ((nativeStructure A).graph_total_iff f _ _).mpr rfl
  | quantity q args ih =>
    refine ⟨⟨fun i => (args ⟨_, i⟩).eval A xs⟩, ?_, ?_⟩
    · intro r i
      exact ih ⟨r, i⟩ xs
    · exact ((nativeStructure A).graph_quantity_iff q _ _).mpr rfl
  | @letBind Γ sort _ init body hi hb =>
    refine ⟨init.eval A xs, hi xs, ?_⟩
    let ys := bindInput (X := fun s => (A.carrier s : Type u)) (init.eval A xs) xs
    let env : Assignment (nativeStructure A).carrier Γ := ⟨fun i => xs ⟨_, i⟩⟩
    have harg : (⟨fun i => ys ⟨_, i⟩⟩ : Assignment (nativeStructure A).carrier (sort :: Γ)) =
        Assignment.cons (s := sort) (init.eval A xs) env := by
      apply Assignment.ext
      intro s i
      cases i <;> rfl
    rw [← harg]
    exact hb ys

/-- The translated evaluator realizes the original value of every total Part I term. -/
theorem ofNative_evaluates (A : TensorStructure R sig) (t : Term sig Γ s)
    (h : usesTotalPrimitives t) (xs : ∀ i : TensorPosition Γ, A.carrier i.1) :
    t.Evaluates (nativeStructure A) ⟨fun i => xs ⟨_, i⟩⟩ ((ofNative t h).eval A xs) := by
  simpa only [toNative_ofNative] using native_evaluates A (ofNative t h) xs

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
    rw [funext (fun i => ih i xs), extendOperation_unit]
    rfl
  | quantity q args ih =>
    change extendOperation k A.carrier R (A.quantity q)
      (fun i => (args i).eval (extendStructure k R A) (fun j => (1 : R) ⊗ₜ[k] xs j)) = _
    rw [funext (fun i => ih i xs), extendOperation_unit]
    rfl
  | letBind init body hi hb =>
    simp only [TensorTerm.eval]
    rw [hi, ← TensorTerm.bindInput_map (fun s (x : A.carrier s) => (1 : R) ⊗ₜ[k] x), hb]

/-- The tower comparison applied to a unit tensor computes the direct coefficient substitution. -/
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
    choose n r m hx using (fun i => TensorProduct.exists_sum_tmul_eq (x i))
    let f : MvPolynomial ((i : TensorPosition Γ) × Fin (n i)) k →ₐ[k] R :=
      MvPolynomial.aeval (fun j => r j.1 j.2)
    have hsub (i : TensorPosition Γ) : mapCoefficients f (formalInput A n m i) = x i := by
      rw [formalInput, map_sum]
      simp only [mapCoefficients_tmul, f, MvPolynomial.aeval_X]
      exact (hx i).symm
    have he := congrArg (mapCoefficients f) (sub_eq_zero.mp (hall n m))
    rw [t.eval_mapCoefficients, t'.eval_mapCoefficients, funext hsub] at he
    exact he
  · intro hall n m
    exact sub_eq_zero.mpr (hall _ (formalInput A n m))

end SHIGURE.TensorRealization
