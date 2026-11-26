import Formal.SHIGURE.Part1.Substitution

/-! # Syntax of equations with external coefficients

A written equality names its primitive quantities and retains their
typed argument terms. Coefficient literals belong to the declared
coefficient type and need no representatives in native state carriers.
-/

universe u

namespace SHIGURE.Quantities

/-- The primitive name of a varying quantity, with its declared total or partial profile. -/
inductive QuantityDeclaration (sig : Signature.{u})
  | total (name : sig.Quantity)
  | partialOp (name : sig.Partial)

namespace QuantityDeclaration

variable {sig : Signature.{u}}

/-- Read the quantity as the operation declared in the original signature. -/
def operation : QuantityDeclaration sig → Operation sig
  | .total name => .quantity name
  | .partialOp name => .partialOp name

end QuantityDeclaration

/-- A finite coefficient expression with one variable for each quantity application. -/
inductive Expression (k L : Type u)
  /-- A coefficient from the base ring. -/
  | scalar (a : k)
  /-- A quantity application identified by an occurrence or a compiled coordinate. -/
  | quantity (x : L)
  /-- Addition of two expressions. -/
  | add (left right : Expression k L)
  /-- Additive inverse. -/
  | neg (arg : Expression k L)
  /-- Multiplication of two expressions. -/
  | mul (left right : Expression k L)

namespace Expression

/-- Rename the quantity inputs of an expression, retaining its scalar literals and operations. -/
def rename {k L M : Type u} (f : L → M) : Expression k L → Expression k M
  | .scalar a => .scalar a
  | .quantity x => .quantity (f x)
  | .add l r => .add (rename f l) (rename f r)
  | .neg x => .neg (rename f x)
  | .mul l r => .mul (rename f l) (rename f r)

variable {k J K N : Type u}

/-- The variable occurrences that the expression actually uses. -/
def occurrences : Expression k J → Set J
  | .scalar _ => ∅
  | .quantity a => {a}
  | .add p q | .mul p q => p.occurrences ∪ q.occurrences
  | .neg p => p.occurrences

/-- Compile only the variables used by the expression. -/
def compile : (p : Expression k J) → (∀ a ∈ p.occurrences, K) → Expression k K
  | .scalar r, _ => .scalar r
  | .quantity a, f => .quantity (f a (Set.mem_singleton _))
  | .add p q, f => .add (p.compile fun a h => f a (Or.inl h)) (q.compile fun a h => f a (Or.inr h))
  | .mul p q, f => .mul (p.compile fun a h => f a (Or.inl h)) (q.compile fun a h => f a (Or.inr h))
  | .neg p, f => .neg (p.compile f)

/-- All coefficient literals and operations are unchanged by compiling and then renaming. -/
theorem rename_compile (p : Expression k J) (f : ∀ a ∈ p.occurrences, K) (g : K → N) :
    (p.compile f).rename g = p.compile (fun a h => g (f a h)) := by
  induction p <;> simp [compile, rename, *]
  rfl

/-- Compiling along a function defined on every occurrence is ordinary renaming. -/
theorem compile_eq_rename (p : Expression k J) (f : J → K) :
    p.compile (fun a _ => f a) = p.rename f := by
  induction p <;> simp [compile, rename, *]
  assumption

end Expression

/-- A named quantity application with its arguments in the Law's input context. -/
abbrev DeclaredApplication (sig : Signature.{u}) (Γ : List sig.SortType) :=
  Σ j : QuantityDeclaration sig, Substitution sig j.operation.arity.inputs Γ

/-- The two written sides of an equality in its designated coefficient type. -/
abbrev WrittenCoefficientEquation (k : Type u) (sig : Signature.{u}) (Γ : List sig.SortType) :=
  Expression k (DeclaredApplication sig Γ) × Expression k (DeclaredApplication sig Γ)

/-- One finite written equation with its original coefficient type. -/
abbrev RegisteredCoefficientEquation (sig : Signature.{u}) (Γ : List sig.SortType) :=
  Σ k : Type u, WrittenCoefficientEquation k sig Γ

namespace RegisteredCoefficientEquation

/-- Read a registered equation at its own coefficient type. -/
noncomputable def atType {sig : Signature.{u}} {Γ : List sig.SortType}
    (e : RegisteredCoefficientEquation sig Γ) (k : Type u) : Option (WrittenCoefficientEquation k sig Γ) := by
  classical
  exact if same : e.1 = k then some (same ▸ e.2) else none

@[simp]
theorem atType_mk {sig : Signature.{u}} {Γ : List sig.SortType} (k : Type u)
    (e : WrittenCoefficientEquation k sig Γ) : atType ⟨k, e⟩ k = some e := by
  classical
  simp [atType]

theorem eq_of_atType {sig : Signature.{u}} {Γ : List sig.SortType}
    {e : RegisteredCoefficientEquation sig Γ} {k : Type u} {w : WrittenCoefficientEquation k sig Γ}
    (read : e.atType k = some w) : e = ⟨k, w⟩ := by
  classical
  obtain ⟨original, writing⟩ := e
  by_cases same : original = k
  · subst original
    rw [atType_mk] at read
    cases Option.some.inj read
    rfl
  · simp [atType, same] at read

end RegisteredCoefficientEquation

end SHIGURE.Quantities
