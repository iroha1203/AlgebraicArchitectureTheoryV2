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

end Expression

/-- A named quantity application with its arguments in the Law's input context. -/
abbrev DeclaredApplication (sig : Signature.{u}) (Γ : List sig.SortType) :=
  Σ j : QuantityDeclaration sig, Substitution sig j.operation.arity.inputs Γ

/-- The two written sides of an equality in its designated coefficient type. -/
abbrev WrittenCoefficientEquation (k : Type u) (sig : Signature.{u}) (Γ : List sig.SortType) :=
  Expression k (DeclaredApplication sig Γ) × Expression k (DeclaredApplication sig Γ)

end SHIGURE.Quantities
