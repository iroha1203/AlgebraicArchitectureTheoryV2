import Formal.SHIGURE.Part1.Signature
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Quantity models on a fixed structure

Definition 5.1 interprets the two finite expressions of each Law directly in
the coefficient algebra. The domains and the evaluated state arguments are
fixed before any quantity values are chosen.

## Implementation notes

The coordinate presentation keeps the compiled expressions. This lets
the polynomial and scheme constructions use arbitrary fixed domain types
without depending on a choice of typed syntax. The written model layer
retains the two fixed finite sides and compiles each actual application.
-/

open CategoryTheory

universe u

namespace SHIGURE.Quantities

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

variable {k L R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- Evaluate with an arbitrary assignment of values to the quantity inputs. -/
def eval (q : L → R) : Expression k L → R
  | .scalar a => algebraMap k R a
  | .quantity x => q x
  | .add l r => l.eval q + r.eval q
  | .neg x => -x.eval q
  | .mul l r => l.eval q * r.eval q

/-- Direct evaluation commutes with every coefficient algebra map. -/
theorem eval_map (f : R →ₐ[k] S) (q : L → R) (t : Expression k L) :
    t.eval (f ∘ q) = f (t.eval q) := by
  induction t <;> simp [eval, Function.comp_apply, *]

/-- Rename the quantity inputs of an expression, retaining its scalar literals and operations. -/
def rename {k L M : Type u} (f : L → M) : Expression k L → Expression k M
  | .scalar a => .scalar a
  | .quantity x => .quantity (f x)
  | .add l r => .add (rename f l) (rename f r)
  | .neg x => .neg (rename f x)
  | .mul l r => .mul (rename f l) (rename f r)

/-- Renaming the inputs gives the same value as reading the original inputs through the renaming. -/
theorem eval_rename {M : Type u} (f : L → M) (q : M → R) (t : Expression k L) :
    (t.rename f).eval q = t.eval (q ∘ f) := by
  induction t <;> simp [rename, eval, Function.comp_apply, *]

/-- Renaming twice agrees with renaming along the composite. -/
theorem rename_comp {k L M N : Type u} (f : L → M) (g : M → N) (t : Expression k L) :
    (t.rename f).rename g = t.rename (g ∘ f) := by
  induction t <;> simp [rename, Function.comp_apply, *]

end Expression

/-- A fixed state structure with its small quantity domains and the Law input
families. Each side is the literal expression at the specified Law input. -/
structure Presentation (k : Type u) {sig : Signature.{u}} (A : Structure sig) where
  /-- The quantity names. -/
  Quantity : Type u
  /-- The fixed domain for a quantity. -/
  Domain : Quantity → Type u
  /-- The required Law names. -/
  Law : Type u
  /-- The inputs at which the Law is required. -/
  Input : Law → Type u
  /-- The left expression at a specified input. -/
  left : ∀ l, Input l → Expression k (Σ j, Domain j)
  /-- The right expression at a specified input. -/
  right : ∀ l, Input l → Expression k (Σ j, Domain j)

namespace Presentation

variable {k : Type u} [CommRing k] {sig : Signature.{u}} {A : Structure sig} (P : Presentation k A)
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- The names of the coordinates keep the quantity tag as well as its argument. -/
abbrev Coordinate := Σ j, P.Domain j

/-- A candidate consists of arbitrary functions on the fixed quantity domains. -/
abbrev Candidate (R : Type u) := ∀ j, P.Domain j → R

/-- Every required equality holds at every designated input. -/
def Holds (q : P.Candidate R) : Prop :=
  ∀ l e, (P.left l e).eval (fun x => q x.1 x.2) = (P.right l e).eval (fun x => q x.1 x.2)

/-- The set of quantity models over the given coefficient algebra. -/
abbrev Model (R : Type u) [CommRing R] [Algebra k R] := {q : P.Candidate R // P.Holds q}

/-- Change the coefficients of a model by postcomposing each quantity function. -/
def map (f : R →ₐ[k] S) (q : P.Model R) : P.Model S :=
  ⟨fun j x => f (q.val j x), by
    intro l e
    change (P.left l e).eval (f ∘ fun x => q.val x.1 x.2) =
      (P.right l e).eval (f ∘ fun x => q.val x.1 x.2)
    rw [Expression.eval_map, Expression.eval_map, q.property l e]⟩

/-- The functor in Definition 5.1, obtained from direct expression evaluation. -/
def modelFunctor : CommAlgCat.{u} k ⥤ Type u where
  obj R := P.Model R
  map f := ↾P.map f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

end Presentation

end SHIGURE.Quantities
