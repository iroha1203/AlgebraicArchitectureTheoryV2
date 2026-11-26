import Formal.SHIGURE.Part1.Substitution
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Quantity models on a fixed structure

Definition 5.1 interprets the two finite expressions of each Law directly in
the coefficient algebra. The domains and the evaluated state arguments are
fixed before any quantity values are chosen.
-/

open CategoryTheory

universe u

namespace SHIGURE.Quantities

/-- A finite coefficient expression with one variable for each quantity application. -/
inductive Expression (k L : Type u)
  /-- A coefficient from the base ring. -/
  | scalar (a : k)
  /-- An application of a named quantity to an already evaluated state input. -/
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

/-- Apply a quantity to a typed state term at an input where that term is defined.
The indexing function records the quantity's tag and its chosen domain element. -/
noncomputable def ofStateTerm {sig : Signature.{u}} {A : Structure sig} {Γ : List sig.SortType}
    {s : sig.SortType} (index : A.carrier s → L) (t : Term sig Γ s)
    (e : Assignment A.carrier Γ) (h : (t.eval A e).Dom) : Expression k L :=
  .quantity (index ((t.eval A e).get h))

omit [CommRing k] in
/-- A defined substitution preserves the actual state argument of the quantity. -/
theorem ofStateTerm_substitute {sig : Signature.{u}} {A : Structure sig} {Γ Δ : List sig.SortType}
    {s : sig.SortType} (index : A.carrier s → L) (t : Term sig Γ s) (θ : Substitution sig Γ Δ)
    (e : θ.domain A) (h : ((t.substitute θ).eval A e.val).Dom)
    (h' : (t.eval A (θ.value A e)).Dom) :
    ofStateTerm (k := k) index (t.substitute θ) e.val h = ofStateTerm index t (θ.value A e) h' := by
  let y := (t.eval A (θ.value A e)).get h'
  have hval : y ∈ (t.substitute θ).eval A e.val :=
    Eq.mpr (congrArg (fun p => y ∈ p) (t.eval_substitute θ A e)) (Part.get_mem h')
  exact congrArg (fun x => Expression.quantity (index x)) (Part.get_eq_of_mem hval h)

end Expression

/-- A quantity application remembers its typed state term and a defined evaluation at this Law input. -/
structure StateQuantityInput {sig : Signature.{u}} (A : Structure sig) {Γ : List sig.SortType}
    (e : Assignment A.carrier Γ) (L : Type u) where
  /-- The result sort of the state term. -/
  sort : sig.SortType
  /-- The written term for the state argument. -/
  term : Term sig Γ sort
  /-- Record the quantity name and its argument in the fixed collection of coordinates. -/
  coordinateOf : A.carrier sort → L
  /-- The application is defined at this input. -/
  defined : (term.eval A e).Dom

namespace StateQuantityInput

variable {k L : Type u} {sig : Signature.{u}} {A : Structure sig} {Γ Δ : List sig.SortType}

/-- Evaluate the state term before using the named quantity coordinate. -/
noncomputable def coordinate {e : Assignment A.carrier Γ} (x : StateQuantityInput A e L) : L :=
  x.coordinateOf ((x.term.eval A e).get x.defined)

/-- Compile the written finite expression to coordinates at the fixed Law input. -/
noncomputable def compile {e : Assignment A.carrier Γ} (t : Expression k (StateQuantityInput A e L)) :
    Expression k L :=
  t.rename coordinate

/-- Substitute the state term, deriving its definedness from the typed substitution theorem. -/
def substitute (θ : Substitution sig Γ Δ) (e : θ.domain A)
    (x : StateQuantityInput A (θ.value A e) L) : StateQuantityInput A e.val L where
  sort := x.sort
  term := x.term.substitute θ
  coordinateOf := x.coordinateOf
  defined := (congrArg Part.Dom (x.term.eval_substitute θ A e)).mpr x.defined

/-- The coordinate of a quantity application is unchanged by defined substitution of its state argument. -/
theorem coordinate_substitute (θ : Substitution sig Γ Δ) (e : θ.domain A)
    (x : StateQuantityInput A (θ.value A e) L) : (substitute θ e x).coordinate = x.coordinate := by
  have h := Expression.ofStateTerm_substitute (k := L) x.coordinateOf x.term θ e
    (substitute θ e x).defined x.defined
  exact Expression.quantity.inj h

/-- Compiling a whole expression after a defined substitution agrees with compiling it on the substituted input. -/
theorem compile_substitute (θ : Substitution sig Γ Δ) (e : θ.domain A)
    (t : Expression k (StateQuantityInput A (θ.value A e) L)) :
    compile (t.rename (substitute θ e)) = compile t := by
  unfold compile
  rw [Expression.rename_comp]
  congr 1
  exact funext (coordinate_substitute θ e)

end StateQuantityInput

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

/-- Keep the written state terms and compile them separately at each fixed Law input. -/
noncomputable def Presentation.ofStateTerms {k : Type u} {sig : Signature.{u}} {A : Structure sig}
    (J : Type u) (D : J → Type u) (L : Type u) (E : L → Type u) (Γ : L → List sig.SortType)
    (input : ∀ l, E l → Assignment A.carrier (Γ l))
    (left right : ∀ l e, Expression k (StateQuantityInput A (input l e) (Σ j, D j))) : Presentation k A where
  Quantity := J
  Domain := D
  Law := L
  Input := E
  left l e := StateQuantityInput.compile (left l e)
  right l e := StateQuantityInput.compile (right l e)

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
