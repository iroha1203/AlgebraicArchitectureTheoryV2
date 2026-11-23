import Formal.SHIGURE.Part1.Laws
import Mathlib.Combinatorics.Quiver.Path

/-! # Path equations, Example 1.6

Use mathlib's `Quiver.Path` for the paths. A directed edge is a unary
operation and a parallel path equation is a Law in a one-variable context.
-/

open Quiver

namespace SHIGURE.Chapter1.Path

/-- A quiver's vertices are the sorts and its named directed edges are unary operations. -/
def signature (V : Type) [Quiver.{0} V] : Signature where
  SortType := V
  Total := Σ src : V, Σ dst : V, src ⟶ dst
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity := fun edge => ⟨[edge.1], edge.2.1⟩
  relInputs := fun r => nomatch r
  partialArity := fun p => nomatch p
  quantityArity := fun q => nomatch q

variable {V : Type} [Quiver.{0} V]

/-- Apply the unary operation named by an edge. -/
def edgeTerm {i j : V} {Γ : List V} (edge : i ⟶ j)
    (t : Term (signature V) Γ i) : Term (signature V) Γ j :=
  Term.app (sig := signature V) (.total ⟨i, j, edge⟩) (Term.argsCons t Term.argsNil)

/-- Convert a path from its source variable to the corresponding iterated operation term. -/
def term {i : V} : {j : V} → Quiver.Path i j → Term (signature V) [i] j
  | _, .nil => .var .here
  | _, .cons previous edge => edgeTerm edge (term previous)

/-- A pair of paths with common source and target. -/
structure Equation (V : Type) [Quiver.{0} V] where
  /-- The sort of the variable to which both terms are applied. -/
  src : V
  /-- The common sort of the two values to compare. -/
  dst : V
  /-- The first path. -/
  left : Quiver.Path src dst
  /-- The second path. -/
  right : Quiver.Path src dst

/-- The unconditional Law comparing the values of two parallel paths. -/
def Equation.toLaw (equation : Equation V) : Law (signature V) :=
  Law.equality (term equation.left) (term equation.right)

/-- An arbitrary indexed family of parallel path equations specifies a theory. -/
def theory {I : Type} (equations : I → Equation V) : Theory where
  signature := signature V
  LawName := I
  law := fun i => (equations i).toLaw

/-- Interpret vertices as carriers and edges as total functions. -/
def realization (X : V → Type) (step : ∀ {i j : V}, (i ⟶ j) → X i → X j) :
    Structure (signature V) where
  carrier := X
  total := fun edge e => step edge.2.2 (e .here)
  relation := fun r => nomatch r
  partialDomain := fun p => nomatch p
  partialValue := fun p => nomatch p
  quantity := fun q => nomatch q

/-- Act on a source value by composing edge maps in path order. -/
def value (X : V → Type) (step : ∀ {i j : V}, (i ⟶ j) → X i → X j)
    {i : V} (x : X i) : {j : V} → Quiver.Path i j → X j
  | _, .nil => x
  | _, .cons previous edge => step edge (value X step x previous)

/-- The term of a path evaluates to the iterated action of its edge maps. -/
theorem evaluates_term (X : V → Type) (step : ∀ {i j : V}, (i ⟶ j) → X i → X j)
    {i j : V} (path : Quiver.Path i j) (e : Assignment X [i]) :
    (term path).Evaluates (realization X step) e (value X step (e .here) path) := by
  induction path with
  | nil => rfl
  | cons previous edge ih =>
    simp only [term, value, edgeTerm]
    refine (Term.evaluates_app_at _ _ _ _
      (Assignment.cons (value X step (e .here) previous) Assignment.empty) ?_ _).2 ?_
    · intro s index
      cases index with
      | here => exact ih
      | there index => nomatch index
    · exact (Structure.graph_total_iff _ _ _ _).2 rfl

/-- A realization satisfies a path equation exactly when the composed functions agree pointwise. -/
theorem holds_equation_iff (X : V → Type) (step : ∀ {i j : V}, (i ⟶ j) → X i → X j)
    (equation : Equation V) :
    equation.toLaw.Holds (realization X step) ↔
      ∀ x : X equation.src, value X step x equation.left = value X step x equation.right := by
  rw [Equation.toLaw, Law.holds_equality_iff]
  constructor
  · intro h x
    let e : Assignment X [equation.src] := Assignment.cons x Assignment.empty
    obtain ⟨y, hleft, hright⟩ := h e
    have left_eq := Term.evaluates_unique (realization X step) (term equation.left) e
      (evaluates_term X step equation.left e) hleft
    have right_eq := Term.evaluates_unique (realization X step) (term equation.right) e
      hright (evaluates_term X step equation.right e)
    exact left_eq.trans right_eq
  · intro h e
    refine ⟨value X step (e .here) equation.left, evaluates_term X step equation.left e, ?_⟩
    rw [h (e .here)]
    exact evaluates_term X step equation.right e

/-- The two endpoints of the round-trip example. -/
inductive Vertex
  | source
  | target

/-- The edges `f : s → t` and `g : t → s`. -/
inductive Edge : Vertex → Vertex → Type
  | forward : Edge .source .target
  | backward : Edge .target .source

/-- The quiver of the round-trip example. -/
instance : Quiver Vertex := ⟨Edge⟩

/-- The Law `g(f(x)) = x` compares a two-edge path with the empty path. -/
def roundTrip : Equation Vertex where
  src := .source
  dst := .source
  left := .cons (.cons .nil Edge.forward) Edge.backward
  right := .nil

/-- Mapping both edges by the identity realizes the round-trip Law. -/
theorem identity_roundTrip :
    roundTrip.toLaw.Holds (realization (fun _ => Bool) (fun _ x => x)) :=
  (holds_equation_iff _ _ roundTrip).2 (fun _ => rfl)

/-- A graph realization with an identity forward map and a constant backward map. -/
def collapseBackward : ∀ {i j : Vertex}, (i ⟶ j) → Bool → Bool
  | _, _, Edge.forward, x => x
  | _, _, Edge.backward, _ => false

/-- The constant backward map breaks the round-trip Law at `true`. -/
theorem collapseBackward_not_roundTrip :
    ¬ roundTrip.toLaw.Holds (realization (fun _ => Bool) collapseBackward) := by
  intro h
  have bad := (holds_equation_iff _ _ roundTrip).1 h true
  change false = true at bad
  cases bad

end SHIGURE.Chapter1.Path
