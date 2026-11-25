import Mathlib.Data.Part
import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Relator

/-! # Multi-sorted signatures and structures

Chapter 1, Definitions 1.1–1.2 and the semantic graph conditions in (1.1).

## Implementation notes

A context is an ordered list of sorts. Its variables are intrinsically typed
de Bruijn indices, with one index per position even when sorts repeat.
Assignments are dependent functions on those indices. They represent the
finite product in (1.1), allow the empty product, and provide projections
whose types are determined by the context.

Total operations and quantities have separate symbol families. A partial
operation has an explicit domain and a map on its subtype. The common
evaluation API uses mathlib's `Part` to preserve the domain without a
decidability condition.
-/

universe u v

namespace SHIGURE

/-- A position of sort `s` in a finite variable context. -/
inductive Var {S : Type u} : List S → S → Type u
  | here {Γ : List S} {s : S} : Var (s :: Γ) s
  | there {Γ : List S} {s t : S} : Var Γ s → Var (t :: Γ) s

/-- A sort-preserving map of all the variable positions of a context. -/
abbrev Renaming {S : Type u} (Γ Δ : List S) :=
  ∀ {s : S}, Var Γ s → Var Δ s

namespace Var

variable {S : Type u} {Γ : List S} {s : S}

/-- The sort of a position occurs in its context. -/
theorem sort_mem (i : Var Γ s) : s ∈ Γ := by
  induction i with
  | here => exact List.mem_cons_self
  | there _ ih => exact List.mem_cons_of_mem _ ih

/-- Include a variable from the first block of an appended context. -/
def inLeft (Δ : List S) : {Γ : List S} → {s : S} → Var Γ s → Var (Γ ++ Δ) s
  | _, _, .here => .here
  | _, _, .there var => .there (inLeft Δ var)

/-- The leading block's head stays at the head of the combined context. -/
theorem inLeft_here (Δ : List S) : (Var.here : Var (s :: Γ) s).inLeft Δ = .here := rfl

/-- A position in the leading block retains its depth after appending a context. -/
theorem inLeft_there (Δ : List S) {t : S} (i : Var Γ s) :
    (Var.there (t := t) i).inLeft Δ = .there (i.inLeft Δ) := rfl

/-- Include a variable following an added prefix of variables. -/
def shift : (Δ : List S) → Var Γ s → Var (Δ ++ Γ) s
  | [], var => var
  | _ :: Δ, var => .there (shift Δ var)

/-- Shifting by an empty block leaves the original variable map. -/
theorem shift_nil : (fun {t : S} (i : Var Γ t) => i.shift []) =
    (fun {t : S} (i : Var Γ t) => i) := rfl

/-- Shifting past a nonempty block moves past its head and its tail. -/
theorem shift_cons (Λ : List S) {t : S} (i : Var Γ s) :
    i.shift (t :: Λ) = Var.there (i.shift Λ) := rfl

/-- Position number in the finite context. -/
def position : {Γ : List S} → {s : S} → Var Γ s → Nat
  | _, _, .here => 0
  | _, _, .there i => i.position.succ

/-- Two variables in the same finite context have distinct position numbers. -/
theorem position_injective (Γ : List S) :
    Function.Injective (fun i : (Σ s, Var Γ s) => i.2.position) := by
  induction Γ with
  | nil =>
    intro i
    exact nomatch i.2
  | cons s Γ ih =>
    rintro ⟨a, i⟩ ⟨b, j⟩ eq
    cases i with
    | here =>
      cases j with
      | here => rfl
      | there j => exact (Nat.noConfusion eq)
    | there i =>
      cases j with
      | here => exact (Nat.noConfusion eq)
      | there j =>
        have tail : (⟨_, i⟩ : Σ s, Var Γ s) = ⟨_, j⟩ := ih (Nat.succ.inj eq)
        exact congrArg (fun i : Σ t, Var Γ t => (⟨i.1, .there i.2⟩ : Σ t, Var (s :: Γ) t)) tail

end Var

namespace Renaming

variable {S : Type u} {Γ Δ : List S} {s : S}

/-- Apply a transported renaming by moving the argument back and the result forward. -/
theorem cast_context_apply {Γ' Δ' : List S} (source : Γ = Γ') (target : Δ = Δ')
    (ρ : Renaming Γ Δ) (i : Var Γ' s) :
    (@cast (Renaming Γ Δ) (Renaming Γ' Δ') (congrArg₂ Renaming source target) ρ) i =
      cast (congrArg (fun ctx => Var ctx s) target)
        (ρ (cast (congrArg (fun ctx => Var ctx s) source.symm) i)) := by
  cases source
  cases target
  rfl

/-- A renaming with only its target transported maps the same variable before transport. -/
theorem cast_target_apply {Δ' : List S} (same : Δ = Δ') (ρ : Renaming Γ Δ) (i : Var Γ s) :
    (@cast (Renaming Γ Δ) (Renaming Γ Δ') (congrArg (Renaming Γ) same) ρ) i =
      cast (congrArg (fun ctx => Var ctx s) same) (ρ i) := by
  cases same
  rfl

/-- Transport the tail of a variable below a fixed head. -/
theorem cast_there_target {Δ' : List S} {t : S} (same : Δ = Δ') (i : Var Δ s) :
    cast (congrArg (fun ctx => Var ctx s) (congrArg (List.cons t) same)) (.there i) =
      .there (cast (congrArg (fun ctx => Var ctx s) same) i) := by
  cases same
  rfl

/-- Transporting the tail of a context keeps the head variable. -/
theorem cast_here_target {Δ' : List S} (same : Δ = Δ') :
    cast (congrArg (Var · s) (congrArg (List.cons s) same)) (.here : Var (s :: Δ) s) = .here := by
  cases same
  rfl

/-- Extend a renaming under a binder, keeping its new variable fixed. -/
def lift (ρ : Renaming Γ Δ) : Renaming (s :: Γ) (s :: Δ)
  | _, .here => .here
  | _, .there var => .there (ρ var)

/-- Lifting the free-variable map retains the new head variable. -/
theorem lift_here (ρ : Renaming Γ Δ) : (lift ρ) (Var.here : Var (s :: Γ) s) = .here := rfl

/-- Lifting the free-variable map applies the original map below the head. -/
theorem lift_there (ρ : Renaming Γ Δ) {t : S} (i : Var Γ t) :
    (lift ρ) (Var.there (t := s) i) = .there (ρ i) := rfl

/-- Map a new head position to a selected variable while applying the older variable map. -/
def cons (head : Var Δ s) (tail : Renaming Γ Δ) : Renaming (s :: Γ) Δ
  | _, .here => head
  | _, .there i => tail i

/-- Selecting the head of a cons renaming reads its distinguished variable. -/
@[simp] theorem cons_here (head : Var Δ s) (tail : Renaming Γ Δ) :
    cons head tail .here = head :=
  rfl

/-- Selecting an older coordinate of a cons renaming applies the older map. -/
@[simp] theorem cons_there (head : Var Δ s) (tail : Renaming Γ Δ) {t : S} (i : Var Γ t) :
    cons head tail (.there i) = tail i :=
  rfl

/-- Add an older variable after the selected prefix. -/
def insertAfter : (Λ : List S) → Renaming (Λ ++ Γ) (Λ ++ s :: Γ)
  | [] => fun i => .there i
  | _ :: Λ => lift (insertAfter Λ)

/-- Move the newest variable past a block while keeping all other positions. -/
def moveHead (Λ : List S) : Renaming (s :: (Λ ++ Γ)) (Λ ++ s :: Γ)
  | _, .here => (Var.here : Var (s :: Γ) s).shift Λ
  | _, .there i => insertAfter Λ i

end Renaming

/-- The finite product of the carriers of a context. -/
structure Assignment {S : Type u} (X : S → Type v) (Γ : List S) where
  /-- The value of each position, at its declared sort. -/
  get : ∀ {s : S}, Var Γ s → X s

namespace Assignment

variable {S : Type u} {X : S → Type v} {Γ : List S} {s : S}

/-- An assignment can be applied to any variable in its context. -/
instance : CoeFun (Assignment X Γ) (fun _ => ∀ {t : S}, Var Γ t → X t) := ⟨get⟩

/-- A transported assignment reads the old assignment at the inverse-transported variable. -/
theorem cast_context_apply {Δ : List S} (same : Γ = Δ) (e : Assignment X Γ) (i : Var Δ s) :
    (cast (congrArg (Assignment X) same) e).get i = e.get (cast (congrArg (fun ctx => Var ctx s) same.symm) i) := by
  cases same
  rfl

/-- Changing a variable's sort transports the value read at that variable. -/
theorem get_cast_sort {t : S} (same : s = t) (e : Assignment X Γ) (i : Var Γ s) :
    e (cast (congrArg (Var Γ) same) i) = cast (congrArg X same) (e i) := by
  cases same
  rfl

/-- The canonical assignment to the empty context. -/
def empty : Assignment X [] := ⟨fun var => nomatch var⟩

/-- Extend an assignment with a new first component. -/
def cons (x : X s) (xs : Assignment X Γ) : Assignment X (s :: Γ) :=
  ⟨fun var => match var with
    | .here => x
    | .there previous => xs previous⟩

/-- Read the first component of an extended assignment. -/
def head (xs : Assignment X (s :: Γ)) : X s := xs .here

/-- Forget the first component of an extended assignment. -/
def tail (xs : Assignment X (s :: Γ)) : Assignment X Γ := ⟨fun var => xs (.there var)⟩

/-- Functions on typed variables agree whenever every component agrees. -/
@[ext] theorem ext {xs ys : Assignment X Γ}
    (h : ∀ {t : S} (var : Var Γ t), xs var = ys var) : xs = ys := by
  cases xs
  cases ys
  congr
  funext t var
  exact h var

/-- The value introduced by context extension. -/
@[simp] theorem cons_here (x : X s) (xs : Assignment X Γ) : cons x xs .here = x := rfl

/-- Previous values remain available after context extension. -/
@[simp] theorem cons_there (x : X s) (xs : Assignment X Γ) {t : S} (var : Var Γ t) :
    cons x xs (.there var) = xs var := rfl

/-- Projection at the first coordinate of an extended assignment. -/
@[simp] theorem head_cons (x : X s) (xs : Assignment X Γ) : (cons x xs).head = x := rfl

/-- Restricting an extended assignment to its old variables recovers it. -/
@[simp] theorem tail_cons (x : X s) (xs : Assignment X Γ) : (cons x xs).tail = xs := rfl

/-- An extended context assignment consists of its first component and its tail. -/
@[simp] theorem cons_head_tail (xs : Assignment X (s :: Γ)) :
    cons xs.head xs.tail = xs := by
  apply ext
  intro t var
  cases var <;> rfl

/-- The empty product has exactly one assignment, even for empty carriers. -/
theorem eq_empty (xs : Assignment X []) : xs = empty := by
  apply ext
  intro t var
  nomatch var

/-- Pull an assignment back along a sort-preserving variable renaming. -/
def pull {Δ : List S} (xs : Assignment X Δ) (ρ : Renaming Γ Δ) : Assignment X Γ :=
  ⟨fun var => xs (ρ var)⟩

/-- A pullback along a transported renaming transports the resulting assignment. -/
theorem pull_cast_inputs {Γ' Δ : List S} (same : Γ' = Γ) (xs : Assignment X Δ) (ρ : Renaming Γ Δ) :
    xs.pull (fun {t} (i : Var Γ' t) => ρ (cast (congrArg (Var · t) same) i)) =
      cast (congrArg (Assignment X) same.symm) (xs.pull ρ) := by
  cases same
  rfl

/-- Pulling back along the identity preserves the assignment. -/
@[simp] theorem pull_id (xs : Assignment X Γ) : xs.pull (fun var => var) = xs := rfl

/-- Pullback computes by reading the selected position. -/
@[simp] theorem pull_apply {Δ : List S} (xs : Assignment X Δ) (ρ : Renaming Γ Δ)
    {t : S} (var : Var Γ t) : xs.pull ρ var = xs (ρ var) :=
  rfl

/-- Pullback along a lifted renaming keeps the binder's value. -/
@[simp] theorem pull_lift_cons {Δ : List S} (xs : Assignment X Δ) (ρ : Renaming Γ Δ)
    (x : X s) : (cons x xs).pull (ρ.lift (s := s)) = cons x (xs.pull ρ) := by
  apply ext
  intro t var
  cases var <;> rfl

/-- Shifting past a binder reads the original assignment. -/
@[simp] theorem pull_cons_there {Δ : List S} (xs : Assignment X Δ) (ρ : Renaming Γ Δ)
    (x : X s) : (cons x xs).pull (fun var => .there (ρ var)) = xs.pull ρ :=
  rfl

/-- Combine the assignments for two consecutive blocks of variables. -/
def append {Δ : List S} : {Γ : List S} →
    Assignment X Γ → Assignment X Δ → Assignment X (Γ ++ Δ)
  | [], _, ys => ys
  | _ :: _, xs, ys => cons xs.head (append xs.tail ys)

/-- Appending an empty first assignment yields the second assignment. -/
@[simp] theorem append_empty {Δ : List S} (xs : Assignment X []) (ys : Assignment X Δ) :
    xs.append ys = ys := rfl

/-- A leading variable passes unchanged through assignment concatenation. -/
@[simp] theorem append_cons {Δ : List S} (x : X s) (xs : Assignment X Γ)
    (ys : Assignment X Δ) : (cons x xs).append ys = cons x (xs.append ys) := rfl

/-- Reading a position in the first block reads the first assignment. -/
@[simp] theorem append_inLeft {Δ : List S} (var : Var Γ s)
    (xs : Assignment X Γ) (ys : Assignment X Δ) : xs.append ys (var.inLeft Δ) = xs var := by
  induction var with
  | here => rfl
  | there var ih => exact ih xs.tail

/-- Reading a position in the second block reads the second assignment. -/
@[simp] theorem append_shift {Δ : List S} (xs : Assignment X Γ)
    (ys : Assignment X Δ) (var : Var Δ s) : xs.append ys (var.shift Γ) = ys var := by
  induction Γ with
  | nil => rfl
  | cons t Γ ih => exact ih xs.tail

/-- The projection of concatenated inputs onto their first context. -/
@[simp] theorem pull_append_left {Δ : List S} (xs : Assignment X Γ) (ys : Assignment X Δ) :
    (xs.append ys).pull (Var.inLeft Δ) = xs := by
  apply ext
  intro t var
  simp

/-- Reading renamed variables after a prefix is independent of that prefix. -/
@[simp] theorem pull_append_shift {Δ Λ : List S} (xs : Assignment X Γ) (ys : Assignment X Δ)
    (ρ : Renaming Λ Δ) : (xs.append ys).pull (fun var => (ρ var).shift Γ) = ys.pull ρ := by
  apply ext
  intro t var
  simp

end Assignment

/-- The finite list of input sorts and the output sort of an operation. -/
structure Arity (S : Type u) where
  /-- Input sorts in argument order. -/
  inputs : List S
  /-- The sort of the result. -/
  output : S

/-- A small signature with separate named symbol families, as in Definition 1.2. -/
structure Signature where
  /-- The carrier sorts. -/
  SortType : Type u
  /-- Symbols for unmarked total operations. -/
  Total : Type u
  /-- Symbols for basic relations. -/
  Rel : Type u
  /-- Symbols for partial operations. -/
  Partial : Type u
  /-- Symbols for quantities, interpreted as marked total operations. -/
  Quantity : Type u
  /-- Arities of total operations. -/
  totalArity : Total → Arity SortType
  /-- Argument sorts of relations. -/
  relInputs : Rel → List SortType
  /-- Arities of partial operations. -/
  partialArity : Partial → Arity SortType
  /-- Arities of quantities. -/
  quantityArity : Quantity → Arity SortType

/-- Operation symbols that can occur at the head of a term. -/
inductive Operation (sig : Signature.{u}) : Type u
  | total : sig.Total → Operation sig
  | partialOp : sig.Partial → Operation sig
  | quantity : sig.Quantity → Operation sig

/-- Recover the typed argument list and result sort of a tagged operation. -/
def Operation.arity {sig : Signature.{u}} : Operation sig → Arity sig.SortType
  | .total f => sig.totalArity f
  | .partialOp p => sig.partialArity p
  | .quantity q => sig.quantityArity q

/-- Interpretation of a signature. Each carrier can be empty. -/
structure Structure (sig : Signature.{u}) where
  /-- The set assigned to each sort. -/
  carrier : sig.SortType → Type u
  /-- A total operation on its entire product of inputs. -/
  total : (f : sig.Total) → Assignment carrier (sig.totalArity f).inputs →
    carrier (sig.totalArity f).output
  /-- A relation is a subset of its product of inputs. -/
  relation : (r : sig.Rel) → Set (Assignment carrier (sig.relInputs r))
  /-- The chosen domain of a partial operation. -/
  partialDomain : (p : sig.Partial) → Set (Assignment carrier (sig.partialArity p).inputs)
  /-- The function on the chosen domain of a partial operation. -/
  partialValue : (p : sig.Partial) → partialDomain p → carrier (sig.partialArity p).output
  /-- A quantity is always defined on its product of inputs. -/
  quantity : (q : sig.Quantity) → Assignment carrier (sig.quantityArity q).inputs →
    carrier (sig.quantityArity q).output

namespace Structure

/-- A structure is determined by its carriers and its primitive interpretations.
The types of those interpretations depend on the carrier family and the partial domains. -/
theorem ext {sig : Signature.{u}} {A B : Structure sig} (carrier : A.carrier = B.carrier)
    (total : HEq A.total B.total) (relation : HEq A.relation B.relation)
    (domain : HEq A.partialDomain B.partialDomain) (partialValue : HEq A.partialValue B.partialValue)
    (quantity : HEq A.quantity B.quantity) : A = B := by
  cases A
  cases B
  cases carrier
  cases total
  cases relation
  cases domain
  cases partialValue
  cases quantity
  rfl

/-- Partial operations on equal domains agree if they return equal values on each input. -/
theorem partialValue_heq {ι : Type u} {Inputs Output : ι → Type u}
    {D E : (p : ι) → Set (Inputs p)} (domains : D = E)
    (f : (p : ι) → D p → Output p) (g : (p : ι) → E p → Output p)
    (values : ∀ p (xs : D p) (hx : xs.val ∈ E p), f p xs = g p ⟨xs.val, hx⟩) : HEq f g := by
  cases domains
  exact heq_of_eq (funext fun p => funext fun xs => values p xs xs.property)

variable {sig : Signature.{u}} (A : Structure sig)

/-- Evaluate an operation on a tuple, preserving its possibly partial domain. -/
def applyOp (op : Operation sig) (xs : Assignment A.carrier op.arity.inputs) :
    Part (A.carrier op.arity.output) :=
  match op with
  | .total f => Part.some (A.total f xs)
  | .partialOp p => ⟨xs ∈ A.partialDomain p, fun hx => A.partialValue p ⟨xs, hx⟩⟩
  | .quantity q => Part.some (A.quantity q xs)

/-- The graph relation of a total operation, quantity, or partial operation. -/
def Graph (op : Operation sig) (xs : Assignment A.carrier op.arity.inputs)
    (value : A.carrier op.arity.output) : Prop :=
  value ∈ A.applyOp op xs

/-- The graph of a total operation records its function value. -/
@[simp] theorem graph_total_iff (f : sig.Total) (xs : Assignment A.carrier (sig.totalArity f).inputs)
    (value : A.carrier (sig.totalArity f).output) :
    A.Graph (.total f) xs value ↔ A.total f xs = value :=
  Part.mem_some_iff.trans eq_comm

/-- The graph of a quantity records its total function value. -/
@[simp] theorem graph_quantity_iff (q : sig.Quantity)
    (xs : Assignment A.carrier (sig.quantityArity q).inputs)
    (value : A.carrier (sig.quantityArity q).output) :
    A.Graph (.quantity q) xs value ↔ A.quantity q xs = value :=
  Part.mem_some_iff.trans eq_comm

/-- The graph of a partial operation contains exactly the inputs in its domain and their values. -/
@[simp] theorem graph_partial_iff (p : sig.Partial)
    (xs : Assignment A.carrier (sig.partialArity p).inputs)
    (value : A.carrier (sig.partialArity p).output) :
    A.Graph (.partialOp p) xs value ↔
      ∃ hx : xs ∈ A.partialDomain p, A.partialValue p ⟨xs, hx⟩ = value :=
  Iff.rfl

/-- The graph of an interpreted operation is functional, as required in (1.1). -/
theorem graph_rightUnique (op : Operation sig) : Relator.RightUnique (A.Graph op) :=
  by
    intro xs y z hy hz
    exact Part.mem_unique hy hz

end Structure

namespace GraphPresentation

variable {X : Type u} {Y : Type v}

/-- Functionality and totality for the graph of a total operation or a quantity. -/
def IsTotal (G : X → Y → Prop) : Prop :=
  Relator.RightUnique G ∧ ∀ x, ∃ y, G x y

/-- Functionality, containment over the given domain, and existence on that domain. -/
def IsPartial (D : Set X) (G : X → Y → Prop) : Prop :=
  Relator.RightUnique G ∧ (∀ x y, G x y → x ∈ D) ∧ ∀ x ∈ D, ∃ y, G x y

/-- Equation (1.1) holds precisely when the total graph has a unique function realization. -/
theorem isTotal_iff_existsUnique (G : X → Y → Prop) :
    IsTotal G ↔ ∃! (f : X → Y), ∀ x y, G x y ↔ f x = y := by
  constructor
  · intro h
    let f : X → Y := fun x => Classical.choose (h.2 x)
    have value_mem (x : X) : G x (f x) := Classical.choose_spec (h.2 x)
    refine ⟨f, ?_, ?_⟩
    · intro x y
      exact ⟨fun hy => h.1 (value_mem x) hy, fun e => e ▸ value_mem x⟩
    · intro g hg
      funext x
      exact h.1 ((hg x (g x)).2 rfl) (value_mem x)
  · rintro ⟨f, hf, _⟩
    refine ⟨?_, fun x => ⟨f x, (hf x (f x)).2 rfl⟩⟩
    intro x y z hy hz
    exact ((hf x y).1 hy).symm.trans ((hf x z).1 hz)

/-- Equation (1.1) reconstructs a partial operation uniquely on its prescribed domain. -/
theorem isPartial_iff_existsUnique (D : Set X) (G : X → Y → Prop) :
    IsPartial D G ↔
      ∃! (f : D → Y), ∀ x y, G x y ↔ ∃ hx : x ∈ D, f ⟨x, hx⟩ = y := by
  constructor
  · intro h
    let f : D → Y := fun x => Classical.choose (h.2.2 x x.property)
    have value_mem (x : D) : G x (f x) := Classical.choose_spec (h.2.2 x x.property)
    refine ⟨f, ?_, ?_⟩
    · intro x y
      constructor
      · intro hy
        let hx := h.2.1 x y hy
        exact ⟨hx, h.1 (value_mem ⟨x, hx⟩) hy⟩
      · rintro ⟨hx, rfl⟩
        exact value_mem ⟨x, hx⟩
    · intro g hg
      funext x
      exact h.1 ((hg x (g x)).2 ⟨x.property, rfl⟩) (value_mem x)
  · rintro ⟨f, hf, _⟩
    refine ⟨?_, ?_, fun x hx => ⟨f ⟨x, hx⟩, (hf x _).2 ⟨hx, rfl⟩⟩⟩
    · intro x y z hy hz
      obtain ⟨hx, ey⟩ := (hf x y).1 hy
      obtain ⟨_, ez⟩ := (hf x z).1 hz
      exact ey.symm.trans ez
    · intro x y hy
      exact ((hf x y).1 hy).choose

/-- The graph of every total operation satisfies (1.1). -/
theorem total_valid {sig : Signature.{u}} (A : Structure sig) (f : sig.Total) :
    IsTotal (A.Graph (.total f)) :=
  ⟨A.graph_rightUnique (.total f), fun xs => ⟨A.total f xs, by simp⟩⟩

/-- The graph of every quantity satisfies the total clauses of (1.1). -/
theorem quantity_valid {sig : Signature.{u}} (A : Structure sig) (q : sig.Quantity) :
    IsTotal (A.Graph (.quantity q)) :=
  ⟨A.graph_rightUnique (.quantity q), fun xs => ⟨A.quantity q xs, by simp⟩⟩

/-- The graph of every partial operation satisfies its three clauses of (1.1). -/
theorem partial_valid {sig : Signature.{u}} (A : Structure sig) (p : sig.Partial) :
    IsPartial (A.partialDomain p) (A.Graph (.partialOp p)) := by
  refine ⟨A.graph_rightUnique (.partialOp p), ?_, ?_⟩
  · intro xs value h
    exact ((A.graph_partial_iff p xs value).1 h).choose
  · intro xs hx
    exact ⟨A.partialValue p ⟨xs, hx⟩, (A.graph_partial_iff p xs _).2 ⟨hx, rfl⟩⟩

end GraphPresentation

end SHIGURE
