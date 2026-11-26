import Formal.SHIGURE.Part1.ContextSelectedStructures
import Formal.SHIGURE.Part1.ContextSelectedTerms
import Formal.SHIGURE.Part2.Quantities.FixedModels
import Formal.SHIGURE.Part2.QuantityTransport.DeclarationStates

/-!
# Typed coefficient syntax for declared quantity Laws

The typed terms retain the original operation at each node. A literal
uses the actual interpreted nullary symbol. The arithmetic relations
compare the declared operations with the coefficient ring on
the value sort of their occurrence.

## Implementation notes

A global ring vocabulary can supply all scalar arithmetic at one sort.
Here each node supplies only its own symbol. This accommodates multiple
declared value sorts and equality Laws that never use arithmetic.
The leaves are indexed by actual term applications and literal symbols
so their dependencies can be read directly from the written Law.
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

/-- A coefficient operation retains its primitive tag and typed profile. -/
structure CoefficientSymbol (sig : Signature.{u}) (profile : Arity sig.SortType) where
  operation : Operation sig
  arity_eq : operation.arity = profile

namespace CoefficientSymbol

variable {sig : Signature.{u}} {profile : Arity sig.SortType}

/-- The original application of the operation at its stated profile. -/
def term (op : CoefficientSymbol sig profile) {Γ : List sig.SortType}
    (args : ∀ {s}, Var profile.inputs s → Term sig Γ s) : Term sig Γ profile.output :=
  Term.reindexedApp op.operation op.arity_eq args

section Graph

open DeclarationContext

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}
variable {profile : Arity P.signature.SortType}

/-- A typed coefficient operator retains all its declared input sorts. -/
theorem keepsInputs (op : CoefficientSymbol P.signature profile)
    (keep : Declaration.ofOperation op.operation ∈ U.declarations) :
    Declaration.sorts profile.inputs ⊆ U.declarations := by
  rw [← op.arity_eq]
  exact operationInputs op.operation keep

/-- A typed coefficient operator retains its declared result sort. -/
theorem keepsResult (op : CoefficientSymbol P.signature profile)
    (keep : Declaration.ofOperation op.operation ∈ U.declarations) :
    Declaration.sort profile.output ∈ U.declarations := by
  rw [← op.arity_eq]
  exact operationOutput op.operation keep

/-- The actual primitive graph, expressed using the declared coefficient profile. -/
def graph (op : CoefficientSymbol P.signature profile) (A : ContextStructure U)
    (keep : Declaration.ofOperation op.operation ∈ U.declarations)
    (input : Assignment A.carrier profile.inputs) (y : A.carrier profile.output) : Prop :=
  A.evaluation.graph op.operation keep
    (cast (congrArg (Assignment A.carrier) (congrArg Arity.inputs op.arity_eq).symm) input)
    (cast (congrArg A.carrier (congrArg Arity.output op.arity_eq).symm) y)

/-- A coefficient primitive returns a unique result wherever it is defined. -/
theorem graph_rightUnique (op : CoefficientSymbol P.signature profile) (A : ContextStructure U)
    (keep : Declaration.ofOperation op.operation ∈ U.declarations) :
    Relator.RightUnique (op.graph A keep) := by
  rcases op with ⟨operation, equality⟩
  subst profile
  exact A.graph_rightUnique operation keep

/-- Restricting a declared coefficient primitive preserves its actual graph. -/
theorem graph_restrict_iff (op : CoefficientSymbol P.signature profile) (A : ContextStructure U)
    (inside : V ≤ U) (keep : Declaration.ofOperation op.operation ∈ V.declarations)
    (input : Assignment (A.restrict inside).carrier profile.inputs)
    (y : (A.restrict inside).carrier profile.output) :
    op.graph (A.restrict inside) keep input y ↔
      op.graph A (inside keep) (mapAssignment (selectedMap V A.carrier) (op.keepsInputs keep) input)
        (selectedMap V A.carrier _ (op.keepsResult keep) y) := by
  rcases op with ⟨operation, equality⟩
  subst profile
  rfl

/-- Actual evaluation of a typed application reads exactly its argument values and primitive graph. -/
theorem evaluates_term_iff (op : CoefficientSymbol P.signature profile) (B : ContextStructure U)
    {Γ : List P.signature.SortType} (args : ∀ {s}, Var profile.inputs s → Term P.signature Γ s)
    (supported : Declaration.termContext (op.term args) ≤ U)
    (e : Assignment B.carrier Γ) (keep : Declaration.ofOperation op.operation ∈ U.declarations)
    (y : B.carrier profile.output) :
    B.evaluates ⟨op.term args, supported⟩ e y ↔
      ∃ input : Assignment B.carrier profile.inputs,
        (∀ {s} (i : Var profile.inputs s), ∃ h, B.evaluates ⟨args i, h⟩ e (input i)) ∧
        op.graph B keep input y := by
  rcases op with ⟨operation, equality⟩
  subst profile
  exact B.evaluates_app_iff operation args ⟨_, supported⟩ rfl e keep y

/-- A coefficient operation on its actual domain evaluates to the specified scalar operation. -/
def Realizes {k : Type u} (op : CoefficientSymbol P.signature profile) (A : ContextStructure U)
    (keep : Declaration.ofOperation op.operation ∈ U.declarations)
    (read : CarrierMap U A.carrier (fun _ => k))
    (meaning : Assignment (fun _ => k) profile.inputs → k) : Prop :=
  ∀ input y, op.graph A keep input y →
    read profile.output (op.keepsResult keep) y = meaning (mapAssignment read (op.keepsInputs keep) input)

/-- Restriction carries the meaning through the actual value graph. -/
theorem Realizes.restrict {k : Type u} {op : CoefficientSymbol P.signature profile}
    {A : ContextStructure U} (inside : V ≤ U) (keep : Declaration.ofOperation op.operation ∈ V.declarations)
    {read : CarrierMap U A.carrier (fun _ => k)} {meaning : Assignment (fun _ => k) profile.inputs → k}
    (valid : op.Realizes A (inside keep) read meaning) :
    op.Realizes (A.restrict inside) keep
      (fun s hs x => read s (inside hs) (selectedMap V A.carrier s hs x)) meaning := by
  intro input y given
  change read profile.output (inside (op.keepsResult keep))
    (selectedMap V A.carrier profile.output (op.keepsResult keep) y) = _
  rw [← mapAssignment_comp _ _ inside]
  exact valid _ _ ((op.graph_restrict_iff A inside keep input y).1 given)

end Graph

end CoefficientSymbol

/-- The arithmetic meaning assigned to a written coefficient operation. -/
inductive ArithmeticOperation (sig : Signature.{u})
  | add {s} (symbol : CoefficientSymbol sig ⟨[s, s], s⟩)
  | neg {s} (symbol : CoefficientSymbol sig ⟨[s], s⟩)
  | sub {s} (symbol : CoefficientSymbol sig ⟨[s, s], s⟩)
  | mul {s} (symbol : CoefficientSymbol sig ⟨[s, s], s⟩)

namespace ArithmeticOperation

open DeclarationContext

/-- The original operation at a written arithmetic node. -/
def operation {sig : Signature.{u}} : ArithmeticOperation sig → Operation sig
  | .add op | .neg op | .sub op | .mul op => op.operation

variable {k : Type u} [CommRing k]
variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}

/-- The actual operation is the indicated arithmetic when read in the coefficient ring. -/
def realizes (A : ContextStructure U) (read : CarrierMap U A.carrier (fun _ => k)) :
    (a : ArithmeticOperation P.signature) → Declaration.ofOperation a.operation ∈ U.declarations → Prop
  | .add op, keep => op.Realizes A keep read (fun x => x .here + x (.there .here))
  | .neg op, keep => op.Realizes A keep read (fun x => - x .here)
  | .sub op, keep => op.Realizes A keep read (fun x => x .here - x (.there .here))
  | .mul op, keep => op.Realizes A keep read (fun x => x .here * x (.there .here))

/-- The interpretation of a written arithmetic operation survives restriction. -/
theorem realizes_restrict (a : ArithmeticOperation P.signature) {A : ContextStructure U}
    (inside : V ≤ U) (keep : Declaration.ofOperation a.operation ∈ V.declarations)
    (read : CarrierMap U A.carrier (fun _ => k)) (valid : a.realizes A read (inside keep)) :
    a.realizes (A.restrict inside)
      (fun s hs x => read s (inside hs) (selectedMap V A.carrier s hs x)) keep := by
  cases a <;> simp only [realizes] at valid ⊢
  all_goals exact CoefficientSymbol.Realizes.restrict inside keep valid

end ArithmeticOperation

/-- The typed syntax of the written coefficient equations.
Each arithmetic node refers to the actual operation of that occurrence. -/
inductive CoefficientTerm {sig : Signature.{u}} (quantity : Set (QuantityDeclaration sig))
    (Γ : List sig.SortType) : sig.SortType → Type u
  | scalar {s} (symbol : CoefficientSymbol sig ⟨[], s⟩) : CoefficientTerm quantity Γ s
  | quantity (j : quantity) (args : Substitution sig j.val.operation.arity.inputs Γ) :
      CoefficientTerm quantity Γ j.val.operation.arity.output
  | add {s} (symbol : CoefficientSymbol sig ⟨[s, s], s⟩)
      (left right : CoefficientTerm quantity Γ s) : CoefficientTerm quantity Γ s
  | neg {s} (symbol : CoefficientSymbol sig ⟨[s], s⟩) (arg : CoefficientTerm quantity Γ s) :
      CoefficientTerm quantity Γ s
  | sub {s} (symbol : CoefficientSymbol sig ⟨[s, s], s⟩)
      (left right : CoefficientTerm quantity Γ s) : CoefficientTerm quantity Γ s
  | mul {s} (symbol : CoefficientSymbol sig ⟨[s, s], s⟩)
      (left right : CoefficientTerm quantity Γ s) : CoefficientTerm quantity Γ s

namespace CoefficientTerm

variable {sig : Signature.{u}} {quantity : Set (QuantityDeclaration sig)} {Γ : List sig.SortType}

/-- The named original quantity applied to the typed state argument terms. -/
abbrev Application (quantity : Set (QuantityDeclaration sig)) (Γ : List sig.SortType) :=
  Σ j : quantity, Substitution sig j.val.operation.arity.inputs Γ

/-- A literal refers to one original nullary symbol and its own value sort. -/
abbrev Literal (sig : Signature.{u}) := Σ s : sig.SortType, CoefficientSymbol sig ⟨[], s⟩

/-- Read the original typed term, with the declared symbols at each node. -/
def toTerm : {s : sig.SortType} → CoefficientTerm quantity Γ s → Term sig Γ s
  | _, .scalar symbol => symbol.term Term.argsNil
  | _, .quantity j args => .app j.val.operation (fun i => args i)
  | _, .add symbol l r => symbol.term ((toTerm l).argsCons ((toTerm r).argsCons Term.argsNil))
  | _, .neg symbol x => symbol.term ((toTerm x).argsCons Term.argsNil)
  | _, .sub symbol l r => symbol.term ((toTerm l).argsCons ((toTerm r).argsCons Term.argsNil))
  | _, .mul symbol l r => symbol.term ((toTerm l).argsCons ((toTerm r).argsCons Term.argsNil))

/-- Collect the literals and applications of the actual syntax as two disjoint kinds of scalar leaves. -/
def leaves : {s : sig.SortType} → CoefficientTerm quantity Γ s → Set (Literal sig ⊕ Application quantity Γ)
  | _, .scalar symbol => {Sum.inl ⟨_, symbol⟩}
  | _, .quantity j args => {Sum.inr ⟨j, args⟩}
  | _, .add _ l r | _, .sub _ l r | _, .mul _ l r => l.leaves ∪ r.leaves
  | _, .neg _ x => x.leaves

/-- Only arithmetic operations appearing in the written expression need an interpretation. -/
def arithmetic : {s : sig.SortType} → CoefficientTerm quantity Γ s → Set (ArithmeticOperation sig)
  | _, .scalar _ | _, .quantity _ _ => ∅
  | _, .add op l r => {ArithmeticOperation.add op} ∪ (l.arithmetic ∪ r.arithmetic)
  | _, .neg op t => {ArithmeticOperation.neg op} ∪ t.arithmetic
  | _, .sub op l r => {ArithmeticOperation.sub op} ∪ (l.arithmetic ∪ r.arithmetic)
  | _, .mul op l r => {ArithmeticOperation.mul op} ∪ (l.arithmetic ∪ r.arithmetic)

/-- Scalars and coordinates have different result types when reading a leaf. -/
def LeafValue {L Q : Type u} (k Z : Type u) : L ⊕ Q → Type u
  | .inl _ => k
  | .inr _ => Z

/-- Translate the occurring literal symbols and state argument tuples at a selected input. -/
def compile {k Z : Type u} :
    {s : sig.SortType} → (t : CoefficientTerm quantity Γ s) →
      (∀ a ∈ t.leaves, LeafValue k Z a) → Expression k Z
  | _, .scalar symbol, read => .scalar (read (.inl ⟨_, symbol⟩) (Set.mem_singleton _))
  | _, .quantity j args, read => .quantity (read (.inr ⟨j, args⟩) (Set.mem_singleton _))
  | _, .add _ l r, read => .add
      (compile l (fun a h => read a (Or.inl h))) (compile r (fun a h => read a (Or.inr h)))
  | _, .neg _ t, read => .neg (compile t read)
  | _, .sub _ l r, read => .add
      (compile l (fun a h => read a (Or.inl h))) (.neg (compile r (fun a h => read a (Or.inr h))))
  | _, .mul _ l r, read => .mul
      (compile l (fun a h => read a (Or.inl h))) (compile r (fun a h => read a (Or.inr h)))

/-- Reindex the variable part of a compiled leaf, retaining scalar contents. -/
def mapLeafValue {L Q k Z W : Type u} (f : Z → W) :
    (a : L ⊕ Q) → LeafValue k Z a → LeafValue k W a
  | .inl _, value => value
  | .inr _, value => f value

/-- Coordinate reindexing commutes with compiling every actual leaf. -/
theorem rename_compile {k Z W : Type u} {s : sig.SortType} (t : CoefficientTerm quantity Γ s)
    (read : ∀ a ∈ t.leaves, LeafValue k Z a) (f : Z → W) :
    (t.compile read).rename f = t.compile (fun a h => mapLeafValue f a (read a h)) := by
  induction t <;> simp [compile, Expression.rename, mapLeafValue, *]
  rfl

/-- The term for a particular written literal or quantity application. -/
def leafTerm (a : Literal sig ⊕ Application quantity Γ) : Σ s : sig.SortType, Term sig Γ s :=
  match a with
  | .inl ⟨s, symbol⟩ => ⟨s, symbol.term Term.argsNil⟩
  | .inr ⟨j, args⟩ => ⟨_, Term.app j.val.operation (fun i => args i)⟩

/-- Each actual leaf has the value sort of its enclosing coefficient term. -/
theorem leafSort_eq {s : sig.SortType} (t : CoefficientTerm quantity Γ s)
    {a : Literal sig ⊕ Application quantity Γ} (used : a ∈ t.leaves) : (leafTerm a).1 = s := by
  induction t with
  | scalar symbol =>
    obtain rfl := Set.mem_singleton_iff.mp used
    rfl
  | quantity j args =>
    obtain rfl := Set.mem_singleton_iff.mp used
    rfl
  | add op l r il ir => exact used.elim il ir
  | neg op t it => exact it used
  | sub op l r il ir => exact used.elim il ir
  | mul op l r il ir => exact used.elim il ir

section References

open DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {Q : Set (QuantityDeclaration P.signature)}
variable {Δ : List P.signature.SortType}

/-- All references in a typed coefficient argument survive in its whole application. -/
theorem coefficientArg_refs {profile : Arity P.signature.SortType}
    (op : CoefficientSymbol P.signature profile)
    (args : ∀ {s}, Var profile.inputs s → Term P.signature Δ s)
    {s : P.signature.SortType} (i : Var profile.inputs s) :
    termReferences (args i) ⊆ termReferences (op.term args) := by
  rcases op with ⟨symbol, same⟩
  subst profile
  intro d used
  change d ∈ termReferences (Term.app symbol args)
  exact Or.inr ⟨_, i, used⟩

/-- Every actual leaf contributes its full primitive references to the original rendered term. -/
theorem leafReferences_subset {s : P.signature.SortType} (t : CoefficientTerm Q Δ s)
    {a : Literal P.signature ⊕ Application Q Δ} (ha : a ∈ t.leaves) :
    termReferences (leafTerm a).2 ⊆ termReferences t.toTerm := by
  induction t with
  | scalar symbol =>
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact Set.Subset.rfl
  | quantity j args =>
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact Set.Subset.rfl
  | add symbol l r hl hr =>
    rcases ha with ha | ha
    · exact (hl ha).trans (coefficientArg_refs symbol (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here)
    · exact (hr ha).trans (coefficientArg_refs symbol (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here))
  | neg symbol t ht =>
    exact (ht ha).trans (coefficientArg_refs symbol (fun i => t.toTerm.argsCons Term.argsNil i) .here)
  | sub symbol l r hl hr =>
    rcases ha with ha | ha
    · exact (hl ha).trans (coefficientArg_refs symbol (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here)
    · exact (hr ha).trans (coefficientArg_refs symbol (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here))
  | mul symbol l r hl hr =>
    rcases ha with ha | ha
    · exact (hl ha).trans (coefficientArg_refs symbol (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here)
    · exact (hr ha).trans (coefficientArg_refs symbol (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here))

/-- The original render of an arithmetic application refers to its own declared operation. -/
theorem coefficientHead_ref {profile : Arity P.signature.SortType}
    (op : CoefficientSymbol P.signature profile)
    (args : ∀ {s}, Var profile.inputs s → Term P.signature Δ s) :
    Declaration.ofOperation op.operation ∈ termReferences (op.term args) := by
  rcases op with ⟨symbol, same⟩
  subst profile
  change Declaration.ofOperation symbol ∈ termReferences (Term.app symbol args)
  exact Or.inl (Set.mem_singleton _)

/-- Written arithmetic nodes are retained by the support of their original typed term. -/
theorem arithmetic_reference {s : P.signature.SortType} (t : CoefficientTerm Q Δ s)
    {a : ArithmeticOperation P.signature} (ha : a ∈ t.arithmetic) :
    Declaration.ofOperation a.operation ∈ termReferences t.toTerm := by
  induction t with
  | scalar => exact False.elim ha
  | quantity => exact False.elim ha
  | add op l r il ir =>
    rcases ha with atHead | atLeft | atRight
    · have eq := Set.mem_singleton_iff.mp atHead
      subst a
      exact coefficientHead_ref op _
    · exact coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i)
        .here (il atLeft)
    · exact coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i)
        (.there .here) (ir atRight)
  | neg op x ix =>
    rcases ha with atHead | atArg
    · have eq := Set.mem_singleton_iff.mp atHead
      subst a
      exact coefficientHead_ref op _
    · exact coefficientArg_refs op (fun i => x.toTerm.argsCons Term.argsNil i) .here (ix atArg)
  | sub op l r il ir =>
    rcases ha with atHead | atLeft | atRight
    · have eq := Set.mem_singleton_iff.mp atHead
      subst a
      exact coefficientHead_ref op _
    · exact coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i)
        .here (il atLeft)
    · exact coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i)
        (.there .here) (ir atRight)

  | mul op l r il ir =>
    rcases ha with atHead | atLeft | atRight
    · have eq := Set.mem_singleton_iff.mp atHead
      subst a
      exact coefficientHead_ref op _
    · exact coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i)
        .here (il atLeft)
    · exact coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i)
        (.there .here) (ir atRight)

end References

end CoefficientTerm
end SHIGURE.Quantities

namespace SHIGURE.Quantities.CoefficientTerm

open DeclarationContext DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {Q : Set (QuantityDeclaration P.signature)}
variable {Γ : List P.signature.SortType} {U : DeclarationContext P} (A : ContextStructure U)

/-- Each written leaf has an actual value whenever the enclosing coefficient term does. -/
theorem exists_evaluated_leaf {s : P.signature.SortType} (t : CoefficientTerm Q Γ s)
    (e : Assignment A.carrier Γ) (a : Literal P.signature ⊕ Application Q Γ) (used : a ∈ t.leaves)
    (keep : termReferences t.toTerm ⊆ U.declarations)
    (supported : Declaration.termContext t.toTerm ≤ U)
    (y : A.carrier s) (value : A.evaluates ⟨t.toTerm, supported⟩ e y) :
    ∃ hTerm : Declaration.termContext (leafTerm a).2 ≤ U, ∃ z, A.evaluates ⟨(leafTerm a).2, hTerm⟩ e z := by
  induction t with
  | scalar sym =>
    obtain rfl := Set.mem_singleton_iff.mp used
    exact ⟨supported, y, value⟩
  | quantity j args =>
    obtain rfl := Set.mem_singleton_iff.mp used
    exact ⟨supported, y, value⟩
  | neg op t it =>
    obtain ⟨input, each, _⟩ := (op.evaluates_term_iff A _ supported e (keep (coefficientHead_ref op _)) y).1 value
    obtain ⟨h, child⟩ := each (.here : Var [_] _)
    exact it used ((coefficientArg_refs op (fun i => t.toTerm.argsCons Term.argsNil i) .here).trans keep) h _ child
  | add op l r il ir
  | sub op l r il ir
  | mul op l r il ir =>
    obtain ⟨input, each, _⟩ := (op.evaluates_term_iff A _ supported e (keep (coefficientHead_ref op _)) y).1 value
    let args := fun {s} (i : Var [_, _] s) => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i
    rcases used with onLeft | onRight
    · obtain ⟨h, child⟩ := each (.here : Var [_, _] _)
      exact il onLeft ((coefficientArg_refs op args .here).trans keep) h _ child
    · obtain ⟨h, child⟩ := each (.there .here : Var [_, _] _)
      exact ir onRight ((coefficientArg_refs op args (.there .here)).trans keep) h _ child

/-- Read a compiled leaf in the coefficient ring at the same candidate. -/
def compiledLeafValue {k Z L Q' : Type u} (q : Z → k) :
    (a : L ⊕ Q') → LeafValue k Z a → k
  | .inl _, c => c
  | .inr _, x => q x

variable {k Z : Type u} [CommRing k]

/-- Actual evaluation of a written coefficient term gives its compiled scalar value. -/
theorem evaluates_read (read : CarrierMap U A.carrier (fun _ => k))
    {s : P.signature.SortType} (t : CoefficientTerm Q Γ s)
    (e : Assignment A.carrier Γ)
    (keep : termReferences t.toTerm ⊆ U.declarations)
    (keepSort : Declaration.sort s ∈ U.declarations)
    (compiled : ∀ a ∈ t.leaves, LeafValue k Z a) (q : Z → k)
    (leafMeaning : ∀ a h (hTerm : Declaration.termContext (leafTerm a).2 ≤ U)
      (z : A.carrier (leafTerm a).1), A.evaluates ⟨(leafTerm a).2, hTerm⟩ e z →
        read s keepSort (cast (congrArg A.carrier (t.leafSort_eq h)) z) =
          compiledLeafValue q a (compiled a h))
    (arithmeticMeaning : ∀ a (h : a ∈ t.arithmetic), a.realizes A read (keep (t.arithmetic_reference h))) :
    ∀ (supported : Declaration.termContext t.toTerm ≤ U) (y : A.carrier s),
      A.evaluates ⟨t.toTerm, supported⟩ e y →
      read s keepSort y = (t.compile compiled).eval q := by
  induction t with
  | scalar sym =>
    intro supported y evaluated
    simpa only [compile, Expression.eval, Algebra.algebraMap_self, RingHom.id_apply,
      compiledLeafValue] using leafMeaning (.inl ⟨_, sym⟩) (Set.mem_singleton _) supported y evaluated
  | quantity j args =>
    intro supported y evaluated
    exact leafMeaning (.inr ⟨j, args⟩) (Set.mem_singleton _) supported y evaluated
  | add op l r il ir =>
    intro supported y evaluated
    obtain ⟨input, each, edge⟩ := (op.evaluates_term_iff A _ supported e
      (keep (coefficientHead_ref op _)) y).1 evaluated
    have meaning := arithmeticMeaning (.add op) (Or.inl (Set.mem_singleton _))
    have readValue := meaning input y edge
    change read _ keepSort y = _ at readValue
    rw [readValue]
    simp only [compile, Expression.eval, mapAssignment_apply]
    obtain ⟨hl, left⟩ := each (.here : Var [_, _] _)
    obtain ⟨hr, right⟩ := each (.there .here : Var [_, _] _)
    exact congrArg₂ (· + ·)
      (il ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here).trans keep) keepSort _ (fun a h => leafMeaning a (Or.inl h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inl h))) hl _ left)
      (ir ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here)).trans keep) keepSort _ (fun a h => leafMeaning a (Or.inr h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inr h))) hr _ right)
  | neg op t it =>
    intro supported y evaluated
    obtain ⟨input, each, edge⟩ := (op.evaluates_term_iff A _ supported e
      (keep (coefficientHead_ref op _)) y).1 evaluated
    have meaning := arithmeticMeaning (.neg op) (Or.inl (Set.mem_singleton _))
    have readValue := meaning input y edge
    change read _ keepSort y = _ at readValue
    rw [readValue]
    simp only [compile, Expression.eval, mapAssignment_apply]
    obtain ⟨hArg, value⟩ := each (.here : Var [_] _)
    exact congrArg Neg.neg
      (it ((coefficientArg_refs op (fun i => t.toTerm.argsCons Term.argsNil i) .here).trans keep) keepSort _ leafMeaning (fun a h => arithmeticMeaning a (Or.inr h)) hArg _ value)
  | sub op l r il ir =>
    intro supported y evaluated
    obtain ⟨input, each, edge⟩ := (op.evaluates_term_iff A _ supported e
      (keep (coefficientHead_ref op _)) y).1 evaluated
    have meaning := arithmeticMeaning (.sub op) (Or.inl (Set.mem_singleton _))
    have readValue := meaning input y edge
    change read _ keepSort y = _ at readValue
    rw [readValue]
    simp only [compile, Expression.eval, mapAssignment_apply, sub_eq_add_neg]
    obtain ⟨hl, left⟩ := each (.here : Var [_, _] _)
    obtain ⟨hr, right⟩ := each (.there .here : Var [_, _] _)
    exact congrArg₂ (fun x y : k => x + -y)
      (il ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here).trans keep) keepSort _ (fun a h => leafMeaning a (Or.inl h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inl h))) hl _ left)
      (ir ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here)).trans keep) keepSort _ (fun a h => leafMeaning a (Or.inr h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inr h))) hr _ right)
  | mul op l r il ir =>
    intro supported y evaluated
    obtain ⟨input, each, edge⟩ := (op.evaluates_term_iff A _ supported e
      (keep (coefficientHead_ref op _)) y).1 evaluated
    have meaning := arithmeticMeaning (.mul op) (Or.inl (Set.mem_singleton _))
    have readValue := meaning input y edge
    change read _ keepSort y = _ at readValue
    rw [readValue]
    simp only [compile, Expression.eval, mapAssignment_apply]
    obtain ⟨hl, left⟩ := each (.here : Var [_, _] _)
    obtain ⟨hr, right⟩ := each (.there .here : Var [_, _] _)
    exact congrArg₂ (· * ·)
      (il ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here).trans keep) keepSort _ (fun a h => leafMeaning a (Or.inl h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inl h))) hl _ left)
      (ir ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here)).trans keep) keepSort _ (fun a h => leafMeaning a (Or.inr h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inr h))) hr _ right)

end SHIGURE.Quantities.CoefficientTerm
