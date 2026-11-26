import Formal.SHIGURE.Part1.ContextSelectedStructures
import Formal.SHIGURE.Part1.ContextSelectedTerms
import Formal.SHIGURE.Part2.Quantities.FixedModels
import Formal.SHIGURE.Part2.QuantityTransport.DeclarationStates

/-!
# Typed coefficient syntax for declared quantity Laws

The typed terms retain the original operation at each node. A literal
uses the actual interpreted nullary symbol. The arithmetic relations
compare the ordinary declared operations with the coefficient ring on
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

/-- A declared coefficient operation may be ordinary or a fixed marked quantity. -/
abbrev CoefficientSymbol := TypedTotal

namespace CoefficientSymbol

section NativeValue

open DeclarationContext

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}
variable {profile : Arity P.signature.SortType}

/-- Read a retained coefficient operator using its actual primitive interpretation. -/
noncomputable def nativeValue (op : CoefficientSymbol P.signature profile) (A : ContextStructure U)
    (keep : Declaration.ofOperation op.symbol.operation ∈ U.declarations)
    (input : Assignment A.carrier profile.inputs) : A.carrier profile.output :=
  by
    rcases op with ⟨symbol, same⟩
    subst profile
    cases symbol with
    | ordinary f => exact A.toRestrictedStructure.total f keep input
    | quantity q => exact A.toRestrictedStructure.quantity q keep input

/-- The native coefficient value satisfies the actual graph of the declared symbol. -/
theorem nativeValue_graph (op : CoefficientSymbol P.signature profile) (A : ContextStructure U)
    (keep : Declaration.ofOperation op.symbol.operation ∈ U.declarations)
    (input : Assignment A.carrier profile.inputs) :
    A.evaluation.graph op.symbol.operation keep
      (cast (congrArg (Assignment A.carrier) (congrArg Arity.inputs op.arity_eq).symm) input)
      (cast (congrArg A.carrier (congrArg Arity.output op.arity_eq).symm) (op.nativeValue A keep input)) := by
  rcases op with ⟨symbol, same⟩
  subst profile
  cases symbol with
  | ordinary f =>
    rw [← A.toRestrictedStructure_evaluation, RestrictedStructure.evaluation_graph]
    exact (RestrictedStructure.graph_total_iff _ _ _ _ _).2 rfl
  | quantity q =>
    rw [← A.toRestrictedStructure_evaluation, RestrictedStructure.evaluation_graph]
    exact (RestrictedStructure.graph_quantity_iff _ _ _ _ _).2 rfl

/-- A typed coefficient operator retains all its declared input sorts. -/
theorem keepsInputs (op : CoefficientSymbol P.signature profile)
    (keep : Declaration.ofOperation op.symbol.operation ∈ U.declarations) :
    Declaration.sorts profile.inputs ⊆ U.declarations := by
  rw [← op.arity_eq]
  exact operationInputs op.symbol.operation keep

/-- A typed coefficient operator retains its declared result sort. -/
theorem keepsResult (op : CoefficientSymbol P.signature profile)
    (keep : Declaration.ofOperation op.symbol.operation ∈ U.declarations) :
    Declaration.sort profile.output ∈ U.declarations := by
  rw [← op.arity_eq]
  exact operationOutput op.symbol.operation keep

/-- Evaluated inputs and a retained graph give the value of the written typed application. -/
theorem evaluates_term (op : CoefficientSymbol P.signature profile) (B : ContextStructure U)
    {Γ : List P.signature.SortType} (args : ∀ {s}, Var profile.inputs s → Term P.signature Γ s)
    (supported : Declaration.termContext (op.term args) ≤ U)
    (e : Assignment B.carrier Γ) (input : Assignment B.carrier profile.inputs)
    (each : ∀ {s} (i : Var profile.inputs s), ∃ h, B.evaluates ⟨args i, h⟩ e (input i))
    (keep : Declaration.ofOperation op.symbol.operation ∈ U.declarations) (y : B.carrier profile.output)
    (edge : B.evaluation.graph op.symbol.operation keep
      (cast (congrArg (Assignment B.carrier) (congrArg Arity.inputs op.arity_eq).symm) input)
      (cast (congrArg B.carrier (congrArg Arity.output op.arity_eq).symm) y)) :
    B.evaluates ⟨op.term args, supported⟩ e y := by
  rcases op with ⟨symbol, same⟩
  subst profile
  exact B.evaluates_app_of_graph symbol.operation args ⟨_, supported⟩ rfl e input each keep y edge

/-- The carrier map of the actual reduct preserves the primitive coefficient operation. -/
theorem nativeValue_restrict (op : CoefficientSymbol P.signature profile) (A : ContextStructure U)
    (inside : V ≤ U) (keep : Declaration.ofOperation op.symbol.operation ∈ V.declarations)
    (input : Assignment (A.restrict inside).carrier profile.inputs) :
    selectedMap V A.carrier profile.output (op.keepsResult keep)
      (op.nativeValue (A.restrict inside) keep input) =
    op.nativeValue A (inside keep) (mapAssignment (selectedMap V A.carrier) (op.keepsInputs keep) input) := by
  rcases op with ⟨symbol, same⟩
  subst profile
  let op : CoefficientSymbol P.signature symbol.operation.arity := ⟨symbol, rfl⟩
  have localValue := op.nativeValue_graph (A.restrict inside) keep input
  apply A.graph_rightUnique symbol.operation (inside keep) localValue
  exact op.nativeValue_graph A (inside keep) _

/-- An interpretation identifies a retained operation's actual values with a coefficient operation. -/
def Realizes {k : Type u} (op : CoefficientSymbol P.signature profile) (A : ContextStructure U)
    (keep : Declaration.ofOperation op.symbol.operation ∈ U.declarations)
    (read : CarrierMap U A.carrier (fun _ => k))
    (meaning : Assignment (fun _ => k) profile.inputs → k) : Prop :=
  ∀ input, read profile.output (op.keepsResult keep) (op.nativeValue A keep input) =
    meaning (mapAssignment read (op.keepsInputs keep) input)

/-- Restriction carries the declared operator's coefficient interpretation through the actual value graph. -/
theorem Realizes.restrict {k : Type u} {op : CoefficientSymbol P.signature profile}
    {A : ContextStructure U} (inside : V ≤ U)
    (keep : Declaration.ofOperation op.symbol.operation ∈ V.declarations)
    {read : CarrierMap U A.carrier (fun _ => k)} {meaning : Assignment (fun _ => k) profile.inputs → k}
    (valid : op.Realizes A (inside keep) read meaning) :
    op.Realizes (A.restrict inside) keep
      (fun s hs x => read s (inside hs) (selectedMap V A.carrier s hs x)) meaning := by
  intro input
  change read profile.output (inside (op.keepsResult keep))
    (selectedMap V A.carrier profile.output (op.keepsResult keep)
      (op.nativeValue (A.restrict inside) keep input)) = _
  rw [nativeValue_restrict]
  exact valid (mapAssignment (selectedMap V A.carrier) (op.keepsInputs keep) input)

end NativeValue

end CoefficientSymbol

/-- The meanings assigned to total symbols at the written arithmetic nodes. -/
inductive ArithmeticOperation (sig : Signature.{u})
  | add {s} (symbol : CoefficientSymbol sig ⟨[s, s], s⟩)
  | neg {s} (symbol : CoefficientSymbol sig ⟨[s], s⟩)
  | mul {s} (symbol : CoefficientSymbol sig ⟨[s, s], s⟩)

namespace ArithmeticOperation

open DeclarationContext

/-- The original operation at a written arithmetic node. -/
def operation {sig : Signature.{u}} : ArithmeticOperation sig → Operation sig
  | .add op | .neg op | .mul op => op.symbol.operation

variable {k : Type u} [CommRing k]
variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}

/-- The actual operation is the indicated arithmetic when read in the coefficient ring. -/
def realizes (A : ContextStructure U) (read : CarrierMap U A.carrier (fun _ => k)) :
    (a : ArithmeticOperation P.signature) → Declaration.ofOperation a.operation ∈ U.declarations → Prop
  | .add op, keep => op.Realizes A keep read (fun x => x .here + x (.there .here))
  | .neg op, keep => op.Realizes A keep read (fun x => - x .here)
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
  | _, .mul symbol l r => symbol.term ((toTerm l).argsCons ((toTerm r).argsCons Term.argsNil))

/-- Collect the literals and applications of the actual syntax as two disjoint kinds of scalar leaves. -/
def leaves : {s : sig.SortType} → CoefficientTerm quantity Γ s → Set (Literal sig ⊕ Application quantity Γ)
  | _, .scalar symbol => {Sum.inl ⟨_, symbol⟩}
  | _, .quantity j args => {Sum.inr ⟨j, args⟩}
  | _, .add _ l r | _, .mul _ l r => l.leaves ∪ r.leaves
  | _, .neg _ x => x.leaves

/-- Only arithmetic operations appearing in the written expression need an interpretation. -/
def arithmetic : {s : sig.SortType} → CoefficientTerm quantity Γ s → Set (ArithmeticOperation sig)
  | _, .scalar _ | _, .quantity _ _ => ∅
  | _, .add op l r => {ArithmeticOperation.add op} ∪ (l.arithmetic ∪ r.arithmetic)
  | _, .neg op t => {ArithmeticOperation.neg op} ∪ t.arithmetic
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
  change d ∈ termReferences (Term.app symbol.operation args)
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
  | mul symbol l r hl hr =>
    rcases ha with ha | ha
    · exact (hl ha).trans (coefficientArg_refs symbol (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here)
    · exact (hr ha).trans (coefficientArg_refs symbol (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here))

/-- The original render of an arithmetic application refers to its own declared operation. -/
theorem coefficientHead_ref {profile : Arity P.signature.SortType}
    (op : CoefficientSymbol P.signature profile)
    (args : ∀ {s}, Var profile.inputs s → Term P.signature Δ s) :
    Declaration.ofOperation op.symbol.operation ∈ termReferences (op.term args) := by
  rcases op with ⟨symbol, same⟩
  subst profile
  change Declaration.ofOperation symbol.operation ∈ termReferences (Term.app symbol.operation args)
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

/-- Evaluate the written arithmetic in the original structure, supplying the fixed literals
and candidate quantity values at the actual leaves. -/
noncomputable def evalNative :
    {s : P.signature.SortType} → (t : CoefficientTerm Q Γ s) →
    (termReferences t.toTerm ⊆ U.declarations) →
    (∀ a ∈ t.leaves, A.carrier s) → A.carrier s
  | _, .scalar sym, _, leaf => leaf (.inl ⟨_, sym⟩) (Set.mem_singleton _)
  | _, .quantity j args, _, leaf => leaf (.inr ⟨j, args⟩) (Set.mem_singleton _)
  | _, .add op l r, keep, leaf =>
    let kept := keep (coefficientHead_ref op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i))
    op.nativeValue A kept
      (Assignment.cons
        (evalNative l ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here).trans keep)
          (fun a h => leaf a (Or.inl h)))
        (Assignment.cons
          (evalNative r ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here)).trans keep)
            (fun a h => leaf a (Or.inr h)))
          Assignment.empty))
  | _, .neg op t, keep, leaf =>
    op.nativeValue A (keep (coefficientHead_ref op (fun i => t.toTerm.argsCons Term.argsNil i)))
      (Assignment.cons (evalNative t ((coefficientArg_refs op (fun i => t.toTerm.argsCons Term.argsNil i) .here).trans keep) leaf) Assignment.empty)
  | _, .mul op l r, keep, leaf =>
    let kept := keep (coefficientHead_ref op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i))
    op.nativeValue A kept
      (Assignment.cons
        (evalNative l ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) .here).trans keep)
          (fun a h => leaf a (Or.inl h)))
        (Assignment.cons
          (evalNative r ((coefficientArg_refs op (fun i => l.toTerm.argsCons (r.toTerm.argsCons Term.argsNil) i) (.there .here)).trans keep)
            (fun a h => leaf a (Or.inr h)))
          Assignment.empty))

/-- The evaluated coefficient tree gives an actual value of its original typed term. -/
theorem evalNative_evaluates (E : RestrictedEvaluation U A.carrier) (valid : E.Structural)
    {s : P.signature.SortType} (t : CoefficientTerm Q Γ s) (e : Assignment A.carrier Γ)
    (keepΓ : Declaration.sorts Γ ⊆ U.declarations)
    (keepSort : Declaration.sort s ∈ U.declarations)
    (keep : termReferences t.toTerm ⊆ U.declarations)
    (leaf : ∀ a ∈ t.leaves, A.carrier s)
    (leaves : let B : ContextStructure U := ⟨A.carrier, A.omitted, E, valid⟩
      ∀ a (h : a ∈ t.leaves), ∃ hTerm,
        B.evaluates ⟨(leafTerm a).2, hTerm⟩ e
          (cast (congrArg A.carrier (t.leafSort_eq h).symm) (leaf a h)))
    (operators : ∀ a ∈ t.arithmetic, ∀ keep values y,
      A.evaluation.graph a.operation keep values y → E.graph a.operation keep values y) :
    let B : ContextStructure U := ⟨A.carrier, A.omitted, E, valid⟩
    ∃ hTerm, B.evaluates ⟨t.toTerm, hTerm⟩ e (t.evalNative A keep leaf) := by
  let B : ContextStructure U := ⟨A.carrier, A.omitted, E, valid⟩
  induction t with
  | scalar sym => exact leaves (.inl ⟨_, sym⟩) (Set.mem_singleton _)
  | quantity j args => exact leaves (.inr ⟨j, args⟩) (Set.mem_singleton _)
  | add op l r il ir =>
    refine ⟨termContext_le_of_references _ keepΓ keepSort keep, ?_⟩
    rw [evalNative]
    apply op.evaluates_term B
    case edge =>
      apply operators (.add op) (Or.inl (Set.mem_singleton _))
      exact op.nativeValue_graph A _ _
    intro t i
    cases i with
    | here =>
      exact il keepSort _ _ (fun a h => leaves a (Or.inl h))
        (fun a h => operators a (Or.inr (Or.inl h)))
    | there i =>
      cases i with
      | here =>
        exact ir keepSort _ _ (fun a h => leaves a (Or.inr h))
          (fun a h => operators a (Or.inr (Or.inr h)))
      | there i => nomatch i
  | neg op t it =>
    refine ⟨termContext_le_of_references _ keepΓ keepSort keep, ?_⟩
    rw [evalNative]
    apply op.evaluates_term B
    case edge =>
      apply operators (.neg op) (Or.inl (Set.mem_singleton _))
      exact op.nativeValue_graph A _ _
    intro s i
    cases i with
    | here => exact it keepSort _ _ leaves (fun a h => operators a (Or.inr h))
    | there i => nomatch i
  | mul op l r il ir =>
    refine ⟨termContext_le_of_references _ keepΓ keepSort keep, ?_⟩
    rw [evalNative]
    apply op.evaluates_term B
    case edge =>
      apply operators (.mul op) (Or.inl (Set.mem_singleton _))
      exact op.nativeValue_graph A _ _
    intro t i
    cases i with
    | here =>
      exact il keepSort _ _ (fun a h => leaves a (Or.inl h))
        (fun a h => operators a (Or.inr (Or.inl h)))
    | there i =>
      cases i with
      | here =>
        exact ir keepSort _ _ (fun a h => leaves a (Or.inr h))
          (fun a h => operators a (Or.inr (Or.inr h)))
      | there i => nomatch i

/-- Read a compiled scalar leaf in the coefficient ring. -/
def compiledLeafValue {k Z L Q' : Type u} (q : Z → k) :
    (a : L ⊕ Q') → LeafValue k Z a → k
  | .inl _, c => c
  | .inr _, x => q x

variable {k Z : Type u} [CommRing k]

/-- The original interpreted arithmetic computes the compiled expression at the native coefficients. -/
theorem evalNative_read (read : CarrierMap U A.carrier (fun _ => k))
    {s : P.signature.SortType} (t : CoefficientTerm Q Γ s)
    (keep : termReferences t.toTerm ⊆ U.declarations) (keepSort : Declaration.sort s ∈ U.declarations)
    (leaf : ∀ a ∈ t.leaves, A.carrier s)
    (compiled : ∀ a ∈ t.leaves, LeafValue k Z a) (q : Z → k)
    (leafMeaning : ∀ a h, read s keepSort (leaf a h) = compiledLeafValue q a (compiled a h))
    (arithmeticMeaning : ∀ a (h : a ∈ t.arithmetic), a.realizes A read (keep (t.arithmetic_reference h))) :
    read s keepSort (t.evalNative A keep leaf) = (t.compile compiled).eval q := by
  induction t with
  | scalar sym =>
    simpa only [evalNative, compile, Expression.eval, Algebra.algebraMap_self, RingHom.id_apply,
      compiledLeafValue] using leafMeaning (.inl ⟨_, sym⟩) (Set.mem_singleton _)
  | quantity j args =>
    exact leafMeaning (.inr ⟨j, args⟩) (Set.mem_singleton _)
  | add op l r il ir =>
    have operation := arithmeticMeaning (.add op) (Or.inl (Set.mem_singleton _))
    simp only [ArithmeticOperation.realizes, CoefficientSymbol.Realizes] at operation
    rw [evalNative, compile, Expression.eval, operation]
    simp only [mapAssignment_apply, Assignment.cons_here, Assignment.cons_there]
    exact congrArg₂ (· + ·)
      (il _ keepSort _ _ (fun a h => leafMeaning a (Or.inl h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inl h))))
      (ir _ keepSort _ _ (fun a h => leafMeaning a (Or.inr h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inr h))))
  | neg op t it =>
    have operation := arithmeticMeaning (.neg op) (Or.inl (Set.mem_singleton _))
    simp only [ArithmeticOperation.realizes, CoefficientSymbol.Realizes] at operation
    rw [evalNative, compile, Expression.eval, operation]
    simp only [mapAssignment_apply, Assignment.cons_here]
    exact congrArg Neg.neg (it _ keepSort _ _ leafMeaning (fun a h => arithmeticMeaning a (Or.inr h)))
  | mul op l r il ir =>
    have operation := arithmeticMeaning (.mul op) (Or.inl (Set.mem_singleton _))
    simp only [ArithmeticOperation.realizes, CoefficientSymbol.Realizes] at operation
    rw [evalNative, compile, Expression.eval, operation]
    simp only [mapAssignment_apply, Assignment.cons_here, Assignment.cons_there]
    exact congrArg₂ (· * ·)
      (il _ keepSort _ _ (fun a h => leafMeaning a (Or.inl h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inl h))))
      (ir _ keepSort _ _ (fun a h => leafMeaning a (Or.inr h))
        (fun a h => arithmeticMeaning a (Or.inr (Or.inr h))))

end SHIGURE.Quantities.CoefficientTerm
