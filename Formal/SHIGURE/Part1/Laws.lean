import Formal.SHIGURE.Part1.Syntax
import Mathlib.Algebra.Ring.Basic

/-! # Law declarations, Atom facts, and residuals

Definitions 1.1 and 1.5, and the domain presentation of (1.2).

## Implementation notes

Law names index the declaration family, so equal formulas with different
names still give different declaration Atoms. An occurrence is a typed
route through a formula tree. An evaluation fact records its input tuple
and the evidence for the stated output, relation, or domain membership.

An ordered ring equation retains its two terms as data. Its Law conclusion
is constructed using the shared-output graph formula of (1.4).
-/

universe u

namespace SHIGURE

/-- A Law is a typed context, a positive input condition, and a positive conclusion. -/
structure Law (sig : Signature.{u}) where
  /-- All variables over which the Law is imposed. -/
  context : List sig.SortType
  /-- The assignments at which the condition applies. -/
  input : Formula sig context
  /-- The condition required at such assignments. -/
  conclusion : Formula sig context

namespace Law

variable {sig : Signature.{u}}

/-- The input set in (1.5). -/
def inputSet (law : Law sig) (A : Structure sig) : Set (Assignment A.carrier law.context) :=
  {e | law.input.Holds A e}

/-- A structure satisfies a Law when its conclusion holds at each designated input. -/
def Holds (law : Law sig) (A : Structure sig) : Prop :=
  ∀ e ∈ law.inputSet A, law.conclusion.Holds A e

/-- The input set reads the Law's antecedent. -/
@[simp] theorem mem_inputSet_iff (law : Law sig) (A : Structure sig)
    (e : Assignment A.carrier law.context) : e ∈ law.inputSet A ↔ law.input.Holds A e :=
  Iff.rfl

/-- Apply Law satisfaction at an assignment satisfying its input condition. -/
theorem holds_at {law : Law sig} {A : Structure sig} (h : law.Holds A)
    {e : Assignment A.carrier law.context} (he : law.input.Holds A e) :
    law.conclusion.Holds A e :=
  h e ((law.mem_inputSet_iff A e).2 he)

/-- An equality imposed on the whole context of its terms. -/
def equality {Γ : List sig.SortType} {s : sig.SortType} (lhs rhs : Term sig Γ s) : Law sig :=
  ⟨Γ, .truth, Formula.termEq lhs rhs⟩

/-- An unconditional equality holds exactly when each input gives the same value on both sides. -/
theorem holds_equality_iff {Γ : List sig.SortType} {s : sig.SortType} (lhs rhs : Term sig Γ s)
    (A : Structure sig) : (equality lhs rhs).Holds A ↔
      ∀ e : Assignment A.carrier Γ, ∃ y, lhs.Evaluates A e y ∧ rhs.Evaluates A e y := by
  constructor
  · intro h e
    simpa only [equality, Formula.holds_termEq, Term.mem_eval_iff] using h e True.intro
  · intro h e _
    simpa only [equality, Formula.holds_termEq, Term.mem_eval_iff] using h e

/-- In a total signature, a Law of equality compares the total evaluated values. -/
theorem holds_equality_totalValue_iff [IsEmpty sig.Partial]
    {Γ : List sig.SortType} {s : sig.SortType} (lhs rhs : Term sig Γ s)
    (A : Structure sig) : (equality lhs rhs).Holds A ↔
      ∀ e : Assignment A.carrier Γ, lhs.totalValue A e = rhs.totalValue A e := by
  rw [holds_equality_iff]
  constructor
  · intro h e
    obtain ⟨value, hl, hr⟩ := h e
    exact (Term.evaluates_unique A lhs e (Term.evaluates_totalValue A lhs e) hl).trans
      (Term.evaluates_unique A rhs e hr (Term.evaluates_totalValue A rhs e))
  · intro h e
    refine ⟨lhs.totalValue A e, Term.evaluates_totalValue A lhs e, ?_⟩
    rw [h e]
    exact Term.evaluates_totalValue A rhs e

end Law

/-- The indexed structural axioms of (1.1), shared by every theory with this signature. -/
inductive GraphAxiom (sig : Signature.{u}) : Type u
  | functional : Operation sig → GraphAxiom sig
  | totality : sig.Total → GraphAxiom sig
  | quantityTotality : sig.Quantity → GraphAxiom sig
  | graphImpliesDomain : sig.Partial → GraphAxiom sig
  | domainImpliesGraph : sig.Partial → GraphAxiom sig

namespace GraphAxiom

variable {sig : Signature.{u}}

/-- The graph of an operation has an output on the supplied inputs. -/
def hasOutput (op : Operation sig) : Formula sig op.arity.inputs :=
  .ex (.atom (.graph op (fun index => .there index) .here))

/-- The formula for output existence reads the graph on the original tuple. -/
theorem holds_hasOutput (op : Operation sig) (A : Structure sig)
    (xs : Assignment A.carrier op.arity.inputs) :
    (hasOutput op).Holds A xs ↔ ∃ y, A.Graph op xs y := by
  simp only [hasOutput, Formula.holds_ex, Formula.holds_atom, Atomic.holds_graph,
    Assignment.pull_cons_there, Assignment.pull_id, Assignment.cons_here]

/-- The variable contexts and positive sequents of (1.1). -/
def toLaw : GraphAxiom sig → Law sig
  | .functional op =>
    ⟨op.arity.output :: op.arity.output :: op.arity.inputs,
      .conj (.atom (.graph op (fun index => .there (.there index)) .here))
        (.atom (.graph op (fun index => .there (.there index)) (.there .here))),
      .atom (.eq .here (.there .here))⟩
  | .totality f =>
    ⟨(sig.totalArity f).inputs, .truth, hasOutput (.total f)⟩
  | .quantityTotality q =>
    ⟨(sig.quantityArity q).inputs, .truth, hasOutput (.quantity q)⟩
  | .graphImpliesDomain p =>
    ⟨(sig.partialArity p).output :: (sig.partialArity p).inputs,
      .atom (.graph (.partialOp p) (fun index => .there index) .here),
      .atom (.domain p (fun index => .there index))⟩
  | .domainImpliesGraph p =>
    ⟨(sig.partialArity p).inputs, .atom (.domain p (fun index => index)),
      hasOutput (.partialOp p)⟩

/-- Every structure satisfies the structural graph sequents of its signature. -/
theorem holds_toLaw (ax : GraphAxiom sig) (A : Structure sig) : ax.toLaw.Holds A := by
  cases ax with
  | functional op =>
    intro e h
    exact A.graph_rightUnique op h.1 h.2
  | totality f =>
    intro e _
    exact (holds_hasOutput (.total f) A e).2 ((GraphPresentation.total_valid A f).2 e)
  | quantityTotality q =>
    intro e _
    exact (holds_hasOutput (.quantity q) A e).2 ((GraphPresentation.quantity_valid A q).2 e)
  | graphImpliesDomain p =>
    intro e h
    exact (GraphPresentation.partial_valid A p).2.1 _ _ h
  | domainImpliesGraph p =>
    intro e h
    exact (holds_hasOutput (.partialOp p) A e).2 ((GraphPresentation.partial_valid A p).2.2 e h)

end GraphAxiom

/-- The three distinct declaration roles of Definition 1.5. -/
inductive LawRole
  | required
  | additional
  | derived

/-- The named Law declarations of a presentation, before attaching derivation trees. -/
structure LawDeclarations (sig : Signature.{u}) where
  /-- The typed names of Law declarations. -/
  LawName : Type u
  /-- The Law attached to each name. -/
  statement : LawName → Law sig
  /-- The declared role of each Law. -/
  role : LawName → LawRole

/-- A theory is a signature with a small family of required Laws. -/
structure Theory where
  /-- The vocabulary of the theory. -/
  signature : Signature.{u}
  /-- Names indexing the required Laws. -/
  LawName : Type u
  /-- The required Laws. -/
  law : LawName → Law signature

/-- Read the theory specified by the required declarations in a Law family. -/
def LawDeclarations.toTheory {sig : Signature.{u}} (laws : LawDeclarations sig) : Theory.{u} where
  signature := sig
  LawName := {name : laws.LawName // laws.role name = .required}
  law := fun name => laws.statement name.val

/-- A structure satisfies a theory by satisfying each of its required Laws. -/
def Theory.Holds (theory : Theory.{u}) (A : Structure theory.signature) : Prop :=
  ∀ name, (theory.law name).Holds A

/-- A formula occurrence records the route from a formula root to one of its nodes. -/
inductive Formula.Occurrence {sig : Signature.{u}} :
    {Γ : List sig.SortType} → Formula sig Γ → Type u
  | root {Γ} (p : Formula sig Γ) : p.Occurrence
  | conjLeft {Γ} {p q : Formula sig Γ} : p.Occurrence → (p.conj q).Occurrence
  | conjRight {Γ} {p q : Formula sig Γ} : q.Occurrence → (p.conj q).Occurrence
  | disjLeft {Γ} {p q : Formula sig Γ} : p.Occurrence → (p.disj q).Occurrence
  | disjRight {Γ} {p q : Formula sig Γ} : q.Occurrence → (p.disj q).Occurrence
  | boundBody {Γ s} {p : Formula sig (s :: Γ)} : p.Occurrence → p.ex.Occurrence

/-- Read the subformula at an occurrence with its complete context, including ambient binders. -/
def Formula.Occurrence.subformula {sig : Signature.{u}} :
    {Γ : List sig.SortType} → {p : Formula sig Γ} → p.Occurrence →
      (Σ Δ : List sig.SortType, Formula sig Δ)
  | Γ, _, .root p => ⟨Γ, p⟩
  | _, _, .conjLeft occ => occ.subformula
  | _, _, .conjRight occ => occ.subformula
  | _, _, .disjLeft occ => occ.subformula
  | _, _, .disjRight occ => occ.subformula
  | _, _, .boundBody occ => occ.subformula

/-- A Law has an input formula and a conclusion formula at distinct declaration positions. -/
inductive LawSide
  | input
  | conclusion

/-- Read the formula at a selected side of a Law declaration. -/
def LawSide.formula {sig : Signature.{u}} (law : Law sig) :
    LawSide → Formula sig law.context
  | .input => law.input
  | .conclusion => law.conclusion

/-- The seven tagged classes of declarative Atoms in Definition 1.1. -/
inductive DeclarationAtom {sig : Signature.{u}} (laws : LawDeclarations sig) : Type u
  | sort : sig.SortType → DeclarationAtom laws
  | total : sig.Total → DeclarationAtom laws
  | relation : sig.Rel → DeclarationAtom laws
  | partialOp : sig.Partial → DeclarationAtom laws
  | quantity : sig.Quantity → DeclarationAtom laws
  | law : laws.LawName → DeclarationAtom laws
  | occurrence (name : laws.LawName) (side : LawSide) :
      (LawSide.formula (laws.statement name) side).Occurrence → DeclarationAtom laws

/-- The tagged evaluation facts of a structure, retaining the full input and its symbol. -/
inductive EvaluationAtom {sig : Signature.{u}} (A : Structure sig) : Type u
  | state (s : sig.SortType) : A.carrier s → EvaluationAtom A
  | total (f : sig.Total) (xs : Assignment A.carrier (sig.totalArity f).inputs)
      (value : A.carrier (sig.totalArity f).output) :
      A.total f xs = value → EvaluationAtom A
  | relation (r : sig.Rel) (xs : Assignment A.carrier (sig.relInputs r)) :
      xs ∈ A.relation r → EvaluationAtom A
  | partialDomain (p : sig.Partial) (xs : Assignment A.carrier (sig.partialArity p).inputs) :
      xs ∈ A.partialDomain p → EvaluationAtom A
  | partialGraph (p : sig.Partial) (xs : A.partialDomain p)
      (value : A.carrier (sig.partialArity p).output) :
      A.partialValue p xs = value → EvaluationAtom A
  | quantity (q : sig.Quantity) (xs : Assignment A.carrier (sig.quantityArity q).inputs)
      (value : A.carrier (sig.quantityArity q).output) :
      A.quantity q xs = value → EvaluationAtom A

/-- Data for specifying a partial operation's domain via an inclusion sort as in (1.2). -/
structure DomainInclusions {sig : Signature.{u}} (p : sig.Partial) where
  /-- A sort intended to name domain points. -/
  domainSort : sig.SortType
  /-- One total inclusion symbol for each input position. -/
  symbol : ∀ {s}, Var (sig.partialArity p).inputs s → TotalSymbol sig
  /-- Each inclusion symbol goes from the domain sort to that input position's sort. -/
  arity_eq : ∀ {s} (index : Var (sig.partialArity p).inputs s),
    (symbol index).operation.arity = ⟨[domainSort], s⟩

namespace DomainInclusions

variable {sig : Signature.{u}} {p : sig.Partial}

/-- Apply an inclusion symbol to a term of the inclusion sort. -/
def inclusionTerm (d : DomainInclusions p) {Γ : List sig.SortType} {s : sig.SortType}
    (index : Var (sig.partialArity p).inputs s) (x : Term sig Γ d.domainSort) : Term sig Γ s :=
  (TypedTotal.mk (d.symbol index) (d.arity_eq index)).term (x.argsCons Term.argsNil)

/-- Interpret the declared inclusion symbols together as a map into the input product. -/
def inclusion (d : DomainInclusions p) (A : Structure sig) (x : A.carrier d.domainSort) :
    Assignment A.carrier (sig.partialArity p).inputs :=
  ⟨fun index => (TypedTotal.mk (d.symbol index) (d.arity_eq index)).value A
    (Assignment.cons x Assignment.empty)⟩

private theorem evaluates_inclusionTerm (d : DomainInclusions p) {Γ : List sig.SortType}
    {s : sig.SortType} (index : Var (sig.partialArity p).inputs s)
    (A : Structure sig) (e : Assignment A.carrier Γ) (x : Term sig Γ d.domainSort)
    (v : A.carrier d.domainSort) (hx : x.Evaluates A e v) :
    (d.inclusionTerm index x).Evaluates A e (d.inclusion A v index) := by
  apply TypedTotal.evaluates_term
  intro t arg
  cases arg with
  | here => exact hx
  | there previous => nomatch previous

private theorem holds_termEq_of_evaluates {Γ : List sig.SortType} {s : sig.SortType}
    {A : Structure sig} {e : Assignment A.carrier Γ} {t₁ t₂ : Term sig Γ s}
    {v₁ v₂ : A.carrier s} (h₁ : t₁.Evaluates A e v₁) (h₂ : t₂.Evaluates A e v₂) :
    (Formula.termEq t₁ t₂).Holds A e ↔ v₁ = v₂ := by
  simp only [Formula.holds_termEq, Term.mem_eval_iff]
  constructor
  · rintro ⟨v, hv₁, hv₂⟩
    exact (Term.evaluates_unique A t₁ e h₁ hv₁).trans (Term.evaluates_unique A t₂ e hv₂ h₂)
  · rintro rfl
    exact ⟨v₁, h₁, h₂⟩

/-- The joint injectivity Law in the first line of (1.2). -/
def injectivityLaw (d : DomainInclusions p) : Law sig where
  context := [d.domainSort, d.domainSort]
  input := Formula.conjoin (sig.partialArity p).inputs fun index =>
    Formula.termEq (d.inclusionTerm index (.var .here))
      (d.inclusionTerm index (.var (.there .here)))
  conclusion := .atom (.eq .here (.there .here))

/-- A tuple is in the image of the inclusion when all its coordinates come from one point. -/
def imageFormula (d : DomainInclusions p) : Formula sig (sig.partialArity p).inputs :=
  .ex (Formula.conjoin (sig.partialArity p).inputs fun index =>
    Formula.termEq (d.inclusionTerm index (.var .here)) (.var (.there index)))

/-- The domain is contained in the inclusion image, the forward direction of (1.2). -/
def domainSubsetImage (d : DomainInclusions p) : Law sig :=
  ⟨(sig.partialArity p).inputs, .atom (.domain p (fun index => index)), d.imageFormula⟩

/-- The inclusion image is contained in the domain, the reverse direction of (1.2). -/
def imageSubsetDomain (d : DomainInclusions p) : Law sig :=
  ⟨(sig.partialArity p).inputs, d.imageFormula, .atom (.domain p (fun index => index))⟩

/-- The image formula has exactly the image of the interpreted inclusion as its locus. -/
theorem holds_imageFormula (d : DomainInclusions p) (A : Structure sig)
    (e : Assignment A.carrier (sig.partialArity p).inputs) :
    d.imageFormula.Holds A e ↔ e ∈ Set.range (d.inclusion A) := by
  simp only [imageFormula, Formula.holds_ex, Formula.holds_conjoin, Set.mem_range]
  apply exists_congr
  intro x
  constructor
  · intro h
    apply Assignment.ext
    intro s i
    exact (holds_termEq_of_evaluates (d.evaluates_inclusionTerm i A
      (Assignment.cons x e) (.var .here) x rfl)
      (show (Term.var (.there i)).Evaluates A (Assignment.cons x e) (e i) from rfl)).1 (h i)
  · intro h s i
    exact (holds_termEq_of_evaluates (d.evaluates_inclusionTerm i A
      (Assignment.cons x e) (.var .here) x rfl)
      (show (Term.var (.there i)).Evaluates A (Assignment.cons x e) (e i) from rfl)).2
      (congrArg (fun a : Assignment A.carrier _ => a i) h)

/-- The first inclusion Law is equivalent to injectivity of the inclusion map. -/
theorem holds_injectivityLaw (d : DomainInclusions p) (A : Structure sig) :
    d.injectivityLaw.Holds A ↔ Function.Injective (d.inclusion A) := by
  have holdsPremise (e : Assignment A.carrier [d.domainSort, d.domainSort]) :
      d.injectivityLaw.input.Holds A e ↔ d.inclusion A (e .here) = d.inclusion A (e (.there .here)) := by
    change (Formula.conjoin _ (fun i =>
      Formula.termEq (d.inclusionTerm i (.var .here))
        (d.inclusionTerm i (.var (.there .here))))).Holds A e ↔ _
    rw [Formula.holds_conjoin]
    constructor
    · intro h
      exact Assignment.ext fun i => (holds_termEq_of_evaluates
        (d.evaluates_inclusionTerm i A e (.var .here) (e .here) rfl)
        (d.evaluates_inclusionTerm i A e (.var (.there .here)) (e (.there .here)) rfl)).1 (h i)
    · intro h _ i
      exact (holds_termEq_of_evaluates
        (d.evaluates_inclusionTerm i A e (.var .here) (e .here) rfl)
        (d.evaluates_inclusionTerm i A e (.var (.there .here)) (e (.there .here)) rfl)).2
          (congrArg (fun a : Assignment A.carrier _ => a i) h)
  constructor
  · intro h x y hxy
    let e := Assignment.cons x (Assignment.cons y Assignment.empty)
    exact h e ((holdsPremise e).2 hxy)
  · intro h e he
    exact h ((holdsPremise e).1 he)

/-- The two containment Laws specify the domain as the inclusion image. -/
theorem holds_domainLaws (d : DomainInclusions p) (A : Structure sig) :
    d.domainSubsetImage.Holds A ∧ d.imageSubsetDomain.Holds A ↔
      A.partialDomain p = Set.range (d.inclusion A) := by
  change (∀ e, e ∈ A.partialDomain p → d.imageFormula.Holds A e) ∧
    (∀ e, d.imageFormula.Holds A e → e ∈ A.partialDomain p) ↔ _
  simp only [holds_imageFormula]
  exact ⟨fun h => Set.Subset.antisymm h.1 h.2, fun h => by simp [h]⟩

end DomainInclusions

end SHIGURE
