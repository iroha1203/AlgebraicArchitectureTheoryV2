import Formal.SHIGURE.Part1.RingEquations

/-! # Capture-free substitution and partial evaluation

Definition 1.7 and Theorem 1.8(1), with the substitution clause of (3).

## Implementation notes

A substitution supplies a term for each typed position. A binder keeps its
own variable and moves the older substitution terms one position outward.
The alternative of substituting textual variable names would require a fresh
name choice and an invariance proof for that choice.

The substitution domain checks every position of the source context,
including unused ones. Evaluation is first compared with any assignment
witnessed by the substituted terms. On the domain, the finite product of
their partial values supplies that assignment, without a finiteness or
decidability assumption on any carrier.

For an ordered ring equation, the written substituted Law retains the
literal formula substitution. The equation presentation keeps the two
substituted terms so the residual can read their values in order. A second
expansion of the term equation can yield a different formula tree. The
guarded comparison proves their equality of input sets and satisfaction.
-/

universe u

namespace SHIGURE

namespace Term

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType} {s : sig.SortType}

/-- Rename free positions in a term, keeping strict binders in place. -/
def rename : {Γ Δ : List sig.SortType} → {s : sig.SortType} →
    Renaming Γ Δ → Term sig Γ s → Term sig Δ s
  | _, _, _, ρ, .var i => .var (ρ i)
  | _, _, _, ρ, .app op args => .app op (fun i => rename ρ (args i))
  | _, _, _, ρ, .letBind init body => .letBind (rename ρ init) (rename ρ.lift body)

/-- Renaming is interpreted by reading the corresponding coordinates of the assignment. -/
theorem evaluates_rename (t : Term sig Γ s) (A : Structure sig) :
    ∀ {Δ : List sig.SortType} (ρ : Renaming Γ Δ) (e : Assignment A.carrier Δ) (y : A.carrier s),
      (t.rename ρ).Evaluates A e y ↔ t.Evaluates A (e.pull ρ) y := by
  induction t with
  | var i => intros; rfl
  | app op args ih =>
    intro Δ ρ e y
    simp only [rename, evaluates_app_iff, ih]
  | letBind init body hi hb =>
    intro Δ ρ e y
    simp only [rename, evaluates_let_iff, hi, hb, Assignment.pull_lift_cons]

end Term

/-- A typed term for every position of the source context in Definition 1.7. -/
structure Substitution (sig : Signature.{u}) (Γ Δ : List sig.SortType) where
  /-- The replacement term for a source variable at its declared sort. -/
  get : ∀ {s}, Var Γ s → Term sig Δ s

namespace Substitution

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType} {s : sig.SortType}

/-- A substitution can be applied to a variable of its context. -/
instance : CoeFun (Substitution sig Γ Δ) (fun _ => ∀ {s}, Var Γ s → Term sig Δ s) :=
  ⟨get⟩

/-- Extend a substitution under one binder, keeping the bound position fixed. -/
def lift (θ : Substitution sig Γ Δ) : Substitution sig (s :: Γ) (s :: Δ) :=
  ⟨fun i => match i with
    | .here => .var .here
    | .there previous => (θ previous).rename (fun j => .there j)⟩

/-- All substituted positions have the values of one target assignment. -/
def EvaluatesAt (θ : Substitution sig Γ Δ) (A : Structure sig)
    (e : Assignment A.carrier Δ) (values : Assignment A.carrier Γ) : Prop :=
  ∀ {s} (i : Var Γ s), (θ i).Evaluates A e (values i)

/-- Under a binder the two assignments are extended by the same value. -/
theorem lift_evaluatesAt {θ : Substitution sig Γ Δ} {A : Structure sig}
    {e : Assignment A.carrier Δ} {values : Assignment A.carrier Γ}
    (h : θ.EvaluatesAt A e values) (x : A.carrier s) :
    (θ.lift (s := s)).EvaluatesAt A (Assignment.cons x e) (Assignment.cons x values) := by
  intro t i
  cases i with
  | here => rfl
  | there previous =>
    change ((θ previous).rename (fun i => .there i)).Evaluates A (Assignment.cons x e)
      ((Assignment.cons x values) (.there previous))
    simpa only [Term.evaluates_rename, Assignment.pull_cons_there, Assignment.pull_id,
      Assignment.cons_there] using h previous

/-- The conjunction requiring every substitution term to be defined. -/
def defined (θ : Substitution sig Γ Δ) : Formula sig Δ :=
  Formula.conjoin Γ (fun i => (θ i).defined)

/-- The intersection of the domains of all substituted terms. -/
def domain (θ : Substitution sig Γ Δ) (A : Structure sig) : Set (Assignment A.carrier Δ) :=
  {e | ∀ {s} (i : Var Γ s), e ∈ (θ i).domain A}

/-- The substitution domain is the locus of the entire definedness conjunction. -/
theorem holds_defined (θ : Substitution sig Γ Δ) (A : Structure sig) (e : Assignment A.carrier Δ) :
    θ.defined.Holds A e ↔ e ∈ θ.domain A := by
  rw [defined, Formula.holds_conjoin]
  constructor
  · intro h t i
    exact (Term.holds_defined _ A e).1 (h i)
  · intro h t i
    exact (Term.holds_defined _ A e).2 (h i)

/-- The evaluated substitution on its domain, as in (1.8). -/
noncomputable def value (θ : Substitution sig Γ Δ) (A : Structure sig) (e : θ.domain A) :
    Assignment A.carrier Γ :=
  ⟨fun i => ((θ i).eval A e.val).get (((θ i).mem_domain_iff A e.val).1 (e.property i))⟩

/-- The evaluated assignment has precisely the substituted values. -/
theorem evaluatesAt_value (θ : Substitution sig Γ Δ) (A : Structure sig) (e : θ.domain A) :
    θ.EvaluatesAt A e.val (θ.value A e) := by
  intro t i
  apply ((θ i).mem_eval_iff A e.val _).1
  exact ⟨_, rfl⟩

end Substitution

namespace Term

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType} {s : sig.SortType}

/-- Simultaneous capture-free substitution in a strict term. -/
def substitute : {Γ Δ : List sig.SortType} → {s : sig.SortType} →
    Substitution sig Γ Δ → Term sig Γ s → Term sig Δ s
  | _, _, _, θ, .var i => θ i
  | _, _, _, θ, .app op args => .app op (fun i => substitute θ (args i))
  | _, _, _, θ, .letBind init body => .letBind (substitute θ init) (substitute θ.lift body)

/-- Theorem 1.8(1) for a tuple of arbitrary evaluated substitution values. -/
theorem evaluates_substitute_of_evaluatesAt (t : Term sig Γ s) (A : Structure sig) :
    ∀ {Δ : List sig.SortType} (θ : Substitution sig Γ Δ) (e : Assignment A.carrier Δ)
      (values : Assignment A.carrier Γ) (y : A.carrier s),
      θ.EvaluatesAt A e values → ((t.substitute θ).Evaluates A e y ↔ t.Evaluates A values y) := by
  induction t with
  | var i =>
    intro Δ θ e values y h
    rw [substitute, evaluates_var_iff]
    exact ⟨fun hy => (θ i).evaluates_unique A e (h i) hy, fun hy => hy ▸ h i⟩
  | app op args ih =>
    intro Δ θ e values y h
    simp only [substitute, evaluates_app_iff, fun i z => ih i θ e values z h]
  | letBind init body hi hb =>
    intro Δ θ e values y h
    simp only [substitute, evaluates_let_iff, fun z => hi θ e values z h]
    exact exists_congr fun x => and_congr_right fun _ =>
      hb θ.lift (Assignment.cons x e) (Assignment.cons x values) y (Substitution.lift_evaluatesAt h x)

/-- Theorem 1.8(1): evaluation and definedness agree on the domain of the substitution. -/
theorem evaluates_substitute (t : Term sig Γ s) (θ : Substitution sig Γ Δ)
    (A : Structure sig) (e : θ.domain A) (y : A.carrier s) :
    (t.substitute θ).Evaluates A e.val y ↔ t.Evaluates A (θ.value A e) y :=
  t.evaluates_substitute_of_evaluatesAt A θ e.val _ y (θ.evaluatesAt_value A e)

/-- Substitution agrees with the original partial value on the domain of the substitution. -/
theorem eval_substitute (t : Term sig Γ s) (θ : Substitution sig Γ Δ)
    (A : Structure sig) (e : θ.domain A) :
    (t.substitute θ).eval A e.val = t.eval A (θ.value A e) := by
  apply Part.ext
  intro y
  simpa only [Term.mem_eval_iff] using t.evaluates_substitute θ A e y

/-- Substitution preserves the input's membership in the domain of the original term. -/
theorem mem_domain_substitute (t : Term sig Γ s) (θ : Substitution sig Γ Δ)
    (A : Structure sig) (e : θ.domain A) :
    e.val ∈ (t.substitute θ).domain A ↔ θ.value A e ∈ t.domain A :=
  exists_congr fun y => t.evaluates_substitute θ A e y

end Term

namespace Atomic

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType}

/-- Substitute the argument terms of an atom and apply the positive graph expansion (1.4). -/
def substitute (θ : Substitution sig Γ Δ) : Atomic sig Γ → Formula sig Δ
  | .eq x y => Formula.termEq (θ x) (θ y)
  | .rel r inputs => Formula.termRel r (fun i => θ (inputs i))
  | .domain p inputs => Formula.termDomain p (fun i => θ (inputs i))
  | .graph op inputs output => Formula.termGraph op (fun i => θ (inputs i)) (θ output)

/-- The graph of an evaluated substitution term has one output value. -/
private theorem evaluated_eq {sig : Signature.{u}} {Γ Δ : List sig.SortType}
    (θ : Substitution sig Γ Δ) (A : Structure sig) (e : Assignment A.carrier Δ)
    (values : Assignment A.carrier Γ) (h : θ.EvaluatesAt A e values)
    {s : sig.SortType} (i : Var Γ s) (y : A.carrier s) :
    y ∈ (θ i).eval A e ↔ y = values i := by
  rw [Term.mem_eval_iff]
  exact ⟨fun hy => (θ i).evaluates_unique A e hy (h i), fun hy => hy.symm ▸ h i⟩

/-- The values read by a tuple of variable arguments form exactly its selected assignment. -/
private theorem evaluated_tuple {sig : Signature.{u}} {Γ Δ Λ : List sig.SortType}
    (θ : Substitution sig Γ Δ) (A : Structure sig) (e : Assignment A.carrier Δ)
    (values : Assignment A.carrier Γ) (h : θ.EvaluatesAt A e values)
    (inputs : Renaming Λ Γ) (xs : Assignment A.carrier Λ) :
    (∀ {s} (i : Var Λ s), xs i ∈ (θ (inputs i)).eval A e) ↔ xs = values.pull inputs := by
  constructor
  · intro hx
    apply Assignment.ext
    intro t i
    exact (evaluated_eq θ A e values h (inputs i) (xs i)).1 (hx i)
  · intro hx t i
    exact (evaluated_eq θ A e values h (inputs i) (xs i)).2
      (congrArg (fun a : Assignment A.carrier Λ => a i) hx)

/-- On evaluated inputs, a substituted atom has the original atom's truth value. -/
theorem holds_substitute_of_evaluatesAt (atom : Atomic sig Γ) (θ : Substitution sig Γ Δ)
    (A : Structure sig) (e : Assignment A.carrier Δ) (values : Assignment A.carrier Γ)
    (h : θ.EvaluatesAt A e values) :
    (atom.substitute θ).Holds A e ↔ atom.Holds A values := by
  cases atom with
  | eq x y =>
    simp only [substitute, Formula.holds_termEq, evaluated_eq θ A e values h]
    change (∃ z, z = values x ∧ z = values y) ↔ values x = values y
    exact ⟨fun ⟨_, hx, hy⟩ => hx.symm.trans hy, fun hxy => ⟨_, rfl, hxy⟩⟩
  | rel r inputs =>
    simp only [substitute, Formula.holds_termRel, evaluated_tuple θ A e values h]
    change (∃ xs, xs = values.pull inputs ∧ xs ∈ A.relation r) ↔ _
    exact ⟨fun ⟨_, rfl, hx⟩ => hx, fun hx => ⟨_, rfl, hx⟩⟩
  | domain p inputs =>
    simp only [substitute, Formula.holds_termDomain, evaluated_tuple θ A e values h]
    exact ⟨fun ⟨_, rfl, hx⟩ => hx, fun hx => ⟨_, rfl, hx⟩⟩
  | graph op inputs output =>
    simp only [substitute, Formula.holds_termGraph, evaluated_tuple θ A e values h inputs,
      evaluated_eq θ A e values h output]
    exact ⟨fun ⟨_, _, rfl, rfl, hg⟩ => hg, fun hg => ⟨_, _, rfl, rfl, hg⟩⟩

end Atomic

namespace Formula

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType}

/-- Extend term substitution from atoms to positive formulas, lifting under quantifiers. -/
def substitute : {Γ Δ : List sig.SortType} → Substitution sig Γ Δ → Formula sig Γ → Formula sig Δ
  | _, _, θ, .atom a => a.substitute θ
  | _, _, _, .truth => .truth
  | _, _, _, .falsehood => .falsehood
  | _, _, θ, .conj p q => .conj (substitute θ p) (substitute θ q)
  | _, _, θ, .disj p q => .disj (substitute θ p) (substitute θ q)
  | _, _, θ, .ex p => .ex (substitute θ.lift p)

/-- Formula substitution preserves satisfaction at any evaluated assignment. -/
theorem holds_substitute_of_evaluatesAt (p : Formula sig Γ) (A : Structure sig) :
    ∀ {Δ : List sig.SortType} (θ : Substitution sig Γ Δ) (e : Assignment A.carrier Δ)
      (values : Assignment A.carrier Γ),
      θ.EvaluatesAt A e values → ((p.substitute θ).Holds A e ↔ p.Holds A values) := by
  induction p with
  | atom a => exact fun θ e values h => a.holds_substitute_of_evaluatesAt θ A e values h
  | truth => intros; rfl
  | falsehood => intros; rfl
  | conj p q hp hq =>
    intro Δ θ e values h
    simp only [substitute, holds_conj, hp θ e values h, hq θ e values h]
  | disj p q hp hq =>
    intro Δ θ e values h
    simp only [substitute, holds_disj, hp θ e values h, hq θ e values h]
  | ex p hp =>
    intro Δ θ e values h
    simp only [substitute, holds_ex]
    exact exists_congr fun x => hp θ.lift (Assignment.cons x e) (Assignment.cons x values)
      (Substitution.lift_evaluatesAt h x)

/-- Formula satisfaction in Theorem 1.8(1), on exactly the domain in (1.8). -/
theorem holds_substitute (p : Formula sig Γ) (θ : Substitution sig Γ Δ)
    (A : Structure sig) (e : θ.domain A) :
    (p.substitute θ).Holds A e.val ↔ p.Holds A (θ.value A e) :=
  p.holds_substitute_of_evaluatesAt A θ e.val _ (θ.evaluatesAt_value A e)

end Formula

namespace Law

variable {sig : Signature.{u}} {Δ : List sig.SortType}

/-- Substitute a Law, adding the definedness of every substitution term to its antecedent. -/
def substitute (law : Law sig) (θ : Substitution sig law.context Δ) : Law sig :=
  ⟨Δ, θ.defined.conj (law.input.substitute θ), law.conclusion.substitute θ⟩

/-- The inputs of the substituted Law are the preimage of the original inputs on the domain. -/
theorem mem_inputSet_substitute (law : Law sig) (θ : Substitution sig law.context Δ)
    (A : Structure sig) (e : Assignment A.carrier Δ) :
    e ∈ (law.substitute θ).inputSet A ↔ ∃ h : e ∈ θ.domain A,
      θ.value A ⟨e, h⟩ ∈ law.inputSet A := by
  simp only [mem_inputSet_iff, substitute]
  constructor
  · intro he
    obtain ⟨hd, hi⟩ := (Formula.holds_conj _ _ _ _).1 he
    have member : e ∈ θ.domain A := (θ.holds_defined A e).1 hd
    exact ⟨member, (law.input.holds_substitute θ A ⟨e, member⟩).1 hi⟩
  · rintro ⟨member, hi⟩
    exact (Formula.holds_conj _ _ _ _).2
      ⟨(θ.holds_defined A e).2 member, (law.input.holds_substitute θ A ⟨e, member⟩).2 hi⟩

end Law

namespace RingEquation

variable {sig : Signature.{u}} {Δ : List sig.SortType}

/-- Substitute an ordered equation, keeping its ring and adding the full definedness antecedent. -/
def substitute (eqn : RingEquation sig) (θ : Substitution sig eqn.context Δ) : RingEquation sig :=
  { context := Δ
    input := θ.defined.conj (eqn.input.substitute θ)
    result := eqn.result
    ring := eqn.ring
    left := eqn.left.substitute θ
    right := eqn.right.substitute θ }

/-- The written Law retains the original expanded conclusion after Formula substitution. -/
def substitutedLaw (eqn : RingEquation sig) (θ : Substitution sig eqn.context Δ) : Law sig :=
  eqn.toLaw.substitute θ

/-- Both views of the substituted equation have the same guarded input set. -/
theorem substitutedLaw_inputSet (eqn : RingEquation sig) (θ : Substitution sig eqn.context Δ)
    (A : Structure sig) :
    (eqn.substitutedLaw θ).inputSet A = (eqn.substitute θ).toLaw.inputSet A :=
  rfl

/-- On the substitution domain, the written conclusion tests the substituted ordered terms. -/
theorem substitutedLaw_conclusion_iff (eqn : RingEquation sig)
    (θ : Substitution sig eqn.context Δ) (A : Structure sig) (e : θ.domain A) :
    (eqn.substitutedLaw θ).conclusion.Holds A e.val ↔
      (eqn.substitute θ).toLaw.conclusion.Holds A e.val := by
  change ((Formula.termEq eqn.left eqn.right).substitute θ).Holds A e.val ↔
    (Formula.termEq (eqn.left.substitute θ) (eqn.right.substitute θ)).Holds A e.val
  rw [Formula.holds_substitute _ θ A e, Formula.holds_termEq, Formula.holds_termEq,
    ← eqn.left.eval_substitute θ A e, ← eqn.right.eval_substitute θ A e]

/-- The written substitution Law and its ordered term presentation have the same models. -/
theorem substitutedLaw_holds_iff (eqn : RingEquation sig)
    (θ : Substitution sig eqn.context Δ) (A : Structure sig) :
    (eqn.substitutedLaw θ).Holds A ↔ (eqn.substitute θ).toLaw.Holds A := by
  have dom (e : Assignment A.carrier Δ) (h : e ∈ (eqn.substitutedLaw θ).inputSet A) :
      e ∈ θ.domain A :=
    ((eqn.toLaw.mem_inputSet_substitute θ A e).1 h).elim fun h _ => h
  constructor
  · intro h e he
    have hd : e ∈ θ.domain A := dom e he
    exact (eqn.substitutedLaw_conclusion_iff θ A ⟨e, hd⟩).1 (h e he)
  · intro h e he
    have hd : e ∈ θ.domain A := dom e he
    exact (eqn.substitutedLaw_conclusion_iff θ A ⟨e, hd⟩).2 (h e he)

/-- The joint locus after substitution is the preimage of the original locus on the domain. -/
theorem mem_jointInputs_substitute (eqn : RingEquation sig) (θ : Substitution sig eqn.context Δ)
    (A : Structure sig) (e : Assignment A.carrier Δ) :
    e ∈ (eqn.substitute θ).jointInputs A ↔ ∃ h : e ∈ θ.domain A,
      θ.value A ⟨e, h⟩ ∈ eqn.jointInputs A := by
  constructor
  · intro he
    obtain ⟨h, hi⟩ := (eqn.toLaw.mem_inputSet_substitute θ A e).1 he.1
    exact ⟨h, hi, (eqn.left.mem_domain_substitute θ A ⟨e, h⟩).1 he.2.1,
      (eqn.right.mem_domain_substitute θ A ⟨e, h⟩).1 he.2.2⟩
  · rintro ⟨h, hi, hl, hr⟩
    exact ⟨(eqn.toLaw.mem_inputSet_substitute θ A e).2 ⟨h, hi⟩,
      (eqn.left.mem_domain_substitute θ A ⟨e, h⟩).2 hl,
      (eqn.right.mem_domain_substitute θ A ⟨e, h⟩).2 hr⟩

/-- The joint input sets are related by the substitution preimage in Theorem 1.8(3). -/
theorem jointInputs_substitute (eqn : RingEquation sig) (θ : Substitution sig eqn.context Δ)
    (A : Structure sig) :
    (eqn.substitute θ).jointInputs A = {e | ∃ h : e ∈ θ.domain A,
      θ.value A ⟨e, h⟩ ∈ eqn.jointInputs A} :=
  Set.ext (eqn.mem_jointInputs_substitute θ A)

/-- Evaluate a joint input of the substituted equation as a joint input of the original one. -/
noncomputable def substituteInput (eqn : RingEquation sig) (θ : Substitution sig eqn.context Δ)
    (A : Structure sig) (e : (eqn.substitute θ).jointInputs A) : eqn.jointInputs A := by
  have he := (eqn.mem_jointInputs_substitute θ A e.val).1 e.property
  have hd : e.val ∈ θ.domain A := he.elim fun h _ => h
  refine ⟨θ.value A ⟨e.val, hd⟩, ?_⟩
  obtain ⟨_, h⟩ := he
  exact h

/-- The substitution clause of Theorem 1.8(3): residual values agree at corresponding joint inputs. -/
theorem residual_substitute (eqn : RingEquation sig) (θ : Substitution sig eqn.context Δ)
    (A : Structure sig) (h : ∀ name, (eqn.ring.law name).Holds A)
    (e : (eqn.substitute θ).jointInputs A) :
    (eqn.substitute θ).residual A h e = eqn.residual A h (eqn.substituteInput θ A e) := by
  have hd : e.val ∈ θ.domain A :=
    ((eqn.mem_jointInputs_substitute θ A e.val).1 e.property).elim fun h _ => h
  let d : θ.domain A := ⟨e.val, hd⟩
  let original := eqn.substituteInput θ A e
  have hl : (eqn.substitute θ).leftValue A e = eqn.leftValue A original := by
    apply Part.mem_unique _ (eqn.leftValue_mem A original)
    apply (eqn.left.mem_eval_iff A original.val _).2
    exact (eqn.left.evaluates_substitute θ A d _).1
      ((Term.mem_eval_iff _ _ _ _).1 ((eqn.substitute θ).leftValue_mem A e))
  have hr : (eqn.substitute θ).rightValue A e = eqn.rightValue A original := by
    apply Part.mem_unique _ (eqn.rightValue_mem A original)
    apply (eqn.right.mem_eval_iff A original.val _).2
    exact (eqn.right.evaluates_substitute θ A d _).1
      ((Term.mem_eval_iff _ _ _ _).1 ((eqn.substitute θ).rightValue_mem A e))
  rw [residual_eq_add_neg, residual_eq_add_neg, hl, hr]
  rfl

/-- Satisfaction of the written substituted Law is the full-domain, zero-residual condition. -/
theorem substitutedLaw_holds_iff_residual (eqn : RingEquation sig)
    (θ : Substitution sig eqn.context Δ) (A : Structure sig)
    (h : ∀ name, (eqn.ring.law name).Holds A) :
    (eqn.substitutedLaw θ).Holds A ↔
      (eqn.substitute θ).jointInputs A = (eqn.substitutedLaw θ).inputSet A ∧
      ∀ e : (eqn.substitute θ).jointInputs A,
        (eqn.substitute θ).residual A h e = eqn.ring.zeroValue A :=
  (eqn.substitutedLaw_holds_iff θ A).trans
    ((eqn.substitute θ).holds_iff_jointInputs_and_residual_zero A h)

/-- Written expansions are generated by the ordered equality and literal substitutions. -/
inductive Expansion : (eqn : RingEquation sig) → Formula sig eqn.context → Type u
  | original (eqn : RingEquation sig) : Expansion eqn (Formula.termEq eqn.left eqn.right)
  | variablePair {eqn : RingEquation sig} (x y : Var eqn.context eqn.result)
      (left : eqn.left = .var x) (right : eqn.right = .var y) :
      Expansion eqn (.atom (.eq x y))
  | substitute {eqn : RingEquation sig} {p : Formula sig eqn.context}
      (prior : Expansion eqn p) {Δ : List sig.SortType} (θ : Substitution sig eqn.context Δ) :
      Expansion (eqn.substitute θ) (p.substitute θ)

/-- A generated expansion and its ordered terms agree on every designated input. -/
theorem Expansion.holds_iff {eqn : RingEquation sig} {p : Formula sig eqn.context}
    (expansion : Expansion eqn p) (A : Structure sig) :
    ∀ (e : Assignment A.carrier eqn.context), eqn.input.Holds A e →
      (p.Holds A e ↔ (Formula.termEq eqn.left eqn.right).Holds A e) := by
  induction expansion with
  | original eqn => intro e _; rfl
  | variablePair x y left right =>
    intro e _
    rw [left, right, Formula.holds_termEq]
    simp only [Term.mem_eval_iff]
    change e x = e y ↔ ∃ z, e x = z ∧ e y = z
    exact ⟨fun h => ⟨e x, rfl, h.symm⟩, fun ⟨_, hx, hy⟩ => hx.trans hy.symm⟩
  | @substitute eqn p prior Δ θ ih =>
    intro e held
    obtain ⟨h, hinput⟩ := (eqn.toLaw.mem_inputSet_substitute θ A e).1 held
    let d : θ.domain A := ⟨e, h⟩
    exact (Formula.holds_substitute p θ A d).trans
      ((ih (θ.value A d) hinput).trans
        ((Formula.holds_substitute (Formula.termEq eqn.left eqn.right) θ A d).symm.trans
          (eqn.substitutedLaw_conclusion_iff θ A d)))

/-- A written equality is an atomic variable equality or starts with its value witness. -/
theorem Expansion.shape {eqn : RingEquation sig} {p : Formula sig eqn.context}
    (expansion : Expansion eqn p) :
    (∃ (s : sig.SortType) (x y : Var eqn.context s), p = .atom (.eq x y)) ∨
      ∃ (s : sig.SortType) (body : Formula sig (s :: eqn.context)), p = body.ex := by
  induction expansion with
  | original eqn => exact Or.inr ⟨eqn.result, eqn.left.graph.conj eqn.right.graph, rfl⟩
  | variablePair x y _ _ => exact Or.inl ⟨_, x, y, rfl⟩
  | @substitute eqn p prior Δ θ ih =>
    rcases ih with ⟨s, x, y, rfl⟩ | ⟨s, body, rfl⟩
    · exact Or.inr ⟨s, (θ x).graph.conj (θ y).graph, rfl⟩
    · exact Or.inr ⟨s, body.substitute θ.lift, rfl⟩

/-- A single written Law retains its ordered terms and the origin of its expansion. -/
structure Written (sig : Signature.{u}) where
  /-- The ordered pair, ring and written input. -/
  equation : RingEquation sig
  /-- The literal written conclusion. -/
  conclusion : Formula sig equation.context
  /-- The syntax history fixes the expansion and the order of the terms. -/
  expansion : Expansion equation conclusion

/-- The usual form of a newly written equality. -/
def write (eqn : RingEquation sig) : Written sig :=
  ⟨eqn, Formula.termEq eqn.left eqn.right, .original eqn⟩

/-- Keep the original atomic notation when the ordered terms are variables. -/
def writeVariables (eqn : RingEquation sig) (x y : Var eqn.context eqn.result)
    (left : eqn.left = .var x) (right : eqn.right = .var y) : Written sig :=
  ⟨eqn, .atom (.eq x y), .variablePair x y left right⟩

/-- The very same Law, with its exact conclusion, can be used in the presentation. -/
def Written.toLaw (written : Written sig) : Law sig :=
  ⟨written.equation.context, written.equation.input, written.conclusion⟩

/-- Apply another substitution to both the literal text and the ordered terms. -/
def Written.substitute (written : Written sig) (θ : Substitution sig written.equation.context Δ) :
    Written sig :=
  ⟨written.equation.substitute θ, written.conclusion.substitute θ, written.expansion.substitute θ⟩

/-- The stored syntax after substitution is literal Law substitution. -/
@[simp] theorem Written.toLaw_substitute (written : Written sig)
    (θ : Substitution sig written.equation.context Δ) :
    (written.substitute θ).toLaw = written.toLaw.substitute θ :=
  rfl

/-- The literal Law tests the ordered residual on the entire designated input set. -/
theorem Written.holds_iff_residual (written : Written sig) (A : Structure sig)
    (ringLaws : ∀ name, (written.equation.ring.law name).Holds A) :
    written.toLaw.Holds A ↔ written.equation.jointInputs A = written.toLaw.inputSet A ∧
      ∀ e : written.equation.jointInputs A,
        written.equation.residual A ringLaws e = written.equation.ring.zeroValue A := by
  have equivalent : written.toLaw.Holds A ↔ written.equation.toLaw.Holds A :=
    ⟨fun holds e he => (written.expansion.holds_iff A e he).1 (holds e he),
      fun holds e he => (written.expansion.holds_iff A e he).2 (holds e he)⟩
  exact equivalent.trans (written.equation.holds_iff_jointInputs_and_residual_zero A ringLaws)

end RingEquation

end SHIGURE
