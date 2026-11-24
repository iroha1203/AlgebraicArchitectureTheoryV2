import Formal.SHIGURE.Part1.ModelSemantics

/-! # Syntactic comparison of an interpretation with the identity

Corollary 2.4a(b) specifies unary terms and derivation obligations for a
self-interpretation. The two composites of an inverse pair each carry
their own such data.

## Implementation notes

A semantic natural isomorphism supplied as input would leave the
unary terms and their compatibility sequents unaccounted for. The
comparison records the terms and sequent derivations from the corollary,
with existence of derivations in both directions for relation and domain
equivalences. Soundness constructs the model isomorphisms.

Ordinary term substitution can discard an undefined argument when
the body omits its variable. The operation equations therefore use
strict application, including when a partial operation supplies the
argument. In relation and domain formulas the proofs of totality
justify substituting the unary terms at every original input.
-/

universe u

namespace SHIGURE.Substitution

variable {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}

/-- Put one term in the sole input position of a unary context. -/
def singleton (arg : Term sig Γ s) : Substitution sig [s] Γ :=
  ⟨fun i => match i with
    | .here => arg
    | .there i => nomatch i⟩

/-- At an actual argument value, the singleton substitution evaluates at that one value. -/
theorem singleton_evaluatesAt (arg : Term sig Γ s) (A : Structure sig)
    (xs : Assignment A.carrier Γ) (value : A.carrier s) (held : arg.Evaluates A xs value) :
    (singleton arg).EvaluatesAt A xs (Assignment.cons value Assignment.empty) := by
  intro t i
  cases i with
  | here => exact held
  | there i => exact nomatch i

end SHIGURE.Substitution

namespace SHIGURE.Term

variable {sig : Signature.{u}} {Γ Λ : List sig.SortType} {s t : sig.SortType}

/-- A primitive operation applied to the variables of its input context. -/
def primitive (op : Operation sig) : Term sig op.arity.inputs op.arity.output :=
  .app op (fun i => .var i)

/-- The primitive term evaluates according to its interpreted graph. -/
theorem primitive_evaluates_iff (A : Structure sig) (op : Operation sig)
    (xs : Assignment A.carrier op.arity.inputs) (y : A.carrier op.arity.output) :
    (primitive op).Evaluates A xs y ↔ A.Graph op xs y := by
  constructor
  · intro held
    obtain ⟨values, vars, graph⟩ := (evaluates_app_iff op _ A xs y).1 held
    have same : values = xs := Assignment.ext (fun i => ((evaluates_var_iff i A xs (values i)).1 (vars i)).symm)
    exact same ▸ graph
  · intro held
    exact (evaluates_app_iff op _ A xs y).2
      ⟨xs, fun i => (evaluates_var_iff i A xs (xs i)).2 rfl, held⟩

/-- Apply a unary term strictly to one argument. -/
def applyUnary (body : Term sig [s] t) (arg : Term sig Γ s) : Term sig Γ t :=
  body.applyStrict (fun i => Substitution.singleton arg i)

/-- On specified values of a tuple of arguments, strict application evaluates the body there. -/
theorem evaluates_applyStrict_of_evaluatesAt (body : Term sig Λ t) (θ : Substitution sig Λ Γ)
    (A : Structure sig) (xs : Assignment A.carrier Γ) (values : Assignment A.carrier Λ)
    (held : θ.EvaluatesAt A xs values) (y : A.carrier t) :
    (body.applyStrict fun i => θ i).Evaluates A xs y ↔ body.Evaluates A values y := by
  rw [evaluates_applyStrict]
  constructor
  · rintro ⟨other, arguments, bodyValue⟩
    have same : other = values :=
      Assignment.ext (fun i => evaluates_unique A _ _ (arguments i) (held i))
    exact same ▸ bodyValue
  · intro out
    exact ⟨values, held, out⟩

/-- The evaluated input to a strict unary application determines its body assignment. -/
theorem evaluates_applyUnary_iff (body : Term sig [s] t) (arg : Term sig Γ s)
    (A : Structure sig) (xs : Assignment A.carrier Γ) (value : A.carrier s)
    (held : arg.Evaluates A xs value) (y : A.carrier t) :
    (body.applyUnary arg).Evaluates A xs y ↔ body.Evaluates A (Assignment.cons value Assignment.empty) y :=
  evaluates_applyStrict_of_evaluatesAt body (Substitution.singleton arg) A xs _
    (Substitution.singleton_evaluatesAt arg A xs value held) y

/-- Strict unary application first evaluates its argument and then the body at that value. -/
theorem evaluates_applyUnary_exists_iff (body : Term sig [s] t) (arg : Term sig Γ s)
    (A : Structure sig) (xs : Assignment A.carrier Γ) (y : A.carrier t) :
    (body.applyUnary arg).Evaluates A xs y ↔
      ∃ value, arg.Evaluates A xs value ∧ body.Evaluates A (Assignment.cons value Assignment.empty) y := by
  constructor
  · intro held
    obtain ⟨values, arguments, _⟩ := (evaluates_applyStrict A body (fun i => Substitution.singleton arg i) xs y).1 held
    have evaluated : arg.Evaluates A xs (values .here) := arguments .here
    exact ⟨values .here, evaluated, (evaluates_applyUnary_iff body arg A xs _ evaluated y).1 held⟩
  · rintro ⟨value, evaluated, result⟩
    exact (evaluates_applyUnary_iff body arg A xs value evaluated y).2 result

end SHIGURE.Term

namespace SHIGURE.Formula

variable {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}

/-- Equality of terms identifies the outputs of their evaluations at the same assignment. -/
theorem values_eq_of_holds_termEq {a b : Term sig Γ s} {A : Structure sig}
    {xs : Assignment A.carrier Γ} {left right : A.carrier s}
    (holds : (termEq a b).Holds A xs)
    (ha : a.Evaluates A xs left) (hb : b.Evaluates A xs right) : left = right := by
  obtain ⟨y, ay, by'⟩ := (holds_termEq a b A xs).1 holds
  exact (Term.evaluates_unique A _ _ ha ((a.mem_eval_iff A xs y).1 ay)).trans
    (Term.evaluates_unique A _ _ ((b.mem_eval_iff A xs y).1 by') hb)

end SHIGURE.Formula

namespace SHIGURE.Interpretation

variable {H : Theory.{u}}

/-- The tuple of unary comparison terms applied to the variables of the original context. -/
def comparisonArguments (sorts : H.signature.SortType → H.signature.SortType)
    (alpha : ∀ s, Term H.signature [s] (sorts s)) (Γ : List H.signature.SortType) :
    Substitution H.signature (Γ.map sorts) Γ :=
  ⟨Var.reindex sorts (fun {_} i => (alpha _).applyUnary (.var i))⟩

/-- The comparison substitution at an original position is its unary term at that variable. -/
theorem comparisonArguments_apply (sorts : H.signature.SortType → H.signature.SortType)
    (alpha : ∀ s, Term H.signature [s] (sorts s)) {Γ : List H.signature.SortType}
    {s : H.signature.SortType} (i : Var Γ s) :
    comparisonArguments sorts alpha Γ (i.mapSorts sorts) = (alpha s).applyUnary (.var i) :=
  Var.reindex_mapSorts sorts (fun {_} j => (alpha _).applyUnary (.var j)) i

/-- The term equality comparing the two ways to apply a primitive operation and the unary terms. -/
def comparisonEquation (c : Interpretation H H) (alpha : ∀ s, Term H.signature [s] (c.onSort s))
    (op : Operation H.signature) : Formula H.signature op.arity.inputs :=
  Formula.termEq ((alpha op.arity.output).applyUnary (Term.primitive op))
    ((c.translation.operation op).applyStrict fun i => comparisonArguments c.onSort alpha _ i)

/-- Unpack the two interpreted terms used in an operation comparison sequent. -/
theorem comparisonEquation_eq_termEq (c : Interpretation H H)
    (alpha : ∀ s, Term H.signature [s] (c.onSort s)) (op : Operation H.signature) :
    c.comparisonEquation alpha op =
      Formula.termEq ((alpha op.arity.output).applyUnary (Term.primitive op))
        ((c.translation.operation op).applyStrict fun i => comparisonArguments c.onSort alpha _ i) :=
  rfl

/-- The hypotheses of Corollary 2.4a(b) for one of the two composite interpretations. -/
structure SyntacticComparison (c : Interpretation H H) where
  /-- The comparison term on each original sort. -/
  alpha (s : H.signature.SortType) : Term H.signature [s] (c.onSort s)
  /-- The inverse comparison term on each retyped sort. -/
  beta (s : H.signature.SortType) : Term H.signature [c.onSort s] s
  /-- The forward unary term is defined everywhere. -/
  alpha_total (s : H.signature.SortType) : Derivation H .truth (alpha s).defined
  /-- The inverse unary term is defined everywhere. -/
  beta_total (s : H.signature.SortType) : Derivation H .truth (beta s).defined
  /-- Applying beta after alpha gives the original variable by derivation. -/
  beta_alpha (s : H.signature.SortType) :
    Derivation H .truth (Formula.termEq ((beta s).applyUnary (alpha s)) (.var .here))
  /-- Applying alpha after beta gives the variable in the translated sort by derivation. -/
  alpha_beta (s : H.signature.SortType) :
    Derivation H .truth (Formula.termEq ((alpha s).applyUnary (beta s)) (.var .here))
  /-- The comparison commutes with every total operation. -/
  total (f : H.signature.Total) : Derivation H .truth (c.comparisonEquation alpha (.total f))
  /-- The comparison commutes with every quantity. -/
  quantity (q : H.signature.Quantity) : Derivation H .truth (c.comparisonEquation alpha (.quantity q))
  /-- The comparison both preserves and reflects each primitive relation by derivation. -/
  relation (r : H.signature.Rel) :
    Derivation.Equivalent H (.atom (.rel r fun i => i))
      ((c.translation.relation r).substitute (comparisonArguments c.onSort alpha _))
  /-- The comparison both preserves and reflects each partial operation domain by derivation. -/
  partialDomain (p : H.signature.Partial) :
    Derivation.Equivalent H (.atom (.domain p fun i => i))
      ((c.translation.partialDomain p).substitute (comparisonArguments c.onSort alpha _))
  /-- On the original domain the comparison commutes with the partial value. -/
  partialValue (p : H.signature.Partial) :
    Derivation H (.atom (.domain p fun i => i)) (c.comparisonEquation alpha (.partialOp p))

end SHIGURE.Interpretation
