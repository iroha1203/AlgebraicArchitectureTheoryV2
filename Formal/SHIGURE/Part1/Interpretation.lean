import Formal.SHIGURE.Part1.Substitution
import Formal.SHIGURE.Part1.Derivations

/-! # Translations and theory interpretations

Definition 1.9. A translation gives syntactic replacements, and an
interpretation also carries the specified derivations in the target
theory.

## Implementation notes

Translation data is indexed by its sort map. This aligns the domains of
the formulas being compared before requiring mutual derivability.
Keeping the syntax and proof trees in one uninterpreted record would
leave their end formulas unconnected.

Operation arguments are translated with a left-to-right block of strict
bindings. Direct syntactic substitution in an operation replacement
could discard an undefined argument if that replacement did not use the
corresponding variable.
-/

universe u v

namespace SHIGURE

namespace Var

variable {S T : Type u} {Γ : List S} {s : S}

/-- Keep a variable position while mapping its sort and those of its context. -/
def mapSorts (f : S → T) : {Γ : List S} → {s : S} → Var Γ s → Var (Γ.map f) (f s)
  | _, _, .here => .here
  | _, _, .there i => .there (mapSorts f i)

/-- Retyping the newest variable keeps its position. -/
theorem mapSorts_here (f : S → T) : (Var.here : Var (s :: Γ) s).mapSorts f = .here := rfl

/-- Retyping a variable below the head retains its depth. -/
theorem mapSorts_there (f : S → T) (i : Var Γ s) {t : S} :
    (Var.there (t := t) i).mapSorts f = .there (i.mapSorts f) := rfl

/-- Transport a family indexed by the variable positions to the retyped context. -/
def reindex (f : S → T) {C : T → Type v} :
    {Γ : List S} → (∀ {s}, Var Γ s → C (f s)) → ∀ {t}, Var (Γ.map f) t → C t
  | [], _, _, i => nomatch i
  | _ :: _, values, _, .here => values .here
  | _ :: _, values, _, .there i => reindex f (fun j => values (.there j)) i

/-- A reindexed family reads its original head value at the new head. -/
theorem reindex_here (f : S → T) {C : T → Type v}
    (values : ∀ {t}, Var (s :: Γ) t → C (f t)) :
    reindex f values .here = values .here := rfl

/-- A reindexed family reads its original tail at each older position. -/
theorem reindex_there (f : S → T) {C : T → Type v}
    (values : ∀ {t}, Var (s :: Γ) t → C (f t)) {t : T} (i : Var (Γ.map f) t) :
    reindex f values (.there i) = reindex f (fun j => values (.there j)) i := rfl

/-- Retyping a family retains each position's value. -/
@[simp] theorem reindex_mapSorts (f : S → T) {C : T → Type v}
    (values : ∀ {t}, Var Γ t → C (f t)) (i : Var Γ s) :
    reindex f values (i.mapSorts f) = values i := by
  induction i with
  | here => rfl
  | there i ih => exact ih (fun j => values (.there j))

end Var

namespace Renaming

variable {S T : Type u} {Γ Δ : List S}

/-- Retype both the source and target of a variable map. -/
def mapSorts (f : S → T) (ρ : Renaming Γ Δ) : Renaming (Γ.map f) (Δ.map f) :=
  Var.reindex f (fun i => (ρ i).mapSorts f)

/-- Retyping a variable map acts on the original typed position. -/
@[simp] theorem mapSorts_apply (f : S → T) (ρ : Renaming Γ Δ) {s : S} (i : Var Γ s) :
    ρ.mapSorts f (i.mapSorts f) = (ρ i).mapSorts f :=
  Var.reindex_mapSorts f (fun j => (ρ j).mapSorts f) i

end Renaming

namespace Assignment

variable {S T : Type u} {X : T → Type u} {Γ : List S}

/-- Retype each coordinate to the named sort of the translated context. -/
def mapSorts (f : S → T) (xs : Assignment (fun s => X (f s)) Γ) :
    Assignment X (Γ.map f) :=
  ⟨Var.reindex f (fun i => xs i)⟩

/-- The retyped assignment reads the original value at its mapped position. -/
@[simp] theorem mapSorts_apply (f : S → T) (xs : Assignment (fun s => X (f s)) Γ)
    {s : S} (i : Var Γ s) : xs.mapSorts f (i.mapSorts f) = xs i :=
  Var.reindex_mapSorts f (fun j => xs j) i

/-- Equality on retyped variable positions determines the entire retyped assignment. -/
theorem ext_mapSorts (f : S → T) {xs ys : Assignment X (Γ.map f)}
    (h : ∀ {s} (i : Var Γ s), xs (i.mapSorts f) = ys (i.mapSorts f)) : xs = ys := by
  induction Γ with
  | nil => exact (eq_empty xs).trans (eq_empty ys).symm
  | cons s Γ ih =>
    have tail := ih (xs := xs.tail) (ys := ys.tail) (fun i => h (.there i))
    apply Assignment.ext
    intro t i
    cases i with
    | here => exact h .here
    | there j => exact congrArg (fun a : Assignment X (Γ.map f) => a j) tail

/-- Retyping an assignment commutes with selecting the variables of a subcontext. -/
theorem mapSorts_pull (f : S → T) {Δ : List S}
    (xs : Assignment (fun s => X (f s)) Δ) (ρ : Renaming Γ Δ) :
    (xs.mapSorts f).pull (ρ.mapSorts f) = (xs.pull ρ).mapSorts f := by
  apply ext_mapSorts f
  intro s i
  simp only [pull_apply, Renaming.mapSorts_apply, mapSorts_apply]

/-- Retyping an extended assignment leaves its bound value in the first coordinate. -/
theorem mapSorts_cons (f : S → T) {s : S} (x : X (f s))
    (xs : Assignment (fun s => X (f s)) Γ) :
    (Assignment.cons (X := fun t => X (f t)) (s := s) x xs).mapSorts f =
      Assignment.cons x (xs.mapSorts f) := by
  apply Assignment.ext
  intro _ i
  cases i <;> rfl

end Assignment

namespace Formula

variable {sig : Signature.{u}} {Γ Δ : List sig.SortType}

/-- Transport a formula along equality of its typed variable contexts. -/
def castContext (same : Γ = Δ) (p : Formula sig Γ) : Formula sig Δ :=
  cast (congrArg (Formula sig) same) p

end Formula

namespace Assignment

variable {S : Type u} {X : S → Type v} {Γ : List S} {s : S}

/-- Inserting a value after a prefix leaves the selected old coordinate unchanged. -/
theorem append_insertAfter {Λ : List S} (first : Assignment X Λ) (x : X s) (e : Assignment X Γ)
    {t : S} (i : Var (Λ ++ Γ) t) :
    (first.append (cons x e)) (Renaming.insertAfter Λ i) = (first.append e) i := by
  induction Λ with
  | nil => rfl
  | cons a Λ ih =>
    cases i with
    | here => rfl
    | there i => exact ih first.tail i

/-- Reading a moved head restores its value ahead of the original input list. -/
theorem pull_moveHead {Λ : List S} (first : Assignment X Λ) (x : X s) (e : Assignment X Γ) :
    (first.append (cons x e)).pull (Renaming.moveHead Λ) = cons x (first.append e) := by
  apply ext
  intro t i
  cases i with
  | here => exact append_shift first (cons x e) .here
  | there i => exact append_insertAfter first x e i

end Assignment

namespace Term

variable {sig : Signature.{u}} {Γ : List sig.SortType} {s : sig.SortType}

/-- Transport a term along equality of its input contexts. -/
def castContext {Δ : List sig.SortType} (same : Γ = Δ) (t : Term sig Γ s) : Term sig Δ s :=
  cast (congrArg (fun E => Term sig E s) same) t

/-- Bind the argument tuple in context order before interpreting the supplied body. -/
def letArguments : {Γ Λ : List sig.SortType} →
    (∀ {t}, Var Λ t → Term sig Γ t) → Term sig (Λ ++ Γ) s → Term sig Γ s
  | _, [], _, body => body
  | Γ, _ :: Λ, args, body =>
    .letBind (args .here) (letArguments (fun i => (args (.there i)).rename (fun j => .there j))
      (body.rename (Renaming.moveHead (Γ := Γ) Λ)))

/-- Binding an empty argument block returns the body. -/
theorem letArguments_nil (args : ∀ {t}, Var ([] : List sig.SortType) t → Term sig Γ t)
    (body : Term sig Γ s) : letArguments args body = body := rfl

/-- A strict argument block binds the head before evaluating every remaining argument. -/
theorem letArguments_cons {Λ : List sig.SortType} {a : sig.SortType}
    (args : ∀ {t}, Var (a :: Λ) t → Term sig Γ t) (body : Term sig (a :: (Λ ++ Γ)) s) :
    letArguments args body = .letBind (args .here)
      (letArguments (fun i => (args (.there i)).rename (fun j => .there j))
        (body.rename (Renaming.moveHead (Γ := Γ) Λ))) := rfl

/-- Supply a term in the argument-variable context to a tuple of strict arguments. -/
def applyStrict {Λ : List sig.SortType} (body : Term sig Λ s)
    (args : ∀ {t}, Var Λ t → Term sig Γ t) : Term sig Γ s :=
  letArguments args (body.rename (Var.inLeft Γ))

/-- Strict application binds the arguments and reads the replacement at their new positions. -/
theorem applyStrict_eq_letArguments {Λ : List sig.SortType} (body : Term sig Λ s)
    (args : ∀ {t}, Var Λ t → Term sig Γ t) :
    body.applyStrict args = letArguments args (body.rename (Var.inLeft Γ)) := rfl

/-- A strict block evaluates every argument and then the body at the extended assignment. -/
theorem evaluates_letArguments {Λ : List sig.SortType} (A : Structure sig) :
    ∀ {Γ : List sig.SortType} (args : ∀ {t}, Var Λ t → Term sig Γ t)
      (body : Term sig (Λ ++ Γ) s) (e : Assignment A.carrier Γ) (y : A.carrier s),
      (letArguments args body).Evaluates A e y ↔
        ∃ xs : Assignment A.carrier Λ, (∀ {t} (i : Var Λ t), (args i).Evaluates A e (xs i)) ∧
          body.Evaluates A (xs.append e) y := by
  induction Λ with
  | nil =>
    intro Γ args body e y
    constructor
    · intro h
      refine ⟨Assignment.empty, ?_, h⟩
      intro t i
      nomatch i
    · exact fun ⟨_, _, h⟩ => h
  | cons a Λ ih =>
    intro Γ args body e y
    rw [letArguments, evaluates_let_iff]
    have compare (x : A.carrier a) :
        (letArguments (fun i => (args (.there i)).rename (fun j => .there j))
          (body.rename (Renaming.moveHead Λ))).Evaluates A (Assignment.cons x e) y ↔
        ∃ xs : Assignment A.carrier Λ,
          (∀ {t} (i : Var Λ t), (args (.there i)).Evaluates A e (xs i)) ∧
            body.Evaluates A (Assignment.cons x (xs.append e)) y := by
      rw [ih]
      simp only [evaluates_rename, Assignment.pull_cons_there, Assignment.pull_id,
        Assignment.pull_moveHead]
    constructor
    · rintro ⟨x, hx, hb⟩
      obtain ⟨xs, hArgs, hBody⟩ := (compare x).1 hb
      refine ⟨Assignment.cons x xs, ?_, hBody⟩
      intro t i
      cases i with
      | here => exact hx
      | there i => exact hArgs i
    · rintro ⟨xs, hArgs, hBody⟩
      refine ⟨xs.head, hArgs .here, (compare xs.head).2 ?_⟩
      exact ⟨xs.tail, fun i => hArgs (.there i), hBody⟩

/-- Strict argument evaluation restricts the body to exactly the values of its argument tuple. -/
theorem evaluates_applyStrict {Λ : List sig.SortType} (A : Structure sig)
    (body : Term sig Λ s) (args : ∀ {t}, Var Λ t → Term sig Γ t)
    (e : Assignment A.carrier Γ) (y : A.carrier s) :
    (body.applyStrict args).Evaluates A e y ↔
      ∃ xs : Assignment A.carrier Λ, (∀ {t} (i : Var Λ t), (args i).Evaluates A e (xs i)) ∧
        body.Evaluates A xs y := by
  simp only [applyStrict, evaluates_letArguments, evaluates_rename, Assignment.pull_append_left]

end Term

/-- The replacement data of Definition 1.9, before imposing the derivation conditions. -/
structure Translation (S T : Signature.{u}) (onSort : S.SortType → T.SortType) where
  /-- One well-typed replacement term for every ordinary, marked, or partial operation. -/
  operation (op : Operation S) :
    Term T (op.arity.inputs.map onSort) (onSort op.arity.output)
  /-- A positive formula on the retyped arguments of every relation symbol. -/
  relation (r : S.Rel) : Formula T ((S.relInputs r).map onSort)
  /-- The designated domain formula for every partial operation. -/
  partialDomain (p : S.Partial) : Formula T ((S.partialArity p).inputs.map onSort)

namespace Translation

variable {S T U : Signature.{u}} {f : S.SortType → T.SortType}
  {g : T.SortType → U.SortType}

/-- Translate terms, using strict bindings for every operation's arguments. -/
def term (tr : Translation S T f) :
    {Γ : List S.SortType} → {s : S.SortType} → Term S Γ s → Term T (Γ.map f) (f s)
  | _, _, .var i => .var (i.mapSorts f)
  | _, _, .app op args => (tr.operation op).applyStrict (Var.reindex f (fun i => tr.term (args i)))
  | _, _, .letBind init body => .letBind (tr.term init) (tr.term body)

/-- The translation of a term variable is the variable at the retyped position. -/
theorem term_var (tr : Translation S T f) {Γ : List S.SortType} {s : S.SortType} (i : Var Γ s) :
    tr.term (.var i) = .var (i.mapSorts f) := rfl

/-- An operation replacement is applied strictly to all translated arguments. -/
theorem term_app (tr : Translation S T f) {Γ : List S.SortType} (op : Operation S)
    (args : ∀ {s}, Var op.arity.inputs s → Term S Γ s) :
    tr.term (.app op args) = (tr.operation op).applyStrict (Var.reindex f (fun i => tr.term (args i))) := rfl

/-- Translation retains a strict binding and translates both of its terms. -/
theorem term_letBind (tr : Translation S T f) {Γ : List S.SortType} {s a : S.SortType}
    (init : Term S Γ a) (body : Term S (a :: Γ) s) :
    tr.term (.letBind init body) = .letBind (tr.term init) (tr.term body) := rfl

/-- Translate a primitive atom by its designated formula or value graph. -/
def atomic (tr : Translation S T f) {Γ : List S.SortType} :
    Atomic S Γ → Formula T (Γ.map f)
  | .eq x y => .atom (.eq (x.mapSorts f) (y.mapSorts f))
  | .rel r inputs => (tr.relation r).rename (inputs.mapSorts f)
  | .domain p inputs => (tr.partialDomain p).rename (inputs.mapSorts f)
  | .graph op inputs y =>
    (tr.operation op).graph.rename (Renaming.cons (y.mapSorts f) (inputs.mapSorts f))

/-- Equality is translated by retyping its two variable positions. -/
theorem atomic_eq (tr : Translation S T f) {Γ : List S.SortType} {s : S.SortType} (x y : Var Γ s) :
    tr.atomic (.eq x y) = .atom (.eq (x.mapSorts f) (y.mapSorts f)) := rfl

/-- Translation of a relation atom applies the translated variable arguments. -/
@[simp] theorem atomic_rel (tr : Translation S T f) {Γ : List S.SortType}
    (r : S.Rel) (inputs : Renaming (S.relInputs r) Γ) :
    tr.atomic (.rel r inputs) = (tr.relation r).rename (inputs.mapSorts f) :=
  rfl

/-- Translation of a domain atom reads the selected partial domain formula. -/
@[simp] theorem atomic_domain (tr : Translation S T f) {Γ : List S.SortType}
    (p : S.Partial) (inputs : Renaming (S.partialArity p).inputs Γ) :
    tr.atomic (.domain p inputs) = (tr.partialDomain p).rename (inputs.mapSorts f) :=
  rfl

/-- Translation of a graph atom selects the arguments and output of the replacement term. -/
@[simp] theorem atomic_graph (tr : Translation S T f) {Γ : List S.SortType}
    (op : Operation S) (inputs : Renaming op.arity.inputs Γ) (y : Var Γ op.arity.output) :
    tr.atomic (.graph op inputs y) =
      (tr.operation op).graph.rename (Renaming.cons (y.mapSorts f) (inputs.mapSorts f)) :=
  rfl

/-- Translate a positive formula after its term arguments have been expanded. -/
def formula (tr : Translation S T f) : {Γ : List S.SortType} → Formula S Γ → Formula T (Γ.map f)
  | _, .atom a => tr.atomic a
  | _, .truth => .truth
  | _, .falsehood => .falsehood
  | _, .conj p q => .conj (tr.formula p) (tr.formula q)
  | _, .disj p q => .disj (tr.formula p) (tr.formula q)
  | _, .ex p => .ex (tr.formula p)

/-- Translation of an atomic formula evaluates the atomic replacement. -/
@[simp] theorem formula_atom (tr : Translation S T f) {Γ : List S.SortType} (a : Atomic S Γ) :
    tr.formula (.atom a) = tr.atomic a := rfl

/-- Translation preserves the truth formula. -/
@[simp] theorem formula_truth (tr : Translation S T f) {Γ : List S.SortType} :
    tr.formula (.truth : Formula S Γ) = .truth := rfl

/-- Translation preserves the falsehood formula. -/
@[simp] theorem formula_falsehood (tr : Translation S T f) {Γ : List S.SortType} :
    tr.formula (.falsehood : Formula S Γ) = .falsehood := rfl

/-- Translation acts on each conjunct. -/
@[simp] theorem formula_conj (tr : Translation S T f) {Γ : List S.SortType} (p q : Formula S Γ) :
    tr.formula (p.conj q) = (tr.formula p).conj (tr.formula q) := rfl

/-- Translation acts on each disjunct. -/
@[simp] theorem formula_disj (tr : Translation S T f) {Γ : List S.SortType} (p q : Formula S Γ) :
    tr.formula (p.disj q) = (tr.formula p).disj (tr.formula q) := rfl

/-- Translating an existential formula retains its binder at the translated sort. -/
@[simp] theorem formula_ex (tr : Translation S T f) {Γ : List S.SortType} {s : S.SortType}
    (p : Formula S (s :: Γ)) : tr.formula p.ex = (tr.formula p).ex :=
  rfl

/-- The raw identity sends each symbol to its own term or atom on variable inputs. -/
def identity (S : Signature.{u}) : Translation S S id where
  operation op := .app op (fun i => .var (i.mapSorts id))
  relation r := .atom (.rel r (fun i => i.mapSorts id))
  partialDomain p := .atom (.domain p (fun i => i.mapSorts id))

/-- Identity sends a declared relation to the same relation on the mapped positions. -/
@[simp] theorem identity_relation (r : S.Rel) :
    (identity S).relation r = .atom (.rel r (fun i => i.mapSorts id)) :=
  rfl

/-- Identity sends a declared domain to the same domain on the mapped positions. -/
@[simp] theorem identity_domain (p : S.Partial) :
    (identity S).partialDomain p = .atom (.domain p (fun i => i.mapSorts id)) :=
  rfl

/-- Compose replacement data by translation into the final signature. -/
def comp (v : Translation T U g) (u : Translation S T f) : Translation S U (g ∘ f) where
  operation op := (v.term (u.operation op)).castContext List.map_map
  relation r := (v.formula (u.relation r)).castContext List.map_map
  partialDomain p := (v.formula (u.partialDomain p)).castContext List.map_map

/-- A composite operation uses the translated replacement term on the composed context. -/
theorem comp_operation (v : Translation T U g) (u : Translation S T f) (op : Operation S) :
    (v.comp u).operation op = (v.term (u.operation op)).castContext List.map_map :=
  rfl

/-- A composite relation uses the successively translated replacement formula. -/
theorem comp_relation (v : Translation T U g) (u : Translation S T f) (r : S.Rel) :
    (v.comp u).relation r = (v.formula (u.relation r)).castContext List.map_map :=
  rfl

/-- A composite partial domain uses the successively translated domain formula. -/
theorem comp_partialDomain (v : Translation T U g) (u : Translation S T f) (p : S.Partial) :
    (v.comp u).partialDomain p = (v.formula (u.partialDomain p)).castContext List.map_map :=
  rfl

end Translation

namespace Derivation

variable {T : Theory.{u}} {Γ : List T.signature.SortType}

/-- A derivation of the substitution guard from the antecedent makes the explicit guard redundant. -/
def underDefinedness {law : Law T.signature} (θ : Substitution T.signature law.context Γ)
    {antecedent : Formula T.signature Γ} (guard : Derivation T antecedent θ.defined)
    (proof : Derivation T (law.substitute θ).input (law.substitute θ).conclusion) :
    Derivation T (antecedent.conj (law.input.substitute θ)) (law.conclusion.substitute θ) :=
  .cut (.andIntro (.cut (.andLeft _ _) guard) (.andRight _ _)) proof

/-- Mutual derivability, forgetting the concrete choice of the two proof trees. -/
def Equivalent (T : Theory.{u}) {Γ : List T.signature.SortType}
    (p q : Formula T.signature Γ) : Prop :=
  Nonempty (Derivation T p q) ∧ Nonempty (Derivation T q p)

/-- Mutual derivability supplies a proof tree in the forward direction. -/
theorem Equivalent.forward {p q : Formula T.signature Γ} (same : Equivalent T p q) :
    Nonempty (Derivation T p q) := same.1

/-- Mutual derivability supplies a proof tree in the reverse direction. -/
theorem Equivalent.backward {p q : Formula T.signature Γ} (same : Equivalent T p q) :
    Nonempty (Derivation T q p) := same.2

/-- A formula is mutually derivable with itself. -/
theorem Equivalent.refl (p : Formula T.signature Γ) : Equivalent T p p :=
  ⟨⟨.refl p⟩, ⟨.refl p⟩⟩

/-- Mutual derivability is symmetric. -/
theorem Equivalent.symm {p q : Formula T.signature Γ} (h : Equivalent T p q) :
    Equivalent T q p :=
  ⟨h.2, h.1⟩

/-- Cutting the proof trees gives transitivity of mutual derivability. -/
theorem Equivalent.trans {p q r : Formula T.signature Γ} (h₁ : Equivalent T p q)
    (h₂ : Equivalent T q r) : Equivalent T p r := by
  obtain ⟨⟨pq⟩, ⟨qp⟩⟩ := h₁
  obtain ⟨⟨qr⟩, ⟨rq⟩⟩ := h₂
  exact ⟨⟨.cut pq qr⟩, ⟨.cut rq qp⟩⟩

/-- Mutual derivability gives the same truth value in each target model. -/
theorem Equivalent.holds_iff {p q : Formula T.signature Γ} (same : Equivalent T p q)
    (B : Structure T.signature) (model : T.Holds B) (e : Assignment B.carrier Γ) :
    p.Holds B e ↔ q.Holds B e := by
  obtain ⟨⟨forward⟩, ⟨backward⟩⟩ := same
  exact ⟨forward.sound B model e, backward.sound B model e⟩

end Derivation

/-- A translation into a theory that proves the clauses of Definition 1.9. -/
structure Interpretation (S T : Theory.{u}) where
  /-- The retyping of every source sort. -/
  onSort : S.signature.SortType → T.signature.SortType
  /-- The replacement terms and formulas at the selected sort map. -/
  translation : Translation S.signature T.signature onSort
  /-- Every ordinary operation replacement is provably total. -/
  total (f : S.signature.Total) :
    Derivation T .truth (translation.operation (.total f)).defined
  /-- Every marked operation replacement is provably total. -/
  quantity (q : S.signature.Quantity) :
    Derivation T .truth (translation.operation (.quantity q)).defined
  /-- The designated domain implies that the corresponding partial term is defined. -/
  partialDefined (p : S.signature.Partial) :
    Derivation T (translation.partialDomain p) (translation.operation (.partialOp p)).defined
  /-- Every defined value of a partial term is on the designated domain. -/
  definedPartial (p : S.signature.Partial) :
    Derivation T (translation.operation (.partialOp p)).defined (translation.partialDomain p)
  /-- Every required Law has its translated derivation in the target. -/
  preserves (name : S.LawName) :
    Derivation T (translation.formula (S.law name).input)
      (translation.formula (S.law name).conclusion)

namespace Translation

variable {S T U : Theory.{u}} {f : S.signature.SortType → T.signature.SortType}

/-- On the same sort map, compare the value graphs and all other primitive formulas. -/
def Equivalent (left right : Translation S.signature T.signature f) : Prop :=
  (∀ op, Derivation.Equivalent T (left.operation op).graph (right.operation op).graph) ∧
  (∀ r, Derivation.Equivalent T (left.relation r) (right.relation r)) ∧
  ∀ p, Derivation.Equivalent T (left.partialDomain p) (right.partialDomain p)

/-- Equivalent translations give equivalent value graphs for each replacement term. -/
theorem Equivalent.operation_graph {l r : Translation S.signature T.signature f}
    (same : Equivalent l r) (op : Operation S.signature) :
    Derivation.Equivalent T (l.operation op).graph (r.operation op).graph := same.1 op

/-- Equivalent translations give equivalent formulas for each relation. -/
theorem Equivalent.relation {l r : Translation S.signature T.signature f}
    (same : Equivalent l r) (rel : S.signature.Rel) :
    Derivation.Equivalent T (l.relation rel) (r.relation rel) := same.2.1 rel

/-- Equivalent translations give equivalent formulas for each partial domain. -/
theorem Equivalent.partialDomain {l r : Translation S.signature T.signature f}
    (same : Equivalent l r) (p : S.signature.Partial) :
    Derivation.Equivalent T (l.partialDomain p) (r.partialDomain p) := same.2.2 p

/-- The three families of primitive comparisons determine equivalence of translations. -/
theorem Equivalent.of_primitives {l r : Translation S.signature T.signature f}
    (ops : ∀ op, Derivation.Equivalent T (l.operation op).graph (r.operation op).graph)
    (rel : ∀ a, Derivation.Equivalent T (l.relation a) (r.relation a))
    (dom : ∀ p, Derivation.Equivalent T (l.partialDomain p) (r.partialDomain p)) : Equivalent l r :=
  ⟨ops, rel, dom⟩

/-- Reflection of all three families of formula comparisons. -/
theorem Equivalent.refl (tr : Translation S.signature T.signature f) : Equivalent tr tr :=
  ⟨fun _ => Derivation.Equivalent.refl _, fun _ => Derivation.Equivalent.refl _,
    fun _ => Derivation.Equivalent.refl _⟩

/-- Symmetry is applied componentwise. -/
theorem Equivalent.symm {left right : Translation S.signature T.signature f}
    (h : Equivalent left right) : Equivalent right left :=
  ⟨fun op => h.1 op |>.symm, fun r => h.2.1 r |>.symm, fun p => h.2.2 p |>.symm⟩

/-- Transitivity follows by cutting the derivations of the primitive comparisons. -/
theorem Equivalent.trans {left middle right : Translation S.signature T.signature f}
    (h₁ : Equivalent left middle) (h₂ : Equivalent middle right) : Equivalent left right :=
  ⟨fun op => (h₁.1 op).trans (h₂.1 op), fun r => (h₁.2.1 r).trans (h₂.2.1 r),
    fun p => (h₁.2.2 p).trans (h₂.2.2 p)⟩

/-- Evaluating a translated formula in a model is independent of mutually derivable replacements. -/
theorem Equivalent.formula_holds_iff {left right : Translation S.signature T.signature f}
    (same : Equivalent (S := S) (T := T) left right) (B : Structure T.signature)
    (model : T.Holds B) {Γ : List S.signature.SortType} (p : Formula S.signature Γ) :
    ∀ e : Assignment B.carrier (Γ.map f), (left.formula p).Holds B e ↔ (right.formula p).Holds B e := by
  induction p with
  | atom a =>
    intro e
    simp only [Translation.formula_atom]
    cases a with
    | eq x y => rfl
    | rel r vars =>
      rw [Translation.atomic_rel, Translation.atomic_rel, Formula.holds_rename, Formula.holds_rename]
      exact (same.2.1 r).holds_iff B model _
    | domain p vars =>
      rw [Translation.atomic_domain, Translation.atomic_domain, Formula.holds_rename, Formula.holds_rename]
      exact (same.2.2 p).holds_iff B model _
    | graph op vars y =>
      rw [Translation.atomic_graph, Translation.atomic_graph, Formula.holds_rename, Formula.holds_rename]
      exact (same.1 op).holds_iff B model _
  | truth => intro; rfl
  | falsehood => intro; rfl
  | conj p q hp hq =>
    intro e
    simp only [Translation.formula_conj, Formula.holds_conj]
    exact and_congr (hp e) (hq e)
  | disj p q hp hq =>
    intro e
    simp only [Translation.formula_disj, Formula.holds_disj]
    exact or_congr (hp e) (hq e)
  | ex p ih =>
    intro e
    rw [Translation.formula_ex, Translation.formula_ex, Formula.holds_ex, Formula.holds_ex]
    exact exists_congr fun x => ih (Assignment.cons x e)

end Translation

namespace Interpretation

variable {S T U : Theory.{u}}

/-- Definition 1.9 identifies equal sort maps with mutually derivable primitive replacements. -/
def Equivalent (u v : Interpretation S T) : Prop :=
  ∃ h : u.onSort = v.onSort, Translation.Equivalent (S := S) (T := T) (h ▸ u.translation) v.translation

/-- Equivalent interpretations have the same sort map. -/
theorem Equivalent.onSort_eq {l r : Interpretation S T} (same : Equivalent l r) : l.onSort = r.onSort :=
  same.choose

/-- Equivalent interpretations compare replacements on their common sort map. -/
theorem Equivalent.translation_equivalent {l r : Interpretation S T} (same : Equivalent l r) :
    Translation.Equivalent (S := S) (T := T) (same.onSort_eq ▸ l.translation) r.translation :=
  same.choose_spec

/-- Equal sort maps and equivalent replacements give equivalent interpretations. -/
theorem Equivalent.of_translation {l r : Interpretation S T} (sorts : l.onSort = r.onSort)
    (replacements : Translation.Equivalent (S := S) (T := T) (sorts ▸ l.translation) r.translation) :
    Equivalent l r := ⟨sorts, replacements⟩

/-- Equivalent interpretations retype the same translated state tuple. -/
def Equivalent.retype {left right : Interpretation S T} (same : left.Equivalent right)
    {X : T.signature.SortType → Type u} {Γ : List S.signature.SortType}
    (e : Assignment X (Γ.map right.onSort)) : Assignment X (Γ.map left.onSort) :=
  (congrArg (List.map · Γ) same.choose).symm ▸ e

/-- The target model agrees on translated formulas after retyping the input. -/
theorem Equivalent.formula_holds_iff {left right : Interpretation S T}
    (same : left.Equivalent right) (B : Structure T.signature) (model : T.Holds B)
    {Γ : List S.signature.SortType} (p : Formula S.signature Γ)
    (e : Assignment B.carrier (Γ.map right.onSort)) :
    (left.translation.formula p).Holds B (same.retype e) ↔ (right.translation.formula p).Holds B e := by
  obtain ⟨sorts, replacements⟩ := same
  cases left
  cases right
  cases sorts
  exact replacements.formula_holds_iff B model p e

/-- Each interpretation is equivalent to itself. -/
theorem Equivalent.refl (u : Interpretation S T) : Equivalent u u :=
  ⟨rfl, Translation.Equivalent.refl _⟩

/-- Comparison of interpretations is symmetric. -/
theorem Equivalent.symm {u v : Interpretation S T} (h : Equivalent u v) : Equivalent v u := by
  obtain ⟨equalSorts, comparing⟩ := h
  refine ⟨equalSorts.symm, ?_⟩
  cases u
  cases v
  cases equalSorts
  exact comparing.symm

/-- Comparison of interpretations is transitive. -/
theorem Equivalent.trans {u v w : Interpretation S T} (h₁ : Equivalent u v)
    (h₂ : Equivalent v w) : Equivalent u w := by
  obtain ⟨h₁, uv⟩ := h₁
  obtain ⟨h₂, vw⟩ := h₂
  refine ⟨h₁.trans h₂, ?_⟩
  cases u
  cases v
  cases w
  cases h₁
  cases h₂
  exact uv.trans vw

/-- The composite replacement data; Appendix A.3 supplies its transported derivations. -/
def compCandidate (v : Interpretation T U) (u : Interpretation S T) :
    Translation S.signature U.signature (v.onSort ∘ u.onSort) :=
  v.translation.comp u.translation

/-- The candidate uses the composition of the two underlying translations. -/
theorem compCandidate_eq_translation_comp (v : Interpretation T U) (u : Interpretation S T) :
    v.compCandidate u = v.translation.comp u.translation := rfl

end Interpretation

end SHIGURE
