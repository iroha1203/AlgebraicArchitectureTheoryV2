import Formal.SHIGURE.Part1.Pullback
import Formal.SHIGURE.Part1.SyntacticComparison

/-! # Finite unary operation words

Theorem 2.6 gives preservation of domains, values and observations for a finite
word, and identifies its domain as a preimage when primitive domains reflect.
The translated word is a term in the target theory and can contain binders.

## Implementation notes

The word stores named operations and the singleton-input equalities that make
successive operations composable. An arbitrary unary term would also allow
other syntax, so the inductive word records exactly the chains of the theorem.
Evaluation reuses the term evaluator and strict unary application. Each snoc
requires a value of the prefix before consulting the next operation's graph.
-/

universe u v

namespace SHIGURE

/-- A finite chain of named unary operations from `source` to the indexed output sort. -/
inductive OperationWord (sig : Signature.{u}) (source : sig.SortType) : sig.SortType → Type u
  /-- The empty word leaves the input unchanged. -/
  | nil : OperationWord sig source source
  /-- Append a primitive with exactly the preceding output sort as its sole input. -/
  | snoc {middle : sig.SortType} (earlier : OperationWord sig source middle)
      (op : Operation sig) (unary : op.arity.inputs = [middle]) :
      OperationWord sig source op.arity.output

namespace OperationWord

variable {sig : Signature.{u}} {source target : sig.SortType}

/-- Regard a word as the term obtained by applying its operations to one variable. -/
def term : {target : sig.SortType} → OperationWord sig source target → Term sig [source] target
  | _, .nil => .var .here
  | _, .snoc earlier op unary => ((Term.primitive op).castContext unary).applyUnary (term earlier)

/-- The value graph of a word at a single input. -/
def Evaluates (w : OperationWord sig source target) (A : Structure sig)
    (x : A.carrier source) (y : A.carrier target) : Prop :=
  w.term.Evaluates A (Assignment.cons x Assignment.empty) y

/-- The partial value of a word at a single input. -/
noncomputable def eval (w : OperationWord sig source target) (A : Structure sig) (x : A.carrier source) :
    Part (A.carrier target) :=
  w.term.eval A (Assignment.cons x Assignment.empty)

/-- The partial value and evaluation graph describe the same output. -/
theorem mem_eval_iff (w : OperationWord sig source target) (A : Structure sig)
    (x : A.carrier source) (y : A.carrier target) : y ∈ w.eval A x ↔ w.Evaluates A x y :=
  w.term.mem_eval_iff A _ y

/-- The set of inputs at which the whole word has a value. -/
def domain (w : OperationWord sig source target) (A : Structure sig) : Set (A.carrier source) :=
  {x | (w.eval A x).Dom}

/-- Definedness of a word means there is a value in its graph. -/
theorem mem_domain_iff (w : OperationWord sig source target) (A : Structure sig) (x : A.carrier source) :
    x ∈ w.domain A ↔ ∃ y, w.Evaluates A x y :=
  Iff.rfl

/-- The selected value of a defined word belongs to its graph. -/
theorem evaluates_get (w : OperationWord sig source target) (A : Structure sig) (x : A.carrier source)
    (defined : x ∈ w.domain A) : w.Evaluates A x ((w.eval A x).get defined) :=
  (w.mem_eval_iff A x _).1 ⟨defined, rfl⟩

/-- The empty word evaluates to the input itself. -/
@[simp] theorem evaluates_nil_iff (A : Structure sig) (x y : A.carrier source) :
    (OperationWord.nil : OperationWord sig source source).Evaluates A x y ↔ x = y :=
  Term.evaluates_var_iff .here A (Assignment.cons x Assignment.empty) y

/-- Every input is in the domain of the empty word. -/
@[simp] theorem domain_nil (A : Structure sig) :
    (OperationWord.nil : OperationWord sig source source).domain A = Set.univ := by
  ext x
  exact iff_true_intro ⟨x, (evaluates_nil_iff A x x).2 rfl⟩

/-- Place a unary value in the primitive's declared input context. -/
def unaryInput {A : Structure sig} {Γ : List sig.SortType} {s : sig.SortType}
    (unary : Γ = [s]) (x : A.carrier s) : Assignment A.carrier Γ :=
  cast (congrArg (Assignment A.carrier) unary.symm) (Assignment.cons x Assignment.empty)

/-- Mapping the input commutes with its transport to the primitive context. -/
private theorem unaryInput_map {A B : Structure sig} {Γ : List sig.SortType} {s : sig.SortType}
    (h : StructureMap A B) (unary : Γ = [s]) (x : A.carrier s) :
    (unaryInput (A := A) unary x).map h.onSort = unaryInput (A := B) unary (h.onSort s x) := by
  subst Γ
  change (Assignment.cons x Assignment.empty).map h.onSort =
    Assignment.cons (h.onSort s x) Assignment.empty
  simp only [Assignment.map_cons, Assignment.map_empty]

/-- Context transport of a term and its input tuple preserves its evaluation. -/
private theorem evaluates_cast_unary {Γ : List sig.SortType} {s t : sig.SortType}
    (t₀ : Term sig Γ t) (A : Structure sig) (unary : Γ = [s]) (x : A.carrier s) (y : A.carrier t) :
    (t₀.castContext unary).Evaluates A (Assignment.cons x Assignment.empty) y ↔
      t₀.Evaluates A (unaryInput unary x) y := by
  subst Γ
  rfl

/-- Appending a step first evaluates the prefix, then applies the primitive graph. -/
theorem evaluates_snoc_iff {middle : sig.SortType} (w : OperationWord sig source middle)
    (op : Operation sig) (unary : op.arity.inputs = [middle]) (A : Structure sig)
    (x : A.carrier source) (y : A.carrier op.arity.output) :
    (w.snoc op unary).Evaluates A x y ↔
      ∃ z, w.Evaluates A x z ∧ A.Graph op (unaryInput unary z) y := by
  let body := (Term.primitive op).castContext unary
  change (body.applyUnary w.term).Evaluates A (Assignment.cons x Assignment.empty) y ↔ _
  constructor
  · intro output
    obtain ⟨xs, arguments, _⟩ :=
      (Term.evaluates_applyStrict A body (fun i => Substitution.singleton w.term i) _ y).1 output
    have prefixValue : w.Evaluates A x (xs .here) := arguments .here
    refine ⟨xs .here, prefixValue, ?_⟩
    have evaluated := (Term.evaluates_applyUnary_iff body w.term A _ _ prefixValue y).1 output
    exact (Term.primitive_evaluates_iff A op _ y).1
      ((evaluates_cast_unary (Term.primitive op) A unary _ y).1 evaluated)
  · rintro ⟨z, prefixValue, primitiveValue⟩
    exact (Term.evaluates_applyUnary_iff body w.term A _ z prefixValue y).2
      ((evaluates_cast_unary (Term.primitive op) A unary z y).2
        ((Term.primitive_evaluates_iff A op _ y).2 primitiveValue))

/-- A structural map takes an evaluation to the evaluation of the image value. -/
theorem evaluates_map {A B : Structure sig} (w : OperationWord sig source target)
    (h : StructureMap A B) {x : A.carrier source} {y : A.carrier target}
    (held : w.Evaluates A x y) : w.Evaluates B (h.onSort source x) (h.onSort target y) := by
  simpa only [Evaluates, Assignment.map_cons, Assignment.map_empty] using h.evaluates_map w.term _ y held

/-- The image of the domain is contained in the target domain, as in (2.8). -/
theorem domain_image_subset {A B : Structure sig} (w : OperationWord sig source target)
    (h : StructureMap A B) : h.onSort source '' w.domain A ⊆ w.domain B := by
  rintro _ ⟨x, ⟨y, value⟩, rfl⟩
  exact ⟨h.onSort target y, w.evaluates_map h value⟩

/-- The defined values of the word commute with the carrier map, as in (2.8). -/
theorem value_comm {A B : Structure sig} (w : OperationWord sig source target)
    (h : StructureMap A B) (x : A.carrier source) (hx : x ∈ w.domain A) :
    h.onSort target ((w.eval A x).get hx) =
      (w.eval B (h.onSort source x)).get (w.domain_image_subset h ⟨x, hx, rfl⟩) :=
  w.term.evaluates_unique B _ (w.evaluates_map h (w.evaluates_get A x hx)) (w.evaluates_get B _ _)

/-- A terminal observation commuting with the carrier map agrees on defined values. -/
theorem observation_comm {A B : Structure sig} (w : OperationWord sig source target)
    (h : StructureMap A B) {O : Type v} (observeA : A.carrier target → O) (observeB : B.carrier target → O)
    (commutes : ∀ y, observeB (h.onSort target y) = observeA y)
    (x : A.carrier source) (hx : x ∈ w.domain A) :
    observeB ((w.eval B (h.onSort source x)).get (w.domain_image_subset h ⟨x, hx, rfl⟩)) =
      observeA ((w.eval A x).get hx) := by
  rw [← w.value_comm h x hx, commutes]

/-- At a mapped tuple, reflection of primitive domains gives an original graph value. -/
private theorem graph_input_reflected {A B : Structure sig} (h : StructureMap A B)
    (reflects : h.ReflectsDomains) (op : Operation sig) (xs : Assignment A.carrier op.arity.inputs)
    (hy : ∃ y, B.Graph op (xs.map h.onSort) y) : ∃ y, A.Graph op xs y := by
  cases op with
  | total f => exact ⟨A.total f xs, (A.graph_total_iff _ _ _).2 rfl⟩
  | quantity q => exact ⟨A.quantity q xs, (A.graph_quantity_iff _ _ _).2 rfl⟩
  | partialOp p =>
    obtain ⟨y, value⟩ := hy
    have hx := reflects p xs ((B.graph_partial_iff p _ y).1 value).1
    exact ⟨A.partialValue p ⟨xs, hx⟩, (A.graph_partial_iff _ _ _).2 ⟨hx, rfl⟩⟩

/-- If primitive domains reflect, the whole word's domain reflects along the structural map. -/
theorem mem_domain_of_map {A B : Structure sig} (w : OperationWord sig source target)
    (h : StructureMap A B) (reflects : h.ReflectsDomains) (x : A.carrier source)
    (defined : h.onSort source x ∈ w.domain B) : x ∈ w.domain A := by
  induction w with
  | nil => rw [domain_nil]; trivial
  | snoc w op unary ih =>
    obtain ⟨y, value⟩ := defined
    obtain ⟨imagePrefix, imageEval, imageStep⟩ := (evaluates_snoc_iff w op unary B _ y).1 value
    obtain ⟨middleValue, prefixEval⟩ := ih ⟨imagePrefix, imageEval⟩
    have imageEq := w.term.evaluates_unique B _ (w.evaluates_map h prefixEval) imageEval
    have mappedStep : B.Graph op ((unaryInput (A := A) unary middleValue).map h.onSort) y := by
      simpa only [unaryInput_map, imageEq] using imageStep
    obtain ⟨original, originalStep⟩ := graph_input_reflected h reflects op _ ⟨y, mappedStep⟩
    exact ⟨original, (evaluates_snoc_iff w op unary A _ original).2 ⟨middleValue, prefixEval, originalStep⟩⟩

/-- Under (2.9), the original domain is exactly the preimage of the target domain. -/
theorem domain_eq_preimage {A B : Structure sig} (w : OperationWord sig source target)
    (h : StructureMap A B) (reflects : h.ReflectsDomains) :
    w.domain A = h.onSort source ⁻¹' w.domain B := by
  ext x
  exact ⟨fun hx => w.domain_image_subset h ⟨x, hx, rfl⟩, w.mem_domain_of_map h reflects x⟩

section Translation

variable {S T : Theory.{u}} {s t : S.signature.SortType}

/-- Evaluate the translated term literally in the target structure at the retyped input. -/
noncomputable def translatedEval (w : OperationWord S.signature s t) (u : Interpretation S T)
    (B : Structure T.signature) (x : B.carrier (u.onSort s)) : Part (B.carrier (u.onSort t)) :=
  (u.translation.term w.term).eval B (Assignment.cons x Assignment.empty)

/-- A value of the translated word is an evaluation of the actual translated term. -/
theorem mem_translated_eval_iff (w : OperationWord S.signature s t) (u : Interpretation S T)
    (B : Structure T.signature) (x : B.carrier (u.onSort s)) (y : B.carrier (u.onSort t)) :
    y ∈ w.translatedEval u B x ↔
      (u.translation.term w.term).Evaluates B (Assignment.cons x Assignment.empty) y :=
  (u.translation.term w.term).mem_eval_iff B _ y

/-- The domain in the target structure of the term translating the word. -/
def translatedDomain (w : OperationWord S.signature s t) (u : Interpretation S T)
    (B : Structure T.signature) : Set (B.carrier (u.onSort s)) :=
  {x | (w.translatedEval u B x).Dom}

/-- A word evaluation in the pullback is precisely its translated graph evaluation in the target. -/
theorem translated_evaluates_iff (w : OperationWord S.signature s t) (u : Interpretation S T)
    (B : Structure T.signature) (model : T.Holds B) (x : B.carrier (u.onSort s))
    (y : B.carrier (u.onSort t)) :
    w.Evaluates (u.pullbackStructure B model) x y ↔
      (u.translation.term w.term).Evaluates B (Assignment.cons x Assignment.empty) y := by
  simpa only [Evaluates, Assignment.mapSorts_cons, Assignment.eq_empty] using
    u.pullback_evaluates_iff B model w.term (Assignment.cons x Assignment.empty) y

/-- Pullback word values agree as partial values with the translated term in the target model. -/
theorem eval_pullback_eq_translated (w : OperationWord S.signature s t) (u : Interpretation S T)
    (B : Structure T.signature) (model : T.Holds B) (x : B.carrier (u.onSort s)) :
    w.eval (u.pullbackStructure B model) x = w.translatedEval u B x := by
  simpa only [eval, translatedEval, Assignment.mapSorts_cons, Assignment.eq_empty] using
    u.pullback_eval_eq B model w.term (Assignment.cons x Assignment.empty)

/-- In the target carrier, the word domain in the pullback is the domain of the translated term. -/
theorem domain_pullback_eq_translated (w : OperationWord S.signature s t) (u : Interpretation S T)
    (B : Structure T.signature) (model : T.Holds B) :
    w.domain (u.pullbackStructure B model) = w.translatedDomain u B := by
  ext x
  change (w.eval (u.pullbackStructure B model) x).Dom ↔ (w.translatedEval u B x).Dom
  rw [w.eval_pullback_eq_translated u B model x]

/-- Equation (2.8) for the translated domain, along a structural map to the pullback. -/
theorem translated_domain_image_subset {A : Structure S.signature} (w : OperationWord S.signature s t)
    (u : Interpretation S T) (B : Structure T.signature) (model : T.Holds B)
    (h : StructureMap A (u.pullbackStructure B model)) :
    h.onSort s '' w.domain A ⊆ w.translatedDomain u B := by
  rw [← w.domain_pullback_eq_translated u B model]
  exact w.domain_image_subset h

/-- The defined word value commutes with the map into the evaluation of the translated term. -/
theorem translated_value_comm {A : Structure S.signature} (w : OperationWord S.signature s t)
    (u : Interpretation S T) (B : Structure T.signature) (model : T.Holds B)
    (h : StructureMap A (u.pullbackStructure B model)) (x : A.carrier s) (hx : x ∈ w.domain A) :
    h.onSort t ((w.eval A x).get hx) =
      (w.translatedEval u B (h.onSort s x)).get
        (w.translated_domain_image_subset u B model h ⟨x, hx, rfl⟩) := by
  apply (u.translation.term w.term).evaluates_unique B _
  · exact (w.translated_evaluates_iff u B model _ _).1 (w.evaluates_map h (w.evaluates_get A x hx))
  · exact (w.mem_translated_eval_iff u B _ _).1 ⟨_, rfl⟩

/-- Equation (2.8) for observations on the translated output sort in the target structure. -/
theorem translated_observation_comm {A : Structure S.signature} (w : OperationWord S.signature s t)
    (u : Interpretation S T) (B : Structure T.signature) (model : T.Holds B)
    (h : StructureMap A (u.pullbackStructure B model)) {O : Type v}
    (observeA : A.carrier t → O) (observeB : B.carrier (u.onSort t) → O)
    (commutes : ∀ y, observeB (h.onSort t y) = observeA y) (x : A.carrier s) (hx : x ∈ w.domain A) :
    observeB ((w.translatedEval u B (h.onSort s x)).get
        (w.translated_domain_image_subset u B model h ⟨x, hx, rfl⟩)) = observeA ((w.eval A x).get hx) := by
  rw [← w.translated_value_comm u B model h x hx, commutes]

/-- Reflection into the pullback identifies the original domain with the translated domain's preimage. -/
theorem translated_domain_eq_preimage {A : Structure S.signature} (w : OperationWord S.signature s t)
    (u : Interpretation S T) (B : Structure T.signature) (model : T.Holds B)
    (h : StructureMap A (u.pullbackStructure B model)) (reflects : h.ReflectsDomains) :
    w.domain A = h.onSort s ⁻¹' w.translatedDomain u B := by
  rw [← w.domain_pullback_eq_translated u B model]
  exact w.domain_eq_preimage h reflects

end Translation

end OperationWord
end SHIGURE
