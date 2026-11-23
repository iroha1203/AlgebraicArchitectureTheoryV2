import Formal.SHIGURE.Part1.Laws
import Formal.SHIGURE.Part1.PathExamples
import Formal.SHIGURE.Part1.RingModuleExamples

/-! # Three Law languages from Example 1.6

The same sorted syntax expresses lens equations, path equations, and the
equations of a commutative ring with a module.
-/

namespace SHIGURE.Chapter1

namespace Lens

/-- The source and view sorts are distinct in the lens theory. -/
inductive SortName
  | source
  | view

/-- The total symbols of a lens. -/
inductive Symbol
  | get
  | put

/-- The two sorted operations in (1.7). -/
def signature : Signature where
  SortType := SortName
  Total := Symbol
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity
    | .get => ⟨[.source], .view⟩
    | .put => ⟨[.source, .view], .source⟩
  relInputs := fun r => nomatch r
  partialArity := fun p => nomatch p
  quantityArity := fun q => nomatch q

/-- Read the view of a source term. -/
def getTerm {Γ : List SortName} (state : Term signature Γ .source) : Term signature Γ .view :=
  Term.app (sig := signature) (.total Symbol.get) (Term.argsCons state Term.argsNil)

/-- Update the view of a source term. -/
def putTerm {Γ : List SortName} (state : Term signature Γ .source)
    (view : Term signature Γ .view) : Term signature Γ .source :=
  Term.app (sig := signature) (.total Symbol.put) (Term.argsCons state (Term.argsCons view Term.argsNil))

/-- Names for the three equations in (1.7). -/
inductive LawName
  | getPut
  | putGet
  | putPut

/-- Each lens equation uses exactly the context displayed in (1.7). -/
def law : LawName → Law signature
  | .getPut =>
    let a : Term signature [.source] .source := .var .here
    Law.equality (putTerm a (getTerm a)) a
  | .putGet =>
    let a : Term signature [.source, .view] .source := .var .here
    let v : Term signature [.source, .view] .view := .var (.there .here)
    Law.equality (getTerm (putTerm a v)) v
  | .putPut =>
    let a : Term signature [.source, .view, .view] .source := .var .here
    let v : Term signature [.source, .view, .view] .view := .var (.there .here)
    let w : Term signature [.source, .view, .view] .view := .var (.there (.there .here))
    Law.equality (putTerm (putTerm a v) w) (putTerm a w)

/-- The required equations of a total lens. -/
def theory : Theory where
  signature := signature
  LawName := LawName
  law := law

/-- The product lens, with an arbitrary complement and projection onto the view. -/
def product (V C : Type) : Structure signature where
  carrier
    | .source => V × C
    | .view => V
  total
    | .get => fun xs => (xs .here).1
    | .put => fun xs => (xs (.there .here), (xs .here).2)
  relation := fun r => nomatch r
  partialDomain := fun p => nomatch p
  partialValue := fun p => nomatch p
  quantity := fun q => nomatch q

/-- In the product lens, get evaluates to the first coordinate. -/
theorem evaluates_get {V C : Type} {Γ : List SortName}
    {state : Term signature Γ .source} {e : Assignment (product V C).carrier Γ}
    {a : V × C} (h : state.Evaluates (product V C) e a) :
    (getTerm state).Evaluates (product V C) e a.1 := by
  unfold getTerm
  let xs : Assignment (product V C).carrier [.source] := Assignment.cons a Assignment.empty
  refine (Term.evaluates_app_at (sig := signature) (.total Symbol.get) _
    (product V C) e xs ?_ _).2 ?_
  · intro sort index
    cases index with
    | here => exact h
    | there index => nomatch index
  · exact (Structure.graph_total_iff (product V C) Symbol.get xs _).2 rfl

/-- In the product lens, put changes only the view coordinate. -/
theorem evaluates_put {V C : Type} {Γ : List SortName}
    {state : Term signature Γ .source} {view : Term signature Γ .view}
    {e : Assignment (product V C).carrier Γ} {a : V × C} {v : V}
    (ha : state.Evaluates (product V C) e a) (hv : view.Evaluates (product V C) e v) :
    (putTerm state view).Evaluates (product V C) e (v, a.2) := by
  unfold putTerm
  let xs : Assignment (product V C).carrier [.source, .view] :=
    Assignment.cons a (Assignment.cons v Assignment.empty)
  refine (Term.evaluates_app_at (sig := signature) (.total Symbol.put) _
    (product V C) e xs ?_ _).2 ?_
  · intro sort index
    cases index with
    | here => exact ha
    | there index =>
      cases index with
      | here => exact hv
      | there index => nomatch index
  · exact (Structure.graph_total_iff (product V C) Symbol.put xs _).2 rfl

/-- The product structure satisfies all three laws in (1.7), including empty carriers. -/
theorem product_holds (V C : Type) : theory.Holds (product V C) := by
  intro name
  cases name with
  | getPut =>
    apply (Law.holds_equality_iff _ _ _).2
    intro e
    have ha : (Term.var Var.here).Evaluates (product V C) e (e Var.here) := rfl
    exact ⟨e Var.here, evaluates_put ha (evaluates_get ha), ha⟩
  | putGet =>
    apply (Law.holds_equality_iff _ _ _).2
    intro e
    have ha : (Term.var Var.here).Evaluates (product V C) e (e Var.here) := rfl
    have hv : (Term.var (Var.there Var.here)).Evaluates (product V C) e
        (e (Var.there Var.here)) := rfl
    exact ⟨e (Var.there Var.here), evaluates_get (evaluates_put ha hv), hv⟩
  | putPut =>
    apply (Law.holds_equality_iff _ _ _).2
    intro e
    have ha : (Term.var Var.here).Evaluates (product V C) e (e Var.here) := rfl
    have hv : (Term.var (Var.there Var.here)).Evaluates (product V C) e
        (e (Var.there Var.here)) := rfl
    have hw : (Term.var (Var.there (Var.there Var.here))).Evaluates (product V C) e
        (e (Var.there (Var.there Var.here))) := rfl
    have hinner := evaluates_put (a := e Var.here) (v := e (Var.there Var.here)) ha hv
    refine ⟨(e (Var.there (Var.there Var.here)), (e Var.here).2), ?_, ?_⟩
    · exact evaluates_put (a := (e (Var.there Var.here), (e Var.here).2))
        (v := e (Var.there (Var.there Var.here))) hinner hw
    · exact evaluates_put (a := e Var.here) (v := e (Var.there (Var.there Var.here))) ha hw

end Lens

namespace Partial

/-- A signature with a single possibly undefined nullary operation. -/
def signature : Signature where
  SortType := Unit
  Total := Empty
  Rel := Empty
  Partial := Unit
  Quantity := Empty
  totalArity := fun f => nomatch f
  relInputs := fun r => nomatch r
  partialArity := fun _ => ⟨[], ()⟩
  quantityArity := fun q => nomatch q

/-- A realization with an arbitrary carrier and an empty domain for its partial operation. -/
def undefinedStructure (X : Type) : Structure signature where
  carrier := fun _ => X
  total := fun f => nomatch f
  relation := fun r => nomatch r
  partialDomain := fun _ => ∅
  partialValue := fun _ x => x.property.elim
  quantity := fun q => nomatch q

/-- The partial nullary operation viewed as a term in any context. -/
def missing {Γ : List Unit} : Term signature Γ () :=
  Term.app (sig := signature) (.partialOp ()) (@Term.argsNil signature Γ)

/-- The partial nullary operation has no value in this realization. -/
theorem missing_no_value (X : Type) {Γ : List Unit}
    (e : Assignment (undefinedStructure X).carrier Γ) (y : X) :
    ¬ (missing (Γ := Γ)).Evaluates (undefinedStructure X) e y := by
  intro h
  have hg := (Term.evaluates_app_at (sig := signature) (.partialOp ()) (@Term.argsNil signature Γ)
    (undefinedStructure X) e Assignment.empty (fun index => nomatch index) y).1 h
  exact ((Structure.graph_partial_iff (undefinedStructure X) () Assignment.empty y).1 hg).choose

/-- A strict binding evaluates its first term even when the body uses only the old variable. -/
theorem strict_unused_undefined (X : Type)
    (e : Assignment (undefinedStructure X).carrier [()]) :
    ¬ (Term.letBind missing (.var (.there .here))).defined.Holds (undefinedStructure X) e := by
  intro h
  obtain ⟨y, hy⟩ := (Term.holds_defined _ (undefinedStructure X) e).1 h
  obtain ⟨x, hx, _⟩ := (Term.evaluates_let_iff missing (.var (.there .here))
    (undefinedStructure X) e y).1 hy
  exact missing_no_value X e x hx

/-- Existential quantification over an empty sort has no witness. -/
theorem existential_empty_false :
    ¬ (Formula.ex (sig := signature) (s := ()) Formula.truth).Holds
      (undefinedStructure Empty) Assignment.empty := by
  rintro ⟨x, _⟩
  nomatch x

/-- Existential truth in the same signature is witnessed in the Boolean realization. -/
theorem existential_bool_true :
    (Formula.ex (sig := signature) (s := ()) Formula.truth).Holds
      (undefinedStructure Bool) Assignment.empty :=
  ⟨true, True.intro⟩

/-- A graph with no edges on a nonempty domain fails the totality clause of (1.1). -/
theorem empty_graph_not_total :
    ¬ GraphPresentation.IsTotal (fun (_ : Unit) (_ : Bool) => False) := by
  intro h
  exact (h.2 ()).choose_spec

/-- The empty relation represents a partial map on the empty domain. -/
theorem empty_graph_partial :
    GraphPresentation.IsPartial (∅ : Set Unit) (fun (_ : Unit) (_ : Bool) => False) := by
  refine ⟨?_, fun _ _ hy => hy.elim, fun _ hx => hx.elim⟩
  intro x y z hy hz
  exact hy.elim

/-- A relation assigning both Boolean values to the same input fails (1.1). -/
theorem multivalued_graph_not_partial :
    ¬ GraphPresentation.IsPartial (Set.univ : Set Unit) (fun (_ : Unit) (_ : Bool) => True) := by
  intro h
  have uniqueOutput : Relator.RightUnique (fun (_ : Unit) (_ : Bool) => True) := h.1
  have bad : false = true := uniqueOutput (a := ()) True.intro True.intro
  cases bad

end Partial

end SHIGURE.Chapter1
