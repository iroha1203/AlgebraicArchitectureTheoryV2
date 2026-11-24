import Formal.SHIGURE.Part1.Laws
import Formal.SHIGURE.Part1.PathExamples
import Formal.SHIGURE.Part1.RingModuleExamples

/-! # Three Law languages from Example 1.6

The same sorted syntax expresses lens equations, path equations, and the
equations of a commutative ring with a module.
-/

namespace SHIGURE.Chapter1

namespace Lens

universe u

/-- The source and view sorts are distinct in the lens theory. -/
inductive SortName : Type u
  | source
  | view

/-- The total symbols of a lens. -/
inductive Symbol : Type u
  | get
  | put

/-- The two sorted operations in (1.7). -/
def signature : Signature.{u} where
  SortType := SortName.{u}
  Total := Symbol.{u}
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity
    | .get => ⟨[.source], .view⟩
    | .put => ⟨[.source, .view], .source⟩
  relInputs := fun r => nomatch r
  partialArity := fun p => nomatch p
  quantityArity := fun q => nomatch q

/-- The lens signature has no partial operation symbols. -/
instance : IsEmpty signature.{u}.Partial := ⟨fun p => nomatch p⟩

/-- Read the view of a source term. -/
def getTerm {Γ : List SortName.{u}} (state : Term signature Γ .source) : Term signature Γ .view :=
  Term.app (sig := signature) (.total Symbol.get) (Term.argsCons state Term.argsNil)

/-- Update the view of a source term. -/
def putTerm {Γ : List SortName.{u}} (state : Term signature Γ .source)
    (view : Term signature Γ .view) : Term signature Γ .source :=
  Term.app (sig := signature) (.total Symbol.put) (Term.argsCons state (Term.argsCons view Term.argsNil))

/-- Names for the three equations in (1.7). -/
inductive LawName : Type u
  | getPut
  | putGet
  | putPut

/-- Each lens equation uses exactly the context displayed in (1.7). -/
def law : LawName.{u} → Law signature.{u}
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
def theory : Theory.{u} where
  signature := signature
  LawName := LawName
  law := law

/-- The product lens, with an arbitrary complement and projection onto the view. -/
def product (V C : Type u) : Structure signature.{u} where
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
theorem evaluates_get {V C : Type u} {Γ : List SortName.{u}}
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
theorem evaluates_put {V C : Type u} {Γ : List SortName.{u}}
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
theorem product_holds (V C : Type u) : theory.Holds (product V C) := by
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

/-- On the Boolean product, change put to leave the original state untouched. -/
def unchangedPut : Structure signature.{0} :=
  { product Bool Unit with
    total
      | .get => (product Bool Unit).total Symbol.get
      | .put => fun xs => xs .here }

/-- Leaving the old view untouched violates put-get when the requested view changes. -/
theorem unchangedPut_not_model : ¬ theory.Holds unchangedPut := by
  intro holds
  let e : Assignment unchangedPut.carrier [.source, .view] :=
    Assignment.cons (false, ()) (Assignment.cons true Assignment.empty)
  have bad := (Law.holds_equality_totalValue_iff _ _ unchangedPut).1 (holds .putGet) e
  change false = true at bad
  cases bad

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

/-- The Boolean identity relation satisfies the total graph axioms. -/
theorem bool_identity_graph_total : GraphPresentation.IsTotal (fun (x y : Bool) => x = y) :=
  ⟨by
    intro x y z h₁ h₂
    exact h₁.symm.trans h₂, fun x => ⟨x, rfl⟩⟩

/-- The relation with the single edge `true → true` defines a map on a proper domain. -/
theorem singleton_graph_partial :
    GraphPresentation.IsPartial ({true} : Set Bool) (fun (x y : Bool) => x = true ∧ y = true) :=
  ⟨by
    intro x y z h₁ h₂
    exact h₁.2.trans h₂.2.symm, fun _ _ h => h.1, fun _ hx => ⟨true, hx, rfl⟩⟩

/-- Claiming an additional domain point for the same graph violates existence in (1.1). -/
theorem singleton_graph_not_total :
    ¬ GraphPresentation.IsPartial Set.univ (fun (x y : Bool) => x = true ∧ y = true) := by
  intro h
  obtain ⟨_, bad, _⟩ := h.2.2 false (Set.mem_univ _)
  cases bad

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

namespace Domain

/-- The Boolean input sort and a distinct sort naming the included points. -/
inductive SortName
  | input
  | included

/-- A unary inclusion and a unary partial operation suffice to test both conditions of (1.2). -/
private def signature : Signature where
  SortType := SortName
  Total := Unit
  Rel := Empty
  Partial := Unit
  Quantity := Empty
  totalArity := fun _ => ⟨[.included], .input⟩
  relInputs := fun r => nomatch r
  partialArity := fun _ => ⟨[.input], .input⟩
  quantityArity := fun q => nomatch q

/-- Use the sole total symbol as the coordinate of the inclusion. -/
private def inclusion : DomainInclusions (sig := signature) () where
  domainSort := .included
  symbol := fun _ => .ordinary ()
  arity_eq := by
    intro s i
    cases i with
    | here => rfl
    | there previous => nomatch previous

/-- The inclusion map and the partial domain vary independently in the test structures. -/
private def realization {C : Type} (inclusionMap : C → Bool) (domain : Set Bool) :
    Structure signature where
  carrier
    | .input => Bool
    | .included => C
  total := fun _ e => inclusionMap e.head
  relation := fun r => nomatch r
  partialDomain := fun _ => {e | e.head ∈ domain}
  partialValue := fun _ e => e.val.head
  quantity := fun q => nomatch q

/-- A named singleton can be sent to either point while the operation is defined only at true. -/
private def singletonRealization (point : Bool) : Structure signature :=
  realization (fun (_ : Unit) => point) {true}

/-- A singleton sort mapped to true describes the true-only partial operation. -/
theorem true_inclusion_holds :
    inclusion.injectivityLaw.Holds (singletonRealization true) ∧
      inclusion.domainSubsetImage.Holds (singletonRealization true) ∧
      inclusion.imageSubsetDomain.Holds (singletonRealization true) := by
  refine ⟨(inclusion.holds_injectivityLaw _).2 ?_, (inclusion.holds_domainLaws _).2 ?_⟩
  · intro x y _
    exact Subsingleton.elim (α := Unit) x y
  · ext e
    constructor
    · intro he
      refine ⟨(), Assignment.ext ?_⟩
      intro s i
      cases i with
      | here => exact he.symm
      | there previous => nomatch previous
    · rintro ⟨x, hx⟩
      exact (congrArg Assignment.head hx).symm

/-- Moving the inclusion's image to false violates the domain specification. -/
theorem false_inclusion_fails :
    ¬ (inclusion.domainSubsetImage.Holds (singletonRealization false) ∧
      inclusion.imageSubsetDomain.Holds (singletonRealization false)) := by
  intro h
  let e := inclusion.inclusion (singletonRealization false) ()
  have hr : e ∈ Set.range (inclusion.inclusion (singletonRealization false)) := ⟨(), rfl⟩
  have hd := h.2 e ((inclusion.holds_imageFormula _ _).2 hr)
  change false = true at hd
  cases hd

/-- An identity inclusion distinguishes the two points of the Boolean inclusion sort. -/
theorem bool_identity_inclusion_injective :
    inclusion.injectivityLaw.Holds (realization (id : Bool → Bool) Set.univ) := by
  apply (inclusion.holds_injectivityLaw _).2
  intro x y h
  exact congrArg Assignment.head h

/-- A constant inclusion identifies the two points and violates the injectivity Law. -/
theorem bool_constant_inclusion_fails :
    ¬ inclusion.injectivityLaw.Holds (realization (fun (_ : Bool) => true) Set.univ) := by
  intro h
  let A := realization (fun (_ : Bool) => true) Set.univ
  have equalImages : inclusion.inclusion A false = inclusion.inclusion A true := by
    apply Assignment.ext
    intro s i
    cases i with
    | here => rfl
    | there previous => nomatch previous
  have bad : false = true := (inclusion.holds_injectivityLaw A).1 h equalImages
  cases bad

end Domain

end SHIGURE.Chapter1
