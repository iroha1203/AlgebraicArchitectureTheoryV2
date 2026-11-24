import Formal.SHIGURE.Part1.ContextSelectedEquations

/-! # Selection of a named residual ring

When a logical context also keeps the names of an attached residual ring,
its five typed symbols, named axioms, and original derivations all select
to the smaller signature.

## Implementation notes

The declaration dependency rules apply to the written Law and to any
derivation registered with a derived Law. The ring certificate has its own
support, including the five ring symbols and the original named proofs.
Putting this support in the declaration dependency rules would prevent a
context from keeping the written equality on its own. The selection keeps
the ring certificate when this separate support fits in the context, and
the presentation reads the ordered text in either case.
-/

universe u

namespace SHIGURE
namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- The nullary operation has no input sort declarations to retain. -/
private theorem noSorts : Declaration.sorts (P := P) [] ⊆ U.declarations := by
  rintro _ ⟨s, h, rfl⟩
  cases h

/-- Construct the support of the unary ring arity from its retained scalar sort. -/
private theorem oneSort {s : P.signature.SortType} (hs : Declaration.sort s ∈ U.declarations) :
    Declaration.sorts [s] ⊆ U.declarations :=
  Declaration.sorts_cons_subset hs noSorts

/-- Use the retained scalar sort at both positions of a binary ring operation. -/
private theorem twoSorts {s : P.signature.SortType} (hs : Declaration.sort s ∈ U.declarations) :
    Declaration.sorts [s, s] ⊆ U.declarations :=
  Declaration.sorts_cons_subset hs (oneSort hs)

/-- Read retention of the named ring zero from the ring vocabulary support. -/
private theorem keepsZero {s : P.signature.SortType} {r : RingVocabulary P.signature s}
    (keep : Declaration.ringVocabularySupport r ⊆ U.declarations) :
    Declaration.ofOperation r.zero.symbol.operation ∈ U.declarations :=
  keep (by simp [Declaration.ringVocabularySupport_eq])

/-- Read retention of the named ring unit from the ring vocabulary support. -/
private theorem keepsOne {s : P.signature.SortType} {r : RingVocabulary P.signature s}
    (keep : Declaration.ringVocabularySupport r ⊆ U.declarations) :
    Declaration.ofOperation r.one.symbol.operation ∈ U.declarations :=
  keep (by simp [Declaration.ringVocabularySupport_eq])

/-- Read retention of the named addition from the ring vocabulary support. -/
private theorem keepsAdd {s : P.signature.SortType} {r : RingVocabulary P.signature s}
    (keep : Declaration.ringVocabularySupport r ⊆ U.declarations) :
    Declaration.ofOperation r.add.symbol.operation ∈ U.declarations :=
  keep (by simp [Declaration.ringVocabularySupport_eq])

/-- Read retention of the named negation from the ring vocabulary support. -/
private theorem keepsNeg {s : P.signature.SortType} {r : RingVocabulary P.signature s}
    (keep : Declaration.ringVocabularySupport r ⊆ U.declarations) :
    Declaration.ofOperation r.neg.symbol.operation ∈ U.declarations :=
  keep (by simp [Declaration.ringVocabularySupport_eq])

/-- Read retention of the named multiplication from the ring vocabulary support. -/
private theorem keepsMul {s : P.signature.SortType} {r : RingVocabulary P.signature s}
    (keep : Declaration.ringVocabularySupport r ⊆ U.declarations) :
    Declaration.ofOperation r.mul.symbol.operation ∈ U.declarations :=
  keep (by simp [Declaration.ringVocabularySupport_eq])

/-- Restrict the five actual operations of a ring when they are retained. -/
def selectRingVocabulary {s : P.signature.SortType} (r : RingVocabulary P.signature s)
    (hs : Declaration.sort s ∈ U.declarations) (keep : Declaration.ringVocabularySupport r ⊆ U.declarations) :
    RingVocabulary (signature U) ⟨s, hs⟩ where
  zero := selectTypedTotal r.zero (keepsZero keep) noSorts hs
  one := selectTypedTotal r.one (keepsOne keep) noSorts hs
  add := selectTypedTotal r.add (keepsAdd keep) (twoSorts hs) hs
  neg := selectTypedTotal r.neg (keepsNeg keep) (oneSort hs) hs
  mul := selectTypedTotal r.mul (keepsMul keep) (twoSorts hs) hs

/-- Reindex the variables of a ring expression in the selected context,
keeping its coefficient-operation nodes as syntax for later interpretation. -/
private def selectRingExpr {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations) :
    RingVocabulary.Expr Γ s → RingVocabulary.Expr (context Γ hΓ) (⟨s, hs⟩ : SortName U)
  | .var i => .var (selectVar hΓ i)
  | .zero => .zero
  | .one => .one
  | .add a b => .add (selectRingExpr hΓ hs a) (selectRingExpr hΓ hs b)
  | .neg a => .neg (selectRingExpr hΓ hs a)
  | .mul a b => .mul (selectRingExpr hΓ hs a) (selectRingExpr hΓ hs b)

/-- A retained nullary ring symbol still yields the corresponding constant term. -/
private theorem selectNullary {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (f : TypedTotal P.signature ⟨[], s⟩)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations)
    (h : termReferences (f.term (@Term.argsNil P.signature Γ)) ⊆ U.declarations) :
    selectTerm (f.term (@Term.argsNil P.signature Γ)) hΓ hs h = (selectTypedTotal f keep noSorts hs).term (@Term.argsNil (signature U) (context Γ hΓ)) := by
  refine (selectTypedTotal_term f Term.argsNil keep hΓ noSorts hs h (fun i => nomatch i)).trans ?_
  apply congrArg (fun (args : ∀ {t}, Var ([] : List (SortName U)) t →
      Term (signature U) (context Γ hΓ) t) => (selectTypedTotal f keep noSorts hs).term args)
  funext t i
  exact nomatch i

/-- Select the one-argument application of a retained ring symbol and its supported argument. -/
private theorem selectUnary {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (f : TypedTotal P.signature ⟨[s], s⟩) (x : Term P.signature Γ s)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations)
    (h : termReferences (f.term (x.argsCons Term.argsNil)) ⊆ U.declarations)
    (hx : termReferences x ⊆ U.declarations) :
    selectTerm (f.term (x.argsCons Term.argsNil)) hΓ hs h =
      (selectTypedTotal f keep (oneSort hs) hs).term ((selectTerm x hΓ hs hx).argsCons Term.argsNil) := by
  let args : ∀ {t}, Var [s] t → Term P.signature Γ t := x.argsCons (@Term.argsNil P.signature Γ)
  have parts {t : P.signature.SortType} (i : Var [s] t) : termReferences (args i) ⊆ U.declarations := by
    cases i with
    | here => exact hx
    | there i => exact nomatch i
  refine (selectTypedTotal_term f args keep hΓ (oneSort hs) hs h parts).trans ?_
  apply congrArg (fun (terms : ∀ {t}, Var (context [s] (oneSort hs)) t →
      Term (signature U) (context Γ hΓ) t) => (selectTypedTotal f keep (oneSort hs) hs).term terms)
  funext t i
  cases i with
  | here => rfl
  | there i => exact nomatch i

/-- Select the ordered pair of supported arguments to a retained binary ring symbol. -/
private theorem selectBinary {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (f : TypedTotal P.signature ⟨[s, s], s⟩) (x y : Term P.signature Γ s)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations)
    (h : termReferences (f.term (x.argsCons (y.argsCons Term.argsNil))) ⊆ U.declarations)
    (hx : termReferences x ⊆ U.declarations) (hy : termReferences y ⊆ U.declarations) :
    selectTerm (f.term (x.argsCons (y.argsCons Term.argsNil))) hΓ hs h =
      (selectTypedTotal f keep (twoSorts hs) hs).term
        ((selectTerm x hΓ hs hx).argsCons ((selectTerm y hΓ hs hy).argsCons Term.argsNil)) := by
  let args : ∀ {t}, Var [s, s] t → Term P.signature Γ t :=
    x.argsCons (y.argsCons (@Term.argsNil P.signature Γ))
  have parts {t : P.signature.SortType} (i : Var [s, s] t) : termReferences (args i) ⊆ U.declarations := by
    cases i with
    | here => exact hx
    | there i =>
      cases i with
      | here => exact hy
      | there i => exact nomatch i
  refine (selectTypedTotal_term f args keep hΓ (twoSorts hs) hs h parts).trans ?_
  apply congrArg (fun (terms : ∀ {t}, Var (context [s, s] (twoSorts hs)) t →
      Term (signature U) (context Γ hΓ) t) => (selectTypedTotal f keep (twoSorts hs) hs).term terms)
  funext t i
  cases i with
  | here => rfl
  | there i =>
    cases i with
    | here => rfl
    | there i => exact nomatch i

/-- Extract the support of one argument term from the supported typed application. -/
private theorem typedArgumentKept {Γ : List P.signature.SortType} {profile : Arity P.signature.SortType}
    (f : TypedTotal P.signature profile) (args : ∀ {s}, Var profile.inputs s → Term P.signature Γ s)
    (h : termReferences (f.term args) ⊆ U.declarations) {s} (i : Var profile.inputs s) :
    termReferences (args i) ⊆ U.declarations := by
  rw [typedTermReferences] at h
  exact fun _ hd => h (Or.inr ⟨_, i, hd⟩)

/-- The retyped ring expression and the selected ordinary syntax give the same term. -/
private theorem selectRingExpr_term {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (r : RingVocabulary P.signature s) (hΓ : Declaration.sorts Γ ⊆ U.declarations)
    (hs : Declaration.sort s ∈ U.declarations) (keep : Declaration.ringVocabularySupport r ⊆ U.declarations)
    (expr : RingVocabulary.Expr Γ s) (h : termReferences (expr.toTerm r) ⊆ U.declarations) :
    selectTerm (expr.toTerm r) hΓ hs h = (selectRingExpr hΓ hs expr).toTerm (selectRingVocabulary r hs keep) := by
  induction expr with
  | var i => rfl
  | zero => exact selectNullary r.zero (keepsZero keep) hΓ hs h
  | one => exact selectNullary r.one (keepsOne keep) hΓ hs h
  | add x y hx hy =>
    let args : ∀ {t}, Var [s, s] t → Term P.signature Γ t :=
      (x.toTerm r).argsCons ((y.toTerm r).argsCons Term.argsNil)
    let a := typedArgumentKept r.add args h .here
    let b := typedArgumentKept r.add args h (.there .here)
    refine (selectBinary r.add _ _ (keepsAdd keep) hΓ hs h a b).trans ?_
    exact congrArg₂ (fun (a b : Term (signature U) (context Γ hΓ) ⟨s, hs⟩) => (selectRingVocabulary r hs keep).add.term
      (a.argsCons (b.argsCons Term.argsNil))) (hx a) (hy b)
  | neg x hx =>
    let args : ∀ {t}, Var [s] t → Term P.signature Γ t := (x.toTerm r).argsCons Term.argsNil
    let a := typedArgumentKept r.neg args h .here
    refine (selectUnary r.neg _ (keepsNeg keep) hΓ hs h a).trans ?_
    exact congrArg (fun (a : Term (signature U) (context Γ hΓ) ⟨s, hs⟩) => (selectRingVocabulary r hs keep).neg.term (a.argsCons Term.argsNil)) (hx a)
  | mul x y hx hy =>
    let args : ∀ {t}, Var [s, s] t → Term P.signature Γ t :=
      (x.toTerm r).argsCons ((y.toTerm r).argsCons Term.argsNil)
    let a := typedArgumentKept r.mul args h .here
    let b := typedArgumentKept r.mul args h (.there .here)
    refine (selectBinary r.mul _ _ (keepsMul keep) hΓ hs h a b).trans ?_
    exact congrArg₂ (fun (a b : Term (signature U) (context Γ hΓ) ⟨s, hs⟩) => (selectRingVocabulary r hs keep).mul.term
      (a.argsCons (b.argsCons Term.argsNil))) (hx a) (hy b)

/-- Retype the ordered sides and coefficient vocabulary of the ring equality together. -/
private theorem selectRingEquality {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (r : RingVocabulary P.signature s) (hs : Declaration.sort s ∈ U.declarations)
    (keep : Declaration.ringVocabularySupport r ⊆ U.declarations)
    (x y : RingVocabulary.Expr Γ s)
    (h : Declaration.lawBody (RingVocabulary.Expr.equality r x y) ⊆ U.declarations) :
    selectLaw (RingVocabulary.Expr.equality r x y) h =
      RingVocabulary.Expr.equality (selectRingVocabulary r hs keep)
        (selectRingExpr (lawSortSupport h) hs x) (selectRingExpr (lawSortSupport h) hs y) := by
  let hΓ := lawSortSupport h
  let conclusion := lawConclusionSupport h
  obtain ⟨_, hx, hy⟩ := termEq_support (x.toTerm r) (y.toTerm r) conclusion
  have same := (selectFormula_termEq _ _ hΓ hs hx hy conclusion).trans
    (congrArg₂ (Formula.termEq (sig := signature U))
      (selectRingExpr_term r hΓ hs keep x hx) (selectRingExpr_term r hΓ hs keep y hy))
  exact congrArg (Law.mk (sig := signature U) (context Γ hΓ) .truth) same

/-- The selected value ring preserves the exact syntax of all seven ring axioms. -/
theorem selectRingVocabulary_law {s : P.signature.SortType} (r : RingVocabulary P.signature s)
    (hs : Declaration.sort s ∈ U.declarations) (keep : Declaration.ringVocabularySupport r ⊆ U.declarations)
    (i : RingVocabulary.LawName) (h : Declaration.lawBody (r.law i) ⊆ U.declarations) :
    selectLaw (r.law i) h = (selectRingVocabulary r hs keep).law i := by
  cases i <;> exact selectRingEquality r hs keep _ _ h

/-- Selection retains the orders, declared ring operations and original named axiom proofs of the residual. -/
noncomputable def selectNamedRingEquation (name : U.RetainedLaw)
    (equation : NamedRingEquation P.laws name.val) (attached : P.ringEquation name.val = some equation)
    (support : U.RetainsRingSupport name.val) : NamedRingEquation (laws U) name := by
  let ordered := selectNamedEquation name equation.toNamedOrderedEquation
  let original := equation.written.equation.ring
  let selectedSort := ordered.written.equation.result
  have hs : Declaration.sort equation.written.equation.result ∈ U.declarations := selectedSort.property
  let keep : Declaration.ringVocabularySupport original ⊆ U.declarations :=
    (Declaration.ringVocabulary_subset_ringEquationSupport attached).trans support
  let ring := selectRingVocabulary original hs keep
  let writing : RingEquation.Written (signature U) :=
    ⟨⟨ordered.written.equation, ring⟩, ordered.written.conclusion, ordered.written.expansion⟩
  refine ⟨writing, ordered.statement_eq, Subtype.val ⁻¹' equation.axiomNames, fun i => ?_⟩
  have retains : Declaration.derivationOf rfl Subtype.val (equation.axioms_derive i) ⊆ U.declarations :=
    fun _ used => support (Declaration.ringProof_mem_ringEquationSupport attached used)
  have body := (namedDerivation_lawBody equation.axiomNames (original.law i) (equation.axioms_derive i)).trans retains
  have lawSame := selectRingVocabulary_law original hs keep i body
  let proof := selectNamedDerivation equation.axiomNames (equation.axioms_derive i) retains
  change Derivation ((laws U).select (Subtype.val ⁻¹' equation.axiomNames)) (ring.law i).input (ring.law i).conclusion
  rw [← lawSame]
  exact proof

/-- Both forms of the selected attachment carry the same ordered pair and literal expansion. -/
theorem selectNamedRingEquation_toOrdered (name : U.RetainedLaw)
    (equation : NamedRingEquation P.laws name.val) (attached : P.ringEquation name.val = some equation)
    (support : U.RetainsRingSupport name.val) :
    (selectNamedRingEquation name equation attached support).toNamedOrderedEquation =
      selectNamedEquation name equation.toNamedOrderedEquation :=
  rfl

/-- The selected residual uses exactly the same set of named ring axioms. -/
theorem selectNamedRingEquation_axiomNames (name : U.RetainedLaw)
    (equation : NamedRingEquation P.laws name.val) (attached : P.ringEquation name.val = some equation)
    (support : U.RetainsRingSupport name.val) :
    Subtype.val '' (selectNamedRingEquation name equation attached support).axiomNames = equation.axiomNames := by
  ext axiomName
  constructor
  · rintro ⟨i, retained, rfl⟩
    exact retained
  · intro used
    exact ⟨⟨axiomName, support (Declaration.ringLaw_mem_ringEquationSupport attached used)⟩, used, rfl⟩

/-- The restriction keeps a named residual ring exactly when the attachment has all its declared support. -/
noncomputable def ringEquation (name : U.RetainedLaw) : Option (NamedRingEquation (laws U) name) := by
  classical
  exact match attached : P.ringEquation name.val with
  | none => none
  | some eqn => if support : U.RetainsRingSupport name.val then
      some (selectNamedRingEquation name eqn attached support) else none

/-- A supported source attachment produces the actual selected residual certificate. -/
theorem ringEquation_of_supported (name : U.RetainedLaw)
    (equation : NamedRingEquation P.laws name.val) (attached : P.ringEquation name.val = some equation)
    (support : U.RetainsRingSupport name.val) :
    ringEquation name = some (selectNamedRingEquation name equation attached support) := by
  classical
  unfold ringEquation
  split
  · rename_i missing
    rw [attached] at missing
    cases missing
  · rename_i original registered
    have same := Option.some.inj (registered.symm.trans attached)
    subst original
    rw [dif_pos support]

/-- When a source attachment cannot be read, its named ring certificate is unavailable. -/
theorem ringEquation_of_unsupported (name : U.RetainedLaw) (missing : ¬ U.RetainsRingSupport name.val) :
    ringEquation name = none := by
  classical
  unfold ringEquation
  split <;> simp [missing]

/-- Every selected residual certificate comes from its corresponding supported source attachment. -/
theorem ringEquation_some (name : U.RetainedLaw) {selected : NamedRingEquation (laws U) name}
    (someEquation : ringEquation name = some selected) :
    ∃ (original : NamedRingEquation P.laws name.val)
      (attached : P.ringEquation name.val = some original) (support : U.RetainsRingSupport name.val),
      selectNamedRingEquation name original attached support = selected := by
  classical
  unfold ringEquation at someEquation
  split at someEquation
  · cases someEquation
  · rename_i original attached
    split at someEquation
    · rename_i support
      exact ⟨original, attached, support, Option.some.inj someEquation⟩
    · cases someEquation

end DeclarationContext.Selected
end SHIGURE
