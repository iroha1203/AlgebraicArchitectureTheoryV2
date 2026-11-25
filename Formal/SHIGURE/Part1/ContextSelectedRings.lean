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
  rw [Declaration.sorts_eq_image]
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

private theorem unaryInputs {s : P.signature.SortType} (hs : Declaration.sort s ∈ U.declarations) :
    context [s] (oneSort hs) = [⟨s, hs⟩] :=
  (context_cons s [] (oneSort hs)).trans (congrArg (List.cons ⟨s, hs⟩) (context_nil noSorts))

private theorem binaryInputs {s : P.signature.SortType} (hs : Declaration.sort s ∈ U.declarations) :
    context [s, s] (twoSorts hs) = [⟨s, hs⟩, ⟨s, hs⟩] :=
  (context_cons s [s] (twoSorts hs)).trans (congrArg (List.cons ⟨s, hs⟩) (unaryInputs hs))

private theorem ambientInputHere {s : P.signature.SortType} {Γ : List P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) {Δ : List (SortName U)}
    (tail : context Γ ((tailSortsSubset s Γ).trans keep) = Δ) :
    let t : SortName U := ⟨s, keep (Declaration.sort_mem_sorts List.mem_cons_self)⟩
    let full := (context_cons s Γ keep).trans (congrArg (List.cons t) tail)
    ambientVar keep (cast (congrArg (Var · t) full.symm) .here) = .here := by
  dsimp only
  cases tail
  exact ambientVar_cast_here keep

private theorem ambientInputThere {s : P.signature.SortType} {Γ : List P.signature.SortType}
    (keep : Declaration.sorts (s :: Γ) ⊆ U.declarations) {Δ : List (SortName U)}
    (tail : context Γ ((tailSortsSubset s Γ).trans keep) = Δ) {t : SortName U} (i : Var Δ t) :
    let head : SortName U := ⟨s, keep (Declaration.sort_mem_sorts List.mem_cons_self)⟩
    let full := (context_cons s Γ keep).trans (congrArg (List.cons head) tail)
    ambientVar keep (cast (congrArg (Var · t) full.symm) (.there i)) =
      .there (ambientVar ((tailSortsSubset s Γ).trans keep) (cast (congrArg (Var · t) tail.symm) i)) := by
  dsimp only
  cases tail
  exact ambientVar_cast_there keep i

/-- Restrict the five actual operations of a ring when they are retained. -/
def selectRingVocabulary {s : P.signature.SortType} (r : RingVocabulary P.signature s)
    (hs : Declaration.sort s ∈ U.declarations) (keep : Declaration.ringVocabularySupport r ⊆ U.declarations) :
    RingVocabulary (signature U) ⟨s, hs⟩ where
  zero := cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) (context_nil noSorts))
    (selectTypedTotal r.zero (keepsZero keep) noSorts hs)
  one := cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) (context_nil noSorts))
    (selectTypedTotal r.one (keepsOne keep) noSorts hs)
  add := cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) (binaryInputs hs))
    (selectTypedTotal r.add (keepsAdd keep) (twoSorts hs) hs)
  neg := cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) (unaryInputs hs))
    (selectTypedTotal r.neg (keepsNeg keep) (oneSort hs) hs)
  mul := cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) (binaryInputs hs))
    (selectTypedTotal r.mul (keepsMul keep) (twoSorts hs) hs)

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

private theorem selectTypedTotal_atInputs {Γ inputs : List P.signature.SortType}
    {s : P.signature.SortType} {target : List (SortName U)}
    (f : TypedTotal P.signature ⟨inputs, s⟩) (args : ∀ {t}, Var inputs t → Term P.signature Γ t)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hInputs : Declaration.sorts inputs ⊆ U.declarations)
    (hs : Declaration.sort s ∈ U.declarations)
    (same : context inputs hInputs = target)
    (h : termReferences (f.term args) ⊆ U.declarations)
    (parts : ∀ {t} (i : Var inputs t), termReferences (args i) ⊆ U.declarations)
    (selected : ∀ {t}, Var target t → Term (signature U) (context Γ hΓ) t)
    (compare : ∀ {t} (i : Var target t),
      let j := ambientVar hInputs (cast (congrArg (Var · t) same.symm) i)
      selectTerm (args j) hΓ t.property (parts j) = selected i) :
    selectTerm (f.term args) hΓ hs h =
      (cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) same)
        (selectTypedTotal f keep hInputs hs)).term selected := by
  refine (selectTypedTotal_term f args keep hΓ hInputs hs h parts).trans ?_
  refine Eq.trans ?_ (TypedTotal.term_cast_inputs same (selectTypedTotal f keep hInputs hs) selected).symm
  apply congrArg (fun (terms : ∀ {t}, Var (context inputs hInputs) t →
      Term (signature U) (context Γ hΓ) t) => (selectTypedTotal f keep hInputs hs).term terms)
  funext t i
  have roundtrip : cast (congrArg (Var · t) same.symm) (cast (congrArg (Var · t) same) i) = i := by
    cases same
    rfl
  simpa only [roundtrip] using compare (cast (congrArg (Var · t) same) i)

/-- A retained nullary ring symbol still yields the corresponding constant term. -/
private theorem selectNullary {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (f : TypedTotal P.signature ⟨[], s⟩)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations)
    (h : termReferences (f.term (@Term.argsNil P.signature Γ)) ⊆ U.declarations) :
    selectTerm (f.term (@Term.argsNil P.signature Γ)) hΓ hs h =
      (cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) (context_nil noSorts))
        (selectTypedTotal f keep noSorts hs)).term (@Term.argsNil (signature U) (context Γ hΓ)) :=
  selectTypedTotal_atInputs f Term.argsNil keep hΓ noSorts hs (context_nil noSorts) h
    (fun i => nomatch i) (@Term.argsNil (signature U) (context Γ hΓ)) (fun i => nomatch i)

/-- Select the one-argument application of a retained ring symbol and its supported argument. -/
private theorem selectUnary {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (f : TypedTotal P.signature ⟨[s], s⟩) (x : Term P.signature Γ s)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations)
    (h : termReferences (f.term (x.argsCons Term.argsNil)) ⊆ U.declarations)
    (hx : termReferences x ⊆ U.declarations) :
    selectTerm (f.term (x.argsCons Term.argsNil)) hΓ hs h =
      (cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) (unaryInputs hs))
        (selectTypedTotal f keep (oneSort hs) hs)).term ((selectTerm x hΓ hs hx).argsCons Term.argsNil) := by
  let args : ∀ {t}, Var [s] t → Term P.signature Γ t := x.argsCons (@Term.argsNil P.signature Γ)
  have parts {t : P.signature.SortType} (i : Var [s] t) : termReferences (args i) ⊆ U.declarations := by
    cases i with
    | here => simpa only [args, Term.argsCons_here] using hx
    | there i => exact nomatch i
  refine selectTypedTotal_atInputs f args keep hΓ (oneSort hs) hs (unaryInputs hs) h parts _ ?_
  intro t i
  cases i with
  | here =>
    have pos : ambientVar (oneSort hs)
        (cast (congrArg (Var · (⟨s, hs⟩ : SortName U)) (unaryInputs hs).symm) .here) = .here :=
      ambientInputHere (oneSort hs) (context_nil noSorts)
    simp only [pos, args, Term.argsCons_here]
    rfl
  | there i => exact nomatch i

/-- Select the ordered pair of supported arguments to a retained binary ring symbol. -/
private theorem selectBinary {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (f : TypedTotal P.signature ⟨[s, s], s⟩) (x y : Term P.signature Γ s)
    (keep : Declaration.ofOperation f.symbol.operation ∈ U.declarations)
    (hΓ : Declaration.sorts Γ ⊆ U.declarations) (hs : Declaration.sort s ∈ U.declarations)
    (h : termReferences (f.term (x.argsCons (y.argsCons Term.argsNil))) ⊆ U.declarations)
    (hx : termReferences x ⊆ U.declarations) (hy : termReferences y ⊆ U.declarations) :
    selectTerm (f.term (x.argsCons (y.argsCons Term.argsNil))) hΓ hs h =
      (cast (congrArg (fun xs => TypedTotal (signature U) ⟨xs, ⟨s, hs⟩⟩) (binaryInputs hs))
        (selectTypedTotal f keep (twoSorts hs) hs)).term
        ((selectTerm x hΓ hs hx).argsCons ((selectTerm y hΓ hs hy).argsCons Term.argsNil)) := by
  let args : ∀ {t}, Var [s, s] t → Term P.signature Γ t :=
    x.argsCons (y.argsCons (@Term.argsNil P.signature Γ))
  have parts {t : P.signature.SortType} (i : Var [s, s] t) : termReferences (args i) ⊆ U.declarations := by
    cases i with
    | here => simpa only [args, Term.argsCons_here] using hx
    | there i =>
      cases i with
      | here => simpa only [args, Term.argsCons_there, Term.argsCons_here] using hy
      | there i => exact nomatch i
  refine selectTypedTotal_atInputs f args keep hΓ (twoSorts hs) hs (binaryInputs hs) h parts _ ?_
  intro t i
  cases i with
  | here =>
    have pos : ambientVar (twoSorts hs)
        (cast (congrArg (Var · (⟨s, hs⟩ : SortName U)) (binaryInputs hs).symm) .here) = .here :=
      ambientInputHere (twoSorts hs) (unaryInputs hs)
    simp only [pos, args, Term.argsCons_here]
    rfl
  | there i =>
    cases i with
    | here =>
      have pos : ambientVar (twoSorts hs)
          (cast (congrArg (Var · (⟨s, hs⟩ : SortName U)) (binaryInputs hs).symm) (.there .here)) =
            .there (.here : Var [s] s) :=
        (ambientInputThere (twoSorts hs) (unaryInputs hs) .here).trans
          (congrArg Var.there (ambientInputHere (oneSort hs) (context_nil noSorts)))
      simp only [pos, args, Term.argsCons_there, Term.argsCons_here]
      rfl
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
  | var i =>
    simp only [RingVocabulary.Expr.toTerm_var] at h ⊢
    simp only [selectRingExpr]
    simp only [RingVocabulary.Expr.toTerm_var (selectRingVocabulary r hs keep)]
    exact selectTerm_var i hΓ hs h
  | zero =>
    simp only [RingVocabulary.Expr.toTerm_zero] at h ⊢
    simp only [selectRingExpr]
    simp only [RingVocabulary.Expr.toTerm_zero (selectRingVocabulary r hs keep)]
    exact selectNullary r.zero (keepsZero keep) hΓ hs h
  | one =>
    simp only [RingVocabulary.Expr.toTerm_one] at h ⊢
    simp only [selectRingExpr]
    simp only [RingVocabulary.Expr.toTerm_one (selectRingVocabulary r hs keep)]
    exact selectNullary r.one (keepsOne keep) hΓ hs h
  | add x y hx hy =>
    simp only [RingVocabulary.Expr.toTerm_add] at h ⊢
    simp only [selectRingExpr]
    simp only [RingVocabulary.Expr.toTerm_add (selectRingVocabulary r hs keep)]
    let args : ∀ {t}, Var [s, s] t → Term P.signature Γ t :=
      (x.toTerm r).argsCons ((y.toTerm r).argsCons Term.argsNil)
    have a : termReferences (x.toTerm r) ⊆ U.declarations := by
      simpa only [args, Term.argsCons_here] using typedArgumentKept r.add args h .here
    have b : termReferences (y.toTerm r) ⊆ U.declarations := by
      simpa only [args, Term.argsCons_there, Term.argsCons_here] using
        typedArgumentKept r.add args h (.there .here)
    refine (selectBinary r.add _ _ (keepsAdd keep) hΓ hs h a b).trans ?_
    exact congrArg₂ (fun (a b : Term (signature U) (context Γ hΓ) ⟨s, hs⟩) => (selectRingVocabulary r hs keep).add.term
      (a.argsCons (b.argsCons Term.argsNil))) (hx a) (hy b)
  | neg x hx =>
    simp only [RingVocabulary.Expr.toTerm_neg] at h ⊢
    simp only [selectRingExpr]
    simp only [RingVocabulary.Expr.toTerm_neg (selectRingVocabulary r hs keep)]
    let args : ∀ {t}, Var [s] t → Term P.signature Γ t := (x.toTerm r).argsCons Term.argsNil
    have a : termReferences (x.toTerm r) ⊆ U.declarations := by
      simpa only [args, Term.argsCons_here] using typedArgumentKept r.neg args h .here
    refine (selectUnary r.neg _ (keepsNeg keep) hΓ hs h a).trans ?_
    exact congrArg (fun (a : Term (signature U) (context Γ hΓ) ⟨s, hs⟩) => (selectRingVocabulary r hs keep).neg.term (a.argsCons Term.argsNil)) (hx a)
  | mul x y hx hy =>
    simp only [RingVocabulary.Expr.toTerm_mul] at h ⊢
    simp only [selectRingExpr]
    simp only [RingVocabulary.Expr.toTerm_mul (selectRingVocabulary r hs keep)]
    let args : ∀ {t}, Var [s, s] t → Term P.signature Γ t :=
      (x.toTerm r).argsCons ((y.toTerm r).argsCons Term.argsNil)
    have a : termReferences (x.toTerm r) ⊆ U.declarations := by
      simpa only [args, Term.argsCons_here] using typedArgumentKept r.mul args h .here
    have b : termReferences (y.toTerm r) ⊆ U.declarations := by
      simpa only [args, Term.argsCons_there, Term.argsCons_here] using
        typedArgumentKept r.mul args h (.there .here)
    refine (selectBinary r.mul _ _ (keepsMul keep) hΓ hs h a b).trans ?_
    exact congrArg₂ (fun (a b : Term (signature U) (context Γ hΓ) ⟨s, hs⟩) => (selectRingVocabulary r hs keep).mul.term
      (a.argsCons (b.argsCons Term.argsNil))) (hx a) (hy b)

/-- A ring expression equality retains the free context of its written terms. -/
private theorem ringEqualitySorts {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (r : RingVocabulary P.signature s) (x y : RingVocabulary.Expr Γ s)
    (h : Declaration.lawBody (RingVocabulary.Expr.equality r x y) ⊆ U.declarations) :
    Declaration.sorts Γ ⊆ U.declarations := by
  let law : Law P.signature := ⟨Γ, .truth, Formula.termEq (x.toTerm r) (y.toTerm r)⟩
  have supported : Declaration.lawBody law ⊆ U.declarations := by
    simpa only [RingVocabulary.Expr.equality_eq, Law.equality_eq, law] using h
  exact (Declaration.sorts_subset_lawBody law).trans supported

/-- Retype the ordered sides and coefficient vocabulary of the ring equality together. -/
private theorem selectRingEquality {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (r : RingVocabulary P.signature s) (hs : Declaration.sort s ∈ U.declarations)
    (keep : Declaration.ringVocabularySupport r ⊆ U.declarations)
    (x y : RingVocabulary.Expr Γ s)
    (h : Declaration.lawBody (RingVocabulary.Expr.equality r x y) ⊆ U.declarations) :
    selectLaw (RingVocabulary.Expr.equality r x y) h =
      RingVocabulary.Expr.equality (selectRingVocabulary r hs keep)
        (selectRingExpr (ringEqualitySorts r x y h) hs x) (selectRingExpr (ringEqualitySorts r x y h) hs y) := by
  let source : Law P.signature := ⟨Γ, .truth, Formula.termEq (x.toTerm r) (y.toTerm r)⟩
  have written : RingVocabulary.Expr.equality r x y = source :=
    (RingVocabulary.Expr.equality_eq r x y).trans (Law.equality_eq _ _)
  have supported : Declaration.lawBody source ⊆ U.declarations := by
    rw [← written]
    exact h
  let hΓ := ringEqualitySorts r x y h
  let conclusion := lawConclusionSupport supported
  obtain ⟨_, hx, hy⟩ := termEq_support (x.toTerm r) (y.toTerm r) conclusion
  have same := (selectFormula_termEq _ _ hΓ hs hx hy conclusion).trans
    (congrArg₂ (Formula.termEq (sig := signature U))
      (selectRingExpr_term r hΓ hs keep x hx) (selectRingExpr_term r hΓ hs keep y hy))
  refine (selectLaw_congr written h supported).trans ?_
  rw [selectLaw_eq, selectFormula_truth, RingVocabulary.Expr.equality_eq, Law.equality_eq]
  exact congrArg (Law.mk (sig := signature U) (context Γ hΓ) .truth) same

/-- The selected value ring preserves the exact syntax of all seven ring axioms. -/
theorem selectRingVocabulary_law {s : P.signature.SortType} (r : RingVocabulary P.signature s)
    (hs : Declaration.sort s ∈ U.declarations) (keep : Declaration.ringVocabularySupport r ⊆ U.declarations)
    (i : RingVocabulary.LawName) (h : Declaration.lawBody (r.law i) ⊆ U.declarations) :
    selectLaw (r.law i) h = (selectRingVocabulary r hs keep).law i := by
  cases i with
  | addAssoc =>
    simp only [RingVocabulary.law_addAssoc] at h ⊢
    exact selectRingEquality r hs keep _ _ h
  | zeroAdd =>
    simp only [RingVocabulary.law_zeroAdd] at h ⊢
    exact selectRingEquality r hs keep _ _ h
  | negAdd =>
    simp only [RingVocabulary.law_negAdd] at h ⊢
    exact selectRingEquality r hs keep _ _ h
  | mulAssoc =>
    simp only [RingVocabulary.law_mulAssoc] at h ⊢
    exact selectRingEquality r hs keep _ _ h
  | mulComm =>
    simp only [RingVocabulary.law_mulComm] at h ⊢
    exact selectRingEquality r hs keep _ _ h
  | oneMul =>
    simp only [RingVocabulary.law_oneMul] at h ⊢
    exact selectRingEquality r hs keep _ _ h
  | mulAdd =>
    simp only [RingVocabulary.law_mulAdd] at h ⊢
    exact selectRingEquality r hs keep _ _ h

/-- Selection retains the orders, declared ring operations and original named axiom proofs of the residual. -/
noncomputable def selectNamedRingEquation (name : U.RetainedLaw)
    (equation : NamedRingEquation P.laws name.val) (attached : P.ringEquation name.val = some equation)
    (support : U.RetainsRingSupport name.val) : NamedRingEquation (laws U) name := by
  let ordered := selectNamedEquation name equation.toNamedOrderedEquation
  let original := equation.written.equation.ring
  let selectedSort := ordered.written.equation.result
  have sameSort : selectedSort.val = equation.written.equation.result := by
    rw [selectNamedEquation_result, NamedRingEquation.toNamedOrderedEquation_written,
      RingEquation.Written.toOrdered_result]
  have hs : Declaration.sort equation.written.equation.result ∈ U.declarations :=
    sameSort ▸ selectedSort.property
  have supported := (U.retainsRingSupport_iff name.val).1 support
  let keep : Declaration.ringVocabularySupport original ⊆ U.declarations :=
    (Declaration.ringVocabulary_subset_ringEquationSupport attached).trans supported
  let ring := selectRingVocabulary original hs keep
  have sortTransport : (⟨equation.written.equation.result, hs⟩ : SortName U) = selectedSort :=
    (Subtype.ext sameSort).symm
  let selectedRing := cast (congrArg (RingVocabulary (signature U)) sortTransport) ring
  let writing : RingEquation.Written (signature U) :=
    ⟨⟨ordered.written.equation, selectedRing⟩, ordered.written.conclusion, ordered.written.expansion⟩
  have statement : writing.toLaw = (laws U).statement name := by
    simpa only [RingEquation.Written.toLaw_eq_ordered, writing, RingEquation.Written.toOrdered_mk]
      using ordered.statement_eq
  refine ⟨writing, statement, Subtype.val ⁻¹' equation.axiomNames, fun i => ?_⟩
  have retains : Declaration.derivationOf rfl Subtype.val (equation.axioms_derive i) ⊆ U.declarations :=
    fun _ used => supported (Declaration.ringProof_mem_ringEquationSupport attached used)
  have body := (namedDerivation_lawBody equation.axiomNames (original.law i) (equation.axioms_derive i)).trans retains
  have lawSame := selectRingVocabulary_law original hs keep i body
  let proof := selectNamedDerivation equation.axiomNames (equation.axioms_derive i) retains
  change Derivation ((laws U).select (Subtype.val ⁻¹' equation.axiomNames))
    (selectedRing.law i).input (selectedRing.law i).conclusion
  have selectedLaw : selectedRing.law i = ring.law i := RingVocabulary.law_cast sortTransport ring i
  rw [selectedLaw, ← lawSame]
  simp only [selectLaw_eq]
  exact proof

/-- Both forms of the selected attachment carry the same ordered pair and literal expansion. -/
theorem selectNamedRingEquation_toOrdered (name : U.RetainedLaw)
    (equation : NamedRingEquation P.laws name.val) (attached : P.ringEquation name.val = some equation)
    (support : U.RetainsRingSupport name.val) :
    (selectNamedRingEquation name equation attached support).toNamedOrderedEquation =
      selectNamedEquation name equation.toNamedOrderedEquation := by
  apply NamedOrderedEquation.eq_of_written_eq
  rw [NamedRingEquation.toNamedOrderedEquation_written, selectNamedRingEquation,
    RingEquation.Written.toOrdered_mk]

/-- The selected residual uses exactly the same set of named ring axioms. -/
theorem selectNamedRingEquation_axiomNames (name : U.RetainedLaw)
    (equation : NamedRingEquation P.laws name.val) (attached : P.ringEquation name.val = some equation)
    (support : U.RetainsRingSupport name.val) :
    Subtype.val '' (selectNamedRingEquation name equation attached support).axiomNames = equation.axiomNames := by
  ext axiomName
  constructor
  · rintro ⟨i, retained, rfl⟩
    change i.val ∈ equation.axiomNames at retained
    exact retained
  · intro used
    have supported := (U.retainsRingSupport_iff name.val).1 support
    exact ⟨⟨axiomName, supported (Declaration.ringLaw_mem_ringEquationSupport attached used)⟩, used, rfl⟩

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
