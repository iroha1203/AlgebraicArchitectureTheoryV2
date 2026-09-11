import ResearchLean.AG.FiniteDecoderRepresentability.EvaluationClassification
import Formal.Util.AssertStandardAxioms

/-!
# Fibers of finite-exception code evaluation

This module proves G-121(A3).  On an infinite Atom carrier, equality of raw
evaluations also recovers the authored default by evaluating outside the union
of two finite exception tables, so evaluation is injective.  On a finite Atom
carrier, a predicate and a chosen default determine the exception table, and
the complete raw-code fiber is therefore equivalent to `Bool`.

## Implementation notes

The finite classification is stated as an equivalence of the actual subtype
fiber, not merely as an existence or cardinality statement.  This retains both
codes even for an empty carrier.  The infinite proof derives the default from
the existing finite exception fields; it does not accept a default-equality
certificate as an additional premise.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open AtomFoundation DoctrineFiberProduct OnePoint

variable {U : AtomCarrier.{u}}

/-- G-121(A3) uses the same discrete Atom topology fixed in G-121(A1). -/
local instance codeFiberAtomTopology : TopologicalSpace U.Atom := ⊥

/-- G-121(A3) reuses the canonical discreteness proof for the bottom topology. -/
local instance codeFiberAtomDiscreteTopology : DiscreteTopology U.Atom :=
  discreteTopology_bot U.Atom

/--
G-121(A3) API lemma: on an infinite carrier, pointwise evaluation equality
recovers equality of raw codes.  Its premises are exactly the target's
`Infinite U.Atom` case and the decidable equality required by evaluation.
-/
theorem atomPredicateCode_eq_of_evaluationEq_of_infinite
    [DecidableEq U.Atom] [Infinite U.Atom]
    {first second : AtomPredicateCode U}
    (h : atomPredicateCodeEvaluationEq first second) :
    first = second := by
  obtain ⟨atom, hatom⟩ :=
    Infinite.exists_notMem_finset (first.exceptions ∪ second.exceptions)
  have hfirst : atom ∉ first.exceptions := by
    exact fun hmem => hatom (Finset.mem_union_left _ hmem)
  have hsecond : atom ∉ second.exceptions := by
    exact fun hmem => hatom (Finset.mem_union_right _ hmem)
  have hdefault : first.defaultValue = second.defaultValue := by
    simpa [AtomPredicateCode.eval, hfirst, hsecond] using h atom
  cases first with
  | mk firstDefault firstExceptions =>
    cases second with
    | mk secondDefault secondExceptions =>
      rw [AtomPredicateCode.mk.injEq]
      refine ⟨hdefault, ?_⟩
      ext x
      have hx := h x
      have hdefaults : firstDefault = secondDefault := hdefault
      subst secondDefault
      by_cases hfirstMem : x ∈ firstExceptions <;>
        by_cases hsecondMem : x ∈ secondExceptions <;>
        cases firstDefault <;>
        simp [AtomPredicateCode.eval, hfirstMem, hsecondMem] at hx ⊢

/--
G-121(A3) main infinite-carrier theorem: raw evaluation is injective.  The
domain assumptions are precisely infinity and the evaluator's decidable equality.
-/
theorem atomPredicateCode_eval_injective_of_infinite
    [DecidableEq U.Atom] [Infinite U.Atom] :
    Function.Injective (fun code : AtomPredicateCode U => code.eval) := by
  intro first second h
  apply atomPredicateCode_eq_of_evaluationEq_of_infinite
  intro atom
  exact congrFun h atom

/--
G-121(A3) continuous-extension uniqueness on an infinite carrier.  Both maps
are genuine continuous maps from G-121(A1), and agreement is required only on
the original Atom carrier.
-/
theorem continuousMap_eq_of_coe_eq_of_infinite
    [DecidableEq U.Atom] [Infinite U.Atom]
    (first second : C(OnePoint U.Atom, Bool))
    (h : ∀ atom : U.Atom,
      first (atom : OnePoint U.Atom) = second (atom : OnePoint U.Atom)) :
    first = second := by
  have hcodes : continuousMapToAtomPredicateCode first =
      continuousMapToAtomPredicateCode second := by
    apply atomPredicateCode_eval_injective_of_infinite
    funext atom
    calc
      (continuousMapToAtomPredicateCode first).eval atom =
          atomPredicateCodeToContinuousMap
            (continuousMapToAtomPredicateCode first) atom := by
        rw [atomPredicateCodeToContinuousMap_apply_coe]
      _ = first atom := by
        rw [atomPredicateCodeToContinuousMap_rightInverse]
      _ = second atom := h atom
      _ = atomPredicateCodeToContinuousMap
          (continuousMapToAtomPredicateCode second) atom := by
        rw [atomPredicateCodeToContinuousMap_rightInverse]
      _ = (continuousMapToAtomPredicateCode second).eval atom := by
        rw [atomPredicateCodeToContinuousMap_apply_coe]
  calc
    first = atomPredicateCodeToContinuousMap
        (continuousMapToAtomPredicateCode first) :=
      (atomPredicateCodeToContinuousMap_rightInverse first).symm
    _ = atomPredicateCodeToContinuousMap
        (continuousMapToAtomPredicateCode second) := congrArg _ hcodes
    _ = second := atomPredicateCodeToContinuousMap_rightInverse second

section Finite

variable [Finite U.Atom]

/--
G-121(A3) finite-fiber API constructor: a Bool predicate and authored default
determine the raw exception table.  The target's `Finite U.Atom` premise is
noncomputably enumerated internally; no `Fintype` or semantic certificate is exposed.
-/
noncomputable def finitePredicateCode (predicate : U.Atom → Bool)
    (defaultValue : Bool) : AtomPredicateCode U := by
  classical
  letI := Fintype.ofFinite U.Atom
  exact
    { defaultValue := defaultValue
      exceptions := Finset.univ.filter (fun atom => predicate atom ≠ defaultValue) }

/--
G-121(A3) constructor API: the authored default is preserved definitionally.
The only premise is the target's finite-carrier branch.
-/
@[simp]
theorem finitePredicateCode_defaultValue (predicate : U.Atom → Bool)
    (defaultValue : Bool) :
    (finitePredicateCode predicate defaultValue).defaultValue = defaultValue := by
  rfl

/--
G-121(A3) API theorem: the finite constructor evaluates to its input predicate.
Its premises are exactly target-level finiteness and the evaluator's decidable equality.
-/
@[simp]
theorem finitePredicateCode_eval (predicate : U.Atom → Bool)
    [DecidableEq U.Atom] (defaultValue : Bool) (atom : U.Atom) :
    (finitePredicateCode predicate defaultValue).eval atom = predicate atom := by
  cases hpredicate : predicate atom <;> cases hdefault : defaultValue <;>
    simp [finitePredicateCode, AtomPredicateCode.eval, hpredicate]

/--
G-121(A3) API uniqueness for a fixed finite predicate and authored default.
Pointwise evaluation equality is the only theorem premise.
-/
theorem eq_finitePredicateCode_of_eval_eq (predicate : U.Atom → Bool)
    [DecidableEq U.Atom] (code : AtomPredicateCode U)
    (h : ∀ atom, code.eval atom = predicate atom) :
    code = finitePredicateCode predicate code.defaultValue := by
  cases code with
  | mk defaultValue exceptions =>
    rw [AtomPredicateCode.mk.injEq]
    refine ⟨rfl, ?_⟩
    ext atom
    have hatom := h atom
    cases hpredicate : predicate atom <;>
      cases hdefault : defaultValue <;>
      simp [finitePredicateCode, AtomPredicateCode.eval,
        hpredicate, hdefault] at hatom ⊢ <;>
      assumption

/--
G-121(A3) main finite fiber: raw codes evaluating to a fixed predicate.  The
subtype retains the actual code and its pointwise evaluation proof.
-/
abbrev FinitePredicateCodeFiber [DecidableEq U.Atom]
    (predicate : U.Atom → Bool) :=
  {code : AtomPredicateCode U // ∀ atom, code.eval atom = predicate atom}

/--
G-121(A3) main finite classification: the complete raw-code fiber is equivalent
to its authored default `Bool`.  This remains two-valued for an empty carrier.
-/
noncomputable def finitePredicateCodeFiberEquiv [DecidableEq U.Atom]
    (predicate : U.Atom → Bool) :
    FinitePredicateCodeFiber predicate ≃ Bool where
  toFun code := code.1.defaultValue
  invFun defaultValue := ⟨finitePredicateCode predicate defaultValue,
    finitePredicateCode_eval predicate defaultValue⟩
  left_inv code := by
    apply Subtype.ext
    exact (eq_finitePredicateCode_of_eval_eq predicate code.1 code.2).symm
  right_inv defaultValue := rfl

/--
G-121(A3) API form of the exact-two classification: every code in the fiber is
the default-false code or the default-true code, and conversely.
-/
theorem eval_eq_iff_eq_false_or_eq_true (predicate : U.Atom → Bool)
    [DecidableEq U.Atom] (code : AtomPredicateCode U) :
    (∀ atom, code.eval atom = predicate atom) ↔
      code = finitePredicateCode predicate false ∨
        code = finitePredicateCode predicate true := by
  constructor
  · intro h
    have hcode := eq_finitePredicateCode_of_eval_eq predicate code h
    cases hdefault : code.defaultValue
    · exact Or.inl (hcode.trans (by simp [hdefault]))
    · exact Or.inr (hcode.trans (by simp [hdefault]))
  · rintro (rfl | rfl) <;> exact finitePredicateCode_eval predicate _

/--
G-121(A3) API theorem separating the two finite-fiber codes by their authored
defaults.  It has no theorem premise, so it also covers an empty Atom carrier.
-/
theorem finitePredicateCode_false_ne_true (predicate : U.Atom → Bool) :
    finitePredicateCode predicate false ≠ finitePredicateCode predicate true := by
  intro h
  have hdefault := congrArg AtomPredicateCode.defaultValue h
  simp only [finitePredicateCode_defaultValue] at hdefault
  exact Bool.noConfusion hdefault

/--
G-121(A3) API identification of the first exact fiber code: the underlying set
of its exception table is precisely the set where the predicate is true.
-/
theorem finitePredicateCode_false_exceptions (predicate : U.Atom → Bool) :
    ((finitePredicateCode predicate false).exceptions : Set U.Atom) =
      {atom | predicate atom = true} := by
  ext atom
  cases h : predicate atom <;> simp [finitePredicateCode, h]

/--
G-121(A3) API identification of the second exact fiber code: the underlying set
of its exception table is precisely the set where the predicate is false.
-/
theorem finitePredicateCode_true_exceptions (predicate : U.Atom → Bool) :
    ((finitePredicateCode predicate true).exceptions : Set U.Atom) =
      {atom | predicate atom = false} := by
  ext atom
  cases h : predicate atom <;> simp [finitePredicateCode, h]

/--
G-121(A3) main finite extension claim: the two extensions have different values
at infinity, directly stating the fixed target even when the carrier is empty.
-/
theorem finitePredicateCode_extensions_apply_infty_ne [DecidableEq U.Atom]
    (predicate : U.Atom → Bool) :
    atomPredicateCodeToContinuousMap (finitePredicateCode predicate false) ∞ ≠
      atomPredicateCodeToContinuousMap (finitePredicateCode predicate true) ∞ := by
  simp only [atomPredicateCodeToContinuousMap_apply_infty,
    finitePredicateCode_defaultValue]
  decide

/--
G-121(A3) API consequence of the infinity-value theorem: the two finite
extensions are unequal as continuous maps, with no nonempty-carrier premise.
-/
theorem finitePredicateCode_extensions_ne [DecidableEq U.Atom]
    (predicate : U.Atom → Bool) :
    atomPredicateCodeToContinuousMap (finitePredicateCode predicate false) ≠
      atomPredicateCodeToContinuousMap (finitePredicateCode predicate true) := by
  intro h
  apply finitePredicateCode_extensions_apply_infty_ne predicate
  exact congrFun (congrArg ContinuousMap.toFun h) ∞

end Finite

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
