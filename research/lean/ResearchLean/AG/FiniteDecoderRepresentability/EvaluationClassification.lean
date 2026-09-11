import ResearchLean.AG.FiniteDecoderRepresentability.OnePointCode
import ResearchLean.AG.DoctrineFiberProduct.ExactBottomCoverageClassification
import Formal.Util.AssertStandardAxioms

/-!
# Evaluation classes of finite-exception codes

This module proves the quotient clause of G-121(A).  It identifies raw
finite-exception codes modulo equality of their evaluations with Bool-valued
predicates whose true set is finite or cofinite.  The inverse is the existing
G-112 `finiteOrCofiniteAtomPredicateCode`, so the new classification is joined
to the accepted coverage code rather than defining a parallel encoder.

## Implementation notes

The evaluation relation is provided as an explicit `Setoid`; no global setoid
instance is installed on `AtomPredicateCode`.  The target subtype records the
finite/cofinite alternative as data, while proof irrelevance ensures that the
chosen proof does not affect the canonical code or the quotient class.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open AtomFoundation DoctrineFiberProduct

variable {U : AtomCarrier.{u}}

/-- Two predicate codes are semantically equal when all Atom evaluations agree. -/
def atomPredicateCodeEvaluationEq [DecidableEq U.Atom]
    (first second : AtomPredicateCode U) : Prop :=
  ∀ atom, first.eval atom = second.eval atom

/-- The setoid of pointwise evaluation equality on raw predicate codes. -/
def atomPredicateCodeEvaluationSetoid [DecidableEq U.Atom] :
    Setoid (AtomPredicateCode U) where
  r := atomPredicateCodeEvaluationEq
  iseqv := by
    constructor
    · intro code atom
      rfl
    · intro first second h atom
      exact (h atom).symm
    · intro first second third hfirst hsecond atom
      exact (hfirst atom).trans (hsecond atom)

/-- Raw predicate codes modulo pointwise equality of their evaluations. -/
abbrev AtomPredicateCodeEvaluationQuotient (U : AtomCarrier.{u})
    [DecidableEq U.Atom] :=
  Quotient (atomPredicateCodeEvaluationSetoid (U := U))

/-- Bool predicates whose true set is finite or cofinite. -/
def FiniteOrCofiniteBoolPredicate (U : AtomCarrier.{u}) :=
  {p : U.Atom → Bool //
    Set.Finite {atom | p atom = true} ∨ Set.Finite {atom | p atom = false}}

/-- Translate the Bool-valued finite/cofinite alternative to the existing Prop API. -/
theorem FiniteOrCofiniteBoolPredicate.asPropFinite
    (predicate : FiniteOrCofiniteBoolPredicate U) :
    Set.Finite {atom | predicate.1 atom = true} ∨
      Set.Finite {atom | ¬ predicate.1 atom = true} := by
  simpa using predicate.2

/-- Use the accepted G-112 encoder as the canonical raw code for a predicate. -/
noncomputable def FiniteOrCofiniteBoolPredicate.toCode [DecidableEq U.Atom]
    (predicate : FiniteOrCofiniteBoolPredicate U) : AtomPredicateCode U :=
  finiteOrCofiniteAtomPredicateCode
    (fun atom => predicate.1 atom = true) predicate.asPropFinite

/-- The existing G-112 finite/cofinite encoder evaluates to its Bool predicate. -/
@[simp]
theorem FiniteOrCofiniteBoolPredicate.toCode_eval [DecidableEq U.Atom]
    (predicate : FiniteOrCofiniteBoolPredicate U) (atom : U.Atom) :
    predicate.toCode.eval atom = predicate.1 atom := by
  have hholds := finiteOrCofiniteAtomPredicateCode_holds_iff
    (fun atom => predicate.1 atom = true) predicate.asPropFinite atom
  cases hvalue : predicate.1 atom <;>
    cases hcode : predicate.toCode.eval atom <;>
    simp_all [AtomPredicateCode.Holds,
      FiniteOrCofiniteBoolPredicate.toCode]

/-- Read a raw code as a finite-or-cofinite Bool predicate. -/
noncomputable def atomPredicateCodeToFiniteOrCofiniteBoolPredicate
    [DecidableEq U.Atom] (code : AtomPredicateCode U) :
    FiniteOrCofiniteBoolPredicate U := by
  refine ⟨code.eval, ?_⟩
  simpa [AtomPredicateCode.Holds] using atomPredicateCode_finiteOrCofinite code

/-- Evaluation-equivalent raw codes define the same finite-or-cofinite predicate. -/
theorem atomPredicateCodeToFiniteOrCofiniteBoolPredicate_eq_of_evaluationEq
    [DecidableEq U.Atom] {first second : AtomPredicateCode U}
    (h : atomPredicateCodeEvaluationEq first second) :
    atomPredicateCodeToFiniteOrCofiniteBoolPredicate first =
      atomPredicateCodeToFiniteOrCofiniteBoolPredicate second := by
  apply Subtype.ext
  funext atom
  exact h atom

/-- Descend raw evaluation to the quotient of predicate codes. -/
noncomputable def evaluationQuotientToFiniteOrCofiniteBoolPredicate
    [DecidableEq U.Atom] :
    AtomPredicateCodeEvaluationQuotient U → FiniteOrCofiniteBoolPredicate U :=
  Quotient.lift atomPredicateCodeToFiniteOrCofiniteBoolPredicate
    (fun _ _ h => atomPredicateCodeToFiniteOrCofiniteBoolPredicate_eq_of_evaluationEq h)

/-- Encode a finite-or-cofinite Bool predicate as the class of its canonical G-112 code. -/
noncomputable def finiteOrCofiniteBoolPredicateToEvaluationQuotient
    [DecidableEq U.Atom] (predicate : FiniteOrCofiniteBoolPredicate U) :
    AtomPredicateCodeEvaluationQuotient U :=
  Quotient.mk _ predicate.toCode

/-- Canonical encoding after quotient evaluation returns the original code class. -/
theorem evaluationQuotient_leftInverse [DecidableEq U.Atom]
    (codeClass : AtomPredicateCodeEvaluationQuotient U) :
    finiteOrCofiniteBoolPredicateToEvaluationQuotient
        (evaluationQuotientToFiniteOrCofiniteBoolPredicate codeClass) =
      codeClass := by
  refine Quotient.inductionOn codeClass ?_
  intro code
  apply Quotient.sound
  intro atom
  exact FiniteOrCofiniteBoolPredicate.toCode_eval _ _

/-- Quotient evaluation after canonical encoding returns the original predicate. -/
theorem evaluationQuotient_rightInverse [DecidableEq U.Atom]
    (predicate : FiniteOrCofiniteBoolPredicate U) :
    evaluationQuotientToFiniteOrCofiniteBoolPredicate
        (finiteOrCofiniteBoolPredicateToEvaluationQuotient predicate) =
      predicate := by
  apply Subtype.ext
  funext atom
  exact FiniteOrCofiniteBoolPredicate.toCode_eval _ _

/--
G-121(A)'s equivalence between code evaluation classes and finite-or-cofinite
Bool-valued predicates.
-/
noncomputable def atomPredicateCodeEvaluationQuotientEquiv
    [DecidableEq U.Atom] :
    AtomPredicateCodeEvaluationQuotient U ≃ FiniteOrCofiniteBoolPredicate U :=
  Equiv.mk evaluationQuotientToFiniteOrCofiniteBoolPredicate
    finiteOrCofiniteBoolPredicateToEvaluationQuotient
    evaluationQuotient_leftInverse evaluationQuotient_rightInverse

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
