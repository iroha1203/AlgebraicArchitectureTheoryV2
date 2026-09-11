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

/--
G-121(A2) main relation: two raw codes agree at every Atom.  The only premise,
`DecidableEq U.Atom`, comes from the existing `AtomPredicateCode.eval` API.
-/
def atomPredicateCodeEvaluationEq [DecidableEq U.Atom]
    (first second : AtomPredicateCode U) : Prop :=
  ∀ atom, first.eval atom = second.eval atom

/--
G-121(A2) API structure for the main relation.  Its sole decidable-equality
premise is inherited from evaluation; no quotient instance is installed globally.
-/
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

/--
G-121(A2) main quotient of raw codes by the explicit evaluation setoid.  Its
decidable-equality premise is exactly the premise required by code evaluation.
-/
abbrev AtomPredicateCodeEvaluationQuotient (U : AtomCarrier.{u})
    [DecidableEq U.Atom] :=
  Quotient (atomPredicateCodeEvaluationSetoid (U := U))

/--
G-121(A2) main semantic image: Bool predicates with finite true set or finite
false set.  The latter is the target's cofinite-true-set alternative.
-/
def FiniteOrCofiniteBoolPredicate (U : AtomCarrier.{u}) :=
  {p : U.Atom → Bool //
    Set.Finite {atom | p atom = true} ∨ Set.Finite {atom | p atom = false}}

/--
G-121(A2) API lemma translating its Bool image condition to the Prop condition
required by the accepted G-112 encoder; it introduces no additional premise.
-/
theorem FiniteOrCofiniteBoolPredicate.asPropFinite
    (predicate : FiniteOrCofiniteBoolPredicate U) :
    Set.Finite {atom | predicate.1 atom = true} ∨
      Set.Finite {atom | ¬ predicate.1 atom = true} := by
  simpa using predicate.2

/--
G-121(A2) API constructor using the accepted G-112 encoder as the canonical raw
code.  Decidable Atom equality is inherited from that encoder's existing API.
-/
noncomputable def FiniteOrCofiniteBoolPredicate.toCode [DecidableEq U.Atom]
    (predicate : FiniteOrCofiniteBoolPredicate U) : AtomPredicateCode U :=
  finiteOrCofiniteAtomPredicateCode
    (fun atom => predicate.1 atom = true) predicate.asPropFinite

/--
G-121(A2) API lemma connecting the accepted G-112 encoder to Bool evaluation.
The only premise is the evaluator's existing decidable Atom equality.
-/
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

/--
G-121(A2) forward API map.  Its image proof is derived from the existing raw-code
classification, and its decidable-equality premise comes from evaluation.
-/
noncomputable def atomPredicateCodeToFiniteOrCofiniteBoolPredicate
    [DecidableEq U.Atom] (code : AtomPredicateCode U) :
    FiniteOrCofiniteBoolPredicate U := by
  refine ⟨code.eval, ?_⟩
  simpa [AtomPredicateCode.Holds] using atomPredicateCode_finiteOrCofinite code

/--
G-121(A2) quotient API lemma: the main pointwise relation is exactly the premise
used to prove equality of forward semantic images.
-/
theorem atomPredicateCodeToFiniteOrCofiniteBoolPredicate_eq_of_evaluationEq
    [DecidableEq U.Atom] {first second : AtomPredicateCode U}
    (h : atomPredicateCodeEvaluationEq first second) :
    atomPredicateCodeToFiniteOrCofiniteBoolPredicate first =
      atomPredicateCodeToFiniteOrCofiniteBoolPredicate second := by
  apply Subtype.ext
  funext atom
  exact h atom

/--
G-121(A2) main forward map descended through the explicit evaluation setoid.
Decidable Atom equality is inherited from the raw evaluator.
-/
noncomputable def evaluationQuotientToFiniteOrCofiniteBoolPredicate
    [DecidableEq U.Atom] :
    AtomPredicateCodeEvaluationQuotient U → FiniteOrCofiniteBoolPredicate U :=
  Quotient.lift atomPredicateCodeToFiniteOrCofiniteBoolPredicate
    (fun _ _ h => atomPredicateCodeToFiniteOrCofiniteBoolPredicate_eq_of_evaluationEq h)

/--
G-121(A2) main inverse map, represented by the class of the accepted G-112 code.
Its decidable-equality premise is inherited from that encoder.
-/
noncomputable def finiteOrCofiniteBoolPredicateToEvaluationQuotient
    [DecidableEq U.Atom] (predicate : FiniteOrCofiniteBoolPredicate U) :
    AtomPredicateCodeEvaluationQuotient U :=
  Quotient.mk _ predicate.toCode

/--
G-121(A2) left-inverse API theorem.  It uses pointwise G-112 encoder evaluation;
the sole typeclass premise is required by raw-code evaluation.
-/
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

/--
G-121(A2) right-inverse API theorem.  It uses the actual G-112 evaluation formula;
the sole typeclass premise is required by raw-code evaluation.
-/
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
Bool-valued predicates.  This is the A2 main theorem; decidable Atom equality is
the existing evaluator's premise, and both inverse laws are proved above.
-/
noncomputable def atomPredicateCodeEvaluationQuotientEquiv
    [DecidableEq U.Atom] :
    AtomPredicateCodeEvaluationQuotient U ≃ FiniteOrCofiniteBoolPredicate U :=
  Equiv.mk evaluationQuotientToFiniteOrCofiniteBoolPredicate
    finiteOrCofiniteBoolPredicateToEvaluationQuotient
    evaluationQuotient_leftInverse evaluationQuotient_rightInverse

/-! ## Instance pair for the evaluation relation -/

/--
G-121(A2) positive instance for the new relation, using the finite fixture and
the all-false raw code.  This is a vacuity-checking API witness with no premise.
-/
theorem atomPredicateCodeEvaluationEq_positive_instance :
    @atomPredicateCodeEvaluationEq FiniteModel.carrier
      (by change DecidableEq FiniteModel.FiniteAtom; infer_instance)
      { defaultValue := false, exceptions := ∅ }
      { defaultValue := false, exceptions := ∅ } := by
  intro atom
  rfl

/--
G-121(A2) negative instance for the new relation: the all-false and all-true
codes disagree at the fixture Atom `componentA`.  It has no external premise.
-/
theorem atomPredicateCodeEvaluationEq_negative_instance :
    ¬ @atomPredicateCodeEvaluationEq FiniteModel.carrier
      (by change DecidableEq FiniteModel.FiniteAtom; infer_instance)
      { defaultValue := false, exceptions := ∅ }
      { defaultValue := true, exceptions := ∅ } := by
  intro h
  have hatom := h FiniteModel.FiniteAtom.componentA
  simp [AtomPredicateCode.eval] at hatom

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
