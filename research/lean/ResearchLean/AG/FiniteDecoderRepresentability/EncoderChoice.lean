import ResearchLean.AG.FiniteDecoderRepresentability.CodeFibers
import Formal.Util.AssertStandardAxioms

/-!
# Agreement with the accepted G-112 encoder

This module proves the remaining encoder-choice clause of G-121(A).  The
accepted G-112 finite/cofinite encoder selects the default-false member of each
finite-carrier evaluation fiber.  On an infinite carrier, the already proved
injectivity of raw evaluation identifies it with the unique code carrying the
same predicate.

## Implementation notes

The finite theorem derives G-112's authored default from the existing encoder
definition and then invokes the complete fiber classification.  The infinite
theorem does not inspect or reproduce the G-112 choice procedure: uniqueness is
deduced from actual evaluation equality, so no parallel encoder is introduced.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open AtomFoundation DoctrineFiberProduct

variable {U : AtomCarrier.{u}}

/--
G-121(A4) API lemma: on a finite carrier the accepted G-112 encoder chooses
authored default `false`.  The target's `Finite` premise is used to discharge
the encoder's first finite-set branch; decidable equality comes from evaluation.
-/
theorem FiniteOrCofiniteBoolPredicate.toCode_defaultValue_of_finite
    [DecidableEq U.Atom] [Finite U.Atom]
    (predicate : FiniteOrCofiniteBoolPredicate U) :
    predicate.toCode.defaultValue = false := by
  classical
  simp only [FiniteOrCofiniteBoolPredicate.toCode,
    finiteOrCofiniteAtomPredicateCode]
  split
  · rfl
  · rename_i hnot
    exact False.elim
      (hnot (Set.toFinite {atom | predicate.1 atom = true}))

/--
G-121(A4) main finite-choice theorem: the accepted G-112 encoder is exactly the
default-false member of the finite raw-code fiber.  No `Fintype` premise is exposed.
-/
theorem FiniteOrCofiniteBoolPredicate.toCode_eq_finitePredicateCode_false
    [DecidableEq U.Atom] [Finite U.Atom]
    (predicate : FiniteOrCofiniteBoolPredicate U) :
    predicate.toCode = finitePredicateCode predicate.1 false := by
  calc
    predicate.toCode =
        finitePredicateCode predicate.1 predicate.toCode.defaultValue :=
      eq_finitePredicateCode_of_eval_eq predicate.1 predicate.toCode
        predicate.toCode_eval
    _ = finitePredicateCode predicate.1 false := by
      rw [predicate.toCode_defaultValue_of_finite]

/--
G-121(A4) main infinite-choice theorem: any raw code with the target predicate's
evaluation is the accepted G-112 code.  Infinite evaluation injectivity supplies
uniqueness; the only other premise is the actual pointwise evaluation formula.
-/
theorem FiniteOrCofiniteBoolPredicate.eq_toCode_of_eval_eq_of_infinite
    [DecidableEq U.Atom] [Infinite U.Atom]
    (predicate : FiniteOrCofiniteBoolPredicate U)
    (code : AtomPredicateCode U)
    (h : ∀ atom, code.eval atom = predicate.1 atom) :
    code = predicate.toCode := by
  apply atomPredicateCode_eval_injective_of_infinite
  funext atom
  exact (h atom).trans (predicate.toCode_eval atom).symm

/--
G-121(A4) API uniqueness form for the infinite G-112 choice: equality with the
accepted code is equivalent to having the prescribed evaluation.
-/
theorem FiniteOrCofiniteBoolPredicate.eq_toCode_iff_eval_eq_of_infinite
    [DecidableEq U.Atom] [Infinite U.Atom]
    (predicate : FiniteOrCofiniteBoolPredicate U)
    (code : AtomPredicateCode U) :
    code = predicate.toCode ↔
      ∀ atom, code.eval atom = predicate.1 atom := by
  constructor
  · rintro rfl
    exact predicate.toCode_eval
  · exact predicate.eq_toCode_of_eval_eq_of_infinite code

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
