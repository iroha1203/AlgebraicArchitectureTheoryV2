import ResearchLean.AG.DoctrineFiberProduct.Schema
import Mathlib.Topology.Compactification.OnePoint.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Finite-exception codes as continuous maps on a one-point compactification

This module proves the first construction in G-121(A): an authored finite or
cofinite `AtomPredicateCode` is exactly a continuous Bool-valued map on the
one-point compactification of the discrete Atom carrier.  The value at infinity
is the authored default, while the finite exceptional set is recovered from
the continuous map itself.

## Implementation notes

The Atom carrier is equipped locally with the bottom topology, so the public
equivalence has no additional topology parameter or premise.  The inverse does
not store a finiteness certificate supplied by a caller: it derives finiteness
from continuity at infinity through `OnePoint.continuous_iff_from_discrete` and
the cofinite filter.  This keeps the raw code equality required by G-121,
including its default value, rather than quotienting by pointwise evaluation.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open Filter OnePoint
open AtomFoundation DoctrineFiberProduct

section

variable {U : AtomCarrier.{u}}

local instance : TopologicalSpace U.Atom := ⊥
local instance : DiscreteTopology U.Atom := discreteTopology_bot U.Atom

/--
Extend a finite-exception predicate code continuously to the one-point
compactification, using its default value at infinity.
-/
noncomputable def atomPredicateCodeToContinuousMap [DecidableEq U.Atom]
    (code : AtomPredicateCode U) : C(OnePoint U.Atom, Bool) :=
  OnePoint.continuousMapMkDiscrete code.eval code.defaultValue (by
    rw [nhds_discrete, Filter.tendsto_pure]
    exact code.exceptions.eventually_cofinite_notMem.mono (by
      intro atom hnot
      simp [AtomPredicateCode.eval, hnot]))

/--
Recover the default and the finite exceptional set from a continuous map on
the discrete Atom carrier's one-point compactification.
-/
noncomputable def continuousMapToAtomPredicateCode [DecidableEq U.Atom]
    (f : C(OnePoint U.Atom, Bool)) : AtomPredicateCode U := by
  have hevent : ∀ᶠ atom : U.Atom in cofinite,
      f (atom : OnePoint U.Atom) = f ∞ := by
    have htendsto := (OnePoint.continuous_iff_from_discrete f).mp f.continuous
    simpa only [nhds_discrete, Filter.tendsto_pure] using htendsto
  have hfinite : {atom : U.Atom | f (atom : OnePoint U.Atom) ≠ f ∞}.Finite := by
    exact Filter.eventually_cofinite.mp (by simpa only [not_not] using hevent)
  exact
    { defaultValue := f ∞
      exceptions := hfinite.toFinset }

/-- The continuous extension reads the authored default at infinity. -/
@[simp]
theorem atomPredicateCodeToContinuousMap_apply_infty [DecidableEq U.Atom]
    (code : AtomPredicateCode U) :
    atomPredicateCodeToContinuousMap code ∞ = code.defaultValue := by
  change code.defaultValue = code.defaultValue
  rfl

/-- On the Atom carrier, the continuous extension is the existing code evaluation. -/
@[simp]
theorem atomPredicateCodeToContinuousMap_apply_coe [DecidableEq U.Atom]
    (code : AtomPredicateCode U) (atom : U.Atom) :
    atomPredicateCodeToContinuousMap code (atom : OnePoint U.Atom) =
      code.eval atom := by
  change code.eval atom = code.eval atom
  rfl

/-- The inverse records exactly the points where the map differs from infinity. -/
@[simp]
theorem continuousMapToAtomPredicateCode_exception_mem [DecidableEq U.Atom]
    (f : C(OnePoint U.Atom, Bool)) (atom : U.Atom) :
    atom ∈ (continuousMapToAtomPredicateCode f).exceptions ↔
      f (atom : OnePoint U.Atom) ≠ f ∞ := by
  simp [continuousMapToAtomPredicateCode]

/-- The inverse code's default is the continuous map's value at infinity. -/
@[simp]
theorem continuousMapToAtomPredicateCode_defaultValue [DecidableEq U.Atom]
    (f : C(OnePoint U.Atom, Bool)) :
    (continuousMapToAtomPredicateCode f).defaultValue = f ∞ := by
  rfl

/-- Recovering a code after continuous extension preserves its raw structure. -/
theorem continuousMapToAtomPredicateCode_leftInverse [DecidableEq U.Atom]
    (code : AtomPredicateCode U) :
    continuousMapToAtomPredicateCode (atomPredicateCodeToContinuousMap code) =
      code := by
  cases code with
  | mk defaultValue exceptions =>
      change AtomPredicateCode.mk _ _ = AtomPredicateCode.mk defaultValue exceptions
      rw [AtomPredicateCode.mk.injEq]
      constructor
      · rw [atomPredicateCodeToContinuousMap_apply_infty]
      · ext atom
        rw [Set.Finite.mem_toFinset]
        simp only [atomPredicateCodeToContinuousMap_apply_coe,
          atomPredicateCodeToContinuousMap_apply_infty]
        simp [AtomPredicateCode.eval]

/-- Extending a code recovered from a continuous map returns the original map. -/
theorem atomPredicateCodeToContinuousMap_rightInverse [DecidableEq U.Atom]
    (f : C(OnePoint U.Atom, Bool)) :
    atomPredicateCodeToContinuousMap (continuousMapToAtomPredicateCode f) = f := by
  ext x
  induction x using OnePoint.rec with
  | infty =>
      rw [atomPredicateCodeToContinuousMap_apply_infty]
      rfl
  | coe atom =>
      rw [atomPredicateCodeToContinuousMap_apply_coe]
      by_cases h : f (atom : OnePoint U.Atom) = f ∞
      · simp [AtomPredicateCode.eval,
          continuousMapToAtomPredicateCode_exception_mem,
          continuousMapToAtomPredicateCode_defaultValue, h]
      · cases hleft : f (atom : OnePoint U.Atom) <;>
          cases hright : f ∞ <;>
          simp_all [AtomPredicateCode.eval,
            continuousMapToAtomPredicateCode_exception_mem,
            continuousMapToAtomPredicateCode_defaultValue]

/--
G-121(A)'s raw equivalence between finite-exception codes and continuous
Bool-valued maps on the one-point compactification of the discrete Atom carrier.
-/
noncomputable def atomPredicateCodeContinuousMapEquiv [DecidableEq U.Atom] :
    AtomPredicateCode U ≃ C(OnePoint U.Atom, Bool) :=
  Equiv.mk atomPredicateCodeToContinuousMap continuousMapToAtomPredicateCode
    continuousMapToAtomPredicateCode_leftInverse
    atomPredicateCodeToContinuousMap_rightInverse

end


#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
