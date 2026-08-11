import ResearchLean.AG.UniformInvariance.PresentationASubnerveDefect
import Formal.Util.AssertStandardAxioms

/-!
# Executable uniform-presentation decider

This module completes claim (ii) of
`G-107-aat-uniform-invariance-characterization`.  It enumerates every subset
of the explicit coarse-target list in a finite comparison presentation, runs
the Cycle 8 exact defect evaluator on every nonempty subset, and identifies
the resulting Boolean check with the full semantic uniform-invariance
predicate.

## Implementation notes

`Finset.toList` has no executable code in the current Lean runtime, so the
checker deliberately starts from the presentation's explicit coarse-target
list and uses the standard executable `List.sublists` recursion.
The coverage theorem below proves that this list enumeration reaches every
finite subset.  The checker body reads no semantic uniformity proof and stores
no rank, defect, or result certificate: its only numerical input is the exact
raw-table evaluator constructed in Cycle 8.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology

/-! ## Semantic predicate and executable subset enumeration -/

/-- A finite comparison presentation is uniform when its generated semantic
comparison geometry is uniformly invariant for every adequate law family. -/
def UniformPresentation (P : FiniteComparisonPresentation) : Prop :=
  P.toGeometry.UniformInvariance

namespace FiniteComparisonPresentation

/-- Every coarse-target subset appears as the finite set underlying a sublist
of the presentation's explicit target enumeration. -/
theorem exists_sublists_toFinset_eq (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) :
    ∃ targets ∈ P.coarseTargetEntries.sublists, targets.toFinset = A := by
  let targets := P.coarseTargetEntries.filter fun target => decide (target ∈ A)
  refine ⟨targets, List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext target
  simp [targets, P.coarseTarget_mem_coarseTargetEntries]

/-- Executably inspect every sublist of the explicit coarse-target
enumeration, ignoring the empty subset and checking exact zero defect on every
nonempty subset. -/
def uniformPresentationCheck (P : FiniteComparisonPresentation) : Bool :=
  P.coarseTargetEntries.sublists.all fun targets =>
    match targets with
    | [] => true
    | _ :: _ =>
        decide (P.computedASubnerveDefect targets.toFinset = (0, 0))

/-- The Boolean checker is true exactly when the computed defect vanishes on
every nonempty finite coarse-target subset. -/
theorem uniformPresentationCheck_eq_true_iff_allNonemptyDefects
    (P : FiniteComparisonPresentation) :
    P.uniformPresentationCheck = true ↔
      ∀ A : Finset P.CoarseTarget, A.Nonempty →
        P.computedASubnerveDefect A = (0, 0) := by
  rw [uniformPresentationCheck, List.all_eq_true]
  constructor
  · intro hcheck A hA
    obtain ⟨targets, htargets, htargetsA⟩ := P.exists_sublists_toFinset_eq A
    cases targets with
    | nil =>
        simp at htargetsA
        subst A
        exact (Finset.not_nonempty_empty hA).elim
    | cons target rest =>
        have hvalue := hcheck (target :: rest) htargets
        simpa [htargetsA] using of_decide_eq_true hvalue
  · intro hzero targets htargets
    cases targets with
    | nil => rfl
    | cons target rest =>
        apply decide_eq_true
        apply hzero
        exact ⟨target, by simp⟩

/-- Finite-subset zero defect is equivalent to zero literal defect on every
nonempty semantic set of coarse targets. -/
theorem allNonemptyComputedASubnerveDefect_eq_zero_iff
    (P : FiniteComparisonPresentation) :
    (∀ A : Finset P.CoarseTarget, A.Nonempty →
        P.computedASubnerveDefect A = (0, 0)) ↔
      (∀ A : Set P.CoarseTarget, A.Nonempty →
        P.toGeometry.aSubnerveDefect A = (0, 0)) := by
  constructor
  · intro hzero A hA
    let AFinset : Finset P.CoarseTarget := A.toFinite.toFinset
    have hAFinset : AFinset.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hsetEmpty : A = ∅ := by
        rw [← A.toFinite.coe_toFinset]
        simp [AFinset, hempty]
      exact hA.ne_empty hsetEmpty
    calc
      P.toGeometry.aSubnerveDefect A =
          P.toGeometry.aSubnerveDefect (↑AFinset : Set P.CoarseTarget) := by
            rw [A.toFinite.coe_toFinset]
      _ = P.computedASubnerveDefect AFinset :=
        (P.computedASubnerveDefect_eq_aSubnerveDefect AFinset).symm
      _ = (0, 0) := hzero AFinset hAFinset
  · intro hzero A hA
    rw [P.computedASubnerveDefect_eq_aSubnerveDefect A]
    exact hzero (↑A : Set P.CoarseTarget) (by simpa using hA)

/-- Main Cycle 9 correctness theorem: the executable all-subset check is true
exactly for presentations whose generated comparison geometry satisfies full
uniform invariance. -/
theorem uniformPresentationCheck_eq_true_iff
    (P : FiniteComparisonPresentation) :
    P.uniformPresentationCheck = true ↔ UniformPresentation P := by
  rw [P.uniformPresentationCheck_eq_true_iff_allNonemptyDefects,
    P.allNonemptyComputedASubnerveDefect_eq_zero_iff,
    UniformPresentation,
    P.toGeometry.uniformInvariance_iff_allNonemptyASubnerveDefect_eq_zero]
  rfl

end FiniteComparisonPresentation

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
