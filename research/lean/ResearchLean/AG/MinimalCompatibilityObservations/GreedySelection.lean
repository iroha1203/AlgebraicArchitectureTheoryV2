import ResearchLean.AG.MinimalCompatibilityObservations.FiniteCover
import Formal.Util.AssertStandardAxioms

/-!
# G-128: finite greedy point selection

The chooser reads the supplied point list in order and updates its current
best point only for a strictly larger number of newly detected changes.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy

variable {G X : Type*} [Group G] [MulAction G X]
variable [DecidableEq G] [DecidableEq X]
variable (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
variable (EG : ExplicitEnumeration G) (EX : ExplicitEnumeration X)

/-- Number of currently uncovered incompatible changes detected by a point. -/
def newCoverage (R : Finset G) (x : X) : ℕ :=
  (R ∩ detectedSet Gamma EG x).card

/-- Select maximum new coverage; equal scores keep the first input point. -/
def greedyPick (R : Finset G) : Option X :=
  EX.values.argmax (newCoverage Gamma EG R)

theorem greedyPick_spec (R : Finset G) (x : X)
    (h : greedyPick Gamma EG EX R = some x) :
    x ∈ EX.values ∧
      (∀ y : X, newCoverage Gamma EG R y ≤ newCoverage Gamma EG R x) ∧
      (∀ y ∈ EX.values,
        newCoverage Gamma EG R x ≤ newCoverage Gamma EG R y →
          EX.values.idxOf x ≤ EX.values.idxOf y) := by
  obtain ⟨hx, hmax, hfirst⟩ := List.argmax_eq_some_iff.mp h
  exact ⟨hx, fun y => hmax y (EX.complete y), hfirst⟩

theorem greedyPick_none_iff (R : Finset G) :
    greedyPick Gamma EG EX R = none ↔ EX.values = [] := by
  exact List.argmax_eq_none

/-- If a maximizing point covers nothing, no point can move a remaining
incompatible change. -/
theorem greedyPick_zero_fixer (R : Finset G)
    (hR : R ⊆ incompatibleSet Gamma EG) (x : X)
    (hpick : greedyPick Gamma EG EX R = some x)
    (hzero : newCoverage Gamma EG R x = 0) :
    ∀ g ∈ R, ∀ y : X, g • y = y := by
  intro g hg y
  have hmax := (greedyPick_spec Gamma EG EX R x hpick).2.1 y
  have hgain : newCoverage Gamma EG R y = 0 := by omega
  by_contra hmove
  have hdet : g ∈ detectedSet Gamma EG y :=
    (mem_detectedSet Gamma EG g y).mpr
      ⟨(mem_incompatibleSet Gamma EG g).mp (hR hg), hmove⟩
  have hmem : g ∈ R ∩ detectedSet Gamma EG y := Finset.mem_inter.mpr ⟨hg, hdet⟩
  have hpositive : 0 < newCoverage Gamma EG R y :=
    Finset.card_pos.mpr ⟨g, hmem⟩
  omega

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
