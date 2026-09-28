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

/-- The failure branch returns an actual finite-table witness when one exists. -/
def greedyFallback : G :=
  (findIncompatibleFixer Gamma EG EX).getD 1

theorem greedyFallback_correct
    (hex : ∃ k : G, k ∉ Gamma ∧ ∀ x : X, k • x = x) :
    greedyFallback Gamma EG EX ∉ Gamma ∧
      ∀ x : X, greedyFallback Gamma EG EX • x = x := by
  cases hfind : findIncompatibleFixer Gamma EG EX with
  | none =>
      exact ((findIncompatibleFixer_none_iff Gamma EG EX).mp hfind hex).elim
  | some k =>
      simpa [greedyFallback, hfind] using
        findIncompatibleFixer_some Gamma EG EX k hfind

/-- A bounded recursive greedy run. Positive gain strictly reduces the
remaining universe; the public caller supplies `U.card` as the fuel. -/
def greedyAux : Nat → Finset G → List X ⊕ G
  | 0, R =>
      if R = ∅ then Sum.inl [] else Sum.inr (greedyFallback Gamma EG EX)
  | fuel + 1, R =>
      if R = ∅ then Sum.inl []
      else
        match greedyPick Gamma EG EX R with
        | none => Sum.inr (greedyFallback Gamma EG EX)
        | some x =>
            if 0 < newCoverage Gamma EG R x then
              match greedyAux fuel (R \ detectedSet Gamma EG x) with
              | Sum.inl xs => Sum.inl (x :: xs)
              | Sum.inr k => Sum.inr k
            else Sum.inr (greedyFallback Gamma EG EX)

/-- Run the greedy cover selection directly on the finite incompatible set. -/
def greedyObservation : List X ⊕ G :=
  greedyAux Gamma EG EX (incompatibleSet Gamma EG).card (incompatibleSet Gamma EG)

private theorem greedyFallback_of_zero (R : Finset G)
    (hR : R ⊆ incompatibleSet Gamma EG) (hne : R ≠ ∅)
    (hzero : ∀ x : X, newCoverage Gamma EG R x = 0) :
    greedyFallback Gamma EG EX ∉ Gamma ∧
      ∀ x : X, greedyFallback Gamma EG EX • x = x := by
  obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hfix : ∀ x : X, g • x = x := by
    intro x
    by_contra hmove
    have hdet : g ∈ detectedSet Gamma EG x :=
      (mem_detectedSet Gamma EG g x).mpr
        ⟨(mem_incompatibleSet Gamma EG g).mp (hR hg), hmove⟩
    have hpositive : 0 < newCoverage Gamma EG R x :=
      Finset.card_pos.mpr ⟨g, Finset.mem_inter.mpr ⟨hg, hdet⟩⟩
    rw [hzero x] at hpositive
    omega
  exact greedyFallback_correct Gamma EG EX
    ⟨g, (mem_incompatibleSet Gamma EG g).mp (hR hg), hfix⟩

/-- With enough fuel, the actual greedy run covers its initial remainder or
returns a genuine incompatible all-point fixer. -/
theorem greedyAux_correct (fuel : Nat) (R : Finset G)
    (hR : R ⊆ incompatibleSet Gamma EG) (hfuel : R.card ≤ fuel) :
    match greedyAux Gamma EG EX fuel R with
    | Sum.inl xs => R ⊆ xs.toFinset.biUnion (detectedSet Gamma EG)
    | Sum.inr k => k ∉ Gamma ∧ ∀ x : X, k • x = x := by
  induction fuel generalizing R with
  | zero =>
      have hempty : R = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hfuel)
      simp [greedyAux, hempty]
  | succ n ih =>
      by_cases hempty : R = ∅
      · simp [greedyAux, hempty]
      · cases hpick : greedyPick Gamma EG EX R with
        | none =>
            have hnil : EX.values = [] :=
              (greedyPick_none_iff Gamma EG EX R).mp hpick
            have hzero : ∀ x : X, newCoverage Gamma EG R x = 0 := by
              intro x
              have hfalse : False := by simpa [hnil] using EX.complete x
              exact hfalse.elim
            have hfb := greedyFallback_of_zero Gamma EG EX R hR hempty hzero
            simpa [greedyAux, hempty, hpick] using hfb
        | some x =>
            by_cases hpos : 0 < newCoverage Gamma EG R x
            · let R' := R \ detectedSet Gamma EG x
              have hsub : R' ⊆ incompatibleSet Gamma EG :=
                (Finset.sdiff_subset).trans hR
              have hcardeq := Finset.card_sdiff_add_card_inter R
                (detectedSet Gamma EG x)
              have hlt : R'.card < R.card := by
                dsimp [R', newCoverage] at *
                omega
              have hfuel' : R'.card ≤ n := by omega
              have hrec := ih R' hsub hfuel'
              cases hrun : greedyAux Gamma EG EX n R' with
              | inr k =>
                  simpa [greedyAux, hempty, hpick, hpos, R', hrun] using hrec
              | inl xs =>
                  have hcov : R' ⊆ xs.toFinset.biUnion (detectedSet Gamma EG) := by
                    simpa [hrun] using hrec
                  have hfull : R ⊆ (x :: xs).toFinset.biUnion
                      (detectedSet Gamma EG) := by
                    intro g hg
                    by_cases hdet : g ∈ detectedSet Gamma EG x
                    · exact Finset.mem_biUnion.mpr ⟨x, by simp, hdet⟩
                    · have hremain : g ∈ R' := Finset.mem_sdiff.mpr ⟨hg, hdet⟩
                      obtain ⟨y, hy, hdy⟩ := Finset.mem_biUnion.mp (hcov hremain)
                      exact Finset.mem_biUnion.mpr ⟨y, by simp [hy], hdy⟩
                  simpa [greedyAux, hempty, hpick, hpos, R', hrun] using hfull
            · have hmax := (greedyPick_spec Gamma EG EX R x hpick).2.1
              have hzero : ∀ y : X, newCoverage Gamma EG R y = 0 := by
                intro y
                have hy := hmax y
                omega
              have hfb := greedyFallback_of_zero Gamma EG EX R hR hempty hzero
              simpa [greedyAux, hempty, hpick, hpos] using hfb

theorem greedyObservation_correct :
    match greedyObservation Gamma EG EX with
    | Sum.inl xs => Sufficient Gamma xs.toFinset
    | Sum.inr k => k ∉ Gamma ∧ (∀ x : X, k • x = x) ∧
        minObservations (X := X) Gamma = ⊤ ∧
        optimalQueries (X := X) Gamma = ⊤ := by
  have haux := greedyAux_correct Gamma EG EX
    (incompatibleSet Gamma EG).card (incompatibleSet Gamma EG)
    (by rfl) (le_refl _)
  unfold greedyObservation
  cases hrun : greedyAux Gamma EG EX (incompatibleSet Gamma EG).card
      (incompatibleSet Gamma EG) with
  | inl xs =>
      have hcover : incompatibleSet Gamma EG ⊆
          xs.toFinset.biUnion (detectedSet Gamma EG) := by
        simpa [hrun] using haux
      have heq : xs.toFinset.biUnion (detectedSet Gamma EG) =
          incompatibleSet Gamma EG :=
        Finset.Subset.antisymm (cover_subset_incompatible Gamma EG xs.toFinset) hcover
      exact (sufficient_iff_cover Gamma EG xs.toFinset).mpr heq
  | inr k =>
      obtain ⟨hk, hfix⟩ : k ∉ Gamma ∧ ∀ x : X, k • x = x := by
        simpa [hrun] using haux
      have hno : ¬ ∃ B : Finset X, Sufficient Gamma B := by
        rintro ⟨B, hB⟩
        exact hk (hB (by intro x hx; exact hfix x))
      have htop := (minObservations_eq_top_iff (X := X) Gamma).mpr hno
      exact ⟨hk, hfix, htop, by rw [optimalQueries_eq_minObservations, htop]⟩

/-- The public greedy output presents the selected points as a set. -/
def greedyObservationSet : Finset X ⊕ G :=
  match greedyObservation Gamma EG EX with
  | Sum.inl xs => Sum.inl xs.toFinset
  | Sum.inr k => Sum.inr k

theorem greedyObservationSet_correct :
    match greedyObservationSet Gamma EG EX with
    | Sum.inl B => Sufficient Gamma B
    | Sum.inr k => k ∉ Gamma ∧ (∀ x : X, k • x = x) ∧
        minObservations (X := X) Gamma = ⊤ ∧
        optimalQueries (X := X) Gamma = ⊤ := by
  unfold greedyObservationSet
  cases h : greedyObservation Gamma EG EX with
  | inl xs => simpa [h] using greedyObservation_correct Gamma EG EX
  | inr k => simpa [h] using greedyObservation_correct Gamma EG EX

/-- With no incompatible changes, greedy returns the empty set immediately. -/
theorem greedyObservation_empty (hU : incompatibleSet Gamma EG = ∅) :
    greedyObservationSet Gamma EG EX = Sum.inl ∅ := by
  simp [greedyObservationSet, greedyObservation, hU, greedyAux]

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
