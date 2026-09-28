import ResearchLean.AG.MinimalCompatibilityObservations.QueryOptimum
import Formal.Util.AssertStandardAxioms

/-!
# G-128: exhaustive finite minimum observation search

The candidate list is built from sublists of the supplied point enumeration.
This keeps the search executable even when the enumeration has duplicates.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy

variable {G X : Type*} [Group G] [MulAction G X]
variable [DecidableEq G] [DecidableEq X]

/-- Decide sufficiency by finite quantification over the supplied change table. -/
def sufficientBool (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
    (EG : ExplicitEnumeration G) (B : Finset X) : Bool :=
  letI : Fintype G := EG.toFintype
  decide (∀ g : G, (∀ x ∈ B, g • x = x) → g ∈ Gamma)

theorem sufficientBool_iff (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
    (EG : ExplicitEnumeration G) (B : Finset X) :
    sufficientBool Gamma EG B = true ↔ Sufficient Gamma B := by
  simp only [sufficientBool, decide_eq_true_eq]
  change (∀ g : G, (∀ x ∈ B, g • x = x) → g ∈ Gamma) ↔
    (∀ g : G, (∀ x ∈ B, g • x = x) → g ∈ Gamma)
  rfl

/-- Every finite observation subset appears, possibly repeatedly, in this
executable enumeration. -/
def candidateSets (EX : ExplicitEnumeration X) : List (Finset X) :=
  EX.values.sublists.map List.toFinset

theorem mem_candidateSets (EX : ExplicitEnumeration X) (B : Finset X) :
    B ∈ candidateSets EX := by
  let points := EX.values.filter fun x => decide (x ∈ B)
  have hpoints : points.toFinset = B := by
    ext x
    simp [points, List.mem_filter, EX.complete]
  have hsub : points ∈ EX.values.sublists :=
    List.mem_sublists.mpr List.filter_sublist
  exact hpoints ▸ List.mem_map.mpr ⟨points, hsub, rfl⟩

/-- Exhaustive minimum among all candidates passing the exact sufficiency
test. `none` means there is no sufficient finite observation set. -/
def minimumObservation (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
    (EG : ExplicitEnumeration G) (EX : ExplicitEnumeration X) : Option (Finset X) :=
  ((candidateSets EX).filter fun B => sufficientBool Gamma EG B).argmin Finset.card

theorem minimumObservation_some (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
    (EG : ExplicitEnumeration G) (EX : ExplicitEnumeration X)
    (B : Finset X) (h : minimumObservation Gamma EG EX = some B) :
    Sufficient Gamma B ∧
      ∀ C : Finset X, Sufficient Gamma C → B.card ≤ C.card := by
  let candidates := (candidateSets EX).filter fun C => sufficientBool Gamma EG C
  have hmem : B ∈ candidates := List.argmin_mem (f := Finset.card) (by simpa [minimumObservation, candidates] using h)
  have hB : Sufficient Gamma B :=
    (sufficientBool_iff Gamma EG B).mp (List.mem_filter.mp hmem).2
  refine ⟨hB, ?_⟩
  intro C hC
  have hc : C ∈ candidates := List.mem_filter.mpr
    ⟨mem_candidateSets EX C, (sufficientBool_iff Gamma EG C).mpr hC⟩
  exact List.le_of_mem_argmin hc (by simpa [minimumObservation, candidates] using h)

theorem minimumObservation_none_iff (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) :
    minimumObservation Gamma EG EX = none ↔
      ¬ ∃ B : Finset X, Sufficient Gamma B := by
  rw [minimumObservation, List.argmin_eq_none]
  constructor
  · intro hempty ⟨B, hB⟩
    have hmem : B ∈ (candidateSets EX).filter fun C => sufficientBool Gamma EG C :=
      List.mem_filter.mpr
        ⟨mem_candidateSets EX B, (sufficientBool_iff Gamma EG B).mpr hB⟩
    simp [hempty] at hmem
  · intro h
    cases hc : (candidateSets EX).filter (fun C => sufficientBool Gamma EG C) with
    | nil => rfl
    | cons B bs =>
        have hm : B ∈ (candidateSets EX).filter (fun C => sufficientBool Gamma EG C) := by
          rw [hc]
          simp
        have hB : Sufficient Gamma B :=
          (sufficientBool_iff Gamma EG B).mp
            (List.mem_filter.mp hm).2
        exact (h ⟨B, hB⟩).elim

theorem minimumObservation_card (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) (B : Finset X)
    (h : minimumObservation Gamma EG EX = some B) :
    (B.card : ℕ∞) = minObservations (X := X) Gamma := by
  obtain ⟨hB, hmin⟩ := minimumObservation_some Gamma EG EX B h
  have hfinite : minObservations (X := X) Gamma ≠ ⊤ := by
    intro ht
    have hle := minObservations_le Gamma B hB
    simp [ht] at hle
  obtain ⟨C, hC, hcard⟩ := minObservations_attained (X := X) Gamma hfinite
  apply le_antisymm
  · have hnat : B.card ≤ C.card := hmin C hC
    have henat : (B.card : ℕ∞) ≤ (C.card : ℕ∞) := by exact_mod_cast hnat
    exact henat.trans_eq hcard
  · exact minObservations_le Gamma B hB

/-- Search the supplied change table for an incompatible element invisible
at every point of the supplied point table. -/
def findIncompatibleFixer (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
    (EG : ExplicitEnumeration G) (EX : ExplicitEnumeration X) : Option G :=
  letI : Fintype X := EX.toFintype
  scan (fun g => decide (g ∉ Gamma ∧ ∀ x : X, g • x = x)) EG.values

theorem findIncompatibleFixer_some (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) (k : G)
    (h : findIncompatibleFixer Gamma EG EX = some k) :
    k ∉ Gamma ∧ ∀ x : X, k • x = x := by
  letI : Fintype X := EX.toFintype
  exact of_decide_eq_true (scan_some _ _ _ h).1

theorem findIncompatibleFixer_none_iff (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) :
    findIncompatibleFixer Gamma EG EX = none ↔
      ¬ ∃ k : G, k ∉ Gamma ∧ ∀ x : X, k • x = x := by
  letI : Fintype X := EX.toFintype
  rw [findIncompatibleFixer, scan_none_iff]
  constructor
  · intro h ⟨k, hk⟩
    have hf := h k (EG.complete k)
    have ht : decide (k ∉ Gamma ∧ ∀ x : X, k • x = x) = true :=
      decide_eq_true hk
    exact Bool.false_ne_true (hf.symm.trans ht)
  · intro h k hk
    by_cases hp : k ∉ Gamma ∧ ∀ x : X, k • x = x
    · exact (h ⟨k, hp⟩).elim
    · exact Bool.eq_false_iff.mpr (by simpa using hp)

theorem no_sufficient_iff_incompatible_fixer (Gamma : Subgroup G)
    (EX : ExplicitEnumeration X) :
    (¬ ∃ B : Finset X, Sufficient Gamma B) ↔
      ∃ k : G, k ∉ Gamma ∧ ∀ x : X, k • x = x := by
  constructor
  · intro hno
    by_contra hn
    letI : Fintype X := EX.toFintype
    have hfull : Sufficient Gamma (Finset.univ : Finset X) := by
      intro g hg
      by_contra hbad
      exact hn ⟨g, hbad, by intro x; exact hg x (Finset.mem_univ x)⟩
    exact hno ⟨Finset.univ, hfull⟩
  · rintro ⟨k, hk, hfix⟩ ⟨B, hB⟩
    exact hk (hB (by intro x hx; exact hfix x))

/-- The two finite searches cover both cases, producing an actual minimum
set or an incompatible all-point fixer. -/
def minimumOrWitness (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
    (EG : ExplicitEnumeration G) (EX : ExplicitEnumeration X) :
    Finset X ⊕ G :=
  match minimumObservation Gamma EG EX with
  | some B => Sum.inl B
  | none => Sum.inr ((findIncompatibleFixer Gamma EG EX).getD 1)

theorem minimumOrWitness_correct (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) :
    match minimumOrWitness Gamma EG EX with
    | Sum.inl B => Sufficient Gamma B ∧
        (B.card : ℕ∞) = minObservations (X := X) Gamma
    | Sum.inr k => k ∉ Gamma ∧ (∀ x : X, k • x = x) ∧
        minObservations (X := X) Gamma = ⊤ ∧
        optimalQueries (X := X) Gamma = ⊤ := by
  unfold minimumOrWitness
  cases hmin : minimumObservation Gamma EG EX with
  | some B =>
      exact ⟨(minimumObservation_some Gamma EG EX B hmin).1,
        minimumObservation_card Gamma EG EX B hmin⟩
  | none =>
      have hno := (minimumObservation_none_iff Gamma EG EX).mp hmin
      have hex := (no_sufficient_iff_incompatible_fixer Gamma EX).mp hno
      have hsome : ∃ k : G, findIncompatibleFixer Gamma EG EX = some k := by
        cases hf : findIncompatibleFixer Gamma EG EX with
        | none => exact ((findIncompatibleFixer_none_iff Gamma EG EX).mp hf hex).elim
        | some k => exact ⟨k, rfl⟩
      obtain ⟨k, hk⟩ := hsome
      simp only [hk, Option.getD_some]
      have hw := findIncompatibleFixer_some Gamma EG EX k hk
      have htop := (minObservations_eq_top_iff (X := X) Gamma).mpr hno
      exact ⟨hw.1, hw.2, htop, by rw [optimalQueries_eq_minObservations, htop]⟩

/-- The same minimum set returned by the finite search classifies every
unknown change from its exact observation table. -/
theorem minimumOrWitness_classifier (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) (B : Finset X)
    (h : minimumOrWitness Gamma EG EX = Sum.inl B) (g : G) :
    classify Gamma EG B (observe B g) = true ↔ g ∈ Gamma := by
  have hB : Sufficient Gamma B := by
    have hc := minimumOrWitness_correct Gamma EG EX
    rw [h] at hc
    exact hc.1
  exact classify_correct Gamma EG B hB g

/-- Feed the actual minimum set returned by exhaustive table search into
the executable fixed-query procedure. -/
theorem minimumOrWitness_optimalProcedure (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) (B : Finset X)
    (h : minimumOrWitness Gamma EG EX = Sum.inl B) :
    CorrectQueryProcedure Gamma
      (finiteFixedProcedure Gamma EG (finitePoints EX B)) ∧
    worstQueries (G := G) (finiteFixedProcedure Gamma EG (finitePoints EX B)) =
      minObservations (X := X) Gamma := by
  have hc := minimumOrWitness_correct Gamma EG EX
  rw [h] at hc
  obtain ⟨hB, hcard⟩ := hc
  let points := finitePoints EX B
  have hcorrect : CorrectQueryProcedure Gamma
      (finiteFixedProcedure Gamma EG points) :=
    finiteFixedProcedure_correct_of_list Gamma EG B hB points
      (finitePoints_toFinset EX B)
  refine ⟨hcorrect, ?_⟩
  apply le_antisymm
  · rw [finiteFixedProcedure_eq_fixed]
    have hupper : worstQueries (G := G) (fixedProcedure Gamma points) ≤
        (points.length : ℕ∞) := by
      unfold worstQueries
      refine iSup_le fun g => iSup_le fun result => iSup_le fun qs => iSup_le fun run => ?_
      obtain ⟨_, hqs⟩ := (fixedProcedure_run Gamma points g).deterministic _ _ run
      subst qs
      rfl
    have hlen : (points.length : ℕ∞) = minObservations (X := X) Gamma := by
      simpa only [points, finitePoints_length] using hcard
    exact hupper.trans_eq hlen
  · exact minObservations_le_worst Gamma _ hcorrect

/-- The search's failure witness is indistinguishable from the identity at
every finite point table, while their compatibility differs. -/
theorem minimumOrWitness_invisible (Gamma : Subgroup G)
    [DecidablePred (· ∈ Gamma)] (EG : ExplicitEnumeration G)
    (EX : ExplicitEnumeration X) (k : G)
    (h : minimumOrWitness Gamma EG EX = Sum.inr k) :
    k ∉ Gamma ∧ (1 : G) ∈ Gamma ∧
      (∀ B : Finset X, observe B k = observe B (1 : G)) ∧
      minObservations (X := X) Gamma = ⊤ ∧
      optimalQueries (X := X) Gamma = ⊤ := by
  have hc := minimumOrWitness_correct Gamma EG EX
  rw [h] at hc
  obtain ⟨hk, hfix, hb, hd⟩ := hc
  refine ⟨hk, Gamma.one_mem, ?_, hb, hd⟩
  intro B
  funext x
  change k • x.1 = (1 : G) • x.1
  simpa using hfix x.1

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
