import ResearchLean.AG.MinimalCompatibilityObservations.GreedySelection
import Formal.Util.AssertStandardAxioms

/-!
# G-128: harmonic bound for the actual greedy observation set
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy

theorem harmonic_drop (n k : ℕ) (hk : k ≤ n) (hn : 0 < n) :
    (k : ℚ) / n ≤ harmonic n - harmonic (n - k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        have hsub : n - (0 + 1) = n - 1 := by omega
        have hsucc : n - 1 + 1 = n := by omega
        rw [hsub, ← hsucc, harmonic_succ]
        simp
      · have hn1 : 0 < n - 1 := by omega
        have hkle : k ≤ n - 1 := by omega
        have hrec := ih (n - 1) hkle hn1
        have hden : (n - 1 : ℕ) ≤ n := by omega
        have hden0 : (0 : ℚ) < (n - 1 : ℕ) := by exact_mod_cast hn1
        have hqden : ((n - 1 : ℕ) : ℚ) ≤ n := by exact_mod_cast hden
        have hdiv : (k : ℚ) / n ≤ (k : ℚ) / (n - 1 : ℕ) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden0 hqden
        have hsucc : n - 1 + 1 = n := by omega
        have hsub : n - (k + 1) = (n - 1) - k := by omega
        rw [hsub, ← hsucc, harmonic_succ]
        have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        have hcast : (((k + 1 : ℕ) : ℚ) / n) = (k : ℚ) / n + (n : ℚ)⁻¹ := by
          push_cast
          field_simp
        rw [hsucc]
        rw [hcast]
        linarith

variable {G X : Type*} [Group G] [MulAction G X]
variable [DecidableEq G] [DecidableEq X]
variable (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
variable (EG : ExplicitEnumeration G) (EX : ExplicitEnumeration X)

theorem greedy_step_card (R : Finset G) (B : Finset X)
    (hR : R ⊆ incompatibleSet Gamma EG)
    (hB : Sufficient Gamma B) (x : X)
    (hpick : greedyPick Gamma EG EX R = some x) :
    R.card ≤ B.card * newCoverage Gamma EG R x := by
  have hcover : B.biUnion (detectedSet Gamma EG) = incompatibleSet Gamma EG :=
    (sufficient_iff_cover Gamma EG B).mp hB
  have hsub : R ⊆ B.biUnion (fun y => R ∩ detectedSet Gamma EG y) := by
    intro g hg
    have hU : g ∈ B.biUnion (detectedSet Gamma EG) := hcover.symm ▸ hR hg
    obtain ⟨y, hy, hgy⟩ := Finset.mem_biUnion.mp hU
    exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_inter.mpr ⟨hg, hgy⟩⟩
  have hcard : R.card ≤ (B.biUnion (fun y => R ∩ detectedSet Gamma EG y)).card :=
    Finset.card_le_card hsub
  have hmul := Finset.card_biUnion_le_card_mul
    (s := B) (f := fun y => R ∩ detectedSet Gamma EG y)
    (newCoverage Gamma EG R x) (by
      intro y hy
      exact (greedyPick_spec Gamma EG EX R x hpick).2.1 y)
  exact hcard.trans hmul

theorem greedy_step_harmonic (R : Finset G) (B : Finset X)
    (hR : R ⊆ incompatibleSet Gamma EG)
    (hB : Sufficient Gamma B) (hne : R ≠ ∅) (x : X)
    (hpick : greedyPick Gamma EG EX R = some x) :
    (1 : ℚ) ≤ (B.card : ℚ) *
      (harmonic R.card - harmonic (R \ detectedSet Gamma EG x).card) := by
  let k := newCoverage Gamma EG R x
  have hcard := greedy_step_card Gamma EG EX R B hR hB x hpick
  have hn : 0 < R.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hk : k ≤ R.card := by
    exact Finset.card_le_card Finset.inter_subset_left
  have hsum := Finset.card_sdiff_add_card_inter R (detectedSet Gamma EG x)
  have hdiff : (R \ detectedSet Gamma EG x).card = R.card - k := by
    dsimp [k, newCoverage] at *
    omega
  have hq : (R.card : ℚ) ≤ (B.card : ℚ) * k := by exact_mod_cast hcard
  have hnq : (0 : ℚ) < R.card := by exact_mod_cast hn
  have hfrac : (1 : ℚ) ≤ (B.card : ℚ) * ((k : ℚ) / R.card) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hnq).mpr (by simpa using hq)
  have hdrop := harmonic_drop R.card k hk hn
  rw [hdiff]
  have hbnonneg : (0 : ℚ) ≤ B.card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hdrop hbnonneg]

theorem greedyAux_harmonic (B : Finset X) (hB : Sufficient Gamma B)
    (fuel : ℕ) (R : Finset G)
    (hR : R ⊆ incompatibleSet Gamma EG) (hfuel : R.card ≤ fuel) :
    ∃ xs : List X, greedyAux Gamma EG EX fuel R = Sum.inl xs ∧
      (xs.length : ℚ) ≤ (B.card : ℚ) * harmonic R.card := by
  induction fuel generalizing R with
  | zero =>
      have hempty : R = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hfuel)
      refine ⟨[], ?_, ?_⟩
      · simp [greedyAux, hempty]
      · simp [hempty, harmonic_zero]
  | succ n ih =>
      by_cases hempty : R = ∅
      · refine ⟨[], ?_, ?_⟩
        · simp [greedyAux, hempty]
        · simp [hempty, harmonic_zero]
      have hcover : B.biUnion (detectedSet Gamma EG) = incompatibleSet Gamma EG :=
        (sufficient_iff_cover Gamma EG B).mp hB
      obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hgu : g ∈ B.biUnion (detectedSet Gamma EG) := hcover.symm ▸ hR hg
      obtain ⟨y, hy, _⟩ := Finset.mem_biUnion.mp hgu
      have hlist : EX.values ≠ [] := by
        intro hnil
        have hymem : y ∈ EX.values := EX.complete y
        simp [hnil] at hymem
      cases hpick : greedyPick Gamma EG EX R with
      | none =>
          exact (hlist ((greedyPick_none_iff Gamma EG EX R).mp hpick)).elim
      | some x =>
          have hcard := greedy_step_card Gamma EG EX R B hR hB x hpick
          have hpos : 0 < newCoverage Gamma EG R x := by
            by_contra hnot
            have : newCoverage Gamma EG R x = 0 := by omega
            rw [this] at hcard
            have hrcard : 0 < R.card := Finset.card_pos.mpr ⟨g, hg⟩
            omega
          let R' := R \ detectedSet Gamma EG x
          have hsub : R' ⊆ incompatibleSet Gamma EG :=
            (Finset.sdiff_subset).trans hR
          have hsum := Finset.card_sdiff_add_card_inter R (detectedSet Gamma EG x)
          have hlt : R'.card < R.card := by
            dsimp [R', newCoverage] at *
            omega
          have hfuel' : R'.card ≤ n := by omega
          obtain ⟨xs, hrun, hlen⟩ := ih R' hsub hfuel'
          refine ⟨x :: xs, ?_, ?_⟩
          · simp [greedyAux, hempty, hpick, hpos, R', hrun]
          · have hstep := greedy_step_harmonic Gamma EG EX R B hR hB hempty x hpick
            dsimp [R'] at hlen ⊢
            simp only [Nat.cast_add, Nat.cast_one]
            nlinarith

/-- The actual finite-table greedy result satisfies the fixed C1 bound. -/
theorem greedyObservationSet_harmonic (Bmin : Finset X)
    (hmin : minimumObservation Gamma EG EX = some Bmin) :
    ∃ Bgr : Finset X,
      greedyObservationSet Gamma EG EX = Sum.inl Bgr ∧
      Sufficient Gamma Bgr ∧
      (Bgr.card : ℚ) ≤
        harmonic (incompatibleSet Gamma EG).card *
          ((minObservations (X := X) Gamma).toNat : ℚ) := by
  have hB := (minimumObservation_some Gamma EG EX Bmin hmin).1
  obtain ⟨xs, hrun, hlen⟩ := greedyAux_harmonic Gamma EG EX Bmin hB
    (incompatibleSet Gamma EG).card (incompatibleSet Gamma EG)
    (by rfl) (le_refl _)
  let Bgr := xs.toFinset
  have houtput : greedyObservationSet Gamma EG EX = Sum.inl Bgr := by
    simp [greedyObservationSet, greedyObservation, hrun, Bgr]
  refine ⟨Bgr, houtput, ?_, ?_⟩
  · have hc := greedyObservationSet_correct Gamma EG EX
    rw [houtput] at hc
    exact hc
  · have hmincard := minimumObservation_card Gamma EG EX Bmin hmin
    have hnat : (minObservations (X := X) Gamma).toNat = Bmin.card := by
      rw [← hmincard]
      exact ENat.toNat_coe _
    rw [hnat]
    have hlist : Bgr.card ≤ xs.length := List.toFinset_card_le xs
    have hq : (Bgr.card : ℚ) ≤ xs.length := by exact_mod_cast hlist
    dsimp [Bgr] at hq ⊢
    nlinarith

theorem greedyObservationSet_harmonic_of_coverable
    (hcover : ∃ B : Finset X, Sufficient Gamma B) :
    ∃ Bgr : Finset X,
      greedyObservationSet Gamma EG EX = Sum.inl Bgr ∧
      Sufficient Gamma Bgr ∧
      (Bgr.card : ℚ) ≤
        harmonic (incompatibleSet Gamma EG).card *
          ((minObservations (X := X) Gamma).toNat : ℚ) := by
  cases hmin : minimumObservation Gamma EG EX with
  | none =>
      exact ((minimumObservation_none_iff Gamma EG EX).mp hmin hcover).elim
  | some Bmin =>
      exact greedyObservationSet_harmonic Gamma EG EX Bmin hmin

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
