import ResearchLean.AG.MinimalCompatibilityObservations.GreedyBound
import Formal.Util.AssertStandardAxioms

/-!
# G-128: independent composition of point observations
-/

namespace AAT.AG.MinimalCompatibilityObservations

variable {G X : Type*} [Group G] [MulAction G X]

/-- Enlarging the compatible subgroup cannot increase the required number
of observations. The result includes infinite minima. -/
theorem minObservations_antitone (Gamma₁ Gamma₂ : Subgroup G)
    (hΓ : Gamma₁ ≤ Gamma₂) :
    minObservations (X := X) Gamma₂ ≤ minObservations (X := X) Gamma₁ := by
  by_cases htop : minObservations (X := X) Gamma₁ = ⊤
  · simp [htop]
  · obtain ⟨B, hB, hcard⟩ := minObservations_attained (X := X) Gamma₁ htop
    have hB₂ : Sufficient Gamma₂ B := hB.trans hΓ
    exact (minObservations_le Gamma₂ B hB₂).trans_eq hcard

variable {G₁ G₂ X₁ X₂ : Type*}
variable [Group G₁] [Group G₂] [MulAction G₁ X₁] [MulAction G₂ X₂]

/-- The product acts independently on the two summands. -/
def independentAction : MulAction (G₁ × G₂) (X₁ ⊕ X₂) where
  smul g x := x.elim (fun a => Sum.inl (g.1 • a)) (fun b => Sum.inr (g.2 • b))
  one_smul := by
    intro x
    cases x with
    | inl a => change Sum.inl ((1 : G₁) • a) = Sum.inl a; simp
    | inr b => change Sum.inr ((1 : G₂) • b) = Sum.inr b; simp
  mul_smul := by
    intro g h x
    cases x with
    | inl a =>
        change Sum.inl ((g.1 * h.1) • a) = Sum.inl (g.1 • (h.1 • a))
        rw [mul_smul]
    | inr b =>
        change Sum.inr ((g.2 * h.2) • b) = Sum.inr (g.2 • (h.2 • b))
        rw [mul_smul]

theorem sufficient_independent_iff (Gamma₁ : Subgroup G₁)
    (Gamma₂ : Subgroup G₂) (B : Finset (X₁ ⊕ X₂)) :
    letI := independentAction (G₁ := G₁) (G₂ := G₂) (X₁ := X₁) (X₂ := X₂)
    Sufficient (Gamma₁.prod Gamma₂) B ↔
      Sufficient Gamma₁ B.toLeft ∧ Sufficient Gamma₂ B.toRight := by
  letI := independentAction (G₁ := G₁) (G₂ := G₂) (X₁ := X₁) (X₂ := X₂)
  constructor
  · intro h
    constructor
    · intro g hg
      have hp : (g, (1 : G₂)) ∈ Gamma₁.prod Gamma₂ := h (by
        intro x hx
        cases x with
        | inl a =>
            change Sum.inl (g • a) = Sum.inl a
            exact congrArg Sum.inl (hg a (Finset.mem_toLeft.mpr hx))
        | inr b =>
            change Sum.inr ((1 : G₂) • b) = Sum.inr b
            simp)
      exact hp.1
    · intro g hg
      have hp : ((1 : G₁), g) ∈ Gamma₁.prod Gamma₂ := h (by
        intro x hx
        cases x with
        | inl a =>
            change Sum.inl ((1 : G₁) • a) = Sum.inl a
            simp
        | inr b =>
            change Sum.inr (g • b) = Sum.inr b
            exact congrArg Sum.inr (hg b (Finset.mem_toRight.mpr hx)))
      exact hp.2
  · rintro ⟨h₁, h₂⟩ g hg
    constructor
    · apply h₁
      intro x hx
      have h := hg (Sum.inl x) (Finset.mem_toLeft.mp hx)
      change Sum.inl (g.1 • x) = Sum.inl x at h
      exact Sum.inl.inj h
    · apply h₂
      intro x hx
      have h := hg (Sum.inr x) (Finset.mem_toRight.mp hx)
      change Sum.inr (g.2 • x) = Sum.inr x at h
      exact Sum.inr.inj h

theorem pointStabilizer_independent (B : Finset (X₁ ⊕ X₂)) :
    letI := independentAction (G₁ := G₁) (G₂ := G₂) (X₁ := X₁) (X₂ := X₂)
    (pointStabilizer B : Subgroup (G₁ × G₂)) =
      (pointStabilizer B.toLeft).prod (pointStabilizer B.toRight) := by
  letI := independentAction (G₁ := G₁) (G₂ := G₂) (X₁ := X₁) (X₂ := X₂)
  ext g
  constructor
  · intro hg
    constructor
    · intro x hx
      have h := hg (Sum.inl x) (Finset.mem_toLeft.mp hx)
      change Sum.inl (g.1 • x) = Sum.inl x at h
      exact Sum.inl.inj h
    · intro x hx
      have h := hg (Sum.inr x) (Finset.mem_toRight.mp hx)
      change Sum.inr (g.2 • x) = Sum.inr x at h
      exact Sum.inr.inj h
  · intro hg x hx
    cases x with
    | inl a =>
        change Sum.inl (g.1 • a) = Sum.inl a
        exact congrArg Sum.inl (hg.1 a (Finset.mem_toLeft.mpr hx))
    | inr b =>
        change Sum.inr (g.2 • b) = Sum.inr b
        exact congrArg Sum.inr (hg.2 b (Finset.mem_toRight.mpr hx))

/-- Minimum observation numbers add for independent systems, including the
infinite cases. -/
theorem minObservations_independent (Gamma₁ : Subgroup G₁)
    (Gamma₂ : Subgroup G₂) :
    letI := independentAction (G₁ := G₁) (G₂ := G₂) (X₁ := X₁) (X₂ := X₂)
    minObservations (X := X₁ ⊕ X₂) (Gamma₁.prod Gamma₂) =
      minObservations (X := X₁) Gamma₁ + minObservations (X := X₂) Gamma₂ := by
  letI := independentAction (G₁ := G₁) (G₂ := G₂) (X₁ := X₁) (X₂ := X₂)
  apply le_antisymm
  · by_cases ht₁ : minObservations (X := X₁) Gamma₁ = ⊤
    · simp [ht₁]
    by_cases ht₂ : minObservations (X := X₂) Gamma₂ = ⊤
    · simp [ht₂]
    obtain ⟨B₁, hB₁, hc₁⟩ := minObservations_attained (X := X₁) Gamma₁ ht₁
    obtain ⟨B₂, hB₂, hc₂⟩ := minObservations_attained (X := X₂) Gamma₂ ht₂
    have hB : Sufficient (Gamma₁.prod Gamma₂) (B₁.disjSum B₂) :=
      (sufficient_independent_iff Gamma₁ Gamma₂ _).mpr (by simpa using And.intro hB₁ hB₂)
    have hle := minObservations_le (Gamma₁.prod Gamma₂) (B₁.disjSum B₂) hB
    have hcard : ((B₁.disjSum B₂).card : ℕ∞) =
        (B₁.card : ℕ∞) + (B₂.card : ℕ∞) := by
      simp [Finset.card_disjSum, Nat.cast_add]
    rw [hcard, hc₁, hc₂] at hle
    exact hle
  · by_cases htp : minObservations (X := X₁ ⊕ X₂) (Gamma₁.prod Gamma₂) = ⊤
    · simp [htp]
    obtain ⟨B, hB, hc⟩ :=
      minObservations_attained (X := X₁ ⊕ X₂) (Gamma₁.prod Gamma₂) htp
    obtain ⟨hB₁, hB₂⟩ := (sufficient_independent_iff Gamma₁ Gamma₂ B).mp hB
    have h₁ := minObservations_le Gamma₁ B.toLeft hB₁
    have h₂ := minObservations_le Gamma₂ B.toRight hB₂
    have hsum := add_le_add h₁ h₂
    have hcard : ((B.toLeft.card : ℕ∞) + (B.toRight.card : ℕ∞)) =
        (B.card : ℕ∞) := by
      rw [← Nat.cast_add, Finset.card_toLeft_add_card_toRight]
    rw [hcard, hc] at hsum
    exact hsum

/-- Minimum sets for the factors combine to an actual minimum set for the
independent product whenever both minima are finite. -/
theorem independent_minimum_disjSum (Gamma₁ : Subgroup G₁)
    (Gamma₂ : Subgroup G₂) (B₁ : Finset X₁) (B₂ : Finset X₂)
    (h₁ : Sufficient Gamma₁ B₁ ∧
      (B₁.card : ℕ∞) = minObservations (X := X₁) Gamma₁)
    (h₂ : Sufficient Gamma₂ B₂ ∧
      (B₂.card : ℕ∞) = minObservations (X := X₂) Gamma₂) :
    letI := independentAction (G₁ := G₁) (G₂ := G₂) (X₁ := X₁) (X₂ := X₂)
    Sufficient (Gamma₁.prod Gamma₂) (B₁.disjSum B₂) ∧
      ((B₁.disjSum B₂).card : ℕ∞) =
        minObservations (X := X₁ ⊕ X₂) (Gamma₁.prod Gamma₂) := by
  letI := independentAction (G₁ := G₁) (G₂ := G₂) (X₁ := X₁) (X₂ := X₂)
  constructor
  · exact (sufficient_independent_iff Gamma₁ Gamma₂ _).mpr (by simpa using And.intro h₁.1 h₂.1)
  · rw [minObservations_independent Gamma₁ Gamma₂,
      Finset.card_disjSum, Nat.cast_add, h₁.2, h₂.2]

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
