import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-! A dimension estimate for a stationary filtration of a finite-dimensional space. -/

namespace SHIGURE.Minimal

/-- A nonzero increasing filtration that can stop only at the whole space reaches
that space by stage `finrank - 1`. -/
theorem filtration_eq_top_at_finrank_sub_one
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (V : ℕ → Submodule K M) (hmono : Monotone V) (hzero : V 0 ≠ ⊥)
    (hstationary : ∀ n, V n = V (n + 1) → V n = ⊤)
    (hpositive : 0 < Module.finrank K M) :
    V (Module.finrank K M - 1) = ⊤ := by
  let d := Module.finrank K M - 1
  by_contra hnot
  have hne : ∀ n, n < d → V n ≠ V (n + 1) := by
    intro n hn heq
    have htop : V n = ⊤ := hstationary n heq
    have hle : V n ≤ V d := hmono (Nat.le_of_lt hn)
    have : V d = ⊤ := top_unique (htop ▸ hle)
    exact hnot this
  have hgrowth : ∀ n, n ≤ d → n + 1 ≤ Module.finrank K (V n) := by
    intro n hn
    induction n with
    | zero =>
      simpa using (Submodule.one_le_finrank_iff.mpr hzero)
    | succ n ih =>
      have hn' : n ≤ d := by omega
      have hlt : n < d := by omega
      have hs : V n < V (n + 1) :=
        lt_of_le_of_ne (hmono (Nat.le_succ n)) (hne n hlt)
      have hr := Submodule.finrank_lt_finrank_of_lt hs
      have hp := ih hn'
      omega
  have hbound := hgrowth d le_rfl
  have hle := Submodule.finrank_le (V d)
  have hrank : Module.finrank K (V d) = Module.finrank K M := by
    have hd : d + 1 = Module.finrank K M := by dsimp [d]; omega
    exact Nat.le_antisymm hle (hd ▸ hbound)
  exact hnot (Submodule.eq_top_of_finrank_eq hrank)

end SHIGURE.Minimal
