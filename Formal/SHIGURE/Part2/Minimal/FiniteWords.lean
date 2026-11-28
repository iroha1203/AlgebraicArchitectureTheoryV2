import Formal.SHIGURE.Part2.Minimal.ReachabilityMaps
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-! Finiteness of typed words of bounded length. -/

namespace SHIGURE.Minimal

variable {S : Type*} {Op : S → S → Type*}

/-- The empty word transported along an equality of its endpoints. -/
def boundedNil {s t : S} (n : ℕ) (h : s = t) :
    {w : Word Op s t // w.length ≤ n} := by
  cases h
  exact ⟨Word.nil s, Nat.zero_le n⟩

/-- Append one operation to a word whose length is at most `n`. -/
def boundedStep {s t : S} (n : ℕ)
    (p : Σ u : S, {w : Word Op s u // w.length ≤ n} × Op u t) :
    {w : Word Op s t // w.length ≤ n + 1} :=
  ⟨Word.snoc p.2.1.1 p.2.2, Nat.add_le_add_right p.2.1.2 1⟩

/-- Finite sorts and operation names give finitely many words of bounded
length between any two specified sorts. -/
theorem finite_bounded_words [Finite S] [∀ s t, Finite (Op s t)] :
    ∀ n : ℕ, ∀ s t : S, Finite {w : Word Op s t // w.length ≤ n} := by
  intro n
  induction n with
  | zero =>
    intro s t
    refine Finite.of_surjective (boundedNil (Op := Op) 0) ?_
    rintro ⟨w, hw⟩
    cases w with
    | nil => exact ⟨rfl, rfl⟩
    | snoc w e => simp [Word.length] at hw
  | succ n ih =>
    intro s t
    classical
    letI : Fintype S := Fintype.ofFinite S
    letI : ∀ u : S, Finite {w : Word Op s u // w.length ≤ n} := fun u => ih s u
    letI : ∀ u : S, Fintype {w : Word Op s u // w.length ≤ n} :=
      fun u => Fintype.ofFinite _
    letI : ∀ u : S, Fintype (Op u t) := fun u => Fintype.ofFinite _
    letI : Finite (PLift (s = t)) := Finite.of_subsingleton
    letI : Fintype (PLift (s = t)) := Fintype.ofFinite _
    let f : PLift (s = t) ⊕ (Σ u : S, {w : Word Op s u // w.length ≤ n} × Op u t) →
        {w : Word Op s t // w.length ≤ n + 1} :=
      Sum.elim (fun h => boundedNil (Op := Op) (n + 1) h.down) (boundedStep (Op := Op) n)
    refine Finite.of_surjective f ?_
    rintro ⟨w, hw⟩
    cases w with
    | nil => exact ⟨Sum.inl ⟨rfl⟩, rfl⟩
    | snoc w e =>
      have hw' : w.length ≤ n := by
        change w.length + 1 ≤ n + 1 at hw
        omega
      exact ⟨Sum.inr ⟨_, ⟨w, hw'⟩, e⟩, rfl⟩

/-- In particular, the family of all short words starting at a fixed sort is finite. -/
theorem finite_shortOutputWord [Finite S] [∀ s t, Finite (Op s t)] (s : S) (n : ℕ) :
    Finite (ShortOutputWord Op s n) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : ∀ t : S, Finite {w : Word Op s t // w.length ≤ n} :=
    fun t => finite_bounded_words n s t
  letI : ∀ t : S, Fintype {w : Word Op s t // w.length ≤ n} :=
    fun t => Fintype.ofFinite _
  let f : (Σ t : S, {w : Word Op s t // w.length ≤ n}) → ShortOutputWord Op s n :=
    fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  refine Finite.of_surjective f ?_
  rintro ⟨⟨t, w⟩, hw⟩
  exact ⟨⟨t, ⟨w, hw⟩⟩, rfl⟩

end SHIGURE.Minimal
