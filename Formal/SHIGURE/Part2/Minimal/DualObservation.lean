import Formal.SHIGURE.Part2.Minimal.WordLength
import Formal.SHIGURE.Part2.Minimal.WordReverse
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Dual observations are reachability in the system with all arrows reversed. -/

namespace SHIGURE.Minimal

variable {K S : Type*} [Field K]
variable {Op : S → S → Type*} {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module K (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module K (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module K (O s)]

/-- Reverse each operation and use the dual observation maps as inputs. -/
def dualSystem (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) :
    Word.LinearSystem (K := K) (fun s t => Op t s)
      (fun s => Module.Dual K (E s)) (fun s => Module.Dual K (O s)) where
  input s := (observe s).dualMap
  operation e := (A.operation e).dualMap

/-- Evaluating a reversed word in the dual system is the dual of its original evaluation. -/
theorem evaluate_reverse (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) {s t : S} (w : Word Op s t) :
    w.reverse.evaluate (E := fun u => Module.Dual K (E u))
        (I := fun u => Module.Dual K (O u))
        (dualSystem (E := E) (I := I) (O := O) A observe) =
      (w.evaluate A).dualMap := by
  induction w with
  | nil => rfl
  | snoc w e ih =>
    rw [Word.reverse_snoc, Word.evaluate_append, ih]
    change (w.evaluate A).dualMap.comp ((A.operation e).dualMap.comp LinearMap.id) =
      ((A.operation e).comp (w.evaluate A)).dualMap
    rw [LinearMap.comp_id, LinearMap.dualMap_comp_dualMap]

/-- Word reversal identifies the generators of bounded dual observation and dual reachability. -/
theorem boundedObservationGenerators_eq_dualGenerators
    (A : Word.LinearSystem (K := K) Op E I) (observe : ∀ s, E s →ₗ[K] O s)
    (s : S) (n : ℕ) :
    boundedObservationGenerators O A observe s n =
      boundedGenerators (E := fun u => Module.Dual K (E u))
        (I := fun u => Module.Dual K (O u))
        (dualSystem (E := E) (I := I) (O := O) A observe) s n := by
  ext φ
  constructor
  · rintro ⟨t, w, ℓ, hw, rfl⟩
    refine ⟨t, w.reverse, ℓ, by simpa using hw, ?_⟩
    rw [evaluate_reverse]
    ext x
    rfl
  · rintro ⟨t, w, ℓ, hw, rfl⟩
    refine ⟨t, w.reverse, ℓ, ?_, ?_⟩
    · exact (Word.length_reverse w).le.trans hw
    · have he := evaluate_reverse A observe w.reverse
      simp only [Word.reverse_reverse] at he
      rw [he]
      ext x
      rfl

/-- Dual observation and reversed-system reachability have the same bounded image. -/
theorem boundedObservation_eq_dualReach (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) (n : ℕ) :
    boundedObservation O A observe s n =
      boundedReach (E := fun u => Module.Dual K (E u))
        (I := fun u => Module.Dual K (O u))
        (dualSystem (E := E) (I := I) (O := O) A observe) s n := by
  unfold boundedObservation boundedReach
  rw [boundedObservationGenerators_eq_dualGenerators]

/-- The same comparison for all finite words. -/
theorem allObservation_eq_dualReach (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) :
    allObservation O A observe s =
      allReach (E := fun u => Module.Dual K (E u))
        (I := fun u => Module.Dual K (O u))
        (dualSystem (E := E) (I := I) (O := O) A observe) s := by
  rw [← iSup_boundedObservation, ← iSup_boundedReach]
  exact iSup_congr fun n => boundedObservation_eq_dualReach A observe s n

variable [Fintype S] [∀ s, FiniteDimensional K (E s)]

/-- All-word dual observation is surjective exactly when the N−1 observation is. -/
theorem allObservation_iff_boundedObservation
    (A : Word.LinearSystem (K := K) Op E I) (observe : ∀ s, E s →ₗ[K] O s)
    (hpositive : 0 < Module.finrank K (∀ s, E s)) :
    (∀ s, allObservation O A observe s = ⊤) ↔
      (∀ s, boundedObservation O A observe s (Module.finrank K (∀ s, E s) - 1) = ⊤) := by
  have hdim : Module.finrank K (∀ s, Module.Dual K (E s)) =
      Module.finrank K (∀ s, E s) := by
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp
  have hp : 0 < Module.finrank K (∀ s, Module.Dual K (E s)) := by simpa [hdim] using hpositive
  have h := allReach_iff_boundedReach
    (E := fun u => Module.Dual K (E u)) (I := fun u => Module.Dual K (O u))
    (dualSystem (E := E) (I := I) (O := O) A observe) hp
  simpa only [← allObservation_eq_dualReach A observe,
    ← boundedObservation_eq_dualReach A observe, hdim] using h

/-- The dual observation statement with total dimension expressed as a sum. -/
theorem allObservation_iff_boundedObservation_sum
    (A : Word.LinearSystem (K := K) Op E I) (observe : ∀ s, E s →ₗ[K] O s)
    (hpositive : 0 < ∑ s, Module.finrank K (E s)) :
    (∀ s, allObservation O A observe s = ⊤) ↔
      (∀ s, boundedObservation O A observe s ((∑ t, Module.finrank K (E t)) - 1) = ⊤) := by
  have hp : 0 < Module.finrank K (∀ s, E s) := by
    simpa only [Module.finrank_pi_fintype] using hpositive
  simpa only [Module.finrank_pi_fintype] using allObservation_iff_boundedObservation A observe hp

end SHIGURE.Minimal
