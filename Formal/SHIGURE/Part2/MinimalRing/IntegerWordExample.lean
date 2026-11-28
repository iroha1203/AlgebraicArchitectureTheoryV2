import Formal.SHIGURE.Part2.MinimalRing.IntegerExample
import Formal.SHIGURE.Part2.MinimalRing.ObservationBaseChange

/-!
# The integer counterexample as an actual word system

The only word is the empty word.  The finite observation product therefore
has one factor and its observation map identifies with multiplication by two.
-/

namespace SHIGURE.MinimalRing.IntegerExample

open SHIGURE.Minimal
open scoped DirectSum TensorProduct

/-- The only output word of length zero in the example. -/
def emptyOutputWord : ShortOutputWord NoOperation () 0 :=
  ⟨⟨(), Word.nil ()⟩, by simp [Word.length]⟩

instance : Unique (ShortOutputWord NoOperation () 0) where
  default := emptyOutputWord
  uniq := by
    rintro ⟨⟨t, w⟩, hw⟩
    cases t
    cases w with
    | nil => rfl
    | snoc w e => exact nomatch e

/-- The single-factor finite observation product is canonically `ℤ`. -/
def observationProductEquiv : (∀ _ : ShortOutputWord NoOperation () 0, ℤ) ≃ₗ[ℤ] ℤ :=
  LinearEquiv.piUnique ℤ (fun _ => ℤ)

/-- The actual all-word reachability map is surjective via the empty word. -/
theorem allWordReach_surjective : Function.Surjective (allWordReachMap system ()) := by
  classical
  intro x
  let w : InputWord NoOperation () := ⟨(), Word.nil ()⟩
  refine ⟨DirectSum.lof ℤ _ (fun _ : InputWord NoOperation () => ℤ) w x, ?_⟩
  change DirectSum.toModule ℤ _ ℤ
    (fun w => (evaluate system w.2).comp (system.input w.1))
    (DirectSum.lof ℤ _ (fun _ : InputWord NoOperation () => ℤ) w x) = x
  rw [DirectSum.toModule_lof]
  rfl

/-- Under the one-factor product equivalence, the actual length-zero
observation map is multiplication by two. -/
theorem boundedObservation_comp_equiv :
    observationProductEquiv.toLinearMap.comp (boundedObservationMap system observation () 0) =
      twice := by
  apply LinearMap.ext
  intro x
  rfl

theorem boundedObservation_injective :
    Function.Injective (boundedObservationMap system observation () 0) := by
  intro x y h
  apply twice_injective
  have hx := LinearMap.congr_fun boundedObservation_comp_equiv x
  have hy := LinearMap.congr_fun boundedObservation_comp_equiv y
  change observationProductEquiv (boundedObservationMap system observation () 0 x) = twice x at hx
  change observationProductEquiv (boundedObservationMap system observation () 0 y) = twice y at hy
  rw [← hx, ← hy, h]

theorem boundedObservation_dualMap_not_surjective :
    ¬ Function.Surjective (boundedObservationMap system observation () 0).dualMap := by
  intro h
  apply twice_dualMap_not_surjective
  intro φ
  obtain ⟨ψ, hψ⟩ := h φ
  refine ⟨observationProductEquiv.symm.toLinearMap.dualMap ψ, ?_⟩
  apply LinearMap.ext
  intro x
  change ψ (observationProductEquiv.symm (twice x)) = φ x
  have hx := LinearMap.congr_fun boundedObservation_comp_equiv x
  change observationProductEquiv (boundedObservationMap system observation () 0 x) = twice x at hx
  rw [← hx, observationProductEquiv.symm_apply_apply]
  exact LinearMap.congr_fun hψ x

/-- The actual length-zero observation of the mod-two system is zero. -/
theorem boundedObservation_baseChange_zmod_two :
    boundedObservationMap (E := fun _ => ZMod 2 ⊗[ℤ] ℤ)
      (I := fun _ => ZMod 2 ⊗[ℤ] ℤ) (O := fun _ => ZMod 2 ⊗[ℤ] ℤ)
      (baseChangeSystem (ZMod 2) system) (fun u => (observation u).baseChange (ZMod 2)) () 0 = 0 := by
  letI : ∀ s t : Unit, Finite (NoOperation s t) := fun _ _ => by
    change Finite Empty
    infer_instance
  have ho : boundedObservationMap system observation () 0 =
      observationProductEquiv.symm.toLinearMap.comp twice := by
    apply LinearMap.ext
    intro x
    apply observationProductEquiv.injective
    change observationProductEquiv (boundedObservationMap system observation () 0 x) =
      observationProductEquiv (observationProductEquiv.symm (twice x))
    rw [observationProductEquiv.apply_symm_apply]
    exact LinearMap.congr_fun boundedObservation_comp_equiv x
  rw [boundedObservationMap_baseChange, ho, LinearMap.baseChange_comp, twice_baseChange_zmod_two]
  simp

end SHIGURE.MinimalRing.IntegerExample
