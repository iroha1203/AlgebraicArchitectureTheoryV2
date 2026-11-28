import Formal.SHIGURE.Part2.MinimalRing.Systems

/-!
# The dual of the actual finite-word observation map

A finite product of output modules has dual canonically isomorphic to the
direct sum of their duals.  The comparison below is over the original
commutative ring and uses the actual observation map and its `dualMap`.
-/

namespace SHIGURE.MinimalRing

open SHIGURE.Minimal
open scoped DirectSum

section FiniteProduct

variable {R ι : Type*} [CommRing R] [Fintype ι]
variable (F : ι → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]

/-- The canonical equivalence between a sum of duals and the dual of a finite product. -/
noncomputable def finiteDualProductEquiv :
    (⨁ i, Module.Dual R (F i)) ≃ₗ[R] Module.Dual R (∀ i, F i) := by
  classical
  exact (DirectSum.linearEquivFunOnFintype R ι (fun i => Module.Dual R (F i))).trans
    (LinearMap.lsum R F R)

/-- A component functional is transported to composition with the corresponding projection. -/
theorem finiteDualProductEquiv_lof [DecidableEq ι] (i : ι) (ℓ : Module.Dual R (F i)) :
    finiteDualProductEquiv F (DirectSum.lof R ι (fun j => Module.Dual R (F j)) i ℓ) =
      ℓ.comp (LinearMap.proj i) := by
  classical
  apply LinearMap.ext
  intro x
  change (LinearMap.lsum R F R)
      ((DirectSum.linearEquivFunOnFintype R ι (fun j => Module.Dual R (F j)))
        (DirectSum.lof R ι (fun j => Module.Dual R (F j)) i ℓ)) x = ℓ (x i)
  rw [DirectSum.linearEquivFunOnFintype_lof, LinearMap.lsum_apply]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- The dual of a map to a finite product becomes the direct-sum map of component duals. -/
theorem finiteDualProductEquiv_dualMap_pi [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module R V] (f : ∀ i, V →ₗ[R] F i) :
    (LinearMap.pi f).dualMap.comp (finiteDualProductEquiv F).toLinearMap =
      DirectSum.toModule R ι (Module.Dual R V) (fun i => (f i).dualMap) := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro ℓ
  change (LinearMap.pi f).dualMap
      (finiteDualProductEquiv F (DirectSum.lof R ι (fun j => Module.Dual R (F j)) i ℓ)) =
    DirectSum.toModule R ι (Module.Dual R V) (fun i => (f i).dualMap)
      (DirectSum.lof R ι (fun j => Module.Dual R (F j)) i ℓ)
  rw [finiteDualProductEquiv_lof, DirectSum.toModule_lof]
  apply LinearMap.ext
  intro x
  rfl

end FiniteProduct

section Observation

variable {R S : Type*} [CommRing R]
variable {Op : S → S → Type*} {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module R (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module R (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module R (O s)]

/-- The direct sum of component dual observations indexed by short words. -/
noncomputable def boundedWordDualObservationMap (A : LinearSystem (R := R) Op E I)
    (observe : ∀ s, E s →ₗ[R] O s) (s : S) (n : ℕ) :
    (⨁ w : ShortOutputWord Op s n, Module.Dual R (O w.1.1)) →ₗ[R]
      Module.Dual R (E s) := by
  classical
  exact DirectSum.toModule R _ _
    (fun w => (evaluate A w.1.2).dualMap.comp (observe w.1.1).dualMap)

/-- The component sum is exactly the dual of the actual finite observation
map after applying the canonical finite-product equivalence. -/
theorem boundedObservationMap_dualMap_comp_equiv
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s)
    (s : S) (n : ℕ) [Fintype (ShortOutputWord Op s n)] :
    (boundedObservationMap A observe s n).dualMap.comp
        (finiteDualProductEquiv (fun w : ShortOutputWord Op s n => O w.1.1)).toLinearMap =
      boundedWordDualObservationMap A observe s n := by
  classical
  simpa only [boundedObservationMap, boundedWordDualObservationMap,
    LinearMap.dualMap_comp_dualMap] using
    (finiteDualProductEquiv_dualMap_pi
      (fun w : ShortOutputWord Op s n => O w.1.1)
      (fun w => (observe w.1.1).comp (evaluate A w.1.2)))

/-- Finite sort and operation types give the actual bounded observation
dual and the component sum the same surjectivity condition. -/
theorem boundedObservationMap_dualMap_surjective_iff
    [Finite S] [∀ s t, Finite (Op s t)]
    (A : LinearSystem (R := R) Op E I) (observe : ∀ s, E s →ₗ[R] O s)
    (s : S) (n : ℕ) :
    Function.Surjective (boundedObservationMap A observe s n).dualMap ↔
      Function.Surjective (boundedWordDualObservationMap A observe s n) := by
  classical
  letI : Finite (ShortOutputWord Op s n) := finite_shortOutputWord s n
  letI : Fintype (ShortOutputWord Op s n) := Fintype.ofFinite _
  rw [← boundedObservationMap_dualMap_comp_equiv]
  constructor
  · intro h y
    obtain ⟨φ, hφ⟩ := h y
    obtain ⟨v, rfl⟩ := (finiteDualProductEquiv
      (fun w : ShortOutputWord Op s n => O w.1.1)).surjective φ
    exact ⟨v, hφ⟩
  · intro h y
    obtain ⟨v, hv⟩ := h y
    exact ⟨finiteDualProductEquiv (fun w : ShortOutputWord Op s n => O w.1.1) v, hv⟩

end Observation
end SHIGURE.MinimalRing
