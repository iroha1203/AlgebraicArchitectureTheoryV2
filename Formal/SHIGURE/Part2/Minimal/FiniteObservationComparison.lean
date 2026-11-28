import Formal.SHIGURE.Part2.Minimal.FiniteWords

/-! The bounded observation map and the canonical dual-of-product comparison. -/

namespace SHIGURE.Minimal

open scoped DirectSum

section FiniteProduct

variable {K ι : Type*} [Field K] [Fintype ι]
variable (F : ι → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module K (F i)]

/-- For a finite index set, the direct sum of the duals is the dual of the product.
The equivalence is the standard composition of the finite direct-sum/product
comparison and `LinearMap.lsum`. -/
noncomputable def finiteDualProductEquiv :
    (⨁ i, Module.Dual K (F i)) ≃ₗ[K] Module.Dual K (∀ i, F i) := by
  classical
  exact (DirectSum.linearEquivFunOnFintype K ι (fun i => Module.Dual K (F i))).trans
    (LinearMap.lsum K F K)

/-- The canonical equivalence takes a summand functional to its composite
with the corresponding product projection. -/
theorem finiteDualProductEquiv_lof [DecidableEq ι] (i : ι) (ℓ : Module.Dual K (F i)) :
    finiteDualProductEquiv F (DirectSum.lof K ι (fun j => Module.Dual K (F j)) i ℓ) =
      ℓ.comp (LinearMap.proj i) := by
  classical
  apply LinearMap.ext
  intro x
  change (LinearMap.lsum K F K)
      ((DirectSum.linearEquivFunOnFintype K ι (fun j => Module.Dual K (F j)))
        (DirectSum.lof K ι (fun j => Module.Dual K (F j)) i ℓ)) x = ℓ (x i)
  rw [DirectSum.linearEquivFunOnFintype_lof, LinearMap.lsum_apply]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- The dual of a map into a finite product, transported along the canonical
equivalence, is induced by the duals of its component maps. -/
theorem finiteDualProductEquiv_dualMap_pi [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module K V] (f : ∀ i, V →ₗ[K] F i) :
    (LinearMap.pi f).dualMap.comp (finiteDualProductEquiv F).toLinearMap =
      DirectSum.toModule K ι (Module.Dual K V) (fun i => (f i).dualMap) := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro ℓ
  change (LinearMap.pi f).dualMap
      (finiteDualProductEquiv F (DirectSum.lof K ι (fun j => Module.Dual K (F j)) i ℓ)) =
    DirectSum.toModule K ι (Module.Dual K V) (fun i => (f i).dualMap)
      (DirectSum.lof K ι (fun j => Module.Dual K (F j)) i ℓ)
  rw [finiteDualProductEquiv_lof, DirectSum.toModule_lof]
  apply LinearMap.ext
  intro x
  rfl

end FiniteProduct

section Observation

variable {K S : Type*} [Field K]
variable {Op : S → S → Type*} {E I O : S → Type*}
variable [∀ s, AddCommGroup (E s)] [∀ s, Module K (E s)]
variable [∀ s, AddCommGroup (I s)] [∀ s, Module K (I s)]
variable [∀ s, AddCommGroup (O s)] [∀ s, Module K (O s)]

/-- The actual bounded observation map, with one product component for each
word of length at most `n`. -/
noncomputable def boundedObservationMap (A : Word.LinearSystem (K := K) Op E I)
    (observe : ∀ s, E s →ₗ[K] O s) (s : S) (n : ℕ) :
    E s →ₗ[K] (∀ w : ShortOutputWord Op s n, O w.1.1) :=
  LinearMap.pi (fun w => (observe w.1.1).comp (w.1.2.evaluate A))

/-- The actual dual of the finite-product observation map agrees, through
the canonical dual-of-product equivalence, with the word-summand map. -/
theorem boundedObservationMap_dualMap_comp_equiv
    (A : Word.LinearSystem (K := K) Op E I) (observe : ∀ s, E s →ₗ[K] O s)
    (s : S) (n : ℕ) [Fintype (ShortOutputWord Op s n)] :
    (boundedObservationMap A observe s n).dualMap.comp
        (finiteDualProductEquiv (fun w : ShortOutputWord Op s n => O w.1.1)).toLinearMap =
      boundedWordDualObservationMap A observe s n := by
  classical
  simpa only [boundedObservationMap, boundedWordDualObservationMap,
    LinearMap.dualMap_comp_dualMap] using
    (finiteDualProductEquiv_dualMap_pi
      (fun w : ShortOutputWord Op s n => O w.1.1)
      (fun w => (observe w.1.1).comp (w.1.2.evaluate A)))

/-- The actual bounded observation dual is surjective exactly when the
word-summand dual observation map is surjective. -/
theorem boundedObservationMap_dualMap_surjective_iff
    (A : Word.LinearSystem (K := K) Op E I) (observe : ∀ s, E s →ₗ[K] O s)
    (s : S) (n : ℕ) [Fintype (ShortOutputWord Op s n)] :
    Function.Surjective (boundedObservationMap A observe s n).dualMap ↔
      Function.Surjective (boundedWordDualObservationMap A observe s n) := by
  classical
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

/-- The N−1 observation condition using the actual dual of the finite-product
observation map, compared with the all-words dual observation map. -/
theorem surjective_allWordDualObservationMap_iff_actual_bounded_dual
    [Fintype S] [∀ s, FiniteDimensional K (E s)]
    [∀ s t, Finite (Op s t)]
    (A : Word.LinearSystem (K := K) Op E I) (observe : ∀ s, E s →ₗ[K] O s)
    (hpositive : 0 < ∑ s, Module.finrank K (E s)) :
    (∀ s, Function.Surjective (allWordDualObservationMap A observe s)) ↔
      (∀ s, Function.Surjective
        (boundedObservationMap A observe s ((∑ t, Module.finrank K (E t)) - 1)).dualMap) := by
  classical
  letI : ∀ s, Finite (ShortOutputWord Op s ((∑ t, Module.finrank K (E t)) - 1)) :=
    fun s => finite_shortOutputWord s _
  letI : ∀ s, Fintype (ShortOutputWord Op s ((∑ t, Module.finrank K (E t)) - 1)) :=
    fun s => Fintype.ofFinite _
  rw [surjective_allWordDualObservationMap_iff_bounded A observe hpositive]
  constructor <;> intro h s
  · exact (boundedObservationMap_dualMap_surjective_iff A observe s _).mpr (h s)
  · exact (boundedObservationMap_dualMap_surjective_iff A observe s _).mp (h s)

end Observation

end SHIGURE.Minimal
