import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Span.Defs

/-! The image of a map out of a direct sum is spanned by its component images. -/

namespace SHIGURE.Minimal

open scoped DirectSum

/-- The range of the map induced by a family of linear maps is the span of
all values of the component maps. -/
theorem range_toModule_eq_span {K ι N : Type*} [Semiring K] [DecidableEq ι]
    [AddCommMonoid N] [Module K N]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module K (M i)]
    (f : ∀ i, M i →ₗ[K] N) (G : Set N)
    (hG : ∀ x, x ∈ G ↔ ∃ (i : ι) (a : M i), x = f i a) :
    LinearMap.range (DirectSum.toModule K ι N f) =
      Submodule.span K G := by
  classical
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    induction v using DirectSum.induction_on with
    | zero => simp
    | of i a =>
      change DirectSum.toModule K ι N f (DirectSum.lof K ι M i a) ∈ _
      rw [DirectSum.toModule_lof]
      exact Submodule.subset_span ((hG _).mpr ⟨i, a, rfl⟩)
    | add v w hv hw =>
      rw [map_add]
      exact Submodule.add_mem _ hv hw
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, a, rfl⟩ := (hG x).mp hx
    exact ⟨DirectSum.lof K ι M i a, DirectSum.toModule_lof K i a⟩

end SHIGURE.Minimal
