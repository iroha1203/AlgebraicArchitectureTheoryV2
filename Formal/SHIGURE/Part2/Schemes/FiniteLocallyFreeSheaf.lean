import Formal.SHIGURE.Part2.Schemes.AffineFiniteLocallyFree

/-! # Finite locally free modules on schemes -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {X Y : Scheme.{u}}

/-- An affine open has a presentation by a coefficient module with a finite
principal cover of free localizations. -/
def HasFiniteLocallyFreeOn (M : X.Modules) {U : X.Opens} (affine : IsAffineOpen U) : Prop :=
  ∃ N : ModuleCat.{u} Γ(X, U), FiniteLocallyFree (Γ(X, U)) N ∧
    Nonempty ((tilde.functor Γ(X, U)).obj N ≅ M.restrict affine.fromSpec)

/-- A module sheaf is finite locally free if such presentations exist on an
affine open cover. -/
def IsFiniteLocallyFreeModule (M : X.Modules) : Prop :=
  ∃ (ι : Type u) (U : ι → X.affineOpens), (⨆ i, (U i : X.Opens)) = ⊤ ∧
    ∀ i, HasFiniteLocallyFreeOn M (U i).property

/-- Finite local freeness implies quasi-coherence. -/
theorem IsFiniteLocallyFreeModule.quasiCoherent {M : X.Modules}
    (h : IsFiniteLocallyFreeModule M) : IsQuasiCoherentModule M := by
  obtain ⟨ι, U, covers, presentations⟩ := h
  apply (isQuasiCoherentModule_iff_affineCover M).mpr
  refine ⟨ι, U, covers, fun i => ?_⟩
  obtain ⟨N, _, e⟩ := presentations i
  exact ⟨N, e⟩

/-- On the inverse image of an affine open, a finite locally free
presentation pulls back along the actual map of section rings. -/
theorem HasFiniteLocallyFreeOn.pullback {f : Y ⟶ X} {M : X.Modules} {U : X.Opens} {V : Y.Opens}
    {hU : IsAffineOpen U} {hV : IsAffineOpen V} (inside : V ≤ f ⁻¹ᵁ U)
    (presentation : HasFiniteLocallyFreeOn M hU) :
    HasFiniteLocallyFreeOn ((Scheme.Modules.pullback f).obj M) hV := by
  let a := f.appLE U V inside
  obtain ⟨N, finite, ⟨e⟩⟩ := presentation
  exact ⟨(ModuleCat.extendScalars a.hom).obj N, finiteLocallyFree_extendScalars a N finite,
    ⟨pullbackTildePresentationIso (hV := hV) inside e⟩⟩

/-- Pullback along an arbitrary morphism preserves finite local freeness. -/
theorem IsFiniteLocallyFreeModule.pullback {f : Y ⟶ X} {M : X.Modules}
    (h : IsFiniteLocallyFreeModule M) :
    IsFiniteLocallyFreeModule ((Scheme.Modules.pullback f).obj M) := by
  obtain ⟨ι, U, covers, presentations⟩ := h
  let I := {V : Y.affineOpens // ∃ i : ι, V.1 ≤ f ⁻¹ᵁ (U i).1}
  refine ⟨I, Subtype.val, iSup_affineOpens_in_preimage_eq_top f (fun i => (U i : X.Opens)) covers, ?_⟩
  rintro ⟨V, i, inside⟩
  exact (presentations i).pullback inside

end

end SHIGURE.SchemeDescent
