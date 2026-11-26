import Formal.SHIGURE.Part2.Schemes.AffineFiniteLocallyFree

/-! # Finite locally free modules on schemes

## Implementation notes

The finite principal cover in B.5 records a finite free basis chart around
each point of an affine open. Using that coefficient predicate on an affine
open cover expresses the local free-basis condition of B.3 with the actual
module sheaf. The affine-open criterion extends these presentations to all
affine opens, and the affine examples identify the condition with the
coefficient predicate on an associated sheaf.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {X Y : Scheme.{u}}

/-- On an affine open in B.3, the actual restriction is the associated sheaf
of a coefficient module satisfying the finite principal-cover condition of B.5. -/
def HasFiniteLocallyFreeOn (M : X.Modules) {U : X.Opens} (affine : IsAffineOpen U) : Prop :=
  ∃ N : ModuleCat.{u} Γ(X, U), FiniteLocallyFree (Γ(X, U)) N ∧
    Nonempty ((tilde.functor Γ(X, U)).obj N ≅ M.restrict affine.fromSpec)

/-- Finite local freeness in B.3, expressed through the B.5 coefficient
presentations on an affine open cover of the scheme. -/
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
