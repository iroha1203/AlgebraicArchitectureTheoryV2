import Formal.SHIGURE.Part2.Descent.FiniteLocallyFree

/-! # Local detection of finite local freeness on principal covers -/

namespace SHIGURE.CoefficientDescent

open TensorProduct

universe u

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- Finite presentation is detected by a finite principal cover of
finitely presented localizations. -/
theorem finitePresentation_of_localizationSpan (s : Finset R)
    (spans : Ideal.span (s : Set R) = ⊤)
    (locally : ∀ f : s,
      Module.FinitePresentation (Localization.Away f.val) (LocalizedModule (Submonoid.powers f.val) M)) :
    Module.FinitePresentation R M := by
  have finite : Module.Finite R M :=
    Module.Finite.of_localizationSpan_finite s spans fun f => by
      letI := locally f
      infer_instance
  obtain ⟨n, map, onto⟩ := Module.Finite.exists_fin' R M
  refine Module.finitePresentation_of_free_of_surjective map onto (Module.Finite.iff_fg.mp ?_)
  refine Module.Finite.of_localizationSpan_finite s spans fun f => ?_
  let Rf := Localization.Away f.val
  let S := Submonoid.powers f.val
  letI : Module.FinitePresentation Rf (LocalizedModule S M) := locally f
  letI : Module.FinitePresentation Rf (Rf ⊗[R] M) :=
    Module.FinitePresentation.of_equiv (LocalizedModule.equivTensorProduct S M)
  letI : Module.Flat R Rf := IsLocalization.flat Rf S
  letI : Module.Finite Rf (Rf ⊗[R] LinearMap.ker map) :=
    finite_baseChange_ker_of_surjective Rf map onto
  exact Module.Finite.equiv (LocalizedModule.equivTensorProduct S (LinearMap.ker map)).symm

/-- Finite local freeness can be checked on any finite principal cover. -/
theorem finiteLocallyFree_of_localizationSpan (s : Finset R)
    (spans : Ideal.span (s : Set R) = ⊤)
    (locally : ∀ f : s,
      FiniteLocallyFree (Localization.Away f.val) (LocalizedModule (Submonoid.powers f.val) M)) :
    FiniteLocallyFree R M := by
  letI : Module.FinitePresentation R M :=
    finitePresentation_of_localizationSpan s spans fun f => (locally f).finitePresentation
  letI : Module.Flat R M := by
    apply Module.flat_of_localized_span R M (s : Set R) spans
    intro f
    let Rf := Localization.Away f.val
    let S := Submonoid.powers f.val
    letI : Module.Flat Rf (LocalizedModule S M) := (locally f).flat
    letI : Module.Flat R Rf := IsLocalization.flat Rf S
    exact Module.Flat.trans R Rf _
  exact finiteLocallyFree_of_finitePresentation_flat

end SHIGURE.CoefficientDescent
