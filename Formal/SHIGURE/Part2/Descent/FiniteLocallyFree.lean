import Formal.SHIGURE.Part2.Descent.Standard
import Mathlib.Algebra.Algebra.Prod
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Finite locally free modules in faithfully flat descent

In Lemma B.5, a finite principal cover records the affine local definition of a finite
locally free module. Finite generation, finite presentation, flatness
and constant rank descend through the comparison of Lemma B.4.

## Implementation notes

The explicit principal-cover definition retains the actual localization
data used in B.5. Finiteness and projectivity together characterize
finite local freeness. The theorem `finiteLocallyFree_iff_finite_projective`
relates the two descriptions, with finite basic opens available from
either one.
The local finite generation theorem and base change of the actual kernel
give finite presentation. The resulting comparison with mathlib's finite
projective modules recovers a finite principal cover in the other direction.
Constant rank is expressed by mathlib's stalk rank and uses its base-change
formula and the surjectivity of the faithfully flat map on prime spectra.
-/

open TensorProduct

namespace SHIGURE.CoefficientDescent

open PrimeSpectrum

universe u

variable {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- Finite local freeness on an affine is witnessed by a finite principal cover and finite free localizations. -/
def FiniteLocallyFree (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M] : Prop :=
  ∃ cover : Finset A, Ideal.span (cover : Set A) = ⊤ ∧
    ∀ f : cover, Module.Free (Localization.Away f.val) (LocalizedModule (Submonoid.powers f.val) M) ∧
      Module.Finite (Localization.Away f.val) (LocalizedModule (Submonoid.powers f.val) M)

/-- In B.5, a finite free surjection with finitely presented scalar extension has
a finite base-changed kernel, identified by the flat comparison. -/
theorem finite_baseChange_ker_of_surjective (B : Type u) [CommRing B] [Algebra A B] [Module.Flat A B]
    {n : ℕ} (f : (Fin n → A) →ₗ[A] M) (surj : Function.Surjective f)
    [Module.FinitePresentation B (B ⊗[A] M)] :
    Module.Finite B (B ⊗[A] LinearMap.ker f) := by
  let fB := AlgebraTensorModule.lTensor B B f
  have fSurj : Function.Surjective fB := LinearMap.lTensor_surjective B surj
  haveI : Module.Finite B (LinearMap.ker (AlgebraTensorModule.lTensor B B f)) :=
    Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker fB fSurj)
  exact Module.Finite.equiv (f.tensorKerEquiv B B).symm

/-- Finite presentation is detected by a finite principal cover of
finitely presented localizations. -/
theorem finitePresentation_of_localizationSpan (s : Finset A)
    (spans : Ideal.span (s : Set A) = ⊤)
    (locally : ∀ f : s,
      Module.FinitePresentation (Localization.Away f.val) (LocalizedModule (Submonoid.powers f.val) M)) :
    Module.FinitePresentation A M := by
  have finite : Module.Finite A M :=
    Module.Finite.of_localizationSpan_finite s spans fun f => by
      letI := locally f
      infer_instance
  obtain ⟨n, map, onto⟩ := Module.Finite.exists_fin' A M
  refine Module.finitePresentation_of_free_of_surjective map onto (Module.Finite.iff_fg.mp ?_)
  refine Module.Finite.of_localizationSpan_finite s spans fun f => ?_
  let Rf := Localization.Away f.val
  let S := Submonoid.powers f.val
  letI : Module.FinitePresentation Rf (LocalizedModule S M) := locally f
  letI : Module.FinitePresentation Rf (Rf ⊗[A] M) :=
    Module.FinitePresentation.of_equiv (LocalizedModule.equivTensorProduct S M)
  letI : Module.Flat A Rf := IsLocalization.flat Rf S
  letI : Module.Finite Rf (Rf ⊗[A] LinearMap.ker map) :=
    finite_baseChange_ker_of_surjective Rf map onto
  exact Module.Finite.equiv (LocalizedModule.equivTensorProduct S (LinearMap.ker map)).symm

/-- Finite local freeness implies finite presentation by localization of a finite free presentation. -/
theorem FiniteLocallyFree.finitePresentation (h : FiniteLocallyFree A M) :
    Module.FinitePresentation A M := by
  obtain ⟨cover, spans, locally⟩ := h
  apply finitePresentation_of_localizationSpan cover spans
  intro g
  letI := (locally g).1
  letI := (locally g).2
  exact Module.finitePresentation_of_projective _ _

/-- Finite local freeness gives flatness on the underlying affine. -/
theorem FiniteLocallyFree.flat (h : FiniteLocallyFree A M) : Module.Flat A M := by
  obtain ⟨cover, spans, locally⟩ := h
  apply Module.flat_of_localized_span A M (cover : Set A) spans
  intro g
  letI : Module.Free (Localization.Away g.val) (LocalizedModule (Submonoid.powers g.val) M) := (locally g).1
  letI : Module.Flat A (Localization.Away g.val) :=
    IsLocalization.flat (Localization.Away g.val) (Submonoid.powers g.val)
  exact Module.Flat.trans A (Localization.Away g.val) _

/-- A finite locally free module is projective. The comparison with finite
projective modules also records finite generation. -/
theorem FiniteLocallyFree.projective (h : FiniteLocallyFree A M) : Module.Projective A M := by
  haveI := h.finitePresentation
  haveI := h.flat
  exact Module.Flat.projective_of_finitePresentation

/-- The finite principal cover can be recovered from finite presentation and flatness. -/
theorem finiteLocallyFree_of_finitePresentation_flat [Module.FinitePresentation A M] [Module.Flat A M] :
    FiniteLocallyFree A M := by
  let good : Set A := {f | Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)}
  have spans : Ideal.span good = ⊤ := by
    by_contra proper
    obtain ⟨p, maximal, le_p⟩ := Ideal.exists_le_maximal _ proper
    haveI : p.IsPrime := maximal.isPrime
    haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    obtain ⟨g, outside, free, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
    exact outside (le_p (Ideal.subset_span (show g ∈ good from free)))
  obtain ⟨cover, keep, spans⟩ := (Ideal.span_eq_top_iff_finite good).1 spans
  exact ⟨cover, spans, fun g => ⟨keep g.property, inferInstance⟩⟩

/-- Finite local freeness can be checked on any finite principal cover. -/
theorem finiteLocallyFree_of_localizationSpan (s : Finset A)
    (spans : Ideal.span (s : Set A) = ⊤)
    (locally : ∀ f : s,
      FiniteLocallyFree (Localization.Away f.val) (LocalizedModule (Submonoid.powers f.val) M)) :
    FiniteLocallyFree A M := by
  letI : Module.FinitePresentation A M :=
    finitePresentation_of_localizationSpan s spans fun f => (locally f).finitePresentation
  letI : Module.Flat A M := by
    apply Module.flat_of_localized_span A M (s : Set A) spans
    intro f
    let Rf := Localization.Away f.val
    let S := Submonoid.powers f.val
    letI : Module.Flat Rf (LocalizedModule S M) := (locally f).flat
    letI : Module.Flat A Rf := IsLocalization.flat Rf S
    exact Module.Flat.trans A Rf _
  exact finiteLocallyFree_of_finitePresentation_flat

variable [Module.FaithfullyFlat A B]

/-- Finite generators descend through the comparison. -/
theorem finite_of_equiv_baseChange (e : B ⊗[A] M ≃ₗ[B] N) [Module.Finite B N] :
    Module.Finite A M := by
  haveI : Module.Finite B (B ⊗[A] M) := Module.Finite.equiv e.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

/-- Finite relations descend by applying finite generation to the actual base-changed kernel. -/
theorem finitePresentation_of_equiv_baseChange (e : B ⊗[A] M ≃ₗ[B] N) [Module.FinitePresentation B N] :
    Module.FinitePresentation A M := by
  haveI := finite_of_equiv_baseChange e
  haveI : Module.FinitePresentation B (B ⊗[A] M) := Module.FinitePresentation.of_equiv e.symm
  obtain ⟨n, f, surj⟩ := Module.Finite.exists_fin' A M
  haveI := finite_baseChange_ker_of_surjective B f surj
  haveI : Module.Finite A (LinearMap.ker f) := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  exact Module.finitePresentation_of_free_of_surjective f surj (Module.Finite.iff_fg.mp ‹_›)

/-- Flatness descends through the comparison. -/
theorem flat_of_equiv_baseChange (e : B ⊗[A] M ≃ₗ[B] N) [Module.Flat B N] :
    Module.Flat A M := by
  haveI : Module.Flat B (B ⊗[A] M) := Module.Flat.of_linearEquiv e
  exact Module.Flat.of_flat_tensorProduct A M B

/-- An actual base-change comparison preserves the prescribed rank at all points. -/
theorem rankAtStalk_of_equiv_baseChange (e : B ⊗[A] M ≃ₗ[B] N)
    [Module.Finite B N] [Module.Flat B N] (n : ℕ)
    (rank : ∀ q : PrimeSpectrum B, Module.rankAtStalk N q = n) (p : PrimeSpectrum A) :
    Module.rankAtStalk M p = n := by
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p
  haveI := finite_of_equiv_baseChange e
  haveI := flat_of_equiv_baseChange e
  rw [← Module.rankAtStalk_baseChange (R := A) (M := M) q, Module.rankAtStalk_eq_of_equiv e]
  exact rank q

/-- The finite principal cover and the finite projective module criteria are equivalent. -/
theorem finiteLocallyFree_iff_finite_projective :
    FiniteLocallyFree A M ↔ Module.Finite A M ∧ Module.Projective A M := by
  constructor
  · intro h
    haveI := h.finitePresentation
    exact ⟨inferInstance, h.projective⟩
  · rintro ⟨finite, projective⟩
    haveI := Module.finitePresentation_of_projective A M
    exact finiteLocallyFree_of_finitePresentation_flat

section Datum

variable [Module A N] [IsScalarTower A B N] (D : Datum A B N)

/-- The actual fixed-vector module of a finite locally free datum is finite locally free. -/
theorem Datum.finiteLocallyFree (h : FiniteLocallyFree B N) :
    FiniteLocallyFree A D.toCoaction.descended := by
  haveI := h.finitePresentation
  haveI := h.flat
  haveI := finitePresentation_of_equiv_baseChange D.toCoaction.comparisonEquiv
  haveI := flat_of_equiv_baseChange D.toCoaction.comparisonEquiv
  exact finiteLocallyFree_of_finitePresentation_flat

/-- The actual fixed-vector module has the same constant rank on the base spectrum. -/
theorem Datum.constantRank (h : FiniteLocallyFree B N) (n : ℕ)
    (rank : ∀ q : PrimeSpectrum B, Module.rankAtStalk N q = n) :
    ∀ p : PrimeSpectrum A, Module.rankAtStalk D.toCoaction.descended p = n := by
  haveI := h.finitePresentation
  haveI := h.flat
  exact rankAtStalk_of_equiv_baseChange D.toCoaction.comparisonEquiv n rank

end Datum

namespace Examples

/-- The product of two rational fields supplies a split faithfully flat cover. -/
private abbrev SplitCover := ℚ × ℚ

/-- The extended rational line is finite locally free on the split affine cover. -/
theorem split_extension_finiteLocallyFree : FiniteLocallyFree SplitCover (SplitCover ⊗[ℚ] ℚ) :=
  finiteLocallyFree_of_finitePresentation_flat

/-- The descending module of the extended rational line has rank one. -/
theorem split_finiteLocallyFree_descends :
    let D := standardDatum (A := ℚ) (B := SplitCover) (M := ℚ)
    FiniteLocallyFree ℚ D.toCoaction.descended ∧
      ∀ p : PrimeSpectrum ℚ, Module.rankAtStalk D.toCoaction.descended p = 1 := by
  let D := standardDatum (A := ℚ) (B := SplitCover) (M := ℚ)
  refine ⟨D.finiteLocallyFree split_extension_finiteLocallyFree,
    D.constantRank split_extension_finiteLocallyFree 1 (fun q => ?_)⟩
  rw [Module.rankAtStalk_baseChange, Module.rankAtStalk_self]
  rfl

/-- A free rational module with an infinite basis cannot have a finite locally free cover. -/
theorem infinite_free_not_finiteLocallyFree : ¬ FiniteLocallyFree ℚ (ℕ →₀ ℚ) := by
  intro localFree
  haveI := localFree.finitePresentation
  have h : Module.Finite ℚ (ℕ →₀ ℚ) := inferInstance
  rcases Module.finite_finsupp_self_iff.mp h with trivialField | finiteBasis
  · exact zero_ne_one (trivialField.elim (0 : ℚ) 1)
  · letI : Finite ℕ := finiteBasis
    exact not_finite ℕ

end Examples

end SHIGURE.CoefficientDescent
