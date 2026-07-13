import Formal.Util.AssertStandardAxioms
import Mathlib.RingTheory.Etale.Kaehler
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ArchitectureOperationPresentation
import ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.TypedLocalizationGeometry

/-!
# Canonical localization of ambient operation derivations

This file extends an ambient derivation across a ring localization through the
localized Kähler differential.  It then applies the construction to every
operation label and every chart and overlap of a typed localization geometry.

## Implementation notes

`localizeDerivation` is the J1b realization of the source note's canonical
ambient-derivation localization.  It uses the localized Kähler differential
because this construction supplies both the extension law and uniqueness for
an arbitrary derivation, without a vanishing condition on a denominator.

Two alternatives are deliberately not used.  A formula on selected fraction
representatives would add a separate well-definedness proof and obscure the
localization universal property.  Accepting chartwise derivations and their
restriction compatibility as fields would move the J1b proof obligation into
input data.  Instead, `chartDerivation` and `overlapDerivation` consume the J0
`ambientDerivation` and the canonical `Localization.Away` instances generated
by the J1a denominator family.  The accompanying extension, uniqueness, and
naturality theorems form the no-unfold API used by J2.
-/

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent

universe uₖ uA uS uN uOp uChart uState uBefore uAfter

variable {k : Type uₖ} {A₀ : Type uA}
variable [Field k] [CommRing A₀] [Algebra k A₀]

namespace AmbientOperationLocalization

/--
The canonical extension of an ambient derivation across a localization.  The
construction localizes its linear map out of the Kähler differential and then
composes with the universal derivation of the localized algebra.
-/
noncomputable def localizeDerivation
    (S : Type uS) [CommRing S] [Algebra k S] [Algebra A₀ S]
    [IsScalarTower k A₀ S]
    (M : Submonoid A₀) [IsLocalization M S]
    (d : Derivation k A₀ A₀) : Derivation k S S :=
  let omegaMap : KaehlerDifferential k A₀ →ₗ[A₀] KaehlerDifferential k S :=
    KaehlerDifferential.map k k A₀ S
  let ringMap : A₀ →ₗ[A₀] S := Algebra.linearMap A₀ S
  let localized : KaehlerDifferential k S →ₗ[A₀] S :=
    IsLocalizedModule.map M omegaMap ringMap d.liftKaehlerDifferential
  (localized.extendScalarsOfIsLocalization M S).compDer
    (KaehlerDifferential.D k S)

/-- The localized derivation extends the ambient derivation on ambient elements. -/
@[simp]
theorem localizeDerivation_algebraMap
    (S : Type uS) [CommRing S] [Algebra k S] [Algebra A₀ S]
    [IsScalarTower k A₀ S]
    (M : Submonoid A₀) [IsLocalization M S]
    (d : Derivation k A₀ A₀) (a : A₀) :
    localizeDerivation S M d (algebraMap A₀ S a) = algebraMap A₀ S (d a) := by
  change
    ((IsLocalizedModule.map M
      (KaehlerDifferential.map k k A₀ S)
      (Algebra.linearMap A₀ S))
      d.liftKaehlerDifferential)
      (KaehlerDifferential.D k S (algebraMap A₀ S a)) = _
  calc
    _ = ((IsLocalizedModule.map M
          (KaehlerDifferential.map k k A₀ S)
          (Algebra.linearMap A₀ S))
          d.liftKaehlerDifferential)
        ((KaehlerDifferential.map k k A₀ S)
          (KaehlerDifferential.D k A₀ a)) := by
            rw [KaehlerDifferential.map_D]
    _ = (Algebra.linearMap A₀ S)
          (d.liftKaehlerDifferential (KaehlerDifferential.D k A₀ a)) :=
      IsLocalizedModule.map_apply _ _ _ _ _
    _ = _ := by simp

/-- The localized derivation agrees with the ambient derivation as a derivation into `S`. -/
theorem localizeDerivation_compAlgebraMap
    (S : Type uS) [CommRing S] [Algebra k S] [Algebra A₀ S]
    [IsScalarTower k A₀ S]
    (M : Submonoid A₀) [IsLocalization M S]
    (d : Derivation k A₀ A₀) :
    (localizeDerivation S M d).compAlgebraMap A₀ =
      (Algebra.linearMap A₀ S).compDer d := by
  apply Derivation.ext
  intro a
  simp

/--
Two derivations out of a localization agree when they agree on the ambient
algebra.  The localized Kähler differentials are spanned by the ambient ones.
-/
theorem derivation_ext_of_isLocalization
    (S : Type uS) [CommRing S] [Algebra k S] [Algebra A₀ S]
    [IsScalarTower k A₀ S]
    (M : Submonoid A₀) [IsLocalization M S]
    {N : Type uN} [AddCommGroup N] [Module k N] [Module S N]
    [IsScalarTower k S N]
    (d₁ d₂ : Derivation k S N)
    (h : ∀ a : A₀, d₁ (algebraMap A₀ S a) = d₂ (algebraMap A₀ S a)) :
    d₁ = d₂ := by
  have hLinear : d₁.liftKaehlerDifferential = d₂.liftKaehlerDifferential := by
    apply LinearMap.ext_on_range
      (KaehlerDifferential.span_range_map_derivation_of_isLocalization k A₀ S M)
    intro a
    simp only [Function.comp_apply, KaehlerDifferential.map_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h a
  apply Derivation.ext
  intro s
  rw [← Derivation.liftKaehlerDifferential_comp_D d₁ s,
    ← Derivation.liftKaehlerDifferential_comp_D d₂ s, hLinear]

end AmbientOperationLocalization

namespace ArchitectureOperationPresentation

open AmbientOperationLocalization

variable {Op : Type uOp} {Chart : Type uChart}
variable {State : Type uState} {BeforeWitness : Type uBefore}
variable {AfterWitness : Type uAfter}
variable [Fintype Op] [Fintype Chart]

/-- The selected ambient operation derivation localized to a chart. -/
noncomputable def chartDerivation
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart)
    (op : Op) (i : Chart) : Derivation k (G.chartRing i) (G.chartRing i) :=
  localizeDerivation (G.chartRing i) (Submonoid.powers (G.denominator i))
    (P.ambientDerivation op)

/-- The selected ambient operation derivation localized to a pairwise overlap. -/
noncomputable def overlapDerivation
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart)
    (op : Op) (i j : Chart) : Derivation k (G.overlapRing i j) (G.overlapRing i j) :=
  localizeDerivation (G.overlapRing i j)
    (Submonoid.powers (G.denominator i * G.denominator j))
    (P.ambientDerivation op)

/-- Each chart derivation extends the selected ambient derivation. -/
@[simp]
theorem chartDerivation_algebraMap
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart)
    (op : Op) (i : Chart) (a : A₀) :
    P.chartDerivation G op i (algebraMap A₀ (G.chartRing i) a) =
      algebraMap A₀ (G.chartRing i) (P.ambientDerivation op a) :=
  localizeDerivation_algebraMap _ _ _ _

/-- Each overlap derivation extends the selected ambient derivation. -/
@[simp]
theorem overlapDerivation_algebraMap
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart)
    (op : Op) (i j : Chart) (a : A₀) :
    P.overlapDerivation G op i j (algebraMap A₀ (G.overlapRing i j) a) =
      algebraMap A₀ (G.overlapRing i j) (P.ambientDerivation op a) :=
  localizeDerivation_algebraMap _ _ _ _

/-- The localized ambient derivations commute with the left overlap restriction. -/
theorem leftChartToOverlap_derivation_natural
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart)
    (op : Op) (i j : Chart) (x : G.chartRing i) :
    P.overlapDerivation G op i j (G.leftChartToOverlap i j x) =
      G.leftChartToOverlap i j (P.chartDerivation G op i x) := by
  let S := G.chartRing i
  let T := G.overlapRing i j
  let φ : S →ₐ[A₀] T := G.leftChartToOverlap i j
  letI : Algebra S T := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A₀ S T :=
    .of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  haveI : IsScalarTower k S T := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply k A₀ T,
      IsScalarTower.algebraMap_apply k A₀ S,
      IsScalarTower.algebraMap_apply A₀ S T]
  have hDer :
      (Algebra.linearMap S T).compDer (P.chartDerivation G op i) =
        (P.overlapDerivation G op i j).compAlgebraMap S := by
    apply derivation_ext_of_isLocalization (k := k) (A₀ := A₀) S
      (Submonoid.powers (G.denominator i))
    intro a
    change
      algebraMap S T
          (localizeDerivation S (Submonoid.powers (G.denominator i))
            (P.ambientDerivation op) (algebraMap A₀ S a)) =
        localizeDerivation T
          (Submonoid.powers (G.denominator i * G.denominator j))
          (P.ambientDerivation op) (algebraMap S T (algebraMap A₀ S a))
    rw [localizeDerivation_algebraMap,
      ← IsScalarTower.algebraMap_apply A₀ S T,
      ← IsScalarTower.algebraMap_apply A₀ S T,
      localizeDerivation_algebraMap]
  exact (Derivation.congr_fun hDer x).symm

/-- The localized ambient derivations commute with the right overlap restriction. -/
theorem rightChartToOverlap_derivation_natural
    (P : ArchitectureOperationPresentation
      k A₀ Op State BeforeWitness AfterWitness)
    (G : TypedLocalizationGeometry k A₀ Chart)
    (op : Op) (i j : Chart) (x : G.chartRing j) :
    P.overlapDerivation G op i j (G.rightChartToOverlap i j x) =
      G.rightChartToOverlap i j (P.chartDerivation G op j x) := by
  let S := G.chartRing j
  let T := G.overlapRing i j
  let φ : S →ₐ[A₀] T := G.rightChartToOverlap i j
  letI : Algebra S T := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A₀ S T :=
    .of_algebraMap_eq fun a ↦ (φ.commutes a).symm
  haveI : IsScalarTower k S T := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply k A₀ T,
      IsScalarTower.algebraMap_apply k A₀ S,
      IsScalarTower.algebraMap_apply A₀ S T]
  have hDer :
      (Algebra.linearMap S T).compDer (P.chartDerivation G op j) =
        (P.overlapDerivation G op i j).compAlgebraMap S := by
    apply derivation_ext_of_isLocalization (k := k) (A₀ := A₀) S
      (Submonoid.powers (G.denominator j))
    intro a
    change
      algebraMap S T
          (localizeDerivation S (Submonoid.powers (G.denominator j))
            (P.ambientDerivation op) (algebraMap A₀ S a)) =
        localizeDerivation T
          (Submonoid.powers (G.denominator i * G.denominator j))
          (P.ambientDerivation op) (algebraMap S T (algebraMap A₀ S a))
    rw [localizeDerivation_algebraMap,
      ← IsScalarTower.algebraMap_apply A₀ S T,
      ← IsScalarTower.algebraMap_apply A₀ S T,
      localizeDerivation_algebraMap]
  exact (Derivation.congr_fun hDer x).symm

end ArchitectureOperationPresentation
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.AmbientOperationLocalization
#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.ArchitectureOperationPresentation
