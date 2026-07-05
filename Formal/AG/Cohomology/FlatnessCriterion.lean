import Formal.AG.Cohomology.HigherOverlap

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

open Opposite

/-- IV.定理11.1: vanishing of a selected `H^1(𝒰, Ob_U)` class. -/
def H1ClassVanishes {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (h1AddCommGroup : AddCommGroup (K.CoverRelativeHn 1))
    (c : K.CoverRelativeHn 1) : Prop :=
  letI := h1AddCommGroup
  c = 0

/--
IV.定理11.1: selected gluing obstruction class.

The cohomological obstruction is explicitly a class `[g] in H^1(𝒰, Ob_U)`.
-/
structure GluingObstructionClass {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob) where
  g : K.CechCocycle 1

namespace GluingObstructionClass

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}

/-- IV.定理11.1: `[g] in H^1(𝒰, Ob_U)`. -/
def h1Class (G : GluingObstructionClass K) : K.CoverRelativeHn 1 :=
  K.cohomologyClassSucc 0 G.g

/-- IV.定理11.1: the stored obstruction class is definitionally `[g]`. -/
theorem h1Class_eq (G : GluingObstructionClass K) :
    G.h1Class = K.cohomologyClassSucc 0 G.g :=
  rfl

end GluingObstructionClass

/--
R5 / IV-4: additive vanishing of the selected gluing obstruction class.

This is the finite-regime reading of `[g] = 0` through the additive
`H^1 = Z^1 / B^1` surface introduced for IV-1.
-/
def AdditiveH1ClassVanishes {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (G : GluingObstructionClass K) : Prop :=
  K.additiveH1Class G.g = 0

/--
R5 / IV-4: finite coboundary characterization of vanishing.

The selected additive `H^1` class vanishes exactly when the obstruction cocycle
is the coboundary of a degree-zero adjustment cochain.
-/
theorem additiveH1ClassVanishes_iff_exists_c0_coboundary
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (G : GluingObstructionClass K) :
    AdditiveH1ClassVanishes K G ↔ ∃ t : K.Cn 0, G.g.1 = K.d 0 t := by
  simpa [AdditiveH1ClassVanishes] using K.additiveH1Class_eq_zero_iff G.g

/--
R5 / IV-4: a concrete finite `C^0` adjustment.

The selected adjustment is a degree-zero cochain.  Its adjusted overlap
residual is defined below as `g - d t`; overlap agreement is therefore the
concrete equation `g - d t = 0`, not a separately supplied implication.
-/
structure FiniteC0AdjustmentSurface {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (G : GluingObstructionClass K) where
  adjustment : K.Cn 0

namespace FiniteC0AdjustmentSurface

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {G : GluingObstructionClass K}

/--
R5 / IV-4: the overlap residual after the selected finite `C^0` adjustment.
-/
def adjustedOverlapResidual (T : FiniteC0AdjustmentSurface K G) : K.Cn 1 :=
  letI := K.cochainAddCommGroup 1
  G.g.1 - (K.d 0 T.adjustment : K.Cn 1)

/--
R5 / IV-4: concrete adjusted overlap agreement after a finite `C^0`
adjustment.
-/
def adjustedOverlapAgreement (T : FiniteC0AdjustmentSurface K G) : Prop :=
  letI := K.cochainAddCommGroup 1
  T.adjustedOverlapResidual = 0

/--
R5 / IV-4: concrete overlap agreement is exactly the coboundary equation for
the selected finite `C^0` adjustment.
-/
theorem adjustedOverlapAgreement_iff_c0_coboundary
    (T : FiniteC0AdjustmentSurface K G) :
    T.adjustedOverlapAgreement ↔ G.g.1 = K.d 0 T.adjustment := by
  letI := K.cochainAddCommGroup 1
  change G.g.1 - K.d 0 T.adjustment = 0 ↔
    G.g.1 = K.d 0 T.adjustment
  exact sub_eq_zero

end FiniteC0AdjustmentSurface

/--
R5 / IV-4: existence of a finite adjusted global lawful-section condition.

In this finite surface, such a condition is witnessed by a concrete `C^0`
adjustment whose adjusted overlap residual `g - d t` vanishes.  This does not
claim a general descent theorem or non-abelian torsor triviality.
-/
def FiniteC0AdjustedGlobalLawfulSection {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (G : GluingObstructionClass K) : Prop :=
  ∃ T : FiniteC0AdjustmentSurface K G, T.adjustedOverlapAgreement

/--
R5 / IV-4: the finite adjusted global lawful-section condition is equivalent
to a degree-zero coboundary potential for `g`.
-/
theorem finiteC0AdjustedGlobalLawfulSection_iff_exists_c0_coboundary
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (G : GluingObstructionClass K) :
    FiniteC0AdjustedGlobalLawfulSection K G ↔
      ∃ t : K.Cn 0, G.g.1 = K.d 0 t := by
  constructor
  · intro h
    rcases h with ⟨T, hT⟩
    exact ⟨T.adjustment,
      (FiniteC0AdjustmentSurface.adjustedOverlapAgreement_iff_c0_coboundary T).1 hT⟩
  · intro h
    rcases h with ⟨t, ht⟩
    refine ⟨⟨t⟩, ?_⟩
    exact (FiniteC0AdjustmentSurface.adjustedOverlapAgreement_iff_c0_coboundary
      (K := K) (G := G) ⟨t⟩).2 ht

/--
R5 / IV-4: finite flatness criterion in additive `H^1` form:
`[g] = 0` iff the finite adjusted global lawful-section condition holds.
-/
theorem finiteC0AdjustedGlobalLawfulSection_iff_additiveH1ClassVanishes
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (G : GluingObstructionClass K) :
    FiniteC0AdjustedGlobalLawfulSection K G ↔ AdditiveH1ClassVanishes K G := by
  rw [finiteC0AdjustedGlobalLawfulSection_iff_exists_c0_coboundary,
    additiveH1ClassVanishes_iff_exists_c0_coboundary]

/-- R5 / IV-4: vanishing additive `H^1` gives the finite adjusted condition. -/
theorem finiteC0AdjustedGlobalLawfulSection_of_additiveH1ClassVanishes
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S}
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {G : GluingObstructionClass K}
    (h : AdditiveH1ClassVanishes K G) :
    FiniteC0AdjustedGlobalLawfulSection K G :=
  (finiteC0AdjustedGlobalLawfulSection_iff_additiveH1ClassVanishes K G).2 h

/-- R5 / IV-4: the finite adjusted condition forces additive `H^1` vanishing. -/
theorem additiveH1ClassVanishes_of_finiteC0AdjustedGlobalLawfulSection
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}
    {Ob : ObstructionSheaf S}
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {G : GluingObstructionClass K}
    (h : FiniteC0AdjustedGlobalLawfulSection K G) :
    AdditiveH1ClassVanishes K G :=
  (finiteC0AdjustedGlobalLawfulSection_iff_additiveH1ClassVanishes K G).1 h

/--
IV.定理11.1: effective abelian `Ob_U`-torsor data.

This package records only the abelianized local-adjustment surface used by the
criterion.  It explicitly records that this abelianization does not recover
triviality of an original non-abelian torsor.
-/
structure EffectiveAbelianObstructionTorsor {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {Ob : ObstructionSheaf S} where
  localAdjustment : Type u
  adjustmentDifferenceCarrier : Type u
  adjustmentAddCommGroup : AddCommGroup adjustmentDifferenceCarrier
  adjust : adjustmentDifferenceCarrier -> localAdjustment -> localAdjustment
  differenceToObCoefficient :
    ∀ W : S.category,
      letI := adjustmentAddCommGroup
      letI := Ob.addCommGroup W
      adjustmentDifferenceCarrier →+ Ob.carrier.toPresheaf.obj (op W)
  actionIsEffective : Prop
  actionIsEffective_holds : actionIsEffective
  differencesReadInOb : Prop
  differencesReadInOb_holds : differencesReadInOb
  abelianizationDoesNotRecoverNonabelianTriviality : Prop
  abelianizationDoesNotRecoverNonabelianTriviality_holds :
    abelianizationDoesNotRecoverNonabelianTriviality

attribute [instance] EffectiveAbelianObstructionTorsor.adjustmentAddCommGroup

/--
IV.定理11.1: explicit hypothesis block for the Cohomological Flatness
Criterion and local-to-global flatness corollary.
-/
structure CohomologicalFlatnessCriterionHypotheses {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (G : GluingObstructionClass K) where
  h1AddCommGroup : AddCommGroup (K.CoverRelativeHn 1)
  torsor : EffectiveAbelianObstructionTorsor (S := S) (Ob := Ob)
  localFlatness : Prop
  localFlatness_holds : localFlatness
  abelianCoefficients : Prop
  abelianCoefficients_holds : abelianCoefficients
  cocycleProvided : Prop
  cocycleProvided_holds : cocycleProvided
  effectiveTorsor : Prop
  effectiveTorsor_holds : effectiveTorsor
  uAdequateCover : Prop
  uAdequateCover_holds : uAdequateCover
  soundness : Prop
  soundness_holds : soundness
  completeness : Prop
  completeness_holds : completeness
  axisExactness : Prop
  axisExactness_holds : axisExactness
  witnessCoverage : Prop
  witnessCoverage_holds : witnessCoverage
  descent : Prop
  descent_holds : descent
  effectiveAdjustment : Prop
  effectiveAdjustment_holds : effectiveAdjustment
  torsorTriviality : Prop
  adjustedGlobalLawfulSection : Prop
  globalFlatness : Prop
  torsorTriviality_of_h1Class_zero :
    localFlatness ->
      abelianCoefficients ->
        cocycleProvided ->
          effectiveTorsor ->
            uAdequateCover ->
              soundness ->
                completeness ->
                  axisExactness ->
                    witnessCoverage ->
                      descent ->
                        effectiveAdjustment ->
                          H1ClassVanishes K h1AddCommGroup G.h1Class ->
                            torsorTriviality
  h1Class_zero_of_torsorTriviality :
    localFlatness ->
      abelianCoefficients ->
        cocycleProvided ->
          effectiveTorsor ->
            uAdequateCover ->
              soundness ->
                completeness ->
                  axisExactness ->
                    witnessCoverage ->
                      descent ->
                        torsorTriviality ->
                          H1ClassVanishes K h1AddCommGroup G.h1Class
  adjustedGlobalLawfulSection_of_torsorTriviality :
    localFlatness ->
      abelianCoefficients ->
        effectiveTorsor ->
          descent ->
            effectiveAdjustment ->
              torsorTriviality ->
                adjustedGlobalLawfulSection
  torsorTriviality_of_adjustedGlobalLawfulSection :
    localFlatness ->
      abelianCoefficients ->
        effectiveTorsor ->
          descent ->
            effectiveAdjustment ->
              adjustedGlobalLawfulSection ->
                torsorTriviality
  adjustedGlobalLawfulSection_gives_globalFlatness :
    adjustedGlobalLawfulSection -> globalFlatness

namespace CohomologicalFlatnessCriterionHypotheses

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : CoverRelativeCechCover S} {Ob : ObstructionSheaf S}
variable {K : CoverRelativeCechComplex 𝒰 Ob}
variable {G : GluingObstructionClass K}

/--
IV.定理11.1 Cohomological Flatness Criterion.

Under the explicit R8 hypothesis block, vanishing of `[g]` is equivalent to
existence of an adjusted global lawful section.  The nonvanishing obstruction
statement is read as the contrapositive of this equivalence.
-/
theorem cohomologicalFlatnessCriterion
    (H : CohomologicalFlatnessCriterionHypotheses K G) :
    H.adjustedGlobalLawfulSection ↔
      H1ClassVanishes K H.h1AddCommGroup G.h1Class :=
  ⟨fun h =>
      H.h1Class_zero_of_torsorTriviality
        H.localFlatness_holds
        H.abelianCoefficients_holds
        H.cocycleProvided_holds
        H.effectiveTorsor_holds
        H.uAdequateCover_holds
        H.soundness_holds
        H.completeness_holds
        H.axisExactness_holds
        H.witnessCoverage_holds
        H.descent_holds
        (H.torsorTriviality_of_adjustedGlobalLawfulSection
          H.localFlatness_holds
          H.abelianCoefficients_holds
          H.effectiveTorsor_holds
          H.descent_holds
          H.effectiveAdjustment_holds
          h),
    fun h =>
      H.adjustedGlobalLawfulSection_of_torsorTriviality
        H.localFlatness_holds
        H.abelianCoefficients_holds
        H.effectiveTorsor_holds
        H.descent_holds
        H.effectiveAdjustment_holds
        (H.torsorTriviality_of_h1Class_zero
          H.localFlatness_holds
          H.abelianCoefficients_holds
          H.cocycleProvided_holds
          H.effectiveTorsor_holds
          H.uAdequateCover_holds
          H.soundness_holds
          H.completeness_holds
          H.axisExactness_holds
          H.witnessCoverage_holds
          H.descent_holds
          H.effectiveAdjustment_holds
          h)⟩

/-- IV.定理11.1: vanishing `[g] = 0` gives an adjusted global lawful section. -/
theorem adjustedGlobalLawfulSection_of_h1Class_zero
    (H : CohomologicalFlatnessCriterionHypotheses K G)
    (h : H1ClassVanishes K H.h1AddCommGroup G.h1Class) :
    H.adjustedGlobalLawfulSection :=
  (H.cohomologicalFlatnessCriterion).2 h

/-- IV.定理11.1: nonzero `[g]` rules out an adjusted global lawful section. -/
theorem noAdjustedGlobalLawfulSection_of_h1Class_nonzero
    (H : CohomologicalFlatnessCriterionHypotheses K G)
    (h : ¬ H1ClassVanishes K H.h1AddCommGroup G.h1Class) :
    ¬ H.adjustedGlobalLawfulSection :=
  fun hs => h ((H.cohomologicalFlatnessCriterion).1 hs)

/--
IV.系11.2 Local-to-Global Flatness.

Under the same explicit hypothesis block, vanishing of the selected `H^1`
class gives global flatness after the effective local adjustment.
-/
theorem localToGlobalFlatness
    (H : CohomologicalFlatnessCriterionHypotheses K G)
    (h : H1ClassVanishes K H.h1AddCommGroup G.h1Class) :
    H.globalFlatness :=
  H.adjustedGlobalLawfulSection_gives_globalFlatness
    (H.adjustedGlobalLawfulSection_of_h1Class_zero h)

end CohomologicalFlatnessCriterionHypotheses

end Cohomology
end AAT.AG
