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
