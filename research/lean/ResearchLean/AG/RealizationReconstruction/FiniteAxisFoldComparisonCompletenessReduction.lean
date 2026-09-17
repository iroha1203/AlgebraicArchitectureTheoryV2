import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldGeneratedLiftFibers
import Formal.Util.AssertStandardAxioms

/-!
# Whole comparison completeness reduces exactly to direct-endpoint completeness

Both the displayed and actual fixed `barAlpha` are isomorphisms, so a
comparison-preserving pair is uniquely determined by its source automorphism.
This module proves that injectivity and surjectivity of the whole comparison
evaluator are respectively equivalent to injectivity and surjectivity of the
direct-endpoint automorphism evaluator.

The reduction does not assume either property.  It identifies the precise
remaining construction: a primitive-syntax encoder and both round trips for
every actual direct-endpoint automorphism.  In particular, the conditional
equivalence at the end is not a completion certificate.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

local instance finiteAxisFoldComparisonCompletenessReductionAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace FiniteAxisFoldComparisonCompletenessReduction

open FiniteAxisFoldAxisSwapPresentation

noncomputable abbrev actualBarAlphaIso :=
  authoredExactBarAlphaAdmissibleIsoAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- Whole comparison evaluation commutes with source projection. -/
theorem comparisonEvaluation_source (pair : ComparisonSubgroup) :
    generatedArrowComparisonSourceHom actualBarAlphaIso.hom
        (comparisonEvaluationHom pair) =
      directAutomorphismEvaluationHom
        (generatedArrowComparisonSourceHom barAlphaIso.hom pair) :=
  rfl

/-- Comparison-evaluator faithfulness is equivalent to direct-endpoint
automorphism-evaluator faithfulness. -/
theorem comparisonEvaluation_injective_iff_direct :
    Function.Injective comparisonEvaluationHom ↔
      Function.Injective directAutomorphismEvaluationHom := by
  constructor
  · intro comparisonInjective first second equality
    have comparisonEquality :
        comparisonEvaluationHom
            (generatedArrowComparisonSectionHom barAlphaIso first) =
          comparisonEvaluationHom
            (generatedArrowComparisonSectionHom barAlphaIso second) := by
      rw [comparisonEvaluation_section, comparisonEvaluation_section, equality]
    have displayedEquality := comparisonInjective comparisonEquality
    exact congrArg
      (fun pair : ComparisonSubgroup =>
        generatedArrowComparisonSourceHom barAlphaIso.hom pair)
      displayedEquality
  · intro directInjective first second equality
    have sourceEquality :
        generatedArrowComparisonSourceHom barAlphaIso.hom first =
          generatedArrowComparisonSourceHom barAlphaIso.hom second := by
      apply directInjective
      rw [← comparisonEvaluation_source, ← comparisonEvaluation_source,
        equality]
    calc
      first = generatedArrowComparisonSectionHom barAlphaIso
          (generatedArrowComparisonSourceHom barAlphaIso.hom first) :=
        (generatedArrowComparisonSection_source_rightInverse
          barAlphaIso first).symm
      _ = generatedArrowComparisonSectionHom barAlphaIso
          (generatedArrowComparisonSourceHom barAlphaIso.hom second) := by
        rw [sourceEquality]
      _ = second :=
        generatedArrowComparisonSection_source_rightInverse barAlphaIso second

/-- Whole comparison-evaluator fullness is equivalent to direct-endpoint
automorphism-evaluator fullness. -/
theorem comparisonEvaluation_surjective_iff_direct :
    Function.Surjective comparisonEvaluationHom ↔
      Function.Surjective directAutomorphismEvaluationHom := by
  constructor
  · intro comparisonSurjective actualAut
    let actualPair := generatedArrowComparisonSectionHom actualBarAlphaIso actualAut
    rcases comparisonSurjective actualPair with ⟨displayedPair, equality⟩
    refine ⟨generatedArrowComparisonSourceHom barAlphaIso.hom displayedPair, ?_⟩
    rw [← comparisonEvaluation_source]
    have sourceEquality := congrArg
      (fun pair : FiniteAxisFoldComparisonRestrictionKernel.RawComparison =>
        generatedArrowComparisonSourceHom actualBarAlphaIso.hom pair) equality
    exact sourceEquality
  · intro directSurjective actualPair
    let actualSource :=
      generatedArrowComparisonSourceHom actualBarAlphaIso.hom actualPair
    rcases directSurjective actualSource with ⟨displayedSource, equality⟩
    refine ⟨generatedArrowComparisonSectionHom barAlphaIso displayedSource, ?_⟩
    rw [comparisonEvaluation_section, equality]
    exact generatedArrowComparisonSection_source_rightInverse
      actualBarAlphaIso actualPair

/-- Consequently, the whole comparison evaluator is bijective exactly when
the direct-endpoint evaluator is bijective. -/
theorem comparisonEvaluation_bijective_iff_direct :
    Function.Bijective comparisonEvaluationHom ↔
      Function.Bijective directAutomorphismEvaluationHom := by
  constructor
  · rintro ⟨injective, surjective⟩
    exact ⟨comparisonEvaluation_injective_iff_direct.mp injective,
      comparisonEvaluation_surjective_iff_direct.mp surjective⟩
  · rintro ⟨injective, surjective⟩
    exact ⟨comparisonEvaluation_injective_iff_direct.mpr injective,
      comparisonEvaluation_surjective_iff_direct.mpr surjective⟩

/-- Conditional packaging only: once primitive syntax independently supplies
direct-endpoint bijectivity, the complete comparison evaluator is a group
equivalence. -/
noncomputable def comparisonEvaluationMulEquivOfDirectBijective
    (directBijective : Function.Bijective directAutomorphismEvaluationHom) :
    ComparisonSubgroup ≃*
      FiniteAxisFoldComparisonRestrictionKernel.RawComparison :=
  MulEquiv.ofBijective comparisonEvaluationHom
    (comparisonEvaluation_bijective_iff_direct.mpr directBijective)

end FiniteAxisFoldComparisonCompletenessReduction

end


#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
