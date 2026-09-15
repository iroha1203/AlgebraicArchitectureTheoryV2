import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldDisplayedKernelEquiv
import Formal.Util.AssertStandardAxioms

/-!
# Source obligation for the canonical comparison section

The actual canonical normalization sections accept arbitrary completed
normalized comparison elements.  They therefore do not themselves construct
source syntax.  This file makes the missing obligation explicit on the fixed
finite-axis-fold input: source preimages for all canonical-section values
would force the composite of source evaluation and normalization to be
surjective.

The identity value is represented by source identity on both the unrestricted
and bottom-qualified comparison groups.  At bottom-normalized identity, the
entire displayed source C2 fragment also reconstructs the two actual lifts
from Cycles 62--64.  These positive results do not supply source syntax for an
arbitrary semantic normalized comparison value.

## Implementation notes

The surjectivity theorem quantifies the requested source term directly; it
does not add a preimage certificate to syntax.  Its proof uses the actual
canonical section right-inverse, so a future construction cannot discharge
the source-section obligation merely by citing semantic split surjectivity.
The bottom identity witness proves its qualification from the decoder's
identity law and subgroup identity membership.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldCanonicalSectionSourceObligationAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace FiniteAxisFoldCanonicalSectionSourceObligation

open FiniteAxisFoldKernelExtendedPresentation
open FiniteAxisFoldComparisonRestrictionKernel
open FiniteAxisFoldBottomRestrictionKernel
open FiniteAxisFoldDisplayedKernelEquiv

/-- The actual direct admissible endpoint for the fixed finite-axis-fold
comparison. -/
noncomputable abbrev ActualDirectEndpoint :=
  authoredExactDirectAdmissibleGeometryAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The actual admissible `barAlpha` isomorphism for the same fixed input. -/
noncomputable abbrev ActualBarAlphaIso :=
  authoredExactBarAlphaAdmissibleIsoAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- Evaluation commutes with the source-conjugation section in the
kernel-extended presentation for every displayed source automorphism. -/
theorem comparisonEvaluation_section
    (a : Aut (ofObject (.direct finiteAxisFoldG122CellInput))) :
    comparisonEvaluationHom
        (generatedArrowComparisonSectionHom barAlphaIso a) =
      generatedArrowComparisonSectionHom ActualBarAlphaIso
        (directAutomorphismEvaluationHom a) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Iso.ext
    apply ObjectProperty.hom_ext
    dsimp [comparisonEvaluationHom, viaBaseAutomorphismEvaluationHom,
      generatedArrowComparisonSectionHom,
      presentationIsoConjugationAutomorphismHom,
      directAutomorphismEvaluationHom, ActualBarAlphaIso]
    rw [Functor.map_comp, Functor.map_comp]
    rfl

/-- Displayability of one actual canonical section value is equivalent to
displayability of its lifted source endpoint automorphism.  This is a
reduction of the missing coverage obligation, not an assumption that it
holds. -/
theorem exists_canonicalSection_preimage_iff_sourceEndpoint_preimage
    (t : NormalizedComparison) :
    (∃ p : ComparisonSubgroup,
      comparisonEvaluationHom p =
        authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible t) ↔
    (∃ a : Aut (ofObject (.direct finiteAxisFoldG122CellInput)),
      directAutomorphismEvaluationHom a =
        canonicalNormalizationAutomorphismSectionHom
          ActualDirectEndpoint t.1.1) := by
  constructor
  · rintro ⟨p, evaluation⟩
    refine ⟨p.1.1, ?_⟩
    have sourceEquality :=
      congrArg (fun q : RawComparison => q.1.1) evaluation
    simpa [authoredExactCanonicalComparisonSectionHom,
      canonicalNormalizationIsoComparisonSectionHom,
      directAutomorphismEvaluationHom] using sourceEquality
  · rintro ⟨a, sourceEquality⟩
    refine ⟨generatedArrowComparisonSectionHom barAlphaIso a, ?_⟩
    rw [comparisonEvaluation_section]
    apply Subtype.ext
    apply Prod.ext
    · exact sourceEquality
    · apply Iso.ext
      apply ObjectProperty.hom_ext
      dsimp [generatedArrowComparisonSectionHom,
        presentationIsoConjugationAutomorphismHom,
        authoredExactCanonicalComparisonSectionHom,
        canonicalNormalizationIsoComparisonSectionHom,
        geometryIsoConjugationAutomorphismHom]
      rw [congrArg Iso.hom sourceEquality]

/-- The same reduction holds for a bottom-qualified normalized comparison.
Equality with the bottom section's underlying raw value supplies the bottom
qualification; it is not accepted as a source-syntax field. -/
theorem exists_bottomCanonicalSection_preimage_iff_sourceEndpoint_preimage
    (t : NormalizedBottomComparison) :
    (∃ p : ComparisonSubgroup,
      comparisonEvaluationHom p =
        (authoredExactCanonicalBottomComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible t).1) ↔
    (∃ a : Aut (ofObject (.direct finiteAxisFoldG122CellInput)),
      directAutomorphismEvaluationHom a =
        canonicalNormalizationAutomorphismSectionHom
          ActualDirectEndpoint t.1.1.1) := by
  simpa only [authoredExactCanonicalBottomComparisonSectionHom_val] using
    (exists_canonicalSection_preimage_iff_sourceEndpoint_preimage t.1)

/-- Source preimages for every actual canonical comparison-section value
would force source evaluation followed by normalization to be surjective. -/
theorem restrictionEvaluation_surjective_of_canonicalSection_preimages
    (preimages : ∀ t : NormalizedComparison, ∃ g : ComparisonSubgroup,
      comparisonEvaluationHom g =
        authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible t) :
    Function.Surjective (restrictionHom.comp comparisonEvaluationHom) := by
  intro t
  rcases preimages t with ⟨g, evaluation⟩
  refine ⟨g, ?_⟩
  change restrictionHom (comparisonEvaluationHom g) = t
  rw [evaluation]
  exact authoredExactCanonicalComparisonSection_rightInverse
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible t

/-- Source identity is an actual source-syntax preimage of the canonical
section at normalized identity. -/
theorem canonicalSection_identity_sourcePreimage :
    comparisonEvaluationHom (1 : ComparisonSubgroup) =
      authoredExactCanonicalComparisonSectionHom
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible
        (1 : NormalizedComparison) := by
  rw [map_one, map_one]

/-- The evaluated source identity is bottom-qualified at both endpoints. -/
theorem sourceIdentity_bottomQualified :
    comparisonEvaluationHom (1 : ComparisonSubgroup) ∈ RawBottomComparison := by
  rw [map_one]
  exact RawBottomComparison.one_mem

/-- Source identity is also a source-syntax preimage of the bottom-qualified
canonical section at normalized identity. -/
theorem bottomCanonicalSection_identity_sourcePreimage :
    (⟨comparisonEvaluationHom (1 : ComparisonSubgroup),
        sourceIdentity_bottomQualified⟩ : RawBottomComparison) =
      authoredExactCanonicalBottomComparisonSectionHom
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible
        (1 : NormalizedBottomComparison) := by
  apply Subtype.ext
  exact (map_one comparisonEvaluationHom).trans
    (congrArg Subtype.val
      (map_one (authoredExactCanonicalBottomComparisonSectionHom
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)).symm)

/-- The bottom-qualified lift fiber over normalized identity. -/
noncomputable abbrev BottomLiftFiberAtOne :=
  AuthoredExactCanonicalBottomComparisonLiftFiber
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible
    (1 : NormalizedBottomComparison)

/-- Evaluate every displayed source C2 element as a lift over bottom-normalized
identity.  Fiber membership is the actual kernel theorem carried by Cycle 64. -/
noncomputable def sourceLiftAtOne (g : sourceSubgroup) : BottomLiftFiberAtOne :=
  ⟨((toActual g).1).1, (toActual g).1.2⟩

/-- Forgetting the lift and bottom qualifications, every constructed lift is
exactly the decoder evaluation of its source C2 term. -/
theorem sourceLiftAtOne_underlying_evaluation (g : sourceSubgroup) :
    (sourceLiftAtOne g).1.1 = comparisonEvaluationHom g.1 :=
  toActual_underlying_evaluation g

/-- The source identity reconstructs the canonical bottom lift at identity. -/
theorem sourceLiftAtOne_identity :
    sourceLiftAtOne (1 : sourceSubgroup) =
      FiniteAxisFoldBottomRestrictionKernel.canonicalLift
        (1 : NormalizedBottomComparison) := by
  apply Subtype.ext
  change ((toActual (1 : sourceSubgroup)).1).1 =
    authoredExactCanonicalBottomComparisonSectionHom
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible 1
  rw [← bottomCanonicalSection_identity_sourcePreimage]
  apply Subtype.ext
  simp [toActual]

/-- The source generator reconstructs the shifted bottom lift at identity. -/
theorem sourceLiftAtOne_sourceGenerator :
    sourceLiftAtOne sourceGenerator =
      FiniteAxisFoldBottomRestrictionKernel.shiftedLift
        (1 : NormalizedBottomComparison) := by
  apply Subtype.ext
  change ((toActual sourceGenerator).1).1 =
    (FiniteAxisFoldBottomRestrictionKernel.canonicalLift
      (1 : NormalizedBottomComparison)).1 *
        FiniteAxisFoldBottomRestrictionKernel.element.1
  have kernelEquality : (toActual sourceGenerator).1 = actualGenerator.1 := by
    exact congrArg Subtype.val sourceActualEquiv_sourceGenerator
  rw [kernelEquality]
  change FiniteAxisFoldBottomRestrictionKernel.element.1 =
    (FiniteAxisFoldBottomRestrictionKernel.canonicalLift
      (1 : NormalizedBottomComparison)).1 *
        FiniteAxisFoldBottomRestrictionKernel.element.1
  rw [show (FiniteAxisFoldBottomRestrictionKernel.canonicalLift
      (1 : NormalizedBottomComparison)).1 = 1 by
    change authoredExactCanonicalBottomComparisonSectionHom
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible 1 = 1
    exact map_one _]
  exact (one_mul _).symm

/-- Every source C2 term reconstructs one of the two displayed lifts in the
identity fiber. -/
theorem sourceLiftAtOne_cases (g : sourceSubgroup) :
    sourceLiftAtOne g = FiniteAxisFoldBottomRestrictionKernel.canonicalLift
        (1 : NormalizedBottomComparison) ∨
      sourceLiftAtOne g = FiniteAxisFoldBottomRestrictionKernel.shiftedLift
        (1 : NormalizedBottomComparison) := by
  rcases g.property with identity | generator
  · left
    have g_eq : g = 1 := Subtype.ext identity
    simpa [g_eq] using sourceLiftAtOne_identity
  · right
    have g_eq : g = sourceGenerator := Subtype.ext generator
    simpa [g_eq] using sourceLiftAtOne_sourceGenerator

/-- Both displayed lifts in the identity fiber have explicit source C2
preimages. -/
theorem displayedIdentityLifts_have_sourcePreimages :
    (∃ g : sourceSubgroup,
      sourceLiftAtOne g = FiniteAxisFoldBottomRestrictionKernel.canonicalLift
          (1 : NormalizedBottomComparison) ∧
        (sourceLiftAtOne g).1.1 = comparisonEvaluationHom g.1) ∧
    (∃ g : sourceSubgroup,
      sourceLiftAtOne g = FiniteAxisFoldBottomRestrictionKernel.shiftedLift
          (1 : NormalizedBottomComparison) ∧
        (sourceLiftAtOne g).1.1 = comparisonEvaluationHom g.1) :=
  ⟨⟨1, sourceLiftAtOne_identity,
      sourceLiftAtOne_underlying_evaluation 1⟩,
    ⟨sourceGenerator, sourceLiftAtOne_sourceGenerator,
      sourceLiftAtOne_underlying_evaluation sourceGenerator⟩⟩

end FiniteAxisFoldCanonicalSectionSourceObligation

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
