import ResearchLean.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPermutationIntrinsicImage
import Formal.Util.AssertStandardAxioms

/-!
# Mixed axis and Extension local reconstruction for G-122 comparisons

This module enlarges the six-element axis image to a 36-element family.  Its
independent local code is a pair consisting of one three-axis permutation and
one explicit finite forward/backward table on `Fin 3`.  Evaluation first
decodes the Extension table through the accepted source-to-actual route, then
applies the axis section, and finally forms the actual normalized comparison.

Reading uses two distinct actual projections.  The global axis projection
recovers the axis table.  After removing that recovered section, the stored
backward-context action recovers the Extension table uniquely.  These readings
give both inverse laws, separate the actual image, and prove its cardinality is
36.  The unique mixed code for each canonical section is then connected to the
full actual restriction-kernel torsor on every represented lift fiber.

## Implementation notes

The Extension component is placed before the axis section so the accepted
axis-kernel remainder removes the axis component exactly.  The reader is not
defined by unpacking the image witness: it uses the actual axis and stored
backward-context projections, with unique choice only after existence and
uniqueness have been proved from those observations.  We reject storing an
actual automorphism, comparison, lift, range witness, or kernel element in the
local code.  The result concerns only this 36-element image and does not claim
coverage of the full comparison group or local recovery of the full kernel.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FiniteAxisFoldAxisSwapPresentation
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel

namespace G122MixedAxisExtensionLocalModel

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance cycle50AtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Independent forward/backward lookup table for the three Extension values. -/
abbrev ExtensionCode := FiniteAxisFoldExtensionPermutationCode (Fin 3)

/-- Independent local code pairing the global axis and Extension tables. -/
abbrev MixedCode := Equiv.Perm (Fin 3) × ExtensionCode

/-- Decode one Extension table to the accepted actual normalized endpoint
automorphism. -/
noncomputable def extensionAut (code : ExtensionCode) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  (finiteAxisFoldExtensionPermutationDecoder (Fin 3) code).1.1.1.1

/-- Evaluate a mixed code by applying the Extension action before the axis
section. -/
noncomputable def mixedAut (code : MixedCode) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  extensionAut code.2 * finiteAxisFoldNormalizedAxisSectionHom code.1

/-- The decoded Extension table is invisible to the global axis projection. -/
theorem extensionAut_axisProjection_eq_one (code : ExtensionCode) :
    finiteAxisFoldNormalizedAxisProjection (extensionAut code) = 1 := by
  exact MonoidHom.mem_ker.mp
    (finiteAxisFoldExtensionPermutationDecoder (Fin 3) code).1.1.1.2

/-- The global axis projection of a mixed evaluation recovers its first table. -/
theorem mixedAut_axisProjection (code : MixedCode) :
    finiteAxisFoldNormalizedAxisProjection (mixedAut code) = code.1 := by
  rw [mixedAut, map_mul, extensionAut_axisProjection_eq_one,
    finiteAxisFoldNormalizedAxisProjection_section, one_mul]

/-- Read the actual stored backward-context action of a normalized endpoint
automorphism. -/
noncomputable def backwardObservation
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  finiteAxisFoldNormalizedContextBackwardProjection automorphism

/-- The backward-context observation of an Extension evaluation is its
independently defined primitive action. -/
theorem extensionAut_backwardObservation (code : ExtensionCode) :
    backwardObservation (extensionAut code) =
      finiteAxisFoldExtensionPermutationBackwardAction (Fin 3) code := by
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      (finiteAxisFoldExtensionPermutationDecoder (Fin 3) code) = _
  exact finiteAxisFoldExtensionPermutationDecoder_backwardProjection code

/-- Remove the axis section selected by the actual global-axis projection. -/
noncomputable def strippedAut
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  automorphism *
    (finiteAxisFoldNormalizedAxisSectionHom
      (finiteAxisFoldNormalizedAxisProjection automorphism))⁻¹

/-- Stripping the recovered axis section from a mixed evaluation leaves
exactly its Extension evaluation. -/
theorem mixedAut_stripped (code : MixedCode) :
    strippedAut (mixedAut code) = extensionAut code.2 := by
  rw [strippedAut, mixedAut_axisProjection, mixedAut]
  simp

/-- The stored backward-context observation after axis removal recovers the
Extension table's primitive action. -/
theorem mixedAut_backwardObservation (code : MixedCode) :
    backwardObservation (strippedAut (mixedAut code)) =
      finiteAxisFoldExtensionPermutationBackwardAction (Fin 3) code.2 := by
  rw [mixedAut_stripped]
  exact extensionAut_backwardObservation code.2

/-- Distinct finite Extension tables have distinct stored backward-context
actions. -/
theorem extensionBackwardAction_injective :
    Function.Injective
      (finiteAxisFoldExtensionPermutationBackwardAction (Fin 3)) := by
  intro first second equality
  apply finiteAxisFoldExtensionPermutationIntrinsicDecoder_injective (Fin 3)
  apply Subtype.ext
  change finiteAxisFoldExtensionPermutationDecoder (Fin 3) first =
    finiteAxisFoldExtensionPermutationDecoder (Fin 3) second
  apply finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
  rw [finiteAxisFoldExtensionPermutationDecoder_backwardProjection,
    finiteAxisFoldExtensionPermutationDecoder_backwardProjection, equality]

/-- The two actual projections jointly separate all mixed codes. -/
theorem mixedAut_injective : Function.Injective mixedAut := by
  intro first second equality
  apply Prod.ext
  · rw [← mixedAut_axisProjection first, ← mixedAut_axisProjection second,
      equality]
  · apply extensionBackwardAction_injective
    rw [← mixedAut_backwardObservation first,
      ← mixedAut_backwardObservation second, equality]

/-- Assemble a mixed code into the actual normalized comparison section. -/
noncomputable def mixedComparison (code : MixedCode) : NormalizedComparison :=
  generatedArrowComparisonSectionHom finiteAxisFoldNormalizedBarAlphaIso
    (mixedAut code)

/-- Source projection of the assembled comparison returns the mixed endpoint
automorphism. -/
@[simp] theorem mixedComparison_source (code : MixedCode) :
    generatedArrowComparisonSourceHom
        finiteAxisFoldNormalizedBarAlphaIso.hom (mixedComparison code) =
      mixedAut code := by
  rfl

/-- The actual normalized comparisons represented by mixed finite codes. -/
abbrev MixedComparisonImage := Set.range mixedComparison

/-- Retain one assembled comparison in the represented semantic image. -/
noncomputable def assembleMixed (code : MixedCode) : MixedComparisonImage :=
  ⟨mixedComparison code, ⟨code, rfl⟩⟩

/-- Read the global three-axis table from an actual represented comparison. -/
noncomputable def readAxis (comparison : MixedComparisonImage) :
    Equiv.Perm (Fin 3) :=
  finiteAxisFoldNormalizedAxisProjection
    (generatedArrowComparisonSourceHom
      finiteAxisFoldNormalizedBarAlphaIso.hom comparison.1)

/-- Read the stored backward-context target after removing the observed axis
section. -/
noncomputable def extensionTarget (comparison : MixedComparisonImage) :
    (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  backwardObservation
    (strippedAut
      (generatedArrowComparisonSourceHom
        finiteAxisFoldNormalizedBarAlphaIso.hom comparison.1))

/-- Every represented comparison has exactly one Extension table matching its
actual stripped backward-context observation. -/
theorem extensionTarget_existsUnique (comparison : MixedComparisonImage) :
    ∃! code : ExtensionCode,
      finiteAxisFoldExtensionPermutationBackwardAction (Fin 3) code =
        extensionTarget comparison := by
  rcases comparison with ⟨comparison, code, rfl⟩
  refine ⟨code.2, ?_, ?_⟩
  · exact (mixedAut_backwardObservation code).symm
  · intro candidate equality
    apply extensionBackwardAction_injective
    exact equality.trans (mixedAut_backwardObservation code)

/-- Recover the unique Extension table selected by the actual observation. -/
noncomputable def readExtension (comparison : MixedComparisonImage) :
    ExtensionCode :=
  Classical.choose (extensionTarget_existsUnique comparison)

/-- The recovered Extension table realizes the observed backward action. -/
theorem readExtension_spec (comparison : MixedComparisonImage) :
    finiteAxisFoldExtensionPermutationBackwardAction (Fin 3)
        (readExtension comparison) = extensionTarget comparison :=
  (Classical.choose_spec (extensionTarget_existsUnique comparison)).1

/-- Any Extension table realizing the observation equals the recovered table. -/
theorem readExtension_unique (comparison : MixedComparisonImage)
    (code : ExtensionCode)
    (equality : finiteAxisFoldExtensionPermutationBackwardAction (Fin 3) code =
      extensionTarget comparison) :
    code = readExtension comparison :=
  (Classical.choose_spec (extensionTarget_existsUnique comparison)).2 code equality

/-- Read both independent finite tables from a represented comparison. -/
noncomputable def readMixed (comparison : MixedComparisonImage) : MixedCode :=
  (readAxis comparison, readExtension comparison)

/-- Reading after mixed assembly recovers both input tables. -/
@[simp] theorem readMixed_assembleMixed (code : MixedCode) :
    readMixed (assembleMixed code) = code := by
  apply Prod.ext
  · exact mixedAut_axisProjection code
  · change readExtension (assembleMixed code) = code.2
    exact (readExtension_unique (assembleMixed code) code.2
      (mixedAut_backwardObservation code).symm).symm

/-- Mixed assembly after reading recovers every represented comparison. -/
@[simp] theorem assembleMixed_readMixed (comparison : MixedComparisonImage) :
    assembleMixed (readMixed comparison) = comparison := by
  rcases comparison with ⟨comparison, code, rfl⟩
  apply Subtype.ext
  change mixedComparison (readMixed (assembleMixed code)) = mixedComparison code
  rw [readMixed_assembleMixed]

/-- Two-sided reconstruction equivalence between independent mixed codes and
their actual comparison image. -/
noncomputable def mixedComparisonEquiv :
    MixedCode ≃ MixedComparisonImage where
  toFun := assembleMixed
  invFun := readMixed
  left_inv := readMixed_assembleMixed
  right_inv := assembleMixed_readMixed

/-- Extension tables are finite because they are equivalent to permutations of
three values. -/
noncomputable instance extensionCodeFintype : Fintype ExtensionCode :=
  Fintype.ofEquiv (Equiv.Perm (Fin 3))
    (FiniteAxisFoldExtensionPermutationCode.tableMulEquiv (E := Fin 3)).toEquiv.symm

/-- The represented semantic image inherits finiteness from the mixed code. -/
noncomputable instance mixedComparisonImageFintype :
    Fintype MixedComparisonImage :=
  Fintype.ofEquiv MixedCode mixedComparisonEquiv

/-- There are exactly six independent Extension lookup tables. -/
theorem extensionCode_card : Fintype.card ExtensionCode = 6 := by
  rw [Fintype.card_congr
    (FiniteAxisFoldExtensionPermutationCode.tableMulEquiv
      (E := Fin 3)).toEquiv]
  decide

/-- Combining the two independently recoverable tables produces 36 actual
normalized comparisons. -/
theorem mixedComparisonImage_card :
    Fintype.card MixedComparisonImage = 36 := by
  rw [Fintype.card_congr mixedComparisonEquiv.symm, Fintype.card_prod,
    extensionCode_card]
  norm_num [Fintype.card_perm]

/-- The joint actual reading separates all represented comparisons. -/
theorem readMixed_injective : Function.Injective readMixed :=
  mixedComparisonEquiv.symm.injective

/-- The actual canonical lift over one represented mixed comparison. -/
noncomputable def canonicalLift (comparison : MixedComparisonImage) :
    AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1 :=
  ⟨authoredExactCanonicalComparisonSectionHom
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1,
    authoredExactCanonicalComparisonSection_rightInverse
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1⟩

/-- Every represented canonical section is induced by one and only one
independent mixed finite code. -/
theorem canonicalSection_unique_mixedCode
    (comparison : MixedComparisonImage) :
    ∃! code : MixedCode,
      authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible
          (mixedComparison code) =
        (canonicalLift comparison).1 := by
  refine ⟨readMixed comparison, ?_, ?_⟩
  · exact congrArg
      (authoredExactCanonicalComparisonSectionHom
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      (congrArg Subtype.val (assembleMixed_readMixed comparison))
  · intro candidate candidateEquality
    have normalized := congrArg
      (fun raw : RawComparison => restrictionHom raw) candidateEquality
    change restrictionHom
        (authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible
          (mixedComparison candidate)) =
      restrictionHom
        (authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible comparison.1) at normalized
    rw [authoredExactCanonicalComparisonSection_rightInverse,
      authoredExactCanonicalComparisonSection_rightInverse] at normalized
    have imageEquality : assembleMixed candidate = comparison := by
      apply Subtype.ext
      exact normalized
    exact mixedComparisonEquiv.injective
      (imageEquality.trans (assembleMixed_readMixed comparison).symm)

/-- From the mixed-code canonical lift, every lift in the same fiber is reached
by one unique element of the full actual restriction kernel. -/
theorem everyLift_unique_kernel_displacement
    (comparison : MixedComparisonImage)
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1) :
    ∃! kernelValue : restrictionHom.kerᵐᵒᵖ,
      kernelValue • canonicalLift comparison = lift :=
  authoredExactCanonicalComparisonLiftFiber_existsUnique_smul_eq
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible comparison.1
    (canonicalLift comparison) lift

/-- Unique mixed-code recovery and the full-kernel torsor theorem hold together
over every represented comparison and lift. -/
theorem mixedCode_fullKernel_reconstruction
    (comparison : MixedComparisonImage)
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1) :
    (∃! code : MixedCode,
      authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible
          (mixedComparison code) =
        (canonicalLift comparison).1) ∧
    (∃! kernelValue : restrictionHom.kerᵐᵒᵖ,
      kernelValue • canonicalLift comparison = lift) :=
  ⟨canonicalSection_unique_mixedCode comparison,
    everyLift_unique_kernel_displacement comparison lift⟩

end
end G122MixedAxisExtensionLocalModel
end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel
