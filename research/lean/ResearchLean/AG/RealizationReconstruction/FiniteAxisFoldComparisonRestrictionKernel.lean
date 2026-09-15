import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldKernelExtendedPresentation
import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalComparisonExactness
import Formal.Util.AssertStandardAxioms

/-!
# A displayed nontrivial element of the actual comparison restriction kernel

Cycle 59 constructed, from the fixed finite-axis-fold source recipes, a
nontrivial raw comparison pair whose source is the direct ambient involution
and whose target is forced by conjugation across the actual `barAlpha`.  This
file proves that both components normalize to identity.  The same pair is
therefore a nontrivial element of the kernel of the actual comparison
restriction homomorphism, not merely an element of the larger ambient endpoint
kernel.

The constructed kernel element acts nontrivially on the canonical section lift
over every normalized comparison element.  This connects one displayed source
recipe to every actual lift fiber, but does not claim that the presentation
enumerates every kernel element or every lift in those fibers.

## Implementation notes

The source normalization equation is the Cycle 56 theorem for the exact recipe.
The target normalization equation is derived from the raw comparison square:
after functorial normalization the source component is identity, and the mapped
`barAlpha` is cancelled using its mapped inverse.  No normalized target
automorphism, kernel membership proof, or lift is accepted as syntax input.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldRestrictionKernelAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace FiniteAxisFoldComparisonRestrictionKernel

/-- The exact raw comparison group for the fixed G-122 input. -/
noncomputable abbrev RawComparison :=
  AuthoredExactCanonicalRawComparisonSubgroup
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The exact normalized comparison group for the same fixed input. -/
noncomputable abbrev NormalizedComparison :=
  AuthoredExactCanonicalNormalizedComparisonSubgroup
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The actual comparison restriction homomorphism for the fixed `barAlpha`. -/
noncomputable abbrev restrictionHom : RawComparison →* NormalizedComparison :=
  geometryNormalizationComparisonSubgroupHom
    (authoredExactBarAlphaAdmissibleIsoAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible).hom

/-- The raw comparison element obtained by evaluating the Cycle 59 displayed
source-conjugation pair. -/
noncomputable def rawElement : RawComparison :=
  FiniteAxisFoldKernelExtendedPresentation.comparisonEvaluationHom
    FiniteAxisFoldKernelExtendedPresentation.ambientComparisonElement

/-- The source endpoint of the constructed raw pair normalizes to identity. -/
theorem endpointNormalization_source :
    (geometryNormalizationEndpointAutomorphismHom
      (authoredExactDirectAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      (authoredExactViaBaseAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      rawElement.1).1 = 1 := by
  change (geometryNormalizationFunctor.{0, 0}
    finiteAxisFoldG122FamilyInput.Carrier).mapIso rawElement.1.1 = Iso.refl _
  rw [rawElement,
    FiniteAxisFoldKernelExtendedPresentation.ambientComparisonElement_evaluation_source]
  exact FiniteAxisFoldAmbientKernelCode.direct.normalization_map_admissibleEvaluateAut

/-- Raw comparison preservation forces the target endpoint to normalize to
identity as well. -/
theorem endpointNormalization_target :
    (geometryNormalizationEndpointAutomorphismHom
      (authoredExactDirectAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      (authoredExactViaBaseAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      rawElement.1).2 = 1 := by
  let c := authoredExactBarAlphaAdmissibleIsoAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible
  let normalizedPair := geometryNormalizationEndpointAutomorphismHom
    (authoredExactDirectAdmissibleGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible)
    (authoredExactViaBaseAdmissibleGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible)
    rawElement.1
  have preserves : normalizedPair ∈ normalizedGeometryComparisonSubgroup c.hom :=
    geometryNormalizationEndpointAutomorphism_preserves_comparison
      c.hom rawElement.1 rawElement.2
  have square := (mem_normalizedGeometryComparisonSubgroup).mp preserves
  have sourceIdentity : normalizedPair.1.hom = 𝟙 _ :=
    congrArg Iso.hom endpointNormalization_source
  have reduced :
      (geometryNormalizationFunctor.{0, 0}
          finiteAxisFoldG122FamilyInput.Carrier).map c.hom =
        (geometryNormalizationFunctor.{0, 0}
            finiteAxisFoldG122FamilyInput.Carrier).map c.hom ≫
          normalizedPair.2.hom := by
    simpa [normalizedPair, c, sourceIdentity] using square
  have targetIdentity : normalizedPair.2.hom = 𝟙 _ := by
    have cancelled := congrArg
      (fun f => (geometryNormalizationFunctor.{0, 0}
          finiteAxisFoldG122FamilyInput.Carrier).map c.inv ≫ f) reduced
    simpa [Functor.map_comp] using cancelled.symm
  apply Iso.ext
  exact targetIdentity

/-- Both endpoints of the source-constructed raw pair normalize to identity. -/
theorem endpointNormalization :
    geometryNormalizationEndpointAutomorphismHom
      (authoredExactDirectAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      (authoredExactViaBaseAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      rawElement.1 = 1 := by
  apply Prod.ext
  · exact endpointNormalization_source
  · exact endpointNormalization_target

/-- The actual comparison restriction sends the constructed raw element to
identity. -/
theorem restrictionHom_rawElement : restrictionHom rawElement = 1 := by
  apply Subtype.ext
  exact endpointNormalization

/-- The same raw element is nonidentity before comparison restriction. -/
theorem rawElement_ne_one : rawElement ≠ 1 := by
  intro equality
  have sourceEquality := congrArg (fun pair : RawComparison => pair.1.1) equality
  exact
    FiniteAxisFoldKernelExtendedPresentation.ambientComparisonElement_evaluation_source_ne_one
      (by simpa [rawElement] using sourceEquality)

/-- The presentation supplies an actual element of the restricted comparison
kernel.  Kernel membership is proved here rather than stored in the syntax. -/
noncomputable def element : restrictionHom.ker :=
  ⟨rawElement, by
    rw [MonoidHom.mem_ker]
    exact restrictionHom_rawElement⟩

/-- The source-constructed comparison restriction-kernel element is
nonidentity. -/
theorem element_ne_one : element ≠ 1 := by
  intro equality
  apply rawElement_ne_one
  exact congrArg Subtype.val equality

/-- The canonical-section lift over an arbitrary normalized comparison
element. -/
noncomputable def canonicalLift (t : NormalizedComparison) :
    AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t :=
  ⟨authoredExactCanonicalComparisonSectionHom
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t,
    authoredExactCanonicalComparisonSection_rightInverse
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t⟩

/-- Acting by the displayed kernel element gives a second lift over every
normalized comparison element. -/
noncomputable def shiftedLift (t : NormalizedComparison) :
    AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t :=
  MulOpposite.op element • canonicalLift t

/-- The displayed nontrivial kernel element acts nontrivially on the canonical
lift in every actual lift fiber. -/
theorem shiftedLift_ne_canonicalLift (t : NormalizedComparison) :
    shiftedLift t ≠ canonicalLift t := by
  intro equality
  change MulOpposite.op element • canonicalLift t = canonicalLift t at equality
  have actionEquality :
      MulOpposite.op element • canonicalLift t =
        (1 : restrictionHom.kerᵐᵒᵖ) • canonicalLift t := by
    simpa only [one_smul] using equality
  have kernelEquality :=
    authoredExactCanonicalComparisonLiftFiber_action_free
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t (canonicalLift t)
      actionEquality
  apply element_ne_one
  exact MulOpposite.op_injective kernelEquality

end FiniteAxisFoldComparisonRestrictionKernel

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
