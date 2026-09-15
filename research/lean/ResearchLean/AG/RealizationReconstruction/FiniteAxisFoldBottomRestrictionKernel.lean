import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalBottomComparison
import Formal.Util.AssertStandardAxioms

/-!
# The displayed restriction-kernel element is bottom and coefficient trivial

Cycle 60 placed the source-displayed finite-axis-fold comparison pair in the
actual restriction kernel.  This file follows that same pair through the raw
bottom projections and coefficient maps at both endpoints.  The source
identities come from the fixed ambient recipe.  Target bottom identity is
forced by the raw `barAlpha` comparison square and its inverse; target
coefficient identity uses that the mandated coefficient ring is `Int`.

The pair therefore gives a nontrivial element of the bottom-qualified
comparison restriction kernel.  Acting by it produces a distinct second lift
over every bottom-qualified normalized comparison element.  This is one
displayed kernel generator in every such fiber, not a presentation of all
bottom-qualified kernel elements or all lifts.

## Implementation notes

Bottom and coefficient target identities are conclusions.  Neither is stored
in the syntax or in a certificate.  The bottom proof maps the already
established raw comparison equation through the bottom functor and cancels the
exact `barAlpha` image.  The coefficient proof uses the initiality theorem for
ring homomorphisms out of the fixed coefficient ring `Int`.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 100000

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldBottomKernelAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace FiniteAxisFoldBottomRestrictionKernel

open FiniteAxisFoldComparisonRestrictionKernel

/-- The source endpoint of the displayed restricted-kernel element is
bottom-trivial. -/
theorem rawElement_source_bottom :
    rawGeometryBottomAutomorphismHom
      (authoredExactDirectAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      rawElement.1.1 = 1 := by
  rw [rawElement,
    FiniteAxisFoldKernelExtendedPresentation.ambientComparisonElement_evaluation_source]
  exact (authoredExactAmbientKernelComparisonPair_raw_bottom
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible).1

/-- The raw comparison equation transports source bottom-triviality to the
target endpoint. -/
theorem rawElement_target_bottom :
    rawGeometryBottomAutomorphismHom
      (authoredExactViaBaseAdmissibleGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      rawElement.1.2 = 1 := by
  let c := authoredExactBarAlphaAdmissibleIsoAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible
  let F := rawGeometryBottomProjection.{0, 0}
    finiteAxisFoldG122FamilyInput.Carrier
  have mapped := congrArg (fun f => F.map f) rawElement.2
  have sourceIdentity :
      (F.mapIso rawElement.1.1).hom = 𝟙 _ :=
    congrArg Iso.hom rawElement_source_bottom
  have reduced : F.map c.hom = F.map c.hom ≫ (F.mapIso rawElement.1.2).hom := by
    simpa [F, c, sourceIdentity, Functor.map_comp] using mapped
  have cancelled := congrArg (fun f => F.map c.inv ≫ f) reduced
  apply Iso.ext
  simpa [F, c, Functor.map_comp] using cancelled.symm

/-- The source coefficient map of the same displayed kernel pair is identity. -/
theorem rawElement_source_coefficient :
    rawElement.1.1.hom.hom.geometry.coefficientHom = RingHom.id Int := by
  rw [rawElement,
    FiniteAxisFoldKernelExtendedPresentation.ambientComparisonElement_evaluation_source]
  exact authoredExactAmbientKernelComparisonPair_fst_hom_coefficientHom
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- Every target coefficient map on the mandated `Int` coefficient ring is
identity. -/
theorem rawElement_target_coefficient :
    rawElement.1.2.hom.hom.geometry.coefficientHom = RingHom.id Int := by
  exact RingHom.ext_int _ _

/-- The exact bottom-qualified raw comparison group for the fixed input. -/
noncomputable abbrev RawBottomComparison :=
  AuthoredExactCanonicalRawBottomComparisonSubgroup
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The exact bottom-qualified normalized comparison group. -/
noncomputable abbrev NormalizedBottomComparison :=
  AuthoredExactCanonicalNormalizedBottomComparisonSubgroup
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The actual bottom-qualified comparison restriction homomorphism. -/
noncomputable abbrev bottomRestrictionHom :
    RawBottomComparison →* NormalizedBottomComparison :=
  geometryNormalizationBottomQualifiedComparisonSubgroupHom
    (authoredExactBarAlphaAdmissibleIsoAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible).hom

/-- The same source-displayed raw pair, now carrying its proved two-ended
bottom qualification. -/
noncomputable def bottomRawElement : RawBottomComparison :=
  ⟨rawElement, (mem_rawGeometryBottomQualifiedComparisonSubgroup).2
    ⟨rawElement_source_bottom, rawElement_target_bottom⟩⟩

/-- Bottom-qualified restriction still erases the displayed raw element. -/
theorem bottomRestrictionHom_bottomRawElement :
    bottomRestrictionHom bottomRawElement = 1 := by
  apply Subtype.ext
  exact restrictionHom_rawElement

/-- The bottom-qualified raw element remains nonidentity. -/
theorem bottomRawElement_ne_one : bottomRawElement ≠ 1 := by
  intro equality
  apply rawElement_ne_one
  exact congrArg Subtype.val equality

/-- The same presentation-derived element in the actual bottom-qualified
restriction kernel. -/
noncomputable def element : bottomRestrictionHom.ker :=
  ⟨bottomRawElement, by
    rw [MonoidHom.mem_ker]
    exact bottomRestrictionHom_bottomRawElement⟩

/-- The bottom-qualified restriction-kernel element is nonidentity. -/
theorem element_ne_one : element ≠ 1 := by
  intro equality
  apply bottomRawElement_ne_one
  exact congrArg Subtype.val equality

/-- The same pair simultaneously fixes bottom and coefficient components at
both endpoints. -/
theorem bottom_coefficient_packet :
    rawGeometryBottomAutomorphismHom
        (authoredExactDirectAdmissibleGeometryAt
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible)
        rawElement.1.1 = 1 ∧
      rawElement.1.1.hom.hom.geometry.coefficientHom = RingHom.id Int ∧
      rawGeometryBottomAutomorphismHom
        (authoredExactViaBaseAdmissibleGeometryAt
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible)
        rawElement.1.2 = 1 ∧
      rawElement.1.2.hom.hom.geometry.coefficientHom = RingHom.id Int :=
  ⟨rawElement_source_bottom, rawElement_source_coefficient,
    rawElement_target_bottom, rawElement_target_coefficient⟩

/-- The canonical bottom-qualified section lift over an arbitrary normalized
bottom comparison element. -/
noncomputable def canonicalLift (t : NormalizedBottomComparison) :
    AuthoredExactCanonicalBottomComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t :=
  ⟨authoredExactCanonicalBottomComparisonSectionHom
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t,
    authoredExactCanonicalBottomComparisonSection_rightInverse
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t⟩

/-- Shift the canonical bottom-qualified lift by the displayed kernel
element. -/
noncomputable def shiftedLift (t : NormalizedBottomComparison) :
    AuthoredExactCanonicalBottomComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t :=
  MulOpposite.op element • canonicalLift t

/-- The displayed bottom-qualified kernel element acts nontrivially in every
bottom-qualified lift fiber. -/
theorem shiftedLift_ne_canonicalLift (t : NormalizedBottomComparison) :
    shiftedLift t ≠ canonicalLift t := by
  intro equality
  change MulOpposite.op element • canonicalLift t = canonicalLift t at equality
  have actionEquality :
      MulOpposite.op element • canonicalLift t =
        (1 : bottomRestrictionHom.kerᵐᵒᵖ) • canonicalLift t := by
    simpa only [one_smul] using equality
  have kernelEquality :=
    authoredExactCanonicalBottomComparisonLiftFiber_action_free
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible t (canonicalLift t)
      actionEquality
  apply element_ne_one
  exact MulOpposite.op_injective kernelEquality

end FiniteAxisFoldBottomRestrictionKernel

end


end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
