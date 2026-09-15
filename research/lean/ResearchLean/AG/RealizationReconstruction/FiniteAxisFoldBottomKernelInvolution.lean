import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldBottomRestrictionKernel
import Formal.Util.AssertStandardAxioms

/-!
# The displayed bottom restriction-kernel generator is an involution

Cycle 61 placed one source-displayed nonidentity element in the actual
bottom-qualified comparison restriction kernel.  This file transports the
source congruence saying that the ambient leaf squares to identity through
the displayed comparison section, the decoder, and both restriction
subgroups.  Thus the same constructed kernel element has order two.

Consequently, in every bottom-qualified lift fiber, the canonical lift and
its shift by this element are two distinct points, and shifting the latter once
more returns to the canonical lift.  This file does not define the generated
subgroup orbit or assert that the generator exhausts the full restriction
kernel or that these two points exhaust the full lift fiber.

## Implementation notes

The order-two proof starts at the source-generated quotient relation
`ambientDirect_sq`.  No semantic automorphism, kernel element, or completed
lift family is accepted as an input.  The two-point cardinality is derived
from the already proved nonidentity action, not installed as a certificate.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 100000

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldBottomKernelInvolutionAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace FiniteAxisFoldBottomKernelInvolution

open FiniteAxisFoldKernelExtendedPresentation
open FiniteAxisFoldComparisonRestrictionKernel
open FiniteAxisFoldBottomRestrictionKernel

/-- The displayed direct ambient automorphism squares to identity by the
source-generated congruence, before decoding. -/
theorem directAmbientAut_mul_self :
    directAmbientAut * directAmbientAut = 1 := by
  apply Iso.ext
  exact Quotient.sound
    FiniteAxisFoldKernelExtendedSyntax.Congruent.ambientDirect_sq

/-- The comparison pair constructed by source conjugation is an involution
inside the displayed comparison group. -/
theorem ambientComparisonElement_mul_self :
    ambientComparisonElement * ambientComparisonElement = 1 := by
  rw [ambientComparisonElement]
  rw [← map_mul]
  rw [directAmbientAut_mul_self, map_one]

/-- Evaluation preserves the source-proved order-two equation. -/
theorem rawElement_mul_self : rawElement * rawElement = 1 := by
  rw [rawElement, ← map_mul, ambientComparisonElement_mul_self, map_one]

/-- Bottom qualification retains the same order-two raw pair. -/
theorem bottomRawElement_mul_self : bottomRawElement * bottomRawElement = 1 := by
  apply Subtype.ext
  exact rawElement_mul_self

/-- The actual bottom-qualified restriction-kernel element supplied by the
presentation is a nontrivial involution. -/
theorem element_mul_self :
    FiniteAxisFoldBottomRestrictionKernel.element *
      FiniteAxisFoldBottomRestrictionKernel.element = 1 := by
  apply Subtype.ext
  exact bottomRawElement_mul_self

/-- Shifting a canonical lift twice by the displayed involution returns to
the original canonical lift. -/
theorem shifted_twice_eq_canonicalLift (t : NormalizedBottomComparison) :
    MulOpposite.op FiniteAxisFoldBottomRestrictionKernel.element •
        FiniteAxisFoldBottomRestrictionKernel.shiftedLift t =
      FiniteAxisFoldBottomRestrictionKernel.canonicalLift t := by
  apply Subtype.ext
  change
    (FiniteAxisFoldBottomRestrictionKernel.canonicalLift t).1 *
          bottomRawElement * bottomRawElement =
      (FiniteAxisFoldBottomRestrictionKernel.canonicalLift t).1
  rw [mul_assoc, bottomRawElement_mul_self, mul_one]

/-- The two explicitly constructed points in a bottom-qualified lift fiber. -/
noncomputable def canonicalShiftedPair (t : NormalizedBottomComparison) :
    Finset (AuthoredExactCanonicalBottomComparisonLiftFiber
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible t) := by
  classical
  exact {FiniteAxisFoldBottomRestrictionKernel.canonicalLift t,
    FiniteAxisFoldBottomRestrictionKernel.shiftedLift t}

/-- The displayed involution cuts out two distinct, explicitly constructed
points in every bottom-qualified lift fiber. -/
theorem canonical_shifted_pair_card (t : NormalizedBottomComparison) :
    (canonicalShiftedPair t).card = 2 := by
  classical
  rw [canonicalShiftedPair]
  rw [Finset.card_pair]
  exact (FiniteAxisFoldBottomRestrictionKernel.shiftedLift_ne_canonicalLift t).symm

end FiniteAxisFoldBottomKernelInvolution

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
