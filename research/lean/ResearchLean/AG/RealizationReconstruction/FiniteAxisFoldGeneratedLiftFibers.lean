import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldAxisSwapPresentation
import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalComparisonExactness
import Formal.Util.AssertStandardAxioms

/-!
# Generated canonical lifts and every actual lift in the six fixed fibers

Each of the six primitive `Fin 3` axis permutations has a generated raw
comparison whose evaluation is the actual canonical section.  This module
packages that value in the corresponding actual normalization lift fiber and
uses the full actual restricted kernel torsor theorem to classify every other
actual lift in the same fiber by a unique displacement.

This retains all actual lifts above each mandated finite value.  It does not
claim that the current generated presentation represents every kernel element
or every normalized comparison value.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

local instance finiteAxisFoldGeneratedLiftFiberAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace FiniteAxisFoldGeneratedLiftFibers

open FiniteAxisFoldAxisSwapPresentation

/-- The generated evaluation, packaged as the canonical actual raw lift over
the normalized comparison belonging to one primitive axis permutation. -/
noncomputable def canonicalLift (permutation : Equiv.Perm (Fin 3)) :
    AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible
      (finiteAxisFoldNormalizedComparisonPermutation permutation) :=
  ⟨comparisonEvaluationHom
      (sectionedAxisPermutationComparisonElement permutation), by
    rw [sectionedAxisPermutationComparisonElement_evaluation]
    exact authoredExactCanonicalComparisonSection_rightInverse
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible
      (finiteAxisFoldNormalizedComparisonPermutation permutation)⟩

/-- The underlying raw comparison is exactly the actual canonical section,
including both endpoints. -/
theorem canonicalLift_val (permutation : Equiv.Perm (Fin 3)) :
    (canonicalLift permutation).1 =
      authoredExactCanonicalComparisonSectionHom
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible
        (finiteAxisFoldNormalizedComparisonPermutation permutation) :=
  sectionedAxisPermutationComparisonElement_evaluation permutation

/-- Every actual lift above the same fixed normalized comparison is reached
from the generated canonical lift by a unique element of the full actual
restricted kernel. -/
theorem everyLift_unique_kernel_displacement
    (permutation : Equiv.Perm (Fin 3))
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible
      (finiteAxisFoldNormalizedComparisonPermutation permutation)) :
    ∃! kernelValue :
        (FiniteAxisFoldComparisonRestrictionKernel.restrictionHom.ker)ᵐᵒᵖ,
      kernelValue • canonicalLift permutation = lift :=
  authoredExactCanonicalComparisonLiftFiber_existsUnique_smul_eq
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible
    (finiteAxisFoldNormalizedComparisonPermutation permutation)
    (canonicalLift permutation) lift

end FiniteAxisFoldGeneratedLiftFibers

end


#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
