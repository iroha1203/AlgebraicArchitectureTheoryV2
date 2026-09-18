import ResearchLean.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition
import Formal.Util.AssertStandardAxioms

/-!
# Full source-kernel exact decomposition

Source projection identifies the complete raw and normalized comparison groups
for the fixed `barAlpha` with the automorphism groups of their direct
endpoints.  Under these identifications, comparison restriction is exactly
direct-endpoint normalization.  Consequently the full comparison restriction
kernel is multiplicatively equivalent to the full direct normalization kernel.

The kernel equivalence is then carried through the Cycle 60 reconstruction,
giving explicit read and assembly maps, both inverse laws, and the transported
conjugation-twisted product in source-kernel coordinates.

## Implementation notes

The source kernel still consists of actual direct-endpoint automorphisms.  It
is not presented as primitive local syntax.  This module isolates the exact
remaining source-side object without treating a completed automorphism or
kernel membership as an authored local certificate.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction

noncomputable section

set_option maxHeartbeats 400000

namespace G122FullSourceKernelExactDecomposition

open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
open G122FullComparisonKernelDecomposition

local instance finiteAxisFoldSourceKernelAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The actual fixed `barAlpha` before normalization. -/
noncomputable abbrev actualBarAlphaIso :=
  authoredExactBarAlphaAdmissibleIsoAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- Source projection identifies the full raw comparison group with all
automorphisms of the actual direct endpoint. -/
noncomputable def rawComparisonSourceMulEquiv :
    RawComparison ≃* Aut finiteAxisFoldActualDirectAdmissibleGeometry :=
  generatedArrowComparisonSourceEquiv actualBarAlphaIso

/-- Normalization on automorphisms of the actual direct endpoint. -/
noncomputable def directNormalizationHom :
    Aut finiteAxisFoldActualDirectAdmissibleGeometry →*
      Aut FiniteAxisFoldNormalizedDirectGeometry :=
  AAT.AG.RealizationComparisonIdempotents.functorAutomorphismHom
    (geometryNormalizationFunctor.{0, 0} FiniteModel.carrier)
    finiteAxisFoldActualDirectAdmissibleGeometry

/-- Comparison restriction becomes direct-endpoint normalization after source
projection. -/
theorem source_restriction_commutes (raw : RawComparison) :
    normalizedComparisonSourceMulEquiv (restrictionHom raw) =
      directNormalizationHom (rawComparisonSourceMulEquiv raw) := by
  apply Iso.ext
  rfl

/-- The full kernel of direct-endpoint normalization. -/
noncomputable abbrev DirectNormalizationKernel := directNormalizationHom.ker

/-- Project a full comparison-kernel value to its source automorphism. -/
noncomputable def fullKernelToSourceKernelHom :
    FullKernel →* DirectNormalizationKernel where
  toFun kernelValue :=
    ⟨rawComparisonSourceMulEquiv kernelValue.1, by
      rw [MonoidHom.mem_ker]
      rw [← source_restriction_commutes]
      rw [MonoidHom.mem_ker.mp kernelValue.property]
      exact map_one normalizedComparisonSourceMulEquiv⟩
  map_one' := by
    apply Subtype.ext
    exact map_one rawComparisonSourceMulEquiv
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul rawComparisonSourceMulEquiv first.1 second.1

/-- Assemble a full comparison-kernel value from a source normalization-kernel
automorphism. -/
noncomputable def sourceKernelToFullKernelHom :
    DirectNormalizationKernel →* FullKernel where
  toFun sourceKernel :=
    ⟨rawComparisonSourceMulEquiv.symm sourceKernel.1, by
      rw [MonoidHom.mem_ker]
      apply normalizedComparisonSourceMulEquiv.injective
      rw [source_restriction_commutes]
      rw [rawComparisonSourceMulEquiv.apply_symm_apply]
      rw [MonoidHom.mem_ker.mp sourceKernel.property]
      simp⟩
  map_one' := by
    apply Subtype.ext
    exact map_one rawComparisonSourceMulEquiv.symm
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul rawComparisonSourceMulEquiv.symm first.1 second.1

/-- Reading after source-kernel assembly is identity. -/
theorem fullKernelToSourceKernel_sourceKernelToFullKernel
    (sourceKernel : DirectNormalizationKernel) :
    fullKernelToSourceKernelHom (sourceKernelToFullKernelHom sourceKernel) =
      sourceKernel := by
  apply Subtype.ext
  exact rawComparisonSourceMulEquiv.apply_symm_apply sourceKernel.1

/-- Source-kernel assembly after reading is identity. -/
theorem sourceKernelToFullKernel_fullKernelToSourceKernel
    (kernelValue : FullKernel) :
    sourceKernelToFullKernelHom (fullKernelToSourceKernelHom kernelValue) =
      kernelValue := by
  apply Subtype.ext
  exact rawComparisonSourceMulEquiv.symm_apply_apply kernelValue.1

/-- The full comparison restriction kernel is multiplicatively equivalent to
the full direct normalization kernel. -/
noncomputable def fullKernelSourceMulEquiv :
    FullKernel ≃* DirectNormalizationKernel where
  toFun := fullKernelToSourceKernelHom
  invFun := sourceKernelToFullKernelHom
  left_inv := sourceKernelToFullKernel_fullKernelToSourceKernel
  right_inv := fullKernelToSourceKernel_sourceKernelToFullKernel
  map_mul' := map_mul fullKernelToSourceKernelHom

/-- Source-kernel and normalized-source coordinates for every raw comparison. -/
abbrev FullSourceKernelCode :=
  DirectNormalizationKernelᵐᵒᵖ × Aut FiniteAxisFoldNormalizedDirectGeometry

/-- Assemble source-kernel coordinates through the full comparison kernel. -/
noncomputable def assembleSourceKernel (code : FullSourceKernelCode) :
    RawComparison :=
  assembleSource
    (MulOpposite.op
      (fullKernelSourceMulEquiv.symm (MulOpposite.unop code.1)), code.2)

/-- Read a raw comparison into source normalization-kernel coordinates. -/
noncomputable def readSourceKernel (raw : RawComparison) :
    FullSourceKernelCode :=
  (MulOpposite.op
      (fullKernelSourceMulEquiv (MulOpposite.unop (readSource raw).1)),
    (readSource raw).2)

/-- Reading after source-kernel assembly is identity. -/
theorem readSourceKernel_assembleSourceKernel (code : FullSourceKernelCode) :
    readSourceKernel (assembleSourceKernel code) = code := by
  simp [readSourceKernel, assembleSourceKernel, readSource_assembleSource]

/-- Source-kernel assembly after reading is identity on every raw comparison. -/
theorem assembleSourceKernel_readSourceKernel (raw : RawComparison) :
    assembleSourceKernel (readSourceKernel raw) = raw := by
  simp [assembleSourceKernel, readSourceKernel, assembleSource_readSource]

/-- Every raw comparison has explicit and unique source-kernel coordinates. -/
noncomputable def fullSourceKernelEquiv :
    FullSourceKernelCode ≃ RawComparison where
  toFun := assembleSourceKernel
  invFun := readSourceKernel
  left_inv := readSourceKernel_assembleSourceKernel
  right_inv := assembleSourceKernel_readSourceKernel

/-- Every raw comparison has one unique source normalization-kernel
displacement over its restricted normalized source automorphism. -/
theorem sourceKernelCoordinate_existsUnique (raw : RawComparison) :
    ∃! sourceKernel : DirectNormalizationKernelᵐᵒᵖ,
      assembleSourceKernel
          (sourceKernel,
            normalizedComparisonSourceMulEquiv (restrictionHom raw)) = raw := by
  refine ⟨(readSourceKernel raw).1, ?_, ?_⟩
  · change assembleSourceKernel (readSourceKernel raw) = raw
    exact assembleSourceKernel_readSourceKernel raw
  · intro candidate equality
    have codeEquality := congrArg readSourceKernel equality
    rw [readSourceKernel_assembleSourceKernel] at codeEquality
    exact congrArg Prod.fst codeEquality

/-- The Cycle 60 twisted product transported to source-kernel coordinates. -/
theorem assembleSourceKernel_mul_formula
    (first second : FullSourceKernelCode) :
    assembleSourceKernel first * assembleSourceKernel second =
      canonicalSectionHom
          (normalizedComparisonSourceMulEquiv.symm (first.2 * second.2)) *
        ((canonicalSectionHom
            (normalizedComparisonSourceMulEquiv.symm second.2))⁻¹ *
          (sourceKernelToFullKernelHom (MulOpposite.unop first.1)).1 *
          canonicalSectionHom
            (normalizedComparisonSourceMulEquiv.symm second.2) *
          (sourceKernelToFullKernelHom (MulOpposite.unop second.1)).1) := by
  change
    (canonicalSectionHom (normalizedComparisonSourceMulEquiv.symm first.2) *
        (sourceKernelToFullKernelHom (MulOpposite.unop first.1)).1) *
      (canonicalSectionHom (normalizedComparisonSourceMulEquiv.symm second.2) *
        (sourceKernelToFullKernelHom (MulOpposite.unop second.1)).1) = _
  rw [map_mul, map_mul]
  group

end G122FullSourceKernelExactDecomposition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition

end

end AAT.AG.LocalSemanticReconstruction
