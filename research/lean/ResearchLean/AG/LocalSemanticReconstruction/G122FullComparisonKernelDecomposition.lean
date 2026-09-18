import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNormalizedAxisProjection
import Formal.Util.AssertStandardAxioms

/-!
# Full comparison reconstruction from normalization and the full kernel

Every raw comparison-preserving change for the fixed normalized `barAlpha` is
reconstructed from its normalized comparison and one unique displacement in
the full actual restriction kernel.  The reading and assembly maps are
explicit, satisfy both inverse laws, and expose the conjugation-twisted kernel
formula for multiplication.

This classifies the full raw comparison group relative to its full restriction
kernel.  It does not independently present every kernel element by primitive
local syntax.

## Implementation notes

The kernel coordinate is taken in the opposite group because assembly uses
right multiplication on the canonical section lift.  Keeping the ordinary
product group would reverse the kernel multiplication and obscure the action
law.  The reconstruction is therefore exposed as a type equivalence, while a
separate theorem records its conjugation-twisted multiplication; declaring the
ordinary product to be multiplicative would state the wrong group law.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction

noncomputable section

namespace G122FullComparisonKernelDecomposition

open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldRestrictionKernelAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The fixed canonical section from the full normalized comparison group to
the full raw comparison group. -/
noncomputable abbrev canonicalSectionHom :
    NormalizedComparison →* RawComparison :=
  authoredExactCanonicalComparisonSectionHom
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The full restriction kernel, retained independently from the normalized
comparison component. -/
noncomputable abbrev FullKernel := restrictionHom.ker

/-- Source data for the full relative reconstruction.  The kernel is opposite
because it acts on a canonical lift by right multiplication. -/
abbrev FullComparisonCode := FullKernelᵐᵒᵖ × NormalizedComparison

/-- The canonical section is a right inverse of restriction on every full
normalized comparison. -/
theorem restriction_canonicalSection (normalized : NormalizedComparison) :
    restrictionHom (canonicalSectionHom normalized) = normalized :=
  authoredExactCanonicalComparisonSection_rightInverse
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible normalized

/-- Assemble a full raw comparison by right-displacing its canonical lift. -/
noncomputable def assemble (code : FullComparisonCode) : RawComparison :=
  canonicalSectionHom code.2 * (MulOpposite.unop code.1).1

/-- The residual displacement of a raw comparison from the canonical lift of
its normalization lies in the full restriction kernel. -/
theorem readKernel_mem (raw : RawComparison) :
    (canonicalSectionHom (restrictionHom raw))⁻¹ * raw ∈ FullKernel := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, restriction_canonicalSection]
  simp

/-- Read the full normalized comparison and its unique right-kernel
displacement from a raw comparison. -/
noncomputable def read (raw : RawComparison) : FullComparisonCode :=
  (MulOpposite.op
      (⟨(canonicalSectionHom (restrictionHom raw))⁻¹ * raw,
        readKernel_mem raw⟩ : FullKernel),
    restrictionHom raw)

/-- Reading after assembly recovers the normalized component. -/
theorem read_assemble_normalized (code : FullComparisonCode) :
    (read (assemble code)).2 = code.2 := by
  simp [read, assemble, restriction_canonicalSection,
    MonoidHom.mem_ker.mp (MulOpposite.unop code.1).property]

/-- Reading after assembly recovers the full kernel displacement. -/
theorem read_assemble_kernel (code : FullComparisonCode) :
    (read (assemble code)).1 = code.1 := by
  apply MulOpposite.unop_injective
  apply Subtype.ext
  change
    (canonicalSectionHom
      (restrictionHom
        (canonicalSectionHom code.2 * (MulOpposite.unop code.1).1)))⁻¹ *
        (canonicalSectionHom code.2 * (MulOpposite.unop code.1).1) =
      (MulOpposite.unop code.1).1
  rw [map_mul, restriction_canonicalSection,
    MonoidHom.mem_ker.mp (MulOpposite.unop code.1).property, mul_one]
  simp

/-- Reading after assembly is identity on the full relative code. -/
theorem read_assemble (code : FullComparisonCode) :
    read (assemble code) = code := by
  apply Prod.ext
  · exact read_assemble_kernel code
  · exact read_assemble_normalized code

/-- Assembly after reading is identity on every full raw comparison. -/
theorem assemble_read (raw : RawComparison) :
    assemble (read raw) = raw := by
  simp [assemble, read]

/-- The full raw comparison group is explicitly equivalent, as a type, to its
full normalized comparison and unique full-kernel displacement. -/
noncomputable def fullComparisonEquiv : FullComparisonCode ≃ RawComparison where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- The normalized comparison factor is exactly the automorphism group of the
normalized direct endpoint; its target component is forced by conjugation. -/
noncomputable def normalizedComparisonSourceMulEquiv :
    NormalizedComparison ≃* Aut FiniteAxisFoldNormalizedDirectGeometry :=
  generatedArrowComparisonSourceEquiv finiteAxisFoldNormalizedBarAlphaIso

/-- Source-automorphism coordinates for the full comparison reconstruction. -/
abbrev FullComparisonSourceCode :=
  FullKernelᵐᵒᵖ × Aut FiniteAxisFoldNormalizedDirectGeometry

/-- Assemble source-automorphism coordinates into a full raw comparison. -/
noncomputable def assembleSource (code : FullComparisonSourceCode) :
    RawComparison :=
  assemble (code.1, normalizedComparisonSourceMulEquiv.symm code.2)

/-- Read a full raw comparison into its unique kernel displacement and its
normalized direct-endpoint source automorphism. -/
noncomputable def readSource (raw : RawComparison) : FullComparisonSourceCode :=
  ((read raw).1, normalizedComparisonSourceMulEquiv (read raw).2)

/-- Source reading after source assembly is identity. -/
theorem readSource_assembleSource (code : FullComparisonSourceCode) :
    readSource (assembleSource code) = code := by
  simp [readSource, assembleSource, read_assemble]

/-- Source assembly after source reading is identity on every raw comparison. -/
theorem assembleSource_readSource (raw : RawComparison) :
    assembleSource (readSource raw) = raw := by
  simp [assembleSource, readSource, assemble_read]

/-- The full raw comparison group is reconstructed from the full kernel and
the normalized direct-endpoint source automorphism, with explicit inverses. -/
noncomputable def fullComparisonSourceEquiv :
    FullComparisonSourceCode ≃ RawComparison where
  toFun := assembleSource
  invFun := readSource
  left_inv := readSource_assembleSource
  right_inv := assembleSource_readSource

/-- Multiplying assembled values yields the conjugation-twisted kernel law.
This is the noncommutative content hidden by the underlying type equivalence. -/
theorem assemble_mul_formula (first second : FullComparisonCode) :
    assemble first * assemble second =
      canonicalSectionHom (first.2 * second.2) *
        ((canonicalSectionHom second.2)⁻¹ *
          (MulOpposite.unop first.1).1 *
          canonicalSectionHom second.2 *
          (MulOpposite.unop second.1).1) := by
  simp only [assemble, map_mul]
  group

/-- Reading a product exposes the product normalized value. -/
theorem read_mul_normalized (first second : RawComparison) :
    (read (first * second)).2 =
      (read first).2 * (read second).2 := by
  simp [read]

/-- Reading a product exposes the conjugation-twisted full-kernel value. -/
theorem read_mul_kernel (first second : RawComparison) :
    (MulOpposite.unop (read (first * second)).1).1 =
      (canonicalSectionHom (read second).2)⁻¹ *
        (MulOpposite.unop (read first).1).1 *
        canonicalSectionHom (read second).2 *
        (MulOpposite.unop (read second).1).1 := by
  change
    (canonicalSectionHom (restrictionHom (first * second)))⁻¹ *
        (first * second) =
      (canonicalSectionHom (restrictionHom second))⁻¹ *
        ((canonicalSectionHom (restrictionHom first))⁻¹ * first) *
        canonicalSectionHom (restrictionHom second) *
        ((canonicalSectionHom (restrictionHom second))⁻¹ * second)
  rw [map_mul, map_mul]
  group

/-- The read kernel is the unique displacement taking the canonical lift to a
given raw comparison over its normalization. -/
theorem readKernel_existsUnique (raw : RawComparison) :
    ∃! kernelValue : FullKernelᵐᵒᵖ,
      canonicalSectionHom (restrictionHom raw) *
          (MulOpposite.unop kernelValue).1 = raw := by
  refine ⟨(read raw).1, ?_, ?_⟩
  · exact assemble_read raw
  · intro candidate equality
    apply MulOpposite.unop_injective
    apply Subtype.ext
    apply mul_left_cancel
      (a := canonicalSectionHom (restrictionHom raw))
    exact equality.trans (assemble_read raw).symm

/-- Every full lift fiber is reconstructed by one unique full-kernel
displacement from its canonical section point. -/
theorem fullLiftFiber_existsUnique_kernel
    (normalized : NormalizedComparison)
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible normalized) :
    ∃! kernelValue : FullKernelᵐᵒᵖ,
      kernelValue • canonicalLift normalized = lift := by
  exact authoredExactCanonicalComparisonLiftFiber_existsUnique_smul_eq
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible
    normalized (canonicalLift normalized) lift

end G122FullComparisonKernelDecomposition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition

end

end AAT.AG.LocalSemanticReconstruction
