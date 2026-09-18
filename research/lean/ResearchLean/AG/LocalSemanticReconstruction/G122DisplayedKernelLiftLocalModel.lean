import ResearchLean.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldBottomKernelInvolution
import Formal.Util.AssertStandardAxioms

/-!
# Displayed kernel-code reconstruction on G-122 lift fibers

This module adds an independent kernel-displacement code to the accepted
four-component comparison code.  The two Boolean codes evaluate to identity
and to the source-constructed nontrivial involution in the full actual
comparison restriction kernel.  Their actions cut out the canonical and
shifted points in every represented lift fiber.

The actual two-point orbit separates the Boolean codes and admits read and
assemble maps inverse in both directions.  Boolean xor is proved compatible
with multiplication in the actual full kernel and hence with iterated action
on lifts.  Finally, comparison-code uniqueness, displayed-orbit code
uniqueness, and the ambient full-kernel torsor are stated together for the
same represented fiber.

## Implementation notes

The kernel code is one bit.  It stores no actual kernel value, lift, orbit
witness, or range proof.  Its nontrivial evaluation is the source-constructed
restriction-kernel element, whose nonidentity and square law are proved in the
accepted realization chain.  This module reconstructs that displayed `C₂`
fragment; it does not claim an independent local presentation of the entire
restriction kernel or every point of the full lift fiber.
-/

namespace AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction
open MulAction Set Subgroup

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance cycle53AtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

open G122FourComponentComparisonLocalModel
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
open AAT.AG.RealizationReconstruction.FiniteAxisFoldBottomKernelInvolution

/-- The source-constructed element is an involution already in the full
comparison restriction kernel. -/
theorem restrictionKernelElement_mul_self :
    element * element = 1 := by
  apply Subtype.ext
  exact rawElement_mul_self

/-- Independent two-case syntax for the displayed kernel displacement. -/
abbrev KernelCode := Bool

/-- Evaluate one bit into the actual full comparison restriction kernel. -/
noncomputable def kernelValue (code : KernelCode) : restrictionHom.kerᵐᵒᵖ :=
  if code then MulOpposite.op element else 1

/-- The false code evaluates to identity. -/
@[simp] theorem kernelValue_false : kernelValue false = 1 := rfl

/-- The true code evaluates to the displayed nonidentity kernel element. -/
@[simp] theorem kernelValue_true :
    kernelValue true = MulOpposite.op element := rfl

/-- The two independent codes are separated by their actual kernel values. -/
theorem kernelValue_injective : Function.Injective kernelValue := by
  intro first second equality
  cases first <;> cases second
  · rfl
  · exfalso
    apply element_ne_one
    exact MulOpposite.op_injective equality.symm
  · exfalso
    apply element_ne_one
    exact MulOpposite.op_injective equality
  · rfl

/-- Boolean xor is the source composition law for the displayed `C₂`. -/
theorem kernelValue_xor (first second : KernelCode) :
    kernelValue (xor first second) = kernelValue first * kernelValue second := by
  cases first <;> cases second
  · simp
  · simp
  · simp
  · apply MulOpposite.unop_injective
    simp [restrictionKernelElement_mul_self]

/-- The actual lift fiber over one represented four-component comparison. -/
abbrev LiftFiber (comparison : LocalComparisonImage) :=
  AuthoredExactCanonicalComparisonLiftFiber
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible comparison.1

/-- Evaluate a kernel code by acting on the actual canonical lift. -/
noncomputable def displayedLift
    (comparison : LocalComparisonImage) (code : KernelCode) :
    LiftFiber comparison :=
  kernelValue code • G122FourComponentComparisonLocalModel.canonicalLift comparison

/-- The false code is exactly the canonical lift. -/
@[simp] theorem displayedLift_false (comparison : LocalComparisonImage) :
    displayedLift comparison false =
      G122FourComponentComparisonLocalModel.canonicalLift comparison := by
  simp [displayedLift]

/-- The true code is the shift by the source-constructed actual kernel
involution. -/
theorem displayedLift_true (comparison : LocalComparisonImage) :
    displayedLift comparison true =
      MulOpposite.op element •
        G122FourComponentComparisonLocalModel.canonicalLift comparison := by
  rfl

/-- Actual action on the canonical lift separates the two Boolean codes. -/
theorem displayedLift_injective (comparison : LocalComparisonImage) :
    Function.Injective (displayedLift comparison) := by
  intro first second equality
  apply kernelValue_injective
  exact authoredExactCanonicalComparisonLiftFiber_action_free
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible comparison.1
    (G122FourComponentComparisonLocalModel.canonicalLift comparison) equality

/-- The displayed shifted lift is genuinely distinct from the canonical
point in every represented fiber. -/
theorem displayedLift_true_ne_false (comparison : LocalComparisonImage) :
    displayedLift comparison true ≠ displayedLift comparison false := by
  intro equality
  cases displayedLift_injective comparison equality

/-- Boolean composition agrees with iterated actual kernel action on the
canonical lift. -/
theorem displayedLift_xor (comparison : LocalComparisonImage)
    (first second : KernelCode) :
    displayedLift comparison (xor first second) =
      kernelValue first • displayedLift comparison second := by
  rw [displayedLift, displayedLift, ← mul_smul, kernelValue_xor]

/-- The actual two-point orbit represented by the independent kernel code. -/
abbrev DisplayedLiftImage (comparison : LocalComparisonImage) :=
  Set.range (displayedLift comparison)

/-- Assemble one independent kernel code into the displayed actual orbit. -/
noncomputable def assembleDisplayed (comparison : LocalComparisonImage)
    (code : KernelCode) : DisplayedLiftImage comparison :=
  ⟨displayedLift comparison code, ⟨code, rfl⟩⟩

/-- Every displayed orbit point has exactly one Boolean code. -/
theorem displayedCode_existsUnique
    (comparison : LocalComparisonImage)
    (lift : DisplayedLiftImage comparison) :
    ∃! code : KernelCode,
      displayedLift comparison code = lift.1 := by
  rcases lift with ⟨lift, code, rfl⟩
  refine ⟨code, rfl, ?_⟩
  intro candidate equality
  exact displayedLift_injective comparison equality

/-- Read the unique independent code from an actual displayed orbit point. -/
noncomputable def readDisplayed (comparison : LocalComparisonImage)
    (lift : DisplayedLiftImage comparison) : KernelCode :=
  Classical.choose (displayedCode_existsUnique comparison lift)

/-- Any code evaluating to the observed lift is the recovered code. -/
theorem readDisplayed_unique (comparison : LocalComparisonImage)
    (lift : DisplayedLiftImage comparison) (code : KernelCode)
    (equality : displayedLift comparison code = lift.1) :
    code = readDisplayed comparison lift :=
  (Classical.choose_spec (displayedCode_existsUnique comparison lift)).2
    code equality

/-- Reading after assembly recovers every independent kernel code. -/
@[simp] theorem readDisplayed_assembleDisplayed
    (comparison : LocalComparisonImage) (code : KernelCode) :
    readDisplayed comparison (assembleDisplayed comparison code) = code := by
  exact (readDisplayed_unique comparison
    (assembleDisplayed comparison code) code rfl).symm

/-- Assembly after reading recovers every actual displayed orbit point. -/
@[simp] theorem assembleDisplayed_readDisplayed
    (comparison : LocalComparisonImage)
    (lift : DisplayedLiftImage comparison) :
    assembleDisplayed comparison (readDisplayed comparison lift) = lift := by
  apply Subtype.ext
  exact (Classical.choose_spec
    (displayedCode_existsUnique comparison lift)).1

/-- Two-sided reconstruction of the actual displayed lift orbit. -/
noncomputable def displayedLiftEquiv (comparison : LocalComparisonImage) :
    KernelCode ≃ DisplayedLiftImage comparison where
  toFun := assembleDisplayed comparison
  invFun := readDisplayed comparison
  left_inv := readDisplayed_assembleDisplayed comparison
  right_inv := assembleDisplayed_readDisplayed comparison

/-- Every represented comparison has exactly one four-component source code. -/
theorem comparisonCode_existsUnique (comparison : LocalComparisonImage) :
    ∃! code : LocalCode, assemble code = comparison := by
  refine ⟨read comparison, assemble_read comparison, ?_⟩
  intro candidate equality
  exact localComparisonEquiv.injective
    (equality.trans (assemble_read comparison).symm)

/-- Comparison code and displayed kernel code are simultaneously unique for
the same represented fiber and actual displayed lift. -/
theorem comparisonAndDisplayedLift_unique_codes
    (comparison : LocalComparisonImage)
    (lift : DisplayedLiftImage comparison) :
    (∃! comparisonCode : LocalCode,
      assemble comparisonCode = comparison) ∧
    (∃! kernelCode : KernelCode,
      assembleDisplayed comparison kernelCode = lift) := by
  refine ⟨comparisonCode_existsUnique comparison, ?_⟩
  refine ⟨readDisplayed comparison lift,
    assembleDisplayed_readDisplayed comparison lift, ?_⟩
  intro candidate equality
  exact displayedLiftEquiv comparison |>.injective
    (equality.trans
      (assembleDisplayed_readDisplayed comparison lift).symm)

/-- The displayed orbit is contained in the same full actual lift fiber on
which the full restriction kernel acts simply transitively. -/
theorem displayedOrbit_and_fullKernel_reconstruction
    (comparison : LocalComparisonImage)
    (displayed : DisplayedLiftImage comparison)
    (lift : LiftFiber comparison) :
    (∃! comparisonCode : LocalCode,
      assemble comparisonCode = comparison) ∧
    (∃! kernelCode : KernelCode,
      assembleDisplayed comparison kernelCode = displayed) ∧
    (∃! fullKernelValue : restrictionHom.kerᵐᵒᵖ,
      fullKernelValue •
        G122FourComponentComparisonLocalModel.canonicalLift comparison = lift) :=
  ⟨comparisonCode_existsUnique comparison,
    (comparisonAndDisplayedLift_unique_codes comparison displayed).2,
    everyLift_unique_kernel_displacement comparison lift⟩

end
end AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel
