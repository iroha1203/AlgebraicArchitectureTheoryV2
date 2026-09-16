import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPermutationImageSeparation
import Formal.Util.AssertStandardAxioms

/-!
# Intrinsic image of a fixed finite Extension-permutation family

For a fixed independently supplied finite carrier `E`, this file packages a
source table as its own group-valued syntax.  The syntax is not a semantic
range: it contains exactly one primitive permutation table and inherits its
group law directly from table composition.

The corresponding subgroup of the actual local-fiber kernel is characterized
by the complete stored-backward context action.  An actual residual element
belongs precisely when that observable action is induced by one independent
table code.  Faithfulness of the full stored-backward projection then proves
that the table decoder is an equivalence onto this action-characterized
subgroup.  Full local-kernel coverage remains a separate question.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- Independent fixed-carrier source syntax: one complete permutation table,
not an element of a semantic image or range. -/
@[ext] structure FiniteAxisFoldExtensionPermutationCode (E : Type) where
  table : Equiv.Perm E

namespace FiniteAxisFoldExtensionPermutationCode

variable {E : Type}

instance : One (FiniteAxisFoldExtensionPermutationCode E) :=
  ⟨⟨1⟩⟩

instance : Mul (FiniteAxisFoldExtensionPermutationCode E) :=
  ⟨fun first second => ⟨first.table * second.table⟩⟩

instance : Inv (FiniteAxisFoldExtensionPermutationCode E) :=
  ⟨fun code => ⟨code.table⁻¹⟩⟩

/-- The independent table syntax has the ordinary permutation group law. -/
instance : Group (FiniteAxisFoldExtensionPermutationCode E) where
  mul_assoc first second third :=
    congrArg FiniteAxisFoldExtensionPermutationCode.mk
      (mul_assoc first.table second.table third.table)
  one_mul code :=
    congrArg FiniteAxisFoldExtensionPermutationCode.mk
      (one_mul code.table)
  mul_one code :=
    congrArg FiniteAxisFoldExtensionPermutationCode.mk
      (mul_one code.table)
  inv_mul_cancel code :=
    congrArg FiniteAxisFoldExtensionPermutationCode.mk
      (inv_mul_cancel code.table)

/-- Forget only the source wrapper and read its complete primitive table. -/
def tableMulEquiv :
    FiniteAxisFoldExtensionPermutationCode E ≃*
      Equiv.Perm E where
  toFun := table
  invFun := fun permutation => ⟨permutation⟩
  left_inv code := by cases code; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end FiniteAxisFoldExtensionPermutationCode

/-- Evaluate an independent fixed-carrier table through the already
constructed source-to-actual route into the actual joint local-fiber kernel. -/
noncomputable def finiteAxisFoldExtensionPermutationDecoder (E : Type) :
    FiniteAxisFoldExtensionPermutationCode E →*
      FiniteAxisFoldResidualLocalFiberKernel :=
  (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E).comp
    FiniteAxisFoldExtensionPermutationCode.tableMulEquiv.toMonoidHom

/-- The complete observable stored-backward action of each independent table.
This is a derived actual action, not syntax and not a supplied certificate. -/
noncomputable def finiteAxisFoldExtensionPermutationBackwardAction (E : Type) :
    FiniteAxisFoldExtensionPermutationCode E →*
      (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  finiteAxisFoldResidualLocalFiberKernelBackwardProjection.comp
    (finiteAxisFoldExtensionPermutationDecoder E)

/-- Intrinsic actual image for the fixed carrier `E`: membership is decided by
whether the complete stored-backward context action is induced by an
independent table.  This subgroup is not used as the source syntax. -/
noncomputable def FiniteAxisFoldExtensionPermutationIntrinsicImage (E : Type) :
    Subgroup FiniteAxisFoldResidualLocalFiberKernel :=
  (MonoidHom.range (finiteAxisFoldExtensionPermutationBackwardAction E)).comap
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection

/-- Intrinsic membership exposes the independent table which induces the
complete stored-backward action. -/
theorem finiteAxisFoldExtensionPermutationIntrinsicImage_mem_iff
    {E : Type} (remainder : FiniteAxisFoldResidualLocalFiberKernel) :
    remainder ∈ FiniteAxisFoldExtensionPermutationIntrinsicImage E ↔
      ∃ code : FiniteAxisFoldExtensionPermutationCode E,
        finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder =
          finiteAxisFoldExtensionPermutationBackwardAction E code := by
  change
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder ∈
        MonoidHom.range (finiteAxisFoldExtensionPermutationBackwardAction E) ↔ _
  constructor
  · rintro ⟨code, equality⟩
    exact ⟨code, equality.symm⟩
  · rintro ⟨code, equality⟩
    exact ⟨code, equality.symm⟩

/-- The source decoder lands in the action-characterized subgroup. -/
noncomputable def finiteAxisFoldExtensionPermutationIntrinsicDecoder
    (E : Type) :
    FiniteAxisFoldExtensionPermutationCode E →*
      FiniteAxisFoldExtensionPermutationIntrinsicImage E :=
  (finiteAxisFoldExtensionPermutationDecoder E).codRestrict
    (FiniteAxisFoldExtensionPermutationIntrinsicImage E)
    (fun code => by
      exact (finiteAxisFoldExtensionPermutationIntrinsicImage_mem_iff
        (finiteAxisFoldExtensionPermutationDecoder E code)).2
          ⟨code, rfl⟩)

/-- Distinct independent finite tables remain distinct in the intrinsic
actual image. -/
theorem finiteAxisFoldExtensionPermutationIntrinsicDecoder_injective
    (E : Type) [Fintype E] :
    Function.Injective
      (finiteAxisFoldExtensionPermutationIntrinsicDecoder E) := by
  intro first second equality
  apply FiniteAxisFoldExtensionPermutationCode.ext
  apply finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_injective E
  exact congrArg Subtype.val equality

/-- Every actual element satisfying the intrinsic stored-backward action
condition is decoded by its inducing independent table. -/
theorem finiteAxisFoldExtensionPermutationIntrinsicDecoder_surjective
    (E : Type) [Fintype E] :
    Function.Surjective
      (finiteAxisFoldExtensionPermutationIntrinsicDecoder E) := by
  intro remainder
  obtain ⟨code, actionEquality⟩ :=
    (finiteAxisFoldExtensionPermutationIntrinsicImage_mem_iff remainder.1).1
      remainder.2
  refine ⟨code, ?_⟩
  apply Subtype.ext
  apply finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
  exact actionEquality.symm

/-- Independent finite tables are exactly equivalent to the subgroup
characterized by their complete actual stored-backward context action. -/
noncomputable def finiteAxisFoldExtensionPermutationIntrinsicDecoderEquiv
    (E : Type) [Fintype E] :
    FiniteAxisFoldExtensionPermutationCode E ≃*
      FiniteAxisFoldExtensionPermutationIntrinsicImage E :=
  MulEquiv.ofBijective
    (finiteAxisFoldExtensionPermutationIntrinsicDecoder E)
    ⟨finiteAxisFoldExtensionPermutationIntrinsicDecoder_injective E,
      finiteAxisFoldExtensionPermutationIntrinsicDecoder_surjective E⟩

/-- Only after the intrinsic action characterization has been fixed do we
recover the equivalent semantic-range statement. -/
theorem finiteAxisFoldExtensionPermutationIntrinsicImage_mem_iff_decoder
    {E : Type} [Fintype E]
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) :
    remainder ∈ FiniteAxisFoldExtensionPermutationIntrinsicImage E ↔
      ∃ code : FiniteAxisFoldExtensionPermutationCode E,
        finiteAxisFoldExtensionPermutationDecoder E code = remainder := by
  constructor
  · intro membership
    let intrinsic : FiniteAxisFoldExtensionPermutationIntrinsicImage E :=
      ⟨remainder, membership⟩
    obtain ⟨code, equality⟩ :=
      finiteAxisFoldExtensionPermutationIntrinsicDecoder_surjective E intrinsic
    exact ⟨code, congrArg Subtype.val equality⟩
  · rintro ⟨code, rfl⟩
    exact (finiteAxisFoldExtensionPermutationIntrinsicDecoder E code).2

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
