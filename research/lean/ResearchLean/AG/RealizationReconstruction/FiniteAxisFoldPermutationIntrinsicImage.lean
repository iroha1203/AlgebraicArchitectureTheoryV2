import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPermutationLocalFiberKernelInjective
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldLocalKernelBackwardFaithfulness
import Formal.Util.AssertStandardAxioms

/-!
# Intrinsic image of a fixed finite Extension-permutation family

For a fixed independently supplied finite carrier `E`, this file packages
explicit forward and backward lookup functions with both inverse laws as its
own group-valued syntax.  The syntax contains no semantic residual element or
image-membership certificate.

The corresponding subgroup of the actual local-fiber kernel is characterized
by transporting the primitive source-context action through the fixed route,
independently of the complete-geometry decoder.  Three factorization laws show
that the decoder has exactly this stored-backward action.  Faithfulness of the
full stored-backward projection then proves that the table decoder is an
equivalence onto the action-characterized subgroup.  Full local-kernel
coverage remains a separate question.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

local instance finiteAxisFoldPermutationIntrinsicAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Independent fixed-carrier source syntax: explicit finite forward and
backward lookup tables with inverse laws, not an element of a semantic image
or range. -/
structure FiniteAxisFoldExtensionPermutationCode (E : Type) [Fintype E] where
  forward : E → E
  backward : E → E
  backward_forward : Function.LeftInverse backward forward
  forward_backward : Function.RightInverse backward forward

namespace FiniteAxisFoldExtensionPermutationCode

variable {E : Type} [Fintype E]

/-- Read an explicit finite forward/backward table as a permutation. -/
def toPerm (code : FiniteAxisFoldExtensionPermutationCode E) : Equiv.Perm E where
  toFun := code.forward
  invFun := code.backward
  left_inv := code.backward_forward
  right_inv := code.forward_backward

/-- Encode a permutation as its two finite lookup tables and inverse laws. -/
def ofPerm (permutation : Equiv.Perm E) :
    FiniteAxisFoldExtensionPermutationCode E where
  forward := permutation
  backward := permutation.symm
  backward_forward := permutation.left_inv
  forward_backward := permutation.right_inv

@[simp] theorem toPerm_ofPerm (permutation : Equiv.Perm E) :
    toPerm (ofPerm permutation) = permutation :=
  rfl

@[simp] theorem ofPerm_toPerm
    (code : FiniteAxisFoldExtensionPermutationCode E) :
    ofPerm (toPerm code) = code := by
  cases code
  rfl

theorem toPerm_injective : Function.Injective (toPerm (E := E)) := by
  intro first second equality
  calc
    first = ofPerm (toPerm first) := (ofPerm_toPerm first).symm
    _ = ofPerm (toPerm second) := congrArg ofPerm equality
    _ = second := ofPerm_toPerm second

instance : One (FiniteAxisFoldExtensionPermutationCode E) :=
  ⟨ofPerm 1⟩

instance : Mul (FiniteAxisFoldExtensionPermutationCode E) :=
  ⟨fun first second => ofPerm (toPerm first * toPerm second)⟩

instance : Inv (FiniteAxisFoldExtensionPermutationCode E) :=
  ⟨fun code => ofPerm (toPerm code)⁻¹⟩

/-- The independent table syntax has the ordinary permutation group law. -/
instance : Group (FiniteAxisFoldExtensionPermutationCode E) where
  mul_assoc first second third := by
    apply toPerm_injective
    exact mul_assoc (toPerm first) (toPerm second) (toPerm third)
  one_mul code := by
    apply toPerm_injective
    exact one_mul (toPerm code)
  mul_one code := by
    apply toPerm_injective
    exact mul_one (toPerm code)
  inv_mul_cancel code := by
    apply toPerm_injective
    exact inv_mul_cancel (toPerm code)

@[simp] theorem toPerm_one :
    toPerm (1 : FiniteAxisFoldExtensionPermutationCode E) = 1 :=
  rfl

@[simp] theorem toPerm_mul
    (first second : FiniteAxisFoldExtensionPermutationCode E) :
    toPerm (first * second) = toPerm first * toPerm second :=
  rfl

@[simp] theorem toPerm_inv
    (code : FiniteAxisFoldExtensionPermutationCode E) :
    toPerm code⁻¹ = (toPerm code)⁻¹ :=
  rfl

/-- Forget only the source wrapper and read its complete primitive table. -/
def tableMulEquiv :
    FiniteAxisFoldExtensionPermutationCode E ≃*
      Equiv.Perm E where
  toFun := toPerm
  invFun := ofPerm
  left_inv := ofPerm_toPerm
  right_inv := toPerm_ofPerm
  map_mul' _ _ := rfl

end FiniteAxisFoldExtensionPermutationCode

private noncomputable abbrev FiniteAxisFoldPermutationIntrinsicPulledGeometryFiber :=
  (exactGeometryPullFunctor
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).obj
      finiteAxisFoldSouthwestGeometryFiber

private theorem finiteAxisFoldPermutationIntrinsicContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- Context-object equivalence supplied by the fixed source-to-southwest
transport, independently of any Extension permutation. -/
noncomputable def finiteAxisFoldSourceToSouthwestContextEquiv :
    finiteAxisFoldSourceGeometryPackage.site.category ≃
      finiteAxisFoldGeometryPackage.site.category where
  toFun := contextForward
    (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
      finiteModelDoctrineFromFixture)
  invFun := contextBackward
    (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
      finiteModelDoctrineFromFixture)
  left_inv := canonicalContextRetraction_eq _ _
  right_inv := canonicalContextSection_eq _ _

/-- Context-object equivalence supplied by the generated exact-left pull. -/
noncomputable def finiteAxisFoldSouthwestToExactLeftContextEquiv :
    finiteAxisFoldGeometryPackage.site.category ≃
      FiniteAxisFoldPermutationIntrinsicPulledGeometryFiber.1.site.category where
  toFun := contextBackward
    (exactGeometryPullLift
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber).base
  invFun := contextForward
    (exactGeometryPullLift
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber).base
  left_inv context := by
    apply finiteAxisFoldPermutationIntrinsicContextObject_eq_of_ctx_eq
    exact UpperGeometryCleavage.generatedExactContextForward_backward_ctx
      finiteAxisFoldSouthwestGeometryFiber.1
      (exactGeometryPullBaseHom
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        finiteAxisFoldSouthwestGeometryFiber)
      context
  right_inv context := by
    apply finiteAxisFoldPermutationIntrinsicContextObject_eq_of_ctx_eq
    exact UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
      finiteAxisFoldSouthwestGeometryFiber.1
      (exactGeometryPullBaseHom
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        finiteAxisFoldSouthwestGeometryFiber)
      context

/-- Context-object equivalence supplied by the fixed top transport. -/
noncomputable def finiteAxisFoldExactLeftToActualContextEquiv :
    FiniteAxisFoldPermutationIntrinsicPulledGeometryFiber.1.site.category ≃
      FiniteAxisFoldResidualContextObject where
  toFun := contextForward
    (geomFiberLift
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldPermutationIntrinsicPulledGeometryFiber).base
  invFun := contextBackward
    (geomFiberLift
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldPermutationIntrinsicPulledGeometryFiber).base
  left_inv := canonicalContextRetraction_eq _ _
  right_inv := canonicalContextSection_eq _ _

/-- The fixed context-object equivalence from original source contexts to the
actual endpoint.  It contains no permutation table or residual element. -/
noncomputable def finiteAxisFoldSourceToActualContextEquiv :
    finiteAxisFoldSourceGeometryPackage.site.category ≃
      FiniteAxisFoldResidualContextObject :=
  finiteAxisFoldSourceToSouthwestContextEquiv.trans
    (finiteAxisFoldSouthwestToExactLeftContextEquiv.trans
      finiteAxisFoldExactLeftToActualContextEquiv)

/-- Conjugate the primitive source context action through the fixed context
route.  This is defined without the complete-geometry decoder. -/
noncomputable def finiteAxisFoldTransportedSourceContextPermutation
    {E : Type} (permutation : Equiv.Perm E) :
    Equiv.Perm FiniteAxisFoldResidualContextObject :=
  finiteAxisFoldSourceToActualContextEquiv.symm.trans
    ((finiteAxisFoldSourceContextObjectPermHom E permutation).trans
      finiteAxisFoldSourceToActualContextEquiv)

/-- The independently defined transported source-context permutations form a
homomorphism before any complete-geometry decoder is mentioned. -/
noncomputable def finiteAxisFoldTransportedSourceContextPermutationHom
    (E : Type) :
    Equiv.Perm E →* Equiv.Perm FiniteAxisFoldResidualContextObject where
  toFun := finiteAxisFoldTransportedSourceContextPermutation
  map_one' := by
    apply Equiv.ext
    intro context
    change finiteAxisFoldSourceToActualContextEquiv
        ((finiteAxisFoldSourceContextObjectPermHom E 1)
          (finiteAxisFoldSourceToActualContextEquiv.symm context)) = context
    rw [map_one]
    exact finiteAxisFoldSourceToActualContextEquiv.apply_symm_apply context
  map_mul' first second := by
    apply Equiv.ext
    intro context
    change finiteAxisFoldSourceToActualContextEquiv
        ((finiteAxisFoldSourceContextObjectPermHom E (first * second))
          (finiteAxisFoldSourceToActualContextEquiv.symm context)) =
      finiteAxisFoldSourceToActualContextEquiv
        ((finiteAxisFoldSourceContextObjectPermHom E first)
          (finiteAxisFoldSourceToActualContextEquiv.symm
            (finiteAxisFoldSourceToActualContextEquiv
              ((finiteAxisFoldSourceContextObjectPermHom E second)
                (finiteAxisFoldSourceToActualContextEquiv.symm context)))))
    rw [map_mul, finiteAxisFoldSourceToActualContextEquiv.symm_apply_apply]
    rfl

/-- The southwest stored-backward action is the primitive source action
conjugated by the fixed source-to-southwest context equivalence. -/
theorem finiteAxisFoldSouthwestPermutation_contextBackward
    {E : Type} (permutation : Equiv.Perm E)
    (context : finiteAxisFoldGeometryPackage.site.category) :
    contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
          permutation).hom.1.base context =
      finiteAxisFoldSourceToSouthwestContextEquiv
        (contextBackward
          ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E)
            permutation).hom.1.base
          (finiteAxisFoldSourceToSouthwestContextEquiv.symm context)) := by
  let canonical :=
    transportAlongHom finiteAxisFoldSourceGeometryPackage.core
      finiteModelDoctrineFromFixture
  have factorization := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac finiteAxisFoldSourceToSouthwestExtInstHom
      ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E)
        permutation).hom)
  have point := congrArg (fun total => contextBackward total context) factorization
  change contextBackward canonical
      (contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
          permutation).hom.1.base context) =
    contextBackward
      ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E)
        permutation).hom.1.base
      (contextBackward canonical context) at point
  have mapped := congrArg finiteAxisFoldSourceToSouthwestContextEquiv point
  change finiteAxisFoldSourceToSouthwestContextEquiv
      (finiteAxisFoldSourceToSouthwestContextEquiv.symm
        (contextBackward
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
            permutation).hom.1.base context)) = _ at mapped
  rw [finiteAxisFoldSourceToSouthwestContextEquiv.apply_symm_apply] at mapped
  exact mapped

/-- The exact-left stored-backward action is the southwest action conjugated
by the independently fixed generated exact context equivalence. -/
theorem finiteAxisFoldExactLeftPermutation_contextBackward
    {E : Type} (permutation : Equiv.Perm E)
    (context :
      FiniteAxisFoldPermutationIntrinsicPulledGeometryFiber.1.site.category) :
    contextBackward
        (((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
              permutation).hom).1.base) context =
      finiteAxisFoldSouthwestToExactLeftContextEquiv
        (contextBackward
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
            permutation).hom.1.base
          (finiteAxisFoldSouthwestToExactLeftContextEquiv.symm context)) := by
  let lift := (exactGeometryPullLift
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
    finiteAxisFoldSouthwestGeometryFiber).base
  have factorization := congrArg (fun total => total.base)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
        permutation).hom)
  have point := congrArg
    (fun total => contextBackward total (contextForward lift context))
    factorization
  change contextBackward
      (((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
            permutation).hom).1.base)
        (contextBackward lift (contextForward lift context)) =
    contextBackward lift
      (contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
          permutation).hom.1.base
        (contextForward lift context)) at point
  have cancel : contextBackward lift (contextForward lift context) = context := by
    apply finiteAxisFoldPermutationIntrinsicContextObject_eq_of_ctx_eq
    exact UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
      finiteAxisFoldSouthwestGeometryFiber.1
      (exactGeometryPullBaseHom
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        finiteAxisFoldSouthwestGeometryFiber)
      context
  rw [cancel] at point
  exact point

/-- The actual stored-backward action is the exact-left action conjugated by
the independently fixed top-transport context equivalence. -/
theorem finiteAxisFoldActualPermutation_contextBackward
    {E : Type} (permutation : Equiv.Perm E)
    (context : FiniteAxisFoldResidualContextObject) :
    contextBackward
        ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E)
          permutation).hom.1.base context =
      finiteAxisFoldExactLeftToActualContextEquiv
        (contextBackward
          (((exactGeometryPullFunctor
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
              ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
                permutation).hom).1.base)
          (finiteAxisFoldExactLeftToActualContextEquiv.symm context)) := by
  let lift := (geomFiberLift
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    FiniteAxisFoldPermutationIntrinsicPulledGeometryFiber).base
  have factorization := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
            permutation).hom))
  have point := congrArg (fun total => contextBackward total context) factorization
  change contextBackward lift
      (contextBackward
        ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E)
          permutation).hom.1.base context) =
    contextBackward
      (((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E)
            permutation).hom).1.base)
      (contextBackward lift context) at point
  have mapped := congrArg finiteAxisFoldExactLeftToActualContextEquiv point
  change finiteAxisFoldExactLeftToActualContextEquiv
      (finiteAxisFoldExactLeftToActualContextEquiv.symm
        (contextBackward
          ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E)
            permutation).hom.1.base context)) = _ at mapped
  rw [finiteAxisFoldExactLeftToActualContextEquiv.apply_symm_apply] at mapped
  exact mapped

/-- Evaluate an independent fixed-carrier table through the already
constructed source-to-actual route into the actual joint local-fiber kernel. -/
noncomputable def finiteAxisFoldExtensionPermutationDecoder
    (E : Type) [Fintype E] :
    FiniteAxisFoldExtensionPermutationCode E →*
      FiniteAxisFoldResidualLocalFiberKernel :=
  (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E).comp
    FiniteAxisFoldExtensionPermutationCode.tableMulEquiv.toMonoidHom

/-- The complete expected stored-backward action of each independent table,
defined directly by the primitive source-context action and the fixed context
route rather than by the complete-geometry decoder. -/
noncomputable def finiteAxisFoldExtensionPermutationBackwardAction
    (E : Type) [Fintype E] :
    FiniteAxisFoldExtensionPermutationCode E →*
      (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ where
  toFun code := MulOpposite.op
    (finiteAxisFoldTransportedSourceContextPermutationHom E
      (FiniteAxisFoldExtensionPermutationCode.toPerm code)⁻¹)
  map_one' := by
    apply MulOpposite.unop_injective
    rw [FiniteAxisFoldExtensionPermutationCode.toPerm_one, inv_one, map_one]
    rfl
  map_mul' first second := by
    apply MulOpposite.unop_injective
    rw [FiniteAxisFoldExtensionPermutationCode.toPerm_mul, mul_inv_rev, map_mul]
    rfl

/-- Intrinsic actual image for the fixed carrier `E`: membership is decided by
whether the complete stored-backward context action is induced by an
independent table.  This subgroup is not used as the source syntax. -/
noncomputable def FiniteAxisFoldExtensionPermutationIntrinsicImage
    (E : Type) [Fintype E] :
    Subgroup FiniteAxisFoldResidualLocalFiberKernel :=
  (MonoidHom.range (finiteAxisFoldExtensionPermutationBackwardAction E)).comap
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection

/-- Intrinsic membership exposes the independent table which induces the
complete stored-backward action. -/
theorem finiteAxisFoldExtensionPermutationIntrinsicImage_mem_iff
    {E : Type} [Fintype E]
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) :
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

/-- The independently transported primitive source action is exactly the
stored-backward action produced by the complete-geometry decoder. -/
theorem finiteAxisFoldExtensionPermutationDecoder_backwardProjection
    {E : Type} [Fintype E]
    (code : FiniteAxisFoldExtensionPermutationCode E) :
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection
        (finiteAxisFoldExtensionPermutationDecoder E code) =
      finiteAxisFoldExtensionPermutationBackwardAction E code := by
  apply MulOpposite.unop_injective
  apply Equiv.ext
  intro context
  change contextBackward
      ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E)
        (FiniteAxisFoldExtensionPermutationCode.toPerm code)).hom.1.base
        context =
    finiteAxisFoldTransportedSourceContextPermutation
      (FiniteAxisFoldExtensionPermutationCode.toPerm code)⁻¹ context
  rw [finiteAxisFoldActualPermutation_contextBackward,
    finiteAxisFoldExactLeftPermutation_contextBackward,
    finiteAxisFoldSouthwestPermutation_contextBackward]
  rfl

/-- The source decoder lands in the action-characterized subgroup. -/
noncomputable def finiteAxisFoldExtensionPermutationIntrinsicDecoder
    (E : Type) [Fintype E] :
    FiniteAxisFoldExtensionPermutationCode E →*
      FiniteAxisFoldExtensionPermutationIntrinsicImage E :=
  (finiteAxisFoldExtensionPermutationDecoder E).codRestrict
    (FiniteAxisFoldExtensionPermutationIntrinsicImage E)
    (fun code => by
      exact (finiteAxisFoldExtensionPermutationIntrinsicImage_mem_iff
        (finiteAxisFoldExtensionPermutationDecoder E code)).2
          ⟨code,
            finiteAxisFoldExtensionPermutationDecoder_backwardProjection code⟩)

/-- Distinct independent finite tables remain distinct in the intrinsic
actual image. -/
theorem finiteAxisFoldExtensionPermutationIntrinsicDecoder_injective
    (E : Type) [Fintype E] :
    Function.Injective
      (finiteAxisFoldExtensionPermutationIntrinsicDecoder E) := by
  intro first second equality
  apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
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
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      (finiteAxisFoldExtensionPermutationDecoder E code) =
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder.1
  rw [finiteAxisFoldExtensionPermutationDecoder_backwardProjection]
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
