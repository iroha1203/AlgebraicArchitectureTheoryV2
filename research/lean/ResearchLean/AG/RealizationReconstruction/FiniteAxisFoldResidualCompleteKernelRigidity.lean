import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualEquationObservableRigidity
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonInputCharacterization
import Formal.Util.AssertStandardAxioms

/-!
# Complete-morphism rigidity of the finite-axis-fold residual intersection

The forward-context kernel has two independently constructed refinements.  The
bidirectional context kernel fixes the complete stored context equivalence, and
the local-fiber kernel fixes every Support, Axis, and Observable comparison over
every context.  This file takes their intersection inside the same actual
forward-context kernel and proves that it is trivial.

The comparison is made against canonical geometry normalization, not against
the raw identity geometry morphism: canonical normalization is the underlying
arrow of the identity in the normalized Karoubi category.  Every computational
field used by complete-morphism extensionality is discharged from the fixed
input and earlier residual rigidity theorems.  No whole morphism equality,
local comparison family, or kernel-triviality certificate is accepted as an
input.

This theorem identifies the exact joint kernel.  It does not prove that every
residual automorphism lies in that kernel, construct the images or source
generators of the four projections, or establish residual source coverage.
-/

namespace AAT.AG.RealizationReconstruction

universe u v

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

/-- Residual elements invisible to both stored context directions and to all
three complete local-fiber action families. -/
noncomputable abbrev FiniteAxisFoldResidualCompleteKernel :=
  FiniteAxisFoldResidualBidirectionalContextKernel ⊓
    FiniteAxisFoldResidualLocalFiberKernel

private noncomputable abbrev FiniteAxisFoldCompleteKernelEndpoint :=
  finiteAxisFoldActualDirectAdmissibleGeometry.obj

private noncomputable abbrev FiniteAxisFoldCompleteKernelCanonical :
    GeometryTotalHom FiniteAxisFoldCompleteKernelEndpoint
      FiniteAxisFoldCompleteKernelEndpoint :=
  canonicalGeometryNormalization FiniteAxisFoldCompleteKernelEndpoint
    finiteAxisFoldActualDirectAdmissibleGeometry.property

private noncomputable abbrev FiniteAxisFoldCompleteKernelActual
    (remainder : FiniteAxisFoldResidualCompleteKernel) :
    GeometryTotalHom FiniteAxisFoldCompleteKernelEndpoint
      FiniteAxisFoldCompleteKernelEndpoint :=
  remainder.1.1.1.1.hom.f.hom

private theorem finiteAxisFoldRingEquivCastSymm_heq_refl
    {alpha : Type u} (R : alpha → Type v) [∀ index, CommRing (R index)]
    {source target : alpha} (equality : target = source) :
    HEq (RingEquiv.cast (R := R) equality).symm
      (RingEquiv.refl (R source)) := by
  cases equality
  rfl

private theorem finiteAxisFold_heq_of_equivCast_eq
    {alpha : Type u} (R : alpha → Type v) {source target : alpha}
    (equality : target = source) (value : R target) (expected : R source)
    (cast_eq : Equiv.cast (congrArg R equality) value = expected) :
    HEq value expected := by
  cases equality
  exact heq_of_eq cast_eq

private theorem finiteAxisFold_castOperation_heq
    {U : AtomCarrier.{u}} (reading : OperationReading U)
    {source source' target target' : ArchitectureObject U}
    (source_eq : source = source') (target_eq : target = target')
    (operation : reading.Op source target) :
    HEq (AtomFoundation.castOperation reading source_eq target_eq operation)
      operation := by
  cases source_eq
  cases target_eq
  rfl

/-- Every element of the exact joint kernel has the same complete raw geometry
morphism as canonical normalization.  All fifteen computational conditions are
constructed from the actual residual element and its two kernel memberships. -/
theorem finiteAxisFoldResidualCompleteKernel_raw_eq_canonical
    (remainder : FiniteAxisFoldResidualCompleteKernel) :
    FiniteAxisFoldCompleteKernelActual remainder =
      FiniteAxisFoldCompleteKernelCanonical := by
  apply UpperGeometryCompatibleProblemInputData.GeometryTotalHomInputConditions.eq
  refine {
    pointedSourceMap := finiteAxisFoldResidual_doctrineSourceMap_eq_id
      remainder.1.1
    pointedAtomEquiv := ?_
    atomEquiv := finiteAxisFoldResidual_atomEquiv_eq_refl remainder.1.1
    objectMap := finiteAxisFoldResidual_objectMap_eq_canonicalObjectNormalization
      remainder.1.1
    equationContext := heq_of_eq
      (finiteAxisFoldResidualBidirectionalContextKernel_contextEquivalence_eq_refl
        ⟨remainder.1, remainder.2.1⟩)
    equationIndex := heq_of_eq
      (finiteAxisFoldResidual_equationEquiv_eq_refl remainder.1.1)
    equationObservable := ?_
    operationMap := ?_
    invariantMap := heq_of_eq
      (finiteAxisFoldResidual_invariantMap_eq_id remainder.1.1)
    axisMap := heq_of_eq
      (finiteAxisFoldResidual_axisMap_eq_id remainder.1.1)
    coordinateEquiv := ?_
    coefficientHom := finiteAxisFoldResidual_coefficientHom_eq_id
      remainder.1.1
    supportImageFixed := ?_
    axisImageFixed := ?_
    observableImageFixed := ?_ }
  · rw [← (FiniteAxisFoldCompleteKernelActual remainder).base.atomEquiv_eq]
    exact finiteAxisFoldResidual_atomEquiv_eq_refl remainder.1.1
  · apply Function.hfunext rfl
    intro context context' context_eq
    cases context_eq
    have raw_eq :=
      finiteAxisFoldResidualContextKernel_observableEquiv_eq_cast_symm
        remainder.1 context
    rw [raw_eq]
    exact finiteAxisFoldRingEquivCastSymm_heq_refl _
      (finiteAxisFoldResidualContextKernel_context_eq remainder.1 context)
  · apply Function.hfunext rfl
    intro source source' source_eq
    cases source_eq
    apply Function.hfunext rfl
    intro target target' target_eq
    cases target_eq
    apply Function.hfunext rfl
    intro operation operation' operation_eq
    cases operation_eq
    have point := finiteAxisFoldResidual_operationMap_eq_canonicalNormalization
      remainder.1.1 operation
    exact (finiteAxisFold_castOperation_heq _ _ _ _).symm.trans
      (heq_of_eq point)
  · apply Function.hfunext rfl
    intro axis axis' axis_eq
    cases axis_eq
    exact heq_of_eq
      (finiteAxisFoldResidual_coordinateEquiv_eq_refl remainder.1.1 axis)
  · have fixed :=
      (finiteAxisFoldResidualLocalFiberKernel_mem_iff remainder.1).mp
        remainder.2.2
    apply Function.hfunext rfl
    intro context context' context_eq
    cases context_eq
    apply Function.hfunext rfl
    intro support support' support_eq
    cases support_eq
    have equality := congrFun
      (congrArg Equiv.toFun (fixed.1 context)) support
    change finiteAxisFoldResidualContextKernelSupportEquiv remainder.1 context
        support = support at equality
    rw [finiteAxisFoldResidualContextKernelSupportEquiv_apply] at equality
    exact finiteAxisFold_heq_of_equivCast_eq
      (fun targetContext => targetContext.ctx.Support)
      (finiteAxisFoldResidualContextKernel_context_eq remainder.1 context)
      _ _ equality
  · have fixed :=
      (finiteAxisFoldResidualLocalFiberKernel_mem_iff remainder.1).mp
        remainder.2.2
    apply Function.hfunext rfl
    intro context context' context_eq
    cases context_eq
    apply Function.hfunext rfl
    intro axis axis' axis_eq
    cases axis_eq
    have equality := congrFun
      (congrArg Equiv.toFun (fixed.2.1 context)) axis
    change finiteAxisFoldResidualContextKernelAxisEquiv remainder.1 context axis =
      axis at equality
    rw [finiteAxisFoldResidualContextKernelAxisEquiv_apply] at equality
    exact finiteAxisFold_heq_of_equivCast_eq
      (fun targetContext => targetContext.ctx.Axis)
      (finiteAxisFoldResidualContextKernel_context_eq remainder.1 context)
      _ _ equality
  · have fixed :=
      (finiteAxisFoldResidualLocalFiberKernel_mem_iff remainder.1).mp
        remainder.2.2
    apply Function.hfunext rfl
    intro context context' context_eq
    cases context_eq
    apply Function.hfunext rfl
    intro observable observable' observable_eq
    cases observable_eq
    have equality := congrFun
      (congrArg Equiv.toFun (fixed.2.2 context)) observable
    change finiteAxisFoldResidualContextKernelObservableEquiv remainder.1 context
        observable = observable at equality
    rw [finiteAxisFoldResidualContextKernelObservableEquiv_apply] at equality
    exact finiteAxisFold_heq_of_equivCast_eq
      (fun targetContext => targetContext.ctx.Observable)
      (finiteAxisFoldResidualContextKernel_context_eq remainder.1 context)
      _ _ equality

/-- At the normalized-category level, every exact joint-kernel element has the
identity hom.  The raw identity here is canonical normalization by definition
of the normalized Karoubi object. -/
theorem finiteAxisFoldResidualCompleteKernel_hom_eq_id
    (remainder : FiniteAxisFoldResidualCompleteKernel) :
    remainder.1.1.1.1.hom = 𝟙 FiniteAxisFoldNormalizedDirectGeometry := by
  apply CategoryTheory.Idempotents.Karoubi.Hom.ext
  apply ObjectProperty.hom_ext
  exact finiteAxisFoldResidualCompleteKernel_raw_eq_canonical remainder

/-- Every element of the exact joint kernel is the identity automorphism. -/
theorem finiteAxisFoldResidualCompleteKernel_element_eq_one
    (remainder : FiniteAxisFoldResidualCompleteKernel) : remainder = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Iso.ext
  exact finiteAxisFoldResidualCompleteKernel_hom_eq_id remainder

/-- The simultaneous bidirectional-context and complete local-fiber kernel is
trivial.  This is complete-morphism faithfulness on that exact intersection. -/
theorem finiteAxisFoldResidualCompleteKernel_eq_bot :
    FiniteAxisFoldResidualCompleteKernel = ⊥ := by
  apply le_antisymm
  · intro remainder membership
    have equality :
        (⟨remainder, membership⟩ : FiniteAxisFoldResidualCompleteKernel) = 1 :=
      finiteAxisFoldResidualCompleteKernel_element_eq_one
        ⟨remainder, membership⟩
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val equality)
  · exact bot_le

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
