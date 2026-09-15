import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualCompleteKernelRigidity
import Formal.Util.AssertStandardAxioms

/-!
# Faithful complete action of the finite-axis-fold residual group

The residual forward-context kernel acts on two pieces of actual stored data:
the inverse context functor and the complete Support, Axis, and Observable local
comparison families.  This file packages those actions into one group
homomorphism.  Cycle 84's complete-morphism rigidity theorem identifies its
kernel with the exact joint kernel and proves that kernel trivial, so the
combined action is faithful.

The final equivalence is onto the actual range of this homomorphism.  It is a
semantic classification of every residual element, not a finite source syntax,
a generator theorem, or a section constructed from primitive AAT input.  In
particular, range membership is not reused here as a presentation certificate.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 200000

/-- The actual stored backward-context action together with all three complete
local-fiber action families. -/
abbrev FiniteAxisFoldResidualCompleteAction :=
  (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ ×
    FiniteAxisFoldResidualLocalFiberActionFamily

/-- The combined action of every element of the full forward-context kernel.
Neither its domain nor either action component is restricted to a selected
representable subset. -/
noncomputable def finiteAxisFoldResidualCompleteProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      FiniteAxisFoldResidualCompleteAction :=
  finiteAxisFoldResidualContextKernelBackwardProjection.prod
    finiteAxisFoldResidualContextKernelLocalFiberProjection

/-- The kernel of the combined actual action is exactly the complete joint
kernel reconstructed in Cycle 84. -/
theorem finiteAxisFoldResidualCompleteProjection_ker :
    MonoidHom.ker finiteAxisFoldResidualCompleteProjection =
      FiniteAxisFoldResidualCompleteKernel := by
  ext remainder
  simp [finiteAxisFoldResidualCompleteProjection,
    FiniteAxisFoldResidualCompleteKernel,
    FiniteAxisFoldResidualBidirectionalContextKernel,
    FiniteAxisFoldResidualLocalFiberKernel]

/-- Complete backward-context and local-fiber action data distinguish every
element of the residual forward-context kernel. -/
theorem finiteAxisFoldResidualCompleteProjection_injective :
    Function.Injective finiteAxisFoldResidualCompleteProjection := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [finiteAxisFoldResidualCompleteProjection_ker]
  exact finiteAxisFoldResidualCompleteKernel_eq_bot

/-- Every residual element is classified uniquely by its complete actual
action.  The codomain is deliberately the actual range, not a claimed source
presentation or independently generated syntax. -/
noncomputable def finiteAxisFoldResidualCompleteProjectionEquivRange :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel ≃*
      MonoidHom.range finiteAxisFoldResidualCompleteProjection :=
  MulEquiv.ofBijective
    (MonoidHom.rangeRestrict finiteAxisFoldResidualCompleteProjection)
    ⟨(by
        intro first second equality
        apply finiteAxisFoldResidualCompleteProjection_injective
        change finiteAxisFoldResidualCompleteProjection first =
          finiteAxisFoldResidualCompleteProjection second
        exact congrArg Subtype.val equality),
      MonoidHom.rangeRestrict_surjective _⟩

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
