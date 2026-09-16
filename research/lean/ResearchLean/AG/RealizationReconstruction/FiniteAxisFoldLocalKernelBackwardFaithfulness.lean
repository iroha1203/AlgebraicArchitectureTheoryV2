import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldBackwardToggleLocalAction
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualFaithfulAction
import Formal.Util.AssertStandardAxioms

/-!
# Faithful backward action on the finite-axis-fold local-fiber kernel

The complete residual action is faithful jointly in its stored backward-context
and local-fiber components.  On the full local-fiber kernel, the second
component is forced to be the identity by subgroup membership.  Consequently
the stored backward-context projection alone is faithful on that subgroup.

The source-owned Extension toggle constructed previously is an element of this
kernel and has nonidentity backward action.  This supplies one explicit
nontrivial element of the faithful action.  It does not characterize the image,
construct generators for every residual element, or prove source coverage.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 200000

/-- Restriction of the actual stored backward-context action to residual
elements whose complete Support, Axis, and Observable actions are identity. -/
noncomputable def finiteAxisFoldResidualLocalFiberKernelBackwardProjection :
    FiniteAxisFoldResidualLocalFiberKernel →*
      (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ where
  toFun remainder :=
    finiteAxisFoldResidualContextKernelBackwardProjection remainder.1
  map_one' := map_one finiteAxisFoldResidualContextKernelBackwardProjection
  map_mul' first second := by
    exact map_mul finiteAxisFoldResidualContextKernelBackwardProjection
      first.1 second.1

/-- Once all three complete local-fiber actions are fixed, the stored backward
context action distinguishes every residual element. -/
theorem finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective :
    Function.Injective
      finiteAxisFoldResidualLocalFiberKernelBackwardProjection := by
  intro first second backwardEquality
  change finiteAxisFoldResidualContextKernelBackwardProjection first.1 =
    finiteAxisFoldResidualContextKernelBackwardProjection second.1 at backwardEquality
  apply Subtype.ext
  apply finiteAxisFoldResidualCompleteProjection_injective
  apply Prod.ext
  · change finiteAxisFoldResidualContextKernelBackwardProjection first.1 =
      finiteAxisFoldResidualContextKernelBackwardProjection second.1
    exact backwardEquality
  · change
      finiteAxisFoldResidualContextKernelLocalFiberProjection first.1 =
        finiteAxisFoldResidualContextKernelLocalFiberProjection second.1
    rw [MonoidHom.mem_ker.mp first.2, MonoidHom.mem_ker.mp second.2]

/-- The normalized source-owned Extension toggle, retained together with the
constructed proof that all three complete local-fiber actions are identity. -/
noncomputable def finiteAxisFoldNormalizedExtensionBackwardLocalFiberKernel :
    FiniteAxisFoldResidualLocalFiberKernel :=
  ⟨finiteAxisFoldNormalizedExtensionBackwardContextKernel,
    finiteAxisFoldNormalizedExtensionBackward_mem_localFiberKernel⟩

/-- The source-owned Extension toggle is a nonidentity element of the full
local-fiber kernel, witnessed by its actual stored backward-context action. -/
theorem finiteAxisFoldNormalizedExtensionBackwardLocalFiberKernel_ne_one :
    finiteAxisFoldNormalizedExtensionBackwardLocalFiberKernel ≠ 1 := by
  intro equality
  apply finiteAxisFoldNormalizedExtensionBackward_backwardProjection_ne_one
  have projected := congrArg
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection equality
  change
    finiteAxisFoldResidualContextKernelBackwardProjection
        finiteAxisFoldNormalizedExtensionBackwardContextKernel =
      finiteAxisFoldResidualContextKernelBackwardProjection 1 at projected
  simpa using projected

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
