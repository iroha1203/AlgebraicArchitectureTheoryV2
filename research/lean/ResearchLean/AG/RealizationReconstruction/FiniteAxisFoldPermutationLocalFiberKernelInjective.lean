import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPermutationLocalFiberKernel
import Formal.Util.AssertStandardAxioms

/-!
# Faithfulness of the finite Extension-permutation local-kernel section

The arbitrary finite Extension-carrier permutation section constructed in the
joint residual local-fiber kernel is injective.  The proof does not assume a
completed semantic action or define syntax from the semantic range.  Instead,
it transports every independently defined source context through the fixed
southwest, exact-left, and top-transport route.  Equality of the normalized
stored backward actions is then cancelled through those three constructed
lifts and read back by the source probe theorem.

This proves image faithfulness.  It does not yet prove that the image covers
the complete local-fiber kernel or classify the remaining fibers.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

local instance finiteAxisFoldPermutationKernelInjectiveAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

private noncomputable abbrev FiniteAxisFoldPermutationInjectivePulledGeometryFiber :=
  (exactGeometryPullFunctor
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).obj
      finiteAxisFoldSouthwestGeometryFiber

/-- The southwest image of an arbitrary independently supplied source
context. -/
noncomputable def finiteAxisFoldPermutationSouthwestProbe
    (sourceContext : finiteAxisFoldSourceGeometryPackage.site.category) :
    finiteAxisFoldGeometryPackage.site.category :=
  contextForward
    (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
      finiteModelDoctrineFromFixture)
    sourceContext

/-- Pull the transported source probe back through the generated exact-left
lift. -/
noncomputable def finiteAxisFoldPermutationExactLeftProbe
    (sourceContext : finiteAxisFoldSourceGeometryPackage.site.category) :
    (authoredExactLeftPulledGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))).1.site.category :=
  contextBackward
    (exactGeometryPullLift
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber).base
    (finiteAxisFoldPermutationSouthwestProbe sourceContext)

/-- Transport the generated exact-left probe to the actual direct endpoint. -/
noncomputable def finiteAxisFoldPermutationActualProbe
    (sourceContext : finiteAxisFoldSourceGeometryPackage.site.category) :
    (authoredExactDirectGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))).1.site.category :=
  contextForward
    (geomFiberLift
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldPermutationInjectivePulledGeometryFiber).base
    (finiteAxisFoldPermutationExactLeftProbe sourceContext)

private theorem finiteAxisFoldPermutationContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- Equality of two southwest stored backward actions on a transported probe
reflects equality of their source stored backward actions on the original
source context. -/
private theorem finiteAxisFoldSouthwestPermutation_backward_eq_reflects_source
    {E : Type} (first second : Equiv.Perm E)
    (sourceContext : finiteAxisFoldSourceGeometryPackage.site.category)
    (equality :
      contextBackward
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom.1.base
          (finiteAxisFoldPermutationSouthwestProbe sourceContext) =
        contextBackward
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom.1.base
          (finiteAxisFoldPermutationSouthwestProbe sourceContext)) :
    contextBackward
        ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E) first).hom.1.base
        sourceContext =
      contextBackward
        ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E) second).hom.1.base
        sourceContext := by
  let canonical :=
    transportAlongHom finiteAxisFoldSourceGeometryPackage.core
      finiteModelDoctrineFromFixture
  have firstFac := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac finiteAxisFoldSourceToSouthwestExtInstHom
      ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E) first).hom)
  have secondFac := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac finiteAxisFoldSourceToSouthwestExtInstHom
      ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E) second).hom)
  have firstPoint := congrArg
    (fun total => contextBackward total
      (finiteAxisFoldPermutationSouthwestProbe sourceContext)) firstFac
  have secondPoint := congrArg
    (fun total => contextBackward total
      (finiteAxisFoldPermutationSouthwestProbe sourceContext)) secondFac
  change contextBackward canonical
      (contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom.1.base
        (finiteAxisFoldPermutationSouthwestProbe sourceContext)) =
    contextBackward
      ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E) first).hom.1.base
      (contextBackward canonical
        (finiteAxisFoldPermutationSouthwestProbe sourceContext)) at firstPoint
  change contextBackward canonical
      (contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom.1.base
        (finiteAxisFoldPermutationSouthwestProbe sourceContext)) =
    contextBackward
      ((finiteAxisFoldSourcePermutationGeometryFiberSectionHom E) second).hom.1.base
      (contextBackward canonical
        (finiteAxisFoldPermutationSouthwestProbe sourceContext)) at secondPoint
  have sourceCancel :
      contextBackward canonical
          (finiteAxisFoldPermutationSouthwestProbe sourceContext) =
        sourceContext := canonicalContextRetraction_eq _ _ _
  rw [equality, sourceCancel] at firstPoint
  rw [sourceCancel] at secondPoint
  exact firstPoint.symm.trans secondPoint

/-- Equality of exact-left stored backward actions on the generated probe
reflects equality of the southwest actions. -/
private theorem finiteAxisFoldExactLeftPermutation_backward_eq_reflects_southwest
    {E : Type} (first second : Equiv.Perm E)
    (sourceContext : finiteAxisFoldSourceGeometryPackage.site.category)
    (equality :
      contextBackward
          (((exactGeometryPullFunctor
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
              ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom).1.base)
          (finiteAxisFoldPermutationExactLeftProbe sourceContext) =
        contextBackward
          (((exactGeometryPullFunctor
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
              ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom).1.base)
          (finiteAxisFoldPermutationExactLeftProbe sourceContext)) :
    contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom.1.base
        (finiteAxisFoldPermutationSouthwestProbe sourceContext) =
      contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom.1.base
        (finiteAxisFoldPermutationSouthwestProbe sourceContext) := by
  let lift := exactGeometryPullLift
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
    finiteAxisFoldSouthwestGeometryFiber
  have firstFac := congrArg (fun total => total.base)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom)
  have secondFac := congrArg (fun total => total.base)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom)
  have firstPoint := congrArg
    (fun total => contextBackward total
      (finiteAxisFoldPermutationSouthwestProbe sourceContext)) firstFac
  have secondPoint := congrArg
    (fun total => contextBackward total
      (finiteAxisFoldPermutationSouthwestProbe sourceContext)) secondFac
  change contextBackward
      (((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom).1.base)
      (finiteAxisFoldPermutationExactLeftProbe sourceContext) =
    contextBackward lift.base
      (contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom.1.base
        (finiteAxisFoldPermutationSouthwestProbe sourceContext)) at firstPoint
  change contextBackward
      (((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom).1.base)
      (finiteAxisFoldPermutationExactLeftProbe sourceContext) =
    contextBackward lift.base
      (contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom.1.base
        (finiteAxisFoldPermutationSouthwestProbe sourceContext)) at secondPoint
  rw [equality] at firstPoint
  have pulledEquality := firstPoint.symm.trans secondPoint
  have ctxEquality := congrArg
    (fun target => (contextForward lift.base target).ctx) pulledEquality
  have firstCancel :=
    UpperGeometryCleavage.generatedExactContextForward_backward_ctx
      finiteAxisFoldSouthwestGeometryFiber.1
      (exactGeometryPullBaseHom
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        finiteAxisFoldSouthwestGeometryFiber)
      (contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom.1.base
        (finiteAxisFoldPermutationSouthwestProbe sourceContext))
  have secondCancel :=
    UpperGeometryCleavage.generatedExactContextForward_backward_ctx
      finiteAxisFoldSouthwestGeometryFiber.1
      (exactGeometryPullBaseHom
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        finiteAxisFoldSouthwestGeometryFiber)
      (contextBackward
        ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom.1.base
        (finiteAxisFoldPermutationSouthwestProbe sourceContext))
  change
    (contextForward
      (UpperGeometryCleavage.exactBaseHom
        finiteAxisFoldSouthwestGeometryFiber.1
        (exactGeometryPullBaseHom
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
          finiteAxisFoldSouthwestGeometryFiber))
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom
          finiteAxisFoldSouthwestGeometryFiber.1
          (exactGeometryPullBaseHom
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
            finiteAxisFoldSouthwestGeometryFiber))
        (contextBackward
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom.1.base
          (finiteAxisFoldPermutationSouthwestProbe sourceContext)))).ctx =
    (contextForward
      (UpperGeometryCleavage.exactBaseHom
        finiteAxisFoldSouthwestGeometryFiber.1
        (exactGeometryPullBaseHom
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
          finiteAxisFoldSouthwestGeometryFiber))
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom
          finiteAxisFoldSouthwestGeometryFiber.1
          (exactGeometryPullBaseHom
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
            finiteAxisFoldSouthwestGeometryFiber))
        (contextBackward
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom.1.base
          (finiteAxisFoldPermutationSouthwestProbe sourceContext)))).ctx at ctxEquality
  rw [firstCancel, secondCancel] at ctxEquality
  exact finiteAxisFoldPermutationContextObject_eq_of_ctx_eq ctxEquality

/-- Equality of actual-direct stored backward actions on the top-transported
probe reflects equality of the exact-left actions. -/
private theorem finiteAxisFoldActualPermutation_backward_eq_reflects_exactLeft
    {E : Type} (first second : Equiv.Perm E)
    (sourceContext : finiteAxisFoldSourceGeometryPackage.site.category)
    (equality :
      contextBackward
          ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E) first).hom.1.base
          (finiteAxisFoldPermutationActualProbe sourceContext) =
        contextBackward
          ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E) second).hom.1.base
          (finiteAxisFoldPermutationActualProbe sourceContext)) :
    contextBackward
        (((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom).1.base)
        (finiteAxisFoldPermutationExactLeftProbe sourceContext) =
      contextBackward
        (((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom).1.base)
        (finiteAxisFoldPermutationExactLeftProbe sourceContext) := by
  let lift := geomFiberLift
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    FiniteAxisFoldPermutationInjectivePulledGeometryFiber
  have firstFac := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom))
  have secondFac := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom))
  have firstPoint := congrArg
    (fun total => contextBackward total
      (finiteAxisFoldPermutationActualProbe sourceContext)) firstFac
  have secondPoint := congrArg
    (fun total => contextBackward total
      (finiteAxisFoldPermutationActualProbe sourceContext)) secondFac
  change contextBackward lift.base
      (contextBackward
        ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E) first).hom.1.base
        (finiteAxisFoldPermutationActualProbe sourceContext)) =
    contextBackward
      (((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) first).hom).1.base)
      (contextBackward lift.base
        (finiteAxisFoldPermutationActualProbe sourceContext)) at firstPoint
  change contextBackward lift.base
      (contextBackward
        ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E) second).hom.1.base
        (finiteAxisFoldPermutationActualProbe sourceContext)) =
    contextBackward
      (((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          ((finiteAxisFoldSouthwestPermutationGeometrySectionHom E) second).hom).1.base)
      (contextBackward lift.base
        (finiteAxisFoldPermutationActualProbe sourceContext)) at secondPoint
  have sourceCancel :
      contextBackward lift.base
          (finiteAxisFoldPermutationActualProbe sourceContext) =
        finiteAxisFoldPermutationExactLeftProbe sourceContext :=
    canonicalContextRetraction_eq _ _ _
  rw [equality, sourceCancel] at firstPoint
  rw [sourceCancel] at secondPoint
  exact firstPoint.symm.trans secondPoint

/-- The normalized complete-geometry permutation section remains faithful on
every finite independently supplied Extension carrier. -/
theorem finiteAxisFoldNormalizedPermutationGeometrySectionHom_injective
    (E : Type) [Fintype E] :
    Function.Injective (finiteAxisFoldNormalizedPermutationGeometrySectionHom E) := by
  intro first second equality
  have sourceBackwardEquality :
      (finiteAxisFoldSourceContextObjectPermHom E) first⁻¹ =
        (finiteAxisFoldSourceContextObjectPermHom E) second⁻¹ := by
    apply Equiv.ext
    intro sourceContext
    have normalizedPoint := congrArg
      (fun automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry =>
        contextBackward automorphism.hom.f.hom.base
          (finiteAxisFoldPermutationActualProbe sourceContext)) equality
    change contextBackward
        ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E) first).hom.1.base
        (finiteAxisFoldPermutationActualProbe sourceContext) =
      contextBackward
        ((finiteAxisFoldActualDirectPermutationGeometrySectionHom E) second).hom.1.base
        (finiteAxisFoldPermutationActualProbe sourceContext) at normalizedPoint
    have exactLeftEquality :=
      finiteAxisFoldActualPermutation_backward_eq_reflects_exactLeft
        first second sourceContext normalizedPoint
    have southwestEquality :=
      finiteAxisFoldExactLeftPermutation_backward_eq_reflects_southwest
        first second sourceContext exactLeftEquality
    have sourceEquality :=
      finiteAxisFoldSouthwestPermutation_backward_eq_reflects_source
        first second sourceContext southwestEquality
    exact sourceEquality
  have inverseEquality : first⁻¹ = second⁻¹ :=
    finiteAxisFoldSourceContextObjectPermHom_injective E sourceBackwardEquality
  calc
    first = (first⁻¹)⁻¹ := by simp
    _ = (second⁻¹)⁻¹ := congrArg Inv.inv inverseEquality
    _ = second := by simp

/-- The homomorphism into the actual joint local-fiber kernel is injective;
subgroup packaging neither supplies nor discards the source probe evidence. -/
theorem finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_injective
    (E : Type) [Fintype E] :
    Function.Injective
      (finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom E) := by
  intro first second equality
  apply finiteAxisFoldNormalizedPermutationGeometrySectionHom_injective E
  exact congrArg
    (fun remainder : FiniteAxisFoldResidualLocalFiberKernel =>
      remainder.1.1.1.1)
    equality

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end
end AAT.AG.RealizationReconstruction
