import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldSourcePermutationGeometryAction
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualContextProjection
import Formal.Util.AssertStandardAxioms

/-!
# Arbitrary finite Extension permutations in the residual context kernel

Every independently supplied permutation of an Extension carrier has identity
forward axis, coordinate, and context actions after the fixed southwest,
exact-left, top-transport, admissible, and normalization route.  This file
packages those constructed identities as a homomorphism into the residual
context kernel.  It does not assert local-fiber identity, injectivity, image
coverage, or full residual coverage.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

local instance finiteAxisFoldGenericPermutationResidualAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

variable {E : Type} (permutation : Equiv.Perm E)

local notation "genericPermutationGeometry" =>
  finiteAxisFoldSourceBackwardPermutationGeometry permutation⁻¹
local notation "genericPermutationGeometryFiberAut" =>
  (finiteAxisFoldSourcePermutationGeometryFiberSectionHom E) permutation
local notation "southwestGenericPermutationAut" =>
  (finiteAxisFoldSouthwestPermutationGeometrySectionHom E) permutation
local notation "actualDirectGenericPermutationAut" =>
  (finiteAxisFoldActualDirectPermutationGeometrySectionHom E) permutation
local notation "normalizedGenericPermutationAut" =>
  (finiteAxisFoldNormalizedPermutationGeometrySectionHom E) permutation

theorem finiteAxisFoldNormalizedGenericPermutation_axisMap :
    (normalizedGenericPermutationAut).hom.f.hom.base.upper.axisMap =
      _root_.id := by
  change (actualDirectGenericPermutationAut).hom.1.base.upper.axisMap =
    _root_.id
  calc
    _ = ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
        southwestGenericPermutationAut).hom.1.base.upper.axisMap :=
      geomFiberTransportMap_axisMap
        finiteAxisFoldBCDatumSquare.context.square.semantic.square.top _
    _ = (southwestGenericPermutationAut).hom.1.base.upper.axisMap :=
      exactGeometryPullMap_axisMap
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare) _
    _ = (genericPermutationGeometryFiberAut).hom.1.base.upper.axisMap := by
      simpa [finiteAxisFoldSouthwestPermutationGeometrySectionHom] using
        geomFiberTransportMap_axisMap
          finiteAxisFoldSourceToSouthwestExtInstHom
          (genericPermutationGeometryFiberAut).hom
    _ = _ := rfl

private theorem finiteAxisFoldSouthwestGenericPermutation_coordinateEquiv
    (axis coordinate : Fin 3) :
    (southwestGenericPermutationAut).hom.1.base.upper.coordinateEquiv
        axis coordinate = coordinate := by
  have factorization := congrArg
    (fun total => total.base.upper.coordinateEquiv axis coordinate)
    (geomFiberTransportMap_fac
      finiteAxisFoldSourceToSouthwestExtInstHom
      (genericPermutationGeometryFiberAut).hom)
  simpa [finiteAxisFoldSouthwestPermutationGeometrySectionHom,
    GeometryTotalHom.comp, PackageTotalHom.comp,
    SignedExactCoreReadingHom.comp, geomFiberLift, geomTransportAlongHom,
    geomTransportAlongGeometryHom, transportAlongHom, transportAlongUpper,
    finiteAxisFoldSourcePermutationGeometryFiberSectionHom,
    finiteAxisFoldSourcePermutationGeometryAut,
    finiteAxisFoldSourceBackwardPermutationGeometry,
    finiteAxisFoldSourceBackwardPermutationGeomReadHom,
    finiteAxisFoldSourceBackwardPermutationTotal,
    finiteAxisFoldSourceBackwardPermutationUpper] using factorization

private theorem finiteAxisFoldExactLeftGenericPermutation_coordinateEquiv
    (axis coordinate : Fin 3) :
    (((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
        (southwestGenericPermutationAut).hom).1.base.upper.coordinateEquiv
          axis coordinate) = coordinate := by
  have factorization := congrArg
    (fun total => total.base.upper.coordinateEquiv axis coordinate)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      (southwestGenericPermutationAut).hom)
  have transported :
      (((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          (southwestGenericPermutationAut).hom).1.base.upper.coordinateEquiv
            axis coordinate) =
        (southwestGenericPermutationAut).hom.1.base.upper.coordinateEquiv
          axis coordinate := by
    simpa [GeometryTotalHom.comp, PackageTotalHom.comp,
      SignedExactCoreReadingHom.comp, exactGeometryPullLift,
      UpperGeometryCleavage.generatedExactGeometryHom,
      UpperGeometryCleavage.exactBaseHom, inverseCorePackageHom,
      inverseCorePackageForwardUpper] using factorization
  exact transported.trans
    (finiteAxisFoldSouthwestGenericPermutation_coordinateEquiv permutation axis coordinate)

private theorem finiteAxisFoldActualDirectGenericPermutation_coordinateEquiv
    (axis coordinate : Fin 3) :
    (actualDirectGenericPermutationAut).hom.1.base.upper.coordinateEquiv
        axis coordinate = coordinate := by
  have factorization := congrArg
    (fun total => total.base.upper.coordinateEquiv axis coordinate)
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          (southwestGenericPermutationAut).hom))
  have transported :
      (actualDirectGenericPermutationAut).hom.1.base.upper.coordinateEquiv
          axis coordinate =
        (((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1.base.upper.coordinateEquiv
              axis coordinate) := by
    simpa [finiteAxisFoldActualDirectPermutationGeometrySectionHom,
      GeometryTotalHom.comp, PackageTotalHom.comp,
      SignedExactCoreReadingHom.comp, geomFiberLift, geomTransportAlongHom,
      geomTransportAlongGeometryHom, transportAlongHom, transportAlongUpper]
      using factorization
  exact transported.trans
    (finiteAxisFoldExactLeftGenericPermutation_coordinateEquiv permutation axis coordinate)

theorem finiteAxisFoldNormalizedGenericPermutation_coordinateEquiv
    (axis coordinate : Fin 3) :
    (normalizedGenericPermutationAut).hom.f.hom.base.upper.coordinateEquiv
        axis coordinate = coordinate := by
  change (actualDirectGenericPermutationAut).hom.1.base.upper.coordinateEquiv
    axis coordinate = coordinate
  exact finiteAxisFoldActualDirectGenericPermutation_coordinateEquiv permutation axis coordinate

private theorem finiteAxisFoldGenericPermutationResidualContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

theorem finiteAxisFoldSouthwestGenericPermutation_contextForward_eq_id :
    (southwestGenericPermutationAut).hom.1.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  let canonical :=
    transportAlongHom finiteAxisFoldSourceGeometryPackage.core
      finiteModelDoctrineFromFixture
  let sourceContext := contextBackward canonical context
  have facbase := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac
      finiteAxisFoldSourceToSouthwestExtInstHom
      (genericPermutationGeometryFiberAut).hom)
  have factorization := congrArg
    (fun total => contextForward total sourceContext) facbase
  have hsection : contextForward canonical sourceContext = context :=
    canonicalContextSection_eq _ _ _
  change
    contextForward
      (southwestGenericPermutationAut).hom.1.base
        (contextForward canonical sourceContext) =
      contextForward canonical sourceContext at factorization
  rw [hsection] at factorization
  simpa [finiteAxisFoldSouthwestPermutationGeometrySectionHom] using factorization

theorem finiteAxisFoldExactLeftGenericPermutation_contextForward_eq_id :
    ((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
        (southwestGenericPermutationAut).hom).1.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  let lift :=
    (exactGeometryPullLift
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber).base
  let pulled :=
    ((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
        (southwestGenericPermutationAut).hom).1.base
  have facbase := congrArg (fun total => total.base)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      (southwestGenericPermutationAut).hom)
  have factorization := congrArg
    (fun total => contextForward total context) facbase
  change
    contextForward lift (contextForward pulled context) =
      contextForward (southwestGenericPermutationAut).hom.1.base
        (contextForward lift context) at factorization
  have southwestIdentity := congrFun
    (finiteAxisFoldSouthwestGenericPermutation_contextForward_eq_id permutation)
    (contextForward lift context)
  change
    contextForward (southwestGenericPermutationAut).hom.1.base
        (contextForward lift context) = contextForward lift context
      at southwestIdentity
  rw [southwestIdentity] at factorization
  have cancelled := congrArg
    (fun target => (contextBackward lift target).ctx) factorization
  change
    (contextBackward
      (UpperGeometryCleavage.exactBaseHom
        finiteAxisFoldSouthwestGeometryFiber.1
        (exactGeometryPullBaseHom
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
          finiteAxisFoldSouthwestGeometryFiber))
      (contextForward
        (UpperGeometryCleavage.exactBaseHom
          finiteAxisFoldSouthwestGeometryFiber.1
          (exactGeometryPullBaseHom
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
            finiteAxisFoldSouthwestGeometryFiber))
        (contextForward pulled context))).ctx =
    (contextBackward
      (UpperGeometryCleavage.exactBaseHom
        finiteAxisFoldSouthwestGeometryFiber.1
        (exactGeometryPullBaseHom
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
          finiteAxisFoldSouthwestGeometryFiber))
      (contextForward
        (UpperGeometryCleavage.exactBaseHom
          finiteAxisFoldSouthwestGeometryFiber.1
          (exactGeometryPullBaseHom
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
            finiteAxisFoldSouthwestGeometryFiber))
        context)).ctx at cancelled
  have leftCancel :
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom
          finiteAxisFoldSouthwestGeometryFiber.1
          (exactGeometryPullBaseHom
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
            finiteAxisFoldSouthwestGeometryFiber))
        (contextForward
          (UpperGeometryCleavage.exactBaseHom
            finiteAxisFoldSouthwestGeometryFiber.1
            (exactGeometryPullBaseHom
              (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
              finiteAxisFoldSouthwestGeometryFiber))
          (contextForward pulled context))).ctx =
        (contextForward pulled context).ctx := by
    simpa using
      UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
        finiteAxisFoldSouthwestGeometryFiber.1
        (exactGeometryPullBaseHom
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
          finiteAxisFoldSouthwestGeometryFiber)
        (contextForward pulled context)
  have rightCancel :
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom
          finiteAxisFoldSouthwestGeometryFiber.1
          (exactGeometryPullBaseHom
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
            finiteAxisFoldSouthwestGeometryFiber))
        (contextForward
          (UpperGeometryCleavage.exactBaseHom
            finiteAxisFoldSouthwestGeometryFiber.1
            (exactGeometryPullBaseHom
              (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
              finiteAxisFoldSouthwestGeometryFiber))
          context)).ctx = context.ctx := by
    simpa using
      UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
        finiteAxisFoldSouthwestGeometryFiber.1
        (exactGeometryPullBaseHom
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
          finiteAxisFoldSouthwestGeometryFiber)
        context
  rw [leftCancel, rightCancel] at cancelled
  exact finiteAxisFoldGenericPermutationResidualContextObject_eq_of_ctx_eq cancelled

private noncomputable abbrev FiniteAxisFoldGenericPermutationResidualPulledGeometryFiber :=
  (exactGeometryPullFunctor
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).obj
      finiteAxisFoldSouthwestGeometryFiber

theorem finiteAxisFoldActualDirectGenericPermutation_contextForward_eq_id :
    (actualDirectGenericPermutationAut).hom.1.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  let lift :=
    (geomFiberLift
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldGenericPermutationResidualPulledGeometryFiber).base
  let sourceContext := contextBackward lift context
  have facbase := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          (southwestGenericPermutationAut).hom))
  have factorization := congrArg
    (fun total => contextForward total sourceContext) facbase
  have hsection : contextForward lift sourceContext = context :=
    canonicalContextSection_eq _ _ _
  change
    contextForward (actualDirectGenericPermutationAut).hom.1.base
        (contextForward lift sourceContext) =
      contextForward lift
        (contextForward
          ((exactGeometryPullFunctor
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
              (southwestGenericPermutationAut).hom).1.base
          sourceContext) at factorization
  have exactLeftIdentity := congrFun
    (finiteAxisFoldExactLeftGenericPermutation_contextForward_eq_id permutation)
    sourceContext
  change
    contextForward
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            (southwestGenericPermutationAut).hom).1.base
        sourceContext = sourceContext at exactLeftIdentity
  rw [exactLeftIdentity, hsection] at factorization
  exact factorization

theorem finiteAxisFoldNormalizedGenericPermutation_contextForward_eq_id :
    (normalizedGenericPermutationAut).hom.f.hom.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  change contextForward
      (actualDirectGenericPermutationAut).hom.1.base context = context
  exact congrFun
    (finiteAxisFoldActualDirectGenericPermutation_contextForward_eq_id permutation)
    context

theorem finiteAxisFoldNormalizedGenericPermutation_mem_axisKernel :
    normalizedGenericPermutationAut ∈
      FiniteAxisFoldNormalizedAxisKernel := by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro axis
    exact congrFun
      (finiteAxisFoldNormalizedGenericPermutation_axisMap permutation) axis

noncomputable def finiteAxisFoldNormalizedPermutationAxisKernelSectionHom
    (E : Type) :
    Equiv.Perm E →* FiniteAxisFoldNormalizedAxisKernel :=
  (finiteAxisFoldNormalizedPermutationGeometrySectionHom E).codRestrict
    FiniteAxisFoldNormalizedAxisKernel
    (fun permutation =>
      finiteAxisFoldNormalizedGenericPermutation_mem_axisKernel permutation)

theorem finiteAxisFoldNormalizedGenericPermutation_mem_axisSignatureKernel :
    finiteAxisFoldNormalizedPermutationAxisKernelSectionHom E permutation ∈
      FiniteAxisFoldNormalizedAxisSignatureKernel := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Equiv.ext
    intro value
    apply Prod.ext
    · exact congrFun
        (finiteAxisFoldNormalizedGenericPermutation_axisMap permutation) value.1
    · exact finiteAxisFoldNormalizedGenericPermutation_coordinateEquiv
        permutation value.1 value.2

noncomputable def
    finiteAxisFoldNormalizedPermutationAxisSignatureKernelSectionHom
    (E : Type) :
    Equiv.Perm E →* FiniteAxisFoldNormalizedAxisSignatureKernel :=
  (finiteAxisFoldNormalizedPermutationAxisKernelSectionHom E).codRestrict
    FiniteAxisFoldNormalizedAxisSignatureKernel
    (fun permutation =>
      finiteAxisFoldNormalizedGenericPermutation_mem_axisSignatureKernel
        permutation)

theorem finiteAxisFoldNormalizedGenericPermutation_mem_contextKernel :
    finiteAxisFoldNormalizedPermutationAxisSignatureKernelSectionHom E
        permutation ∈
      FiniteAxisFoldNormalizedAxisSignatureContextKernel := by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro context
    exact congrFun
      (finiteAxisFoldNormalizedGenericPermutation_contextForward_eq_id permutation)
      context

noncomputable def finiteAxisFoldNormalizedPermutationContextKernelSectionHom
    (E : Type) :
    Equiv.Perm E →*
      FiniteAxisFoldNormalizedAxisSignatureContextKernel :=
  (finiteAxisFoldNormalizedPermutationAxisSignatureKernelSectionHom E).codRestrict
    FiniteAxisFoldNormalizedAxisSignatureContextKernel
    (fun permutation =>
      finiteAxisFoldNormalizedGenericPermutation_mem_contextKernel permutation)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end
end AAT.AG.RealizationReconstruction
