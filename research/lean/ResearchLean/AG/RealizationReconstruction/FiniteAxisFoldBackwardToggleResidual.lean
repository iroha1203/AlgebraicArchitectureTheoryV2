import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldBackwardToggleSurvival
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualLocalFiberProjection
import Formal.Util.AssertStandardAxioms

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option maxHeartbeats 1200000

local instance finiteAxisFoldBackwardResidualAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

theorem finiteAxisFoldNormalizedExtensionBackward_axisMap :
    finiteAxisFoldNormalizedExtensionBackwardAut.hom.f.hom.base.upper.axisMap =
      _root_.id := by
  change finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base.upper.axisMap =
    _root_.id
  calc
    _ = ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
        finiteAxisFoldSouthwestExtensionBackwardAut).hom.1.base.upper.axisMap :=
      geomFiberTransportMap_axisMap
        finiteAxisFoldBCDatumSquare.context.square.semantic.square.top _
    _ = finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base.upper.axisMap :=
      exactGeometryPullMap_axisMap
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare) _
    _ = finiteAxisFoldExtensionBackwardGeometryFiberAut.hom.1.base.upper.axisMap := by
      simpa [finiteAxisFoldSouthwestExtensionBackwardAut] using
        geomFiberTransportMap_axisMap
          finiteAxisFoldSourceToSouthwestExtInstHom
          finiteAxisFoldExtensionBackwardGeometryFiberAut.hom
    _ = _ := rfl

private theorem finiteAxisFoldSouthwestExtensionBackward_coordinateEquiv
    (axis coordinate : Fin 3) :
    finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base.upper.coordinateEquiv
        axis coordinate = coordinate := by
  have factorization := congrArg
    (fun total => total.base.upper.coordinateEquiv axis coordinate)
    (geomFiberTransportMap_fac
      finiteAxisFoldSourceToSouthwestExtInstHom
      finiteAxisFoldExtensionBackwardGeometryFiberAut.hom)
  simpa [finiteAxisFoldSouthwestExtensionBackwardAut,
    GeometryTotalHom.comp, PackageTotalHom.comp,
    SignedExactCoreReadingHom.comp, geomFiberLift, geomTransportAlongHom,
    geomTransportAlongGeometryHom, transportAlongHom, transportAlongUpper,
    finiteAxisFoldExtensionBackwardGeometryFiberAut,
    finiteAxisFoldExtensionBackwardGeometryFiberHom,
    finiteAxisFoldExtensionBackwardGeometry,
    finiteAxisFoldExtensionBackwardGeomReadHom,
    finiteAxisFoldExtensionBackwardTotal,
    finiteAxisFoldExtensionBackwardUpper] using factorization

private theorem finiteAxisFoldExactLeftExtensionBackward_coordinateEquiv
    (axis coordinate : Fin 3) :
    (((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
        finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base.upper.coordinateEquiv
          axis coordinate) = coordinate := by
  have factorization := congrArg
    (fun total => total.base.upper.coordinateEquiv axis coordinate)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestExtensionBackwardAut.hom)
  have transported :
      (((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base.upper.coordinateEquiv
            axis coordinate) =
        finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base.upper.coordinateEquiv
          axis coordinate := by
    simpa [GeometryTotalHom.comp, PackageTotalHom.comp,
      SignedExactCoreReadingHom.comp, exactGeometryPullLift,
      UpperGeometryCleavage.generatedExactGeometryHom,
      UpperGeometryCleavage.exactBaseHom, inverseCorePackageHom,
      inverseCorePackageForwardUpper] using factorization
  exact transported.trans
    (finiteAxisFoldSouthwestExtensionBackward_coordinateEquiv axis coordinate)

private theorem finiteAxisFoldActualDirectExtensionBackward_coordinateEquiv
    (axis coordinate : Fin 3) :
    finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base.upper.coordinateEquiv
        axis coordinate = coordinate := by
  have factorization := congrArg
    (fun total => total.base.upper.coordinateEquiv axis coordinate)
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          finiteAxisFoldSouthwestExtensionBackwardAut.hom))
  have transported :
      finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base.upper.coordinateEquiv
          axis coordinate =
        (((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base.upper.coordinateEquiv
              axis coordinate) := by
    simpa [finiteAxisFoldActualDirectExtensionBackwardAut,
      GeometryTotalHom.comp, PackageTotalHom.comp,
      SignedExactCoreReadingHom.comp, geomFiberLift, geomTransportAlongHom,
      geomTransportAlongGeometryHom, transportAlongHom, transportAlongUpper]
      using factorization
  exact transported.trans
    (finiteAxisFoldExactLeftExtensionBackward_coordinateEquiv axis coordinate)

theorem finiteAxisFoldNormalizedExtensionBackward_coordinateEquiv
    (axis coordinate : Fin 3) :
    finiteAxisFoldNormalizedExtensionBackwardAut.hom.f.hom.base.upper.coordinateEquiv
        axis coordinate = coordinate := by
  change finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base.upper.coordinateEquiv
    axis coordinate = coordinate
  exact finiteAxisFoldActualDirectExtensionBackward_coordinateEquiv axis coordinate

private theorem finiteAxisFoldBackwardResidualContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

theorem finiteAxisFoldSouthwestExtensionBackward_contextForward_eq_id :
    finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  let canonical :=
    transportAlongHom finiteAxisFoldSourceGeometryPackage.core
      finiteModelDoctrineFromFixture
  let sourceContext := contextBackward canonical context
  have facbase := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac
      finiteAxisFoldSourceToSouthwestExtInstHom
      finiteAxisFoldExtensionBackwardGeometryFiberAut.hom)
  have factorization := congrArg
    (fun total => contextForward total sourceContext) facbase
  have hsection : contextForward canonical sourceContext = context :=
    canonicalContextSection_eq _ _ _
  change
    contextForward
        finiteAxisFoldTransportedExtensionBackwardAut.hom.1.base
        (contextForward canonical sourceContext) =
      contextForward canonical sourceContext at factorization
  rw [hsection] at factorization
  simpa [finiteAxisFoldSouthwestExtensionBackwardAut] using factorization

theorem finiteAxisFoldExactLeftExtensionBackward_contextForward_eq_id :
    ((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
        finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  let lift :=
    (exactGeometryPullLift
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber).base
  let pulled :=
    ((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
        finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base
  have facbase := congrArg (fun total => total.base)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestExtensionBackwardAut.hom)
  have factorization := congrArg
    (fun total => contextForward total context) facbase
  change
    contextForward lift (contextForward pulled context) =
      contextForward finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base
        (contextForward lift context) at factorization
  have southwestIdentity := congrFun
    finiteAxisFoldSouthwestExtensionBackward_contextForward_eq_id
    (contextForward lift context)
  change
    contextForward finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base
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
  exact finiteAxisFoldBackwardResidualContextObject_eq_of_ctx_eq cancelled

private noncomputable abbrev FiniteAxisFoldBackwardResidualPulledGeometryFiber :=
  (exactGeometryPullFunctor
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).obj
      finiteAxisFoldSouthwestGeometryFiber

theorem finiteAxisFoldActualDirectExtensionBackward_contextForward_eq_id :
    finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  let lift :=
    (geomFiberLift
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldBackwardResidualPulledGeometryFiber).base
  let sourceContext := contextBackward lift context
  have facbase := congrArg (fun total => total.base)
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          finiteAxisFoldSouthwestExtensionBackwardAut.hom))
  have factorization := congrArg
    (fun total => contextForward total sourceContext) facbase
  have hsection : contextForward lift sourceContext = context :=
    canonicalContextSection_eq _ _ _
  change
    contextForward finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base
        (contextForward lift sourceContext) =
      contextForward lift
        (contextForward
          ((exactGeometryPullFunctor
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
              finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base
          sourceContext) at factorization
  have exactLeftIdentity := congrFun
    finiteAxisFoldExactLeftExtensionBackward_contextForward_eq_id sourceContext
  change
    contextForward
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base
        sourceContext = sourceContext at exactLeftIdentity
  rw [exactLeftIdentity, hsection] at factorization
  exact factorization

theorem finiteAxisFoldNormalizedExtensionBackward_contextForward_eq_id :
    finiteAxisFoldNormalizedExtensionBackwardAut.hom.f.hom.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  change contextForward
      finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base context = context
  exact congrFun
    finiteAxisFoldActualDirectExtensionBackward_contextForward_eq_id context

noncomputable def finiteAxisFoldNormalizedExtensionBackwardAxisKernel :
    FiniteAxisFoldNormalizedAxisKernel :=
  ⟨finiteAxisFoldNormalizedExtensionBackwardAut, by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro axis
    exact congrFun finiteAxisFoldNormalizedExtensionBackward_axisMap axis⟩

noncomputable def finiteAxisFoldNormalizedExtensionBackwardAxisSignatureKernel :
    FiniteAxisFoldNormalizedAxisSignatureKernel :=
  ⟨finiteAxisFoldNormalizedExtensionBackwardAxisKernel, by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Equiv.ext
    intro value
    apply Prod.ext
    · exact congrFun finiteAxisFoldNormalizedExtensionBackward_axisMap value.1
    · exact finiteAxisFoldNormalizedExtensionBackward_coordinateEquiv value.1 value.2⟩

noncomputable def finiteAxisFoldNormalizedExtensionBackwardContextKernel :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel :=
  ⟨finiteAxisFoldNormalizedExtensionBackwardAxisSignatureKernel, by
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro context
    exact congrFun
      finiteAxisFoldNormalizedExtensionBackward_contextForward_eq_id context⟩

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end
end AAT.AG.RealizationReconstruction
