import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualBackwardToggle
import Formal.Util.AssertStandardAxioms

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

local instance finiteAxisFoldBackwardSurvivalAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The transported image of the source Boolean-false context at southwest. -/
noncomputable def finiteAxisFoldSouthwestBackwardToggleContext :
    finiteAxisFoldGeometryPackage.site.category :=
  contextForward
    (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
      finiteModelDoctrineFromFixture)
    (show finiteAxisFoldSourceGeometryPackage.site.category from
      ⟨finiteAxisFoldBooleanFalseContext⟩)

/-- Source-to-southwest opcartesian transport retains the nontrivial stored
backward action. -/
theorem finiteAxisFoldTransportedExtensionBackward_moves_southwestContext :
    contextBackward
        finiteAxisFoldTransportedExtensionBackwardAut.hom.1.base
        finiteAxisFoldSouthwestBackwardToggleContext ≠
      finiteAxisFoldSouthwestBackwardToggleContext := by
  intro equality
  have facbase :
      PackageTotalHom.comp
          (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
            finiteModelDoctrineFromFixture)
          finiteAxisFoldTransportedExtensionBackwardAut.hom.1.base =
        PackageTotalHom.comp
          finiteAxisFoldExtensionBackwardGeometryFiberAut.hom.1.base
          (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
            finiteModelDoctrineFromFixture) := by
    simpa [GeometryTotalHom.comp, geomFiberLift,
      geomTransportAlongGeometryHom] using congrArg
      (fun total => total.base)
      (geomFiberTransportMap_fac
        finiteAxisFoldSourceToSouthwestExtInstHom
        finiteAxisFoldExtensionBackwardGeometryFiberAut.hom)
  have factorization := congrArg
    (fun total =>
      contextBackward total finiteAxisFoldSouthwestBackwardToggleContext)
    facbase
  change
    contextBackward
        (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
          finiteModelDoctrineFromFixture)
        (contextBackward
          finiteAxisFoldTransportedExtensionBackwardAut.hom.1.base
          finiteAxisFoldSouthwestBackwardToggleContext) =
      contextBackward
        finiteAxisFoldExtensionBackwardGeometryFiberAut.hom.1.base
        (contextBackward
          (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
            finiteModelDoctrineFromFixture)
          finiteAxisFoldSouthwestBackwardToggleContext) at factorization
  have sourceCancel :
      contextBackward
          (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
            finiteModelDoctrineFromFixture)
          finiteAxisFoldSouthwestBackwardToggleContext =
        (show finiteAxisFoldSourceGeometryPackage.site.category from
          ⟨finiteAxisFoldBooleanFalseContext⟩) :=
    canonicalContextRetraction_eq _ _ _
  rw [equality, sourceCancel] at factorization
  exact finiteAxisFoldBooleanFalseContext_toggle_ne
    (congrArg (fun context => context.ctx) factorization).symm

private theorem finiteAxisFoldContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- Pull the southwest witness back through the generated exact-left lift. -/
noncomputable def finiteAxisFoldExactLeftBackwardToggleContext :
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
    finiteAxisFoldSouthwestBackwardToggleContext

/-- Generated exact pull also retains the nontrivial stored backward action;
the proof cancels the generated lift rather than unfolding the opaque
universal-property factor. -/
theorem finiteAxisFoldExactLeftExtensionBackward_moves_context :
    contextBackward
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base
        finiteAxisFoldExactLeftBackwardToggleContext ≠
      finiteAxisFoldExactLeftBackwardToggleContext := by
  intro equality
  have facbase := congrArg (fun total => total.base)
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestExtensionBackwardAut.hom)
  have factorization := congrArg
    (fun total =>
      contextBackward total finiteAxisFoldSouthwestBackwardToggleContext)
    facbase
  change
    contextBackward
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base
        finiteAxisFoldExactLeftBackwardToggleContext =
      contextBackward
        (exactGeometryPullLift
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
          finiteAxisFoldSouthwestGeometryFiber).base
        (contextBackward
          finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base
          finiteAxisFoldSouthwestBackwardToggleContext) at factorization
  rw [equality] at factorization
  have ctxeq := congrArg
    (fun context =>
      (contextForward
        (exactGeometryPullLift
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
          finiteAxisFoldSouthwestGeometryFiber).base context).ctx)
    factorization
  have leftCancel :=
    UpperGeometryCleavage.generatedExactContextForward_backward_ctx
      finiteAxisFoldSouthwestGeometryFiber.1
      (exactGeometryPullBaseHom
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        finiteAxisFoldSouthwestGeometryFiber)
      finiteAxisFoldSouthwestBackwardToggleContext
  have rightCancel :=
    UpperGeometryCleavage.generatedExactContextForward_backward_ctx
      finiteAxisFoldSouthwestGeometryFiber.1
      (exactGeometryPullBaseHom
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        finiteAxisFoldSouthwestGeometryFiber)
      (contextBackward
        finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base
        finiteAxisFoldSouthwestBackwardToggleContext)
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
        finiteAxisFoldSouthwestBackwardToggleContext)).ctx =
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
          finiteAxisFoldSouthwestExtensionBackwardAut.hom.1.base
          finiteAxisFoldSouthwestBackwardToggleContext))).ctx at ctxeq
  rw [leftCancel, rightCancel] at ctxeq
  apply finiteAxisFoldTransportedExtensionBackward_moves_southwestContext
  exact (finiteAxisFoldContextObject_eq_of_ctx_eq ctxeq).symm

private noncomputable abbrev FiniteAxisFoldBackwardPulledGeometryFiber :=
  (exactGeometryPullFunctor
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).obj
      finiteAxisFoldSouthwestGeometryFiber

/-- The exact-left witness transported to the actual direct endpoint. -/
noncomputable def finiteAxisFoldActualBackwardToggleContext :
    (authoredExactDirectGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))).1.site.category :=
  contextForward
    (geomFiberLift
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldBackwardPulledGeometryFiber).base
    finiteAxisFoldExactLeftBackwardToggleContext

/-- Top transport retains the stored backward movement. -/
theorem finiteAxisFoldActualDirectExtensionBackward_moves_context :
    contextBackward
        finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base
        finiteAxisFoldActualBackwardToggleContext ≠
      finiteAxisFoldActualBackwardToggleContext := by
  intro equality
  have facbase :
      PackageTotalHom.comp
          (geomFiberLift
            finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
            FiniteAxisFoldBackwardPulledGeometryFiber).base
          finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base =
        PackageTotalHom.comp
          (((exactGeometryPullFunctor
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
              finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base)
          (geomFiberLift
            finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
            FiniteAxisFoldBackwardPulledGeometryFiber).base := by
    simpa [finiteAxisFoldActualDirectExtensionBackwardAut,
      FiniteAxisFoldBackwardPulledGeometryFiber, GeometryTotalHom.comp] using
      congrArg (fun total => total.base)
        (geomFiberTransportMap_fac
          finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
          ((exactGeometryPullFunctor
            (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
              finiteAxisFoldSouthwestExtensionBackwardAut.hom))
  have factorization := congrArg
    (fun total =>
      contextBackward total finiteAxisFoldActualBackwardToggleContext)
    facbase
  change
    contextBackward
        (geomFiberLift
          finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
          FiniteAxisFoldBackwardPulledGeometryFiber).base
        (contextBackward
          finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base
          finiteAxisFoldActualBackwardToggleContext) =
      contextBackward
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1.base
        (contextBackward
          (geomFiberLift
            finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
            FiniteAxisFoldBackwardPulledGeometryFiber).base
          finiteAxisFoldActualBackwardToggleContext) at factorization
  have sourceCancel :
      contextBackward
          (geomFiberLift
            finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
            FiniteAxisFoldBackwardPulledGeometryFiber).base
          finiteAxisFoldActualBackwardToggleContext =
        finiteAxisFoldExactLeftBackwardToggleContext :=
    canonicalContextRetraction_eq _ _ _
  rw [equality, sourceCancel] at factorization
  exact finiteAxisFoldExactLeftExtensionBackward_moves_context
    factorization.symm

/-- Canonical normalization retains the same nontrivial stored backward
action on the actual transported witness. -/
theorem finiteAxisFoldNormalizedExtensionBackward_moves_context :
    contextBackward
        finiteAxisFoldNormalizedExtensionBackwardAut.hom.f.hom.base
        finiteAxisFoldActualBackwardToggleContext ≠
      finiteAxisFoldActualBackwardToggleContext := by
  intro equality
  apply finiteAxisFoldActualDirectExtensionBackward_moves_context
  change
    contextBackward
        (PackageTotalHom.comp
          (canonicalObjectNormalizationTotal
            finiteAxisFoldActualDirectAdmissibleGeometry.obj.core
            finiteAxisFoldActualDirectAdmissibleGeometry.property)
          finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base)
        finiteAxisFoldActualBackwardToggleContext =
      finiteAxisFoldActualBackwardToggleContext at equality
  change
    contextBackward
        (canonicalObjectNormalizationTotal
          finiteAxisFoldActualDirectAdmissibleGeometry.obj.core
          finiteAxisFoldActualDirectAdmissibleGeometry.property)
        (contextBackward
          finiteAxisFoldActualDirectExtensionBackwardAut.hom.1.base
          finiteAxisFoldActualBackwardToggleContext) =
      finiteAxisFoldActualBackwardToggleContext at equality
  exact equality

/-- The actual normalized candidate survives as a nonidentity
automorphism. -/
theorem finiteAxisFoldNormalizedExtensionBackwardAut_ne_one :
    finiteAxisFoldNormalizedExtensionBackwardAut ≠ 1 := by
  intro equality
  apply finiteAxisFoldNormalizedExtensionBackward_moves_context
  exact congrArg
    (fun automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry =>
      contextBackward automorphism.hom.f.hom.base
        finiteAxisFoldActualBackwardToggleContext)
    equality

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end
end AAT.AG.RealizationReconstruction
