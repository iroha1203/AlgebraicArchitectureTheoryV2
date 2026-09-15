import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualContextInverseProjection
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualEquationRigidity
import Formal.Util.AssertStandardAxioms

/-!
# Equation-observable rigidity in the forward-context kernel

The actual finite-axis-fold endpoint observable ring is not definitionally
`Int`: it is carried through the fixed support, exact-left-pull, and top
transport construction.  This file follows the actual inverse transport chain
to construct a ring equivalence from every endpoint observable fiber to `Int`.

On the full forward-context kernel, every forwarded context is already proved
equal to its source.  We compose the actual observable transport with the
dependent cast supplied by that equality, obtaining a self-equivalence of each
actual endpoint observable fiber.  Conjugation through the constructed
equivalence to `Int` proves that every such self-equivalence is the identity,
and hence that the raw observable equivalence is exactly the inverse canonical
cast.  Neither an endpoint observable identification nor an observable
transport certificate is accepted as input.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization CrossStageCoherence TransportCoherence

noncomputable section

local instance finiteAxisFoldEquationObservableAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

private noncomputable abbrev FiniteAxisFoldEquationObservableEndpointCore :=
  finiteAxisFoldActualDirectAdmissibleGeometry.obj.core

/-- Every actual endpoint observable fiber is identified with `Int` by
following the inverse of the three fixed construction transports. -/
noncomputable def finiteAxisFoldEndpointObservableEquivInt
    (context : Site.ContextCategoryObject
      FiniteAxisFoldEquationObservableEndpointCore.contextPreorder) :
    FiniteAxisFoldEquationObservableEndpointCore.algebra.equationSystem.Observable
        context ≃+* Int := by
  let southwest := authoredSouthwestGeometryFiberAt finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second) Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
  let leftData := exactGeometryPullBaseHom
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare) southwest
  let pulled := inverseCorePackage southwest.1.core leftData
  let topData := geomFiberBaseHom
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    (authoredExactLeftPulledGeometryAt finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second) Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second)))
  let backTop := transportAlongUpperInverse pulled topData.doctrineHom
  let backLeft := inverseCorePackageForwardUpper southwest.1.core leftData
  let backSupport := transportAlongUpperInverse finiteWitnessSourcePackage
    finiteModelDoctrineFromFixture
  exact ((backTop.equationTransport.observableEquiv context).trans
    (backLeft.equationTransport.observableEquiv
      (backTop.equationTransport.contextForward context))).trans
    (backSupport.equationTransport.observableEquiv
      (backLeft.equationTransport.contextForward
        (backTop.equationTransport.contextForward context)))

private theorem finiteAxisFoldRingEquivInt_eq_refl (equiv : Int ≃+* Int) :
    equiv = RingEquiv.refl Int := by
  ext value
  exact map_intCast equiv value

private theorem finiteAxisFoldSelfRingEquiv_eq_refl_of_equivInt
    {R : Type} [CommRing R] (identification : R ≃+* Int)
    (automorphism : R ≃+* R) :
    automorphism = RingEquiv.refl R := by
  have conjugate_eq :
      (identification.symm.trans automorphism).trans identification =
        RingEquiv.refl Int :=
    finiteAxisFoldRingEquivInt_eq_refl _
  apply RingEquiv.ext
  intro value
  apply identification.injective
  calc
    identification (automorphism value) =
        ((identification.symm.trans automorphism).trans identification)
          (identification value) := by
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply,
        RingEquiv.symm_apply_apply]
    _ = (RingEquiv.refl Int) (identification value) :=
      DFunLike.congr_fun conjugate_eq (identification value)
    _ = identification value := rfl

/-- The actual observable equivalence, normalized to a self-equivalence by the
proved equality between its forwarded context object and the source context. -/
noncomputable def finiteAxisFoldResidualObservableSelfEquiv
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : Site.ContextCategoryObject
      FiniteAxisFoldEquationObservableEndpointCore.contextPreorder) :
    FiniteAxisFoldEquationObservableEndpointCore.algebra.equationSystem.Observable
        context ≃+*
      FiniteAxisFoldEquationObservableEndpointCore.algebra.equationSystem.Observable
        context := by
  let transport :=
    remainder.1.1.1.hom.f.hom.base.upper.equationTransport
  have context_forward_eq : transport.contextForward context = context :=
    finiteAxisFoldResidualContextKernel_context_eq remainder context
  exact (transport.observableEquiv context).trans
    (RingEquiv.cast
      (R := fun targetContext =>
        FiniteAxisFoldEquationObservableEndpointCore.algebra.equationSystem.Observable
          targetContext)
      context_forward_eq)

/-- Every context-indexed actual observable transport in the full
forward-context kernel is identity after normalization by the pointwise
context equality proved from kernel membership. -/
theorem finiteAxisFoldResidualContextKernel_observableSelfEquiv_eq_refl
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : Site.ContextCategoryObject
      FiniteAxisFoldEquationObservableEndpointCore.contextPreorder) :
    finiteAxisFoldResidualObservableSelfEquiv remainder context =
      RingEquiv.refl _ := by
  apply finiteAxisFoldSelfRingEquiv_eq_refl_of_equivInt
    (finiteAxisFoldEndpointObservableEquivInt context)

/-- The raw actual observable equivalence is the inverse of the dependent cast
generated by the proved forward-context equality.  This states the same
rigidity before composing the codomain back to the source fiber. -/
theorem finiteAxisFoldResidualContextKernel_observableEquiv_eq_cast_symm
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : Site.ContextCategoryObject
      FiniteAxisFoldEquationObservableEndpointCore.contextPreorder) :
    remainder.1.1.1.hom.f.hom.base.upper.equationTransport.observableEquiv
        context =
      (RingEquiv.cast
        (R := fun targetContext =>
          FiniteAxisFoldEquationObservableEndpointCore.algebra.equationSystem.Observable
            targetContext)
        (finiteAxisFoldResidualContextKernel_context_eq remainder context)).symm := by
  let castBack := RingEquiv.cast
    (R := fun targetContext =>
      FiniteAxisFoldEquationObservableEndpointCore.algebra.equationSystem.Observable
        targetContext)
    (finiteAxisFoldResidualContextKernel_context_eq remainder context)
  apply RingEquiv.ext
  intro value
  apply castBack.injective
  change castBack
      (remainder.1.1.1.hom.f.hom.base.upper.equationTransport.observableEquiv
        context value) = castBack (castBack.symm value)
  rw [castBack.apply_symm_apply]
  have normalized_eq := DFunLike.congr_fun
    (congrArg RingEquiv.toEquiv
      (finiteAxisFoldResidualContextKernel_observableSelfEquiv_eq_refl
        remainder context)) value
  exact normalized_eq

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
