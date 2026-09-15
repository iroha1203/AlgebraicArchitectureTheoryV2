import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualObjectOperationRigidity
import Formal.Util.AssertStandardAxioms

/-!
# Equation-data rigidity in the finite-axis-fold residual kernel

The fixed actual endpoint has one equation index.  Consequently every residual
equation transport fixes that index and preserves the role attached to the same
index, after the already proved Atom, object, and operation identifications.

The context equivalence itself is deliberately not identified with the
identity: the fixed equation reading is constant in the context variable, so
index rigidity does not classify that remaining component.  This module also
does not identify transported observable values; those retain dependent casts
along the context equivalence and remain a separate obligation.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization CrossStageCoherence TransportCoherence

noncomputable section

local instance finiteAxisFoldResidualEquationAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

private noncomputable abbrev FiniteAxisFoldResidualEquationCore :=
  finiteAxisFoldActualDirectAdmissibleGeometry.obj.core

private noncomputable abbrev ResidualEquationUpper
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel) :
    SignedExactCoreReadingHom FiniteAxisFoldResidualEquationCore
      FiniteAxisFoldResidualEquationCore :=
  remainder.1.1.hom.f.hom.base.upper

private noncomputable abbrev ResidualEquationTransport
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel) :=
  (ResidualEquationUpper remainder).equationTransport

private theorem finiteAxisFoldResidualEquationIndex_subsingleton
    (first second : FiniteAxisFoldResidualEquationCore.equationSystem.Index) :
    first = second := by
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
  let outer := transportAlongUpper pulled topData.doctrineHom
  apply outer.equationTransport.equationEquiv.symm.injective
  let backward := inverseCorePackageBackwardUpper southwest.1.core leftData
  apply backward.equationTransport.equationEquiv.symm.injective
  let support := transportAlongUpper finiteWitnessSourcePackage
    finiteModelDoctrineFromFixture
  apply support.equationTransport.equationEquiv.symm.injective
  change PUnit.unit = PUnit.unit
  rfl

/-- The complete equation-index equivalence of every residual element is the
identity on the fixed singleton family. -/
theorem finiteAxisFoldResidual_equationEquiv_eq_refl
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel) :
    (ResidualEquationTransport remainder).equationEquiv = Equiv.refl _ := by
  apply Equiv.ext
  intro index
  exact finiteAxisFoldResidualEquationIndex_subsingleton _ _

/-- Every residual equation map fixes every equation index. -/
theorem finiteAxisFoldResidual_equationMap_apply
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    (index : FiniteAxisFoldResidualEquationCore.equationSystem.Index) :
    (ResidualEquationTransport remainder).equationMap index = index := by
  exact congrFun
    (congrArg Equiv.toFun
      (finiteAxisFoldResidual_equationEquiv_eq_refl remainder)) index

/-- Every residual transport preserves the role at the same actual equation
index; unlike the context component, the index cannot move. -/
theorem finiteAxisFoldResidual_equationRole_eq
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    (index : FiniteAxisFoldResidualEquationCore.equationSystem.Index) :
    FiniteAxisFoldResidualEquationCore.equationSystem.role
        ((ResidualEquationTransport remainder).equationMap index) =
      FiniteAxisFoldResidualEquationCore.equationSystem.role index :=
  (ResidualEquationTransport remainder).role_eq index

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
