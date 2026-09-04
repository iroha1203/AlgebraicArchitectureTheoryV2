import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeTransportIdentityClassification
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeObservableExactness
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeRawFailureLocus
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportWitnesses

/-!
# G-116 finite witness packet

This module packages every clause of G-116(h) on the fixed finite axis-fold
datum, its generated cochain, and its second diagnostic cell.  The two object
pairs have distinct roles: auxiliary decorations witness noninjectivity over
one configuration, while the cyclic and acyclic configurations are separated
by the selected equation residual.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteWitnessPacketAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

private noncomputable abbrev finiteAxisFoldGeneratedCochain :
    DefectCochain finiteAxisFoldBCDatumSquare.toTransportData :=
  initialRawDefectCochain finiteAxisFoldBCDatumSquare.toTransportData

private noncomputable abbrev finiteAxisFoldSecondCell :
    finiteAxisFoldBCDatumSquare.context.Category :=
  Discrete.mk DoubleDiamondTwoCell.second

/-- The cyclic and acyclic objects have different Atom configurations. -/
theorem finiteAxisFold_cyclic_configuration_ne_acyclic :
    FiniteModel.object.configuration ≠
      FiniteModel.acyclicObject.configuration := by
  intro equality
  have cyclic : FiniteModel.hasDependencyCycle FiniteModel.object := by
    simpa [FiniteModel.hasCycleWitness, FiniteModel.hasDependencyCycle] using
      FiniteModel.object_hasCycleWitness
  have acyclic : ¬ FiniteModel.hasDependencyCycle FiniteModel.acyclicObject := by
    intro cycle
    exact cycle.1
  apply acyclic
  simpa only [FiniteModel.hasDependencyCycle, equality] using cyclic

/-- The selected finite residual distinguishes the cyclic and acyclic
configurations inside the fixed support package. -/
theorem finiteAxisFold_supportResidual_separates_cyclic_acyclic :
    ∃ (W : Site.ContextCategoryObject
        finiteAxisFoldSupportPackage.algebra.contextPreorder)
      (index : finiteAxisFoldSupportPackage.algebra.equationSystem.Index)
      (atom : FiniteModel.carrier.Atom),
      finiteAxisFoldSupportPackage.algebra.equationSystem.equationResidual
          W (transportArchitectureObject
            finiteModelDoctrineFromFixture.atomEquiv FiniteModel.object)
            index atom ≠
        finiteAxisFoldSupportPackage.algebra.equationSystem.equationResidual
          W (transportArchitectureObject
            finiteModelDoctrineFromFixture.atomEquiv FiniteModel.acyclicObject)
            index atom := by
  let transport := transportAlongEquationSystemExact
    finiteWitnessSourcePackage finiteModelDoctrineFromFixture
  let sourceW : Site.ContextCategoryObject
      finiteWitnessSourcePackage.algebra.contextPreorder :=
    Site.ContextCategoryObject.of
      finiteWitnessSourcePackage.algebra.contextPreorder
      FiniteModel.equationProbeContext
  refine ⟨transport.contextFunctor.obj sourceW,
    transport.equationMap PUnit.unit,
    finiteModelDoctrineFromFixture.atomEquiv
      FiniteModel.FiniteAtom.componentA, ?_⟩
  intro targetEquality
  have sourceEquality :
      finiteWitnessSourcePackage.algebra.equationSystem.equationResidual
          sourceW FiniteModel.object PUnit.unit
            FiniteModel.FiniteAtom.componentA =
        finiteWitnessSourcePackage.algebra.equationSystem.equationResidual
          sourceW FiniteModel.acyclicObject PUnit.unit
            FiniteModel.FiniteAtom.componentA := by
    apply (transport.observableEquiv sourceW).injective
    rw [transport.equationResidual_eq, transport.equationResidual_eq]
    exact targetEquality
  exact finiteSelectiveTwo_noCycleResidual_object_sensitive sourceEquality

/-- The generated cochain fires at the fixed second cell. -/
theorem finiteAxisFold_generatedCochain_second_ne_one :
    finiteAxisFoldGeneratedCochain DoubleDiamondTwoCell.second ≠ 1 := by
  change initialRawDefectCochain
      finiteAxisFoldBCDatumSquare.toTransportData
        DoubleDiamondTwoCell.second ≠ 1
  rw [finiteAxisFold_toTransportData, finiteAxisFold_initialRawDefect_second]
  exact finiteAxisFoldSwap_ne_one

/-- G-116(h): all required evidence on the fixed finite axis-fold cell in one
packet.  The final conjunct is the literal equation-residual equality on the
actual via-base package `P'`. -/
theorem finiteAxisFold_idempotentExchange_witnessPacket :
    let input := finiteAxisFoldBCDatumSquare
    let rawCell := DoubleDiamondTwoCell.second
    let cell : input.context.Category := Discrete.mk rawCell
    let cochain := initialRawDefectCochain input.toTransportData
    let P := input.context.supportPackage rawCell
    let P' := ((authoredSupportViaBaseRoute input.context).obj cell).1
    cochain rawCell ≠ 1 ∧
    CanonicalObjectNormalizationAdmissible P ∧
    (∃ x₁ x₂ : ArchitectureObject FiniteModel.carrier,
      x₁ ≠ x₂ ∧
      x₁.configuration = x₂.configuration ∧
      canonicalObjectNormalization P x₁ =
        canonicalObjectNormalization P x₂) ∧
    (∃ y₁ y₂ : ArchitectureObject FiniteModel.carrier,
      y₁.configuration ≠ y₂.configuration ∧
      ∃ (W : Site.ContextCategoryObject P.algebra.contextPreorder)
        (index : P.algebra.equationSystem.Index)
        (atom : FiniteModel.carrier.Atom),
        P.algebra.equationSystem.equationResidual W y₁ index atom ≠
          P.algebra.equationSystem.equationResidual W y₂ index atom) ∧
    authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell ≠
      𝟙 ((authoredSupportViaBaseRoute input.context).obj cell) ∧
    ¬ IsIso
      ((authoredDiagnosticObjectCollapseComparisonAtCochain
        input cochain).app cell) ∧
    ((∀ (W : Site.ContextCategoryObject P'.algebra.contextPreorder)
      (object : ArchitectureObject FiniteModel.carrier)
      (index : P'.algebra.equationSystem.Index)
      (atom : FiniteModel.carrier.Atom),
      P'.algebra.equationSystem.equationResidual W
          ((authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
            input cochain cell).1.upper.objectMap object) index atom =
        P'.algebra.equationSystem.equationResidual
          W object index atom) ∧
    (∀ (W : Site.ContextCategoryObject P'.algebra.contextPreorder)
      (object : ArchitectureObject FiniteModel.carrier)
      (index : P'.algebra.equationSystem.Index)
      (atom : FiniteModel.carrier.Atom),
      P'.algebra.equationSystem.equationResidual W
          (((authoredDiagnosticObjectCollapseComparisonAtCochain
            input cochain).app cell).1.upper.objectMap object) index atom =
        P'.algebra.equationSystem.equationResidual W
          (((authoredSupportCanonicalMate input.context).app cell).1.upper.objectMap
            object) index atom)) := by
  dsimp only
  have fires := finiteAxisFold_generatedCochain_second_ne_one
  have admissible := finiteAxisFold_canonicalNormalizationAdmissibleAt
    DoubleDiamondTwoCell.second
  have sameConfiguration :
      finiteAxisFoldUnitObject.configuration =
        finiteAxisFoldBoolObject.configuration := by
    simpa [finiteAxisFoldUnitObject, finiteAxisFoldBoolObject] using
      finiteAxisFoldEraseObject_configuration FiniteModel.object
  have sameNormalization :
      canonicalObjectNormalization finiteAxisFoldSupportPackage
          finiteAxisFoldUnitObject =
        canonicalObjectNormalization finiteAxisFoldSupportPackage
          finiteAxisFoldBoolObject := by
    rw [finiteCanonicalObjectNormalization_eq_erase,
      finiteCanonicalObjectNormalization_eq_erase]
    exact finiteAxisFoldEraseObject_unit_eq_bool
  have separatedConfigurations :
      (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv
          FiniteModel.object).configuration ≠
        (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv
          FiniteModel.acyclicObject).configuration := by
    simpa [finiteModelDoctrineFromFixture] using
      finiteAxisFold_cyclic_configuration_ne_acyclic
  have projectorNotIso :=
    finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso
      finiteAxisFoldGeneratedCochain DoubleDiamondTwoCell.second fires
  have projectorNeIdentity :
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          finiteAxisFoldBCDatumSquare finiteAxisFoldGeneratedCochain
            finiteAxisFoldSecondCell ≠
        𝟙 ((authoredSupportViaBaseRoute
          finiteAxisFoldBCDatumSquare.context).obj finiteAxisFoldSecondCell) := by
    intro equality
    apply projectorNotIso
    rw [equality]
    infer_instance
  have comparisonNotIso :
      ¬ IsIso ((authoredDiagnosticObjectCollapseComparisonAtCochain
        finiteAxisFoldBCDatumSquare finiteAxisFoldGeneratedCochain).app
          finiteAxisFoldSecondCell) := by
    intro comparisonIsIso
    apply projectorNotIso
    exact (authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff
      finiteAxisFoldBCDatumSquare finiteAxisFoldGeneratedCochain
        finiteAxisFoldSecondCell).1 comparisonIsIso
  refine ⟨fires, admissible, ?_, ?_, projectorNeIdentity,
    comparisonNotIso, ?_⟩
  · exact ⟨finiteAxisFoldUnitObject, finiteAxisFoldBoolObject,
      finiteAxisFoldUnitObject_ne_boolObject, sameConfiguration,
      sameNormalization⟩
  · rcases finiteAxisFold_supportResidual_separates_cyclic_acyclic with
      ⟨W, index, atom, separatedResiduals⟩
    exact ⟨transportArchitectureObject
        finiteModelDoctrineFromFixture.atomEquiv FiniteModel.object,
      transportArchitectureObject
        finiteModelDoctrineFromFixture.atomEquiv FiniteModel.acyclicObject,
      separatedConfigurations, W, index, atom, separatedResiduals⟩
  · exact ⟨authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual
        finiteAxisFoldBCDatumSquare finiteAxisFoldGeneratedCochain
          finiteAxisFoldSecondCell fires admissible,
      authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual
        finiteAxisFoldBCDatumSquare finiteAxisFoldGeneratedCochain
          finiteAxisFoldSecondCell fires admissible⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
