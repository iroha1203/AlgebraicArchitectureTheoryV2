import ResearchLean.AG.DoctrineFiberProduct.FiniteCorePackageULift

/-!
# Concrete witnesses for the finite-model equation universe lift

This module specializes the lifted NoCycle equation and exact detector to the
canonical lifts of the reviewed cyclic and acyclic finite-model objects.  All
matching, acceptance, circuit, and equation facts are generated from the
existing finite witnesses and the canonical lift/reflection graph.

No semantic result, matching proof, circuit, or equation certificate is
accepted as an input.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/-! ## Canonical lifted objects and descent -/

/-- The canonical universe lift of the reviewed cyclic finite-model object. -/
def finiteModelLiftCyclicObject :
    ArchitectureObject finiteModelLiftCarrier.{u} :=
  finiteModelLiftArchitectureObject.{u} FiniteModel.object

/-- The canonical universe lift of the reviewed relation-free finite-model object. -/
def finiteModelLiftAcyclicObject :
    ArchitectureObject finiteModelLiftCarrier.{u} :=
  finiteModelLiftArchitectureObject.{u} FiniteModel.acyclicObject

/-- Semantic descent of the lifted cyclic object recovers the reviewed core object. -/
theorem finiteModelLiftCyclicObject_descent :
    finiteModelSemanticDescent.{u} finiteModelLiftCyclicObject.{u} =
      FiniteModel.corePackage.object := by
  rw [FiniteModel.corePackage_object]
  change FiniteModel.objectOfConfiguration
      (finiteModelReflectAtomConfiguration.{u}
        (finiteModelLiftAtomConfiguration.{u}
          FiniteModel.object.configuration)) =
    FiniteModel.object
  rw [finiteModelReflectAtomConfiguration_lift]
  rfl

/-- Semantic descent of the lifted acyclic object recovers the source acyclic object. -/
theorem finiteModelLiftAcyclicObject_descent :
    finiteModelSemanticDescent.{u} finiteModelLiftAcyclicObject.{u} =
      FiniteModel.acyclicObject := by
  change FiniteModel.objectOfConfiguration
      (finiteModelReflectAtomConfiguration.{u}
        (finiteModelLiftAtomConfiguration.{u}
          FiniteModel.acyclicObject.configuration)) =
    FiniteModel.acyclicObject
  rw [finiteModelReflectAtomConfiguration_lift]
  rfl

/-- The lifted equation witness uses the canonical context preorder of the cyclic object. -/
noncomputable def finiteModelLiftEquationWitnessContext :
    Site.ContextPreorderCategory finiteModelLiftCyclicObject.{u} :=
  Site.contextMorphismPreorderCategory finiteModelLiftCyclicObject.{u}

/-! ## Cyclic positive detector and equation failure -/

/-- The canonical lifted cycle datum matches the canonical lifted cyclic object. -/
theorem finiteModelLiftCycleQueryDatum_matches_cyclic :
    finiteModelLiftCycleQueryDatum.{u}.Matches
      finiteModelLiftCyclicObject.{u} := by
  change (finiteModelLiftFiniteCircuitDatum.{u}
      FiniteModel.cycleQueryDatum).Matches finiteModelLiftCyclicObject.{u}
  rw [finiteModelLiftFiniteCircuitDatum_matches_iff,
    finiteModelLiftCyclicObject_descent]
  exact FiniteModel.cycleQueryDatum_matches_core

/-- The exact lifted detector evaluates to true on its canonical cycle datum. -/
theorem finiteModelLiftCycleQueryDatum_eval_true :
    ((finiteModelLiftEquationCircuitReading.{u}
        finiteModelLiftEquationWitnessContext.{u}).code
      (ULift.up PUnit.unit)).eval finiteModelLiftCycleQueryDatum.{u} = true := by
  change (CircuitDetectorCode.exact finiteModelLiftCycleQueryDatum.{u}).eval
      finiteModelLiftCycleQueryDatum.{u} = true
  exact (CircuitDetectorCode.eval_exact_eq_true_iff
    finiteModelLiftCycleQueryDatum.{u}
    finiteModelLiftCycleQueryDatum.{u}).mpr rfl

/-- The matching accepted cycle datum gives a nonempty lifted circuit fiber. -/
theorem finiteModelLiftCyclicObject_circuit_nonempty :
    Nonempty
      ((finiteModelLiftEquationCircuitReading.{u}
        finiteModelLiftEquationWitnessContext.{u}).Circuit
          finiteModelLiftCyclicObject.{u} (ULift.up PUnit.unit)) := by
  refine ⟨⟨finiteModelLiftCycleQueryDatum.{u},
    finiteModelLiftCycleQueryDatum_matches_cyclic.{u}, ?_⟩⟩
  simpa [EquationCircuitReading.accepts] using
    finiteModelLiftCycleQueryDatum_eval_true.{u}

/-- Detector soundness turns the concrete lifted cycle into NoCycle equation failure. -/
theorem finiteModelLiftCyclicObject_equationHolds_fails :
    ¬ (finiteModelLiftEquationSystem.{u}
        finiteModelLiftEquationWitnessContext.{u}).EquationHolds
      (ULift.up PUnit.unit) finiteModelLiftCyclicObject.{u} :=
  finiteModelLiftEquationCircuitReading_sound.{u}
    finiteModelLiftEquationWitnessContext.{u}
    (ULift.up PUnit.unit) finiteModelLiftCyclicObject.{u}
    finiteModelLiftCycleQueryDatum.{u}
    finiteModelLiftCycleQueryDatum_matches_cyclic.{u}
    finiteModelLiftCycleQueryDatum_eval_true.{u}

/-! ## Acyclic negative detector and equation fulfillment -/

/-- The lifted relation-free object fulfills the direct lifted NoCycle equation. -/
theorem finiteModelLiftAcyclicObject_equationHolds :
    (finiteModelLiftEquationSystem.{u}
        finiteModelLiftEquationWitnessContext.{u}).EquationHolds
      (ULift.up PUnit.unit) finiteModelLiftAcyclicObject.{u} := by
  rw [finiteModelLiftEquationHolds_iff_source,
    finiteModelLiftAcyclicObject_descent]
  exact FiniteModel.acyclic_noCycleEquationHolds
    (Site.contextMorphismPreorderCategory FiniteModel.object)

/-- The positive three-edge cycle datum does not match the lifted acyclic object. -/
theorem finiteModelLiftCycleQueryDatum_not_matches_acyclic :
    ¬ finiteModelLiftCycleQueryDatum.{u}.Matches
      finiteModelLiftAcyclicObject.{u} := by
  change ¬ (finiteModelLiftFiniteCircuitDatum.{u}
      FiniteModel.cycleQueryDatum).Matches finiteModelLiftAcyclicObject.{u}
  rw [finiteModelLiftFiniteCircuitDatum_matches_iff,
    finiteModelLiftAcyclicObject_descent]
  intro hmatches
  have hrelation :=
    ((hmatches
      (.relationPresent FiniteModel.FiniteAtom.dependsAB
        FiniteModel.FiniteAtom.dependsBC) true
      (by simp [FiniteModel.cycleQueryDatum])).mpr rfl).2.2
  simp [FiniteModel.acyclicObject, FiniteModel.acyclicConfiguration] at hrelation

/-- The canonical lifted cyclic and acyclic objects remain distinct. -/
theorem finiteModelLiftCyclicObject_ne_acyclicObject :
    finiteModelLiftCyclicObject.{u} ≠ finiteModelLiftAcyclicObject.{u} := by
  intro heq
  exact finiteModelLiftCycleQueryDatum_not_matches_acyclic.{u}
    (heq ▸ finiteModelLiftCycleQueryDatum_matches_cyclic.{u})

/-! ## Generated-package witness -/

/-- The base object of the generated lifted package is the canonical cyclic object. -/
theorem finiteModelLiftCorePackage_base_object :
    finiteModelLiftCorePackage.{u}.algebra.object
        finiteModelLiftCorePackage.{u}.algebra.base =
      finiteModelLiftCyclicObject.{u} := by
  change finiteModelLiftCorePackage.{u}.object =
    finiteModelLiftCyclicObject.{u}
  rw [finiteModelLiftCorePackage_object, FiniteModel.corePackage_object]
  rfl

/-- The generated package has an actual accepted circuit at its base object. -/
theorem finiteModelLiftCorePackage_base_circuit_nonempty :
    Nonempty
      (finiteModelLiftCorePackage.{u}.algebra.Circuit
        finiteModelLiftCorePackage.{u}.algebra.base
        (ULift.up PUnit.unit)) := by
  apply (ObjectAlgebra.circuit_nonempty_iff
    finiteModelLiftCorePackage.{u}.algebra
    finiteModelLiftCorePackage.{u}.algebra.base
    (ULift.up PUnit.unit)).2
  refine ⟨finiteModelLiftCycleQueryDatum.{u}, ?_, ?_⟩
  · rw [finiteModelLiftCorePackage_base_object]
    exact finiteModelLiftCycleQueryDatum_matches_cyclic.{u}
  · change (CircuitDetectorCode.exact
      finiteModelLiftCycleQueryDatum.{u}).eval
        finiteModelLiftCycleQueryDatum.{u} = true
    exact finiteModelLiftCycleQueryDatum_eval_true.{u}

/-- The generated package's actual base circuit refutes its selected equation. -/
theorem finiteModelLiftCorePackage_base_equationHolds_fails :
    ¬ finiteModelLiftCorePackage.{u}.algebra.equationSystem.EquationHolds
      (ULift.up PUnit.unit)
      (finiteModelLiftCorePackage.{u}.algebra.object
        finiteModelLiftCorePackage.{u}.algebra.base) := by
  obtain ⟨circuit⟩ :=
    finiteModelLiftCorePackage_base_circuit_nonempty.{u}
  exact finiteModelLiftCorePackage.{u}.algebra.circuit_sound
    finiteModelLiftCorePackage.{u}.algebra.base
    (ULift.up PUnit.unit) circuit

/-! ## Negative exact-detector datum -/

/-- Canonical lift of the empty finite circuit datum. -/
def finiteModelLiftEmptyQueryDatum :
    FiniteCircuitDatum finiteModelLiftCarrier.{u} :=
  finiteModelLiftFiniteCircuitDatum.{u} ⟨[]⟩

/-- The exact lifted cycle detector rejects the distinct empty datum. -/
theorem finiteModelLiftEmptyQueryDatum_eval_false :
    ((finiteModelLiftEquationCircuitReading.{u}
        finiteModelLiftEquationWitnessContext.{u}).code
      (ULift.up PUnit.unit)).eval finiteModelLiftEmptyQueryDatum.{u} = false := by
  apply Bool.eq_false_of_not_eq_true
  intro haccepts
  have heq : finiteModelLiftCycleQueryDatum.{u} =
      finiteModelLiftEmptyQueryDatum.{u} :=
    (CircuitDetectorCode.eval_exact_eq_true_iff
      finiteModelLiftCycleQueryDatum.{u}
      finiteModelLiftEmptyQueryDatum.{u}).mp haccepts
  have hqueries := congrArg FiniteCircuitDatum.queries heq
  simp [finiteModelLiftCycleQueryDatum, finiteModelLiftEmptyQueryDatum,
    finiteModelLiftFiniteCircuitDatum, FiniteModel.cycleQueryDatum] at hqueries

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
