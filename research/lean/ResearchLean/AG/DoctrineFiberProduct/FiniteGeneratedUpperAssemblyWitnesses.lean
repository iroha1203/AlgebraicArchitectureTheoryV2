import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperAssembly
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperComputationalWitnesses

/-!
# Concrete witness for the complete generated upper assembly

This module applies the complete assembly producer once to the existing
selective-two noninvertible fixture and fires every one of its eighteen
`SignedExactCoreReadingHom` projections.  Structural laws are tested on
distinct finite families and on the cyclic and acyclic configurations.  The
equation field is identified with the previously fired seven-field transport,
and the detector, collapse operation, and dependent coordinate equivalence
retain their concrete nonconstant observations.

The invariant index and signature axis of the fixture are singleton types, so
their transport laws are recorded as rigid laws rather than sensitivity
claims.  Likewise, `coordinate_eq` records the fixture's constant coordinate
reading; nontrivial coordinate behavior is witnessed separately by applying
`coordinateEquiv` to `3` and taking its round trip.  The canonical backward
upper is used only to generate the detector's source index and data; no
completed reflected upper is used to construct or justify the assembly, and
no canonical-factor rewrite or caller-supplied law certificate is used here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## The single assembled hom -/

/--
The complete reflected signed-reading hom generated once from the selective-two
high lift and its genuinely noninvertible prefix.
-/
noncomputable def finiteSelectiveTwoReflectedSignedExactCoreReadingHom :
    FiniteGeneratedReflectedSignedExactCoreReadingHomOutput
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessBase :=
  finiteGeneratedReflectedSignedExactCoreReadingHom.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/-- Internal finite cover used to fire composition on the empty fixture family. -/
private theorem finiteSelectiveTwoEmptyFamily_listFinite :
    FiniteModel.emptyFamily.ListFinite := by
  refine ⟨[], ?_⟩
  intro atom hmem
  simpa [FiniteModel.emptyFamily] using hmem

/-! ## Structural projections -/

/--
The assembled Atom equivalence separates the two concrete fixture Atoms
`componentA` and `componentC`.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_atomEquiv_nonconstant :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv
        FiniteModel.FiniteAtom.componentA ≠
      finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv
        FiniteModel.FiniteAtom.componentC := by
  intro equality
  have sourceEquality :=
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv.injective equality
  exact (by decide : FiniteModel.FiniteAtom.componentA ≠
    FiniteModel.FiniteAtom.componentC) sourceEquality

/-- The assembled extraction field transports the generated family exactly. -/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_extraction_eq :
    finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.family =
      finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.family.transport
        finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv :=
  finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.extraction_eq

/--
The assembled composition field fires on the distinct selected and empty
families, using the concrete finite witnesses for both.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_composition_eq :
    (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.composition.compose
          (FiniteModel.allFamily.transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv)
          (FiniteModel.allFamily_listFinite.transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv) =
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.composition.compose
          FiniteModel.allFamily FiniteModel.allFamily_listFinite).transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv) ∧
      (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.composition.compose
          (FiniteModel.emptyFamily.transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv)
          (finiteSelectiveTwoEmptyFamily_listFinite.transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv) =
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.composition.compose
          FiniteModel.emptyFamily finiteSelectiveTwoEmptyFamily_listFinite).transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv) := by
  constructor
  · exact finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.composition_eq
      FiniteModel.allFamily FiniteModel.allFamily_listFinite
  · exact finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.composition_eq
      FiniteModel.emptyFamily finiteSelectiveTwoEmptyFamily_listFinite

/-- The complete assembled object map returns the actual reflected nontrivial object. -/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_objectMap :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.objectMap
        finiteSelectiveTwoNontrivialObject =
      finiteSelectiveTwoActualReflectedNontrivialObject.{u} := by
  change
    (finiteGeneratedReflectedSignedExactCoreReadingHom.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase).objectMap
        finiteSelectiveTwoNontrivialObject =
      finiteGeneratedReflectedArchitectureObject.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoNontrivialObject
  exact finiteGeneratedReflectedSignedExactCoreReadingHom_objectMap.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoNontrivialObject

/--
The assembled object-formation field fires independently on the cyclic and
acyclic finite configurations.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_object_formation_eq :
    (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.objectMap
          (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.objectReading.object
            FiniteModel.configuration) =
        finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.objectReading.object
          (FiniteModel.configuration.transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv)) ∧
      (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.objectMap
          (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.objectReading.object
            FiniteModel.acyclicConfiguration) =
        finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.objectReading.object
          (FiniteModel.acyclicConfiguration.transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv)) := by
  constructor
  · exact finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.object_formation_eq
      FiniteModel.configuration
  · exact finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.object_formation_eq
      FiniteModel.acyclicConfiguration

/-- The assembled configuration map is the actual reflected complete map. -/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_configurationMap :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.configurationMap
        finiteSelectiveTwoNontrivialObject =
      finiteGeneratedReflectedConfigurationMap.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoNontrivialObject := by
  change
    (finiteGeneratedReflectedSignedExactCoreReadingHom.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase).configurationMap
        finiteSelectiveTwoNontrivialObject = _
  exact finiteGeneratedReflectedSignedExactCoreReadingHom_configurationMap.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoNontrivialObject

/-- The concrete configuration map uses exactly the assembled Atom equivalence. -/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_configurationMap_atomMap :
    (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.configurationMap
      finiteSelectiveTwoNontrivialObject).atomMap =
        finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv :=
  finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.configurationMap_atomMap
    finiteSelectiveTwoNontrivialObject

/-- The nontrivial object's assembled configuration is exact Atom transport. -/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_configuration_eq :
    (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.objectMap
      finiteSelectiveTwoNontrivialObject).configuration =
        finiteSelectiveTwoNontrivialObject.configuration.transport
          finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv :=
  finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.configuration_eq
    finiteSelectiveTwoNontrivialObject

/-! ## Equation and detector projections -/

/--
The concrete outer equation index obtained by transporting the finite core
detector index through the generated backward upper.
-/
noncomputable def finiteSelectiveTwoDetectorSourceIndex :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.equationSystem.Index :=
  finiteSelectiveTwoCollapseBackwardUpper.equationMap PUnit.unit

/--
The accepted finite cycle datum transported into the outer generated detector.
-/
noncomputable def finiteSelectiveTwoOuterCycleQueryDatum :
    FiniteCircuitDatum FiniteModel.carrier :=
  finiteSelectiveTwoCollapseBackwardUpper.queryMap
    FiniteModel.cycleQueryDatum

/-- The rejected empty datum transported into the outer generated detector. -/
noncomputable def finiteSelectiveTwoOuterEmptyQueryDatum :
    FiniteCircuitDatum FiniteModel.carrier :=
  finiteSelectiveTwoCollapseBackwardUpper.queryMap ⟨[]⟩

/--
The assembled equation field is the same previously witnessed exact transport;
that structure's three data fields and four law fields have all been fired.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_equationTransport :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.equationTransport =
      finiteSelectiveTwoReflectedEquationSystemExactTransport.{u} := by
  change
    (finiteGeneratedReflectedSignedExactCoreReadingHom.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase).equationTransport =
        finiteGeneratedReflectedEquationSystemExactTransport.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
  exact finiteGeneratedReflectedSignedExactCoreReadingHom_equationTransport.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/--
The assembled detector-code law fires at the concrete generated index.  The
same source and target codes accept the transported cycle datum and reject the
transported empty datum, so both controls are connected to this assembled hom.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_detectorCode_eq :
    (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.circuits.code
          (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.equationMap
            finiteSelectiveTwoDetectorSourceIndex) =
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.circuits.code
          finiteSelectiveTwoDetectorSourceIndex).transport
            finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.atomEquiv) ∧
      (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.circuits.code
          finiteSelectiveTwoDetectorSourceIndex).eval
            finiteSelectiveTwoOuterCycleQueryDatum = true ∧
      (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.circuits.code
          (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.equationMap
            finiteSelectiveTwoDetectorSourceIndex)).eval
        (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.queryMap
          finiteSelectiveTwoOuterCycleQueryDatum) = true ∧
      (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.circuits.code
          finiteSelectiveTwoDetectorSourceIndex).eval
            finiteSelectiveTwoOuterEmptyQueryDatum = false ∧
      (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.circuits.code
          (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.equationMap
            finiteSelectiveTwoDetectorSourceIndex)).eval
        (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.queryMap
          finiteSelectiveTwoOuterEmptyQueryDatum) = false := by
  have hsourceCycle :
      finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.circuits.accepts
          finiteSelectiveTwoDetectorSourceIndex
          finiteSelectiveTwoOuterCycleQueryDatum = true := by
    simpa only [finiteSelectiveTwoDetectorSourceIndex,
      finiteSelectiveTwoOuterCycleQueryDatum] using
      (finiteSelectiveTwoCollapseBackwardUpper.accepts_iff
        PUnit.unit FiniteModel.cycleQueryDatum).mp
          FiniteModel.cycleQueryDatum_accepted
  have htargetCycle :
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.circuits.accepts
          (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.equationMap
            finiteSelectiveTwoDetectorSourceIndex)
          (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.queryMap
            finiteSelectiveTwoOuterCycleQueryDatum) = true :=
    (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.accepts_iff
      finiteSelectiveTwoDetectorSourceIndex
      finiteSelectiveTwoOuterCycleQueryDatum).mp hsourceCycle
  have hsourceEmpty :
      finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.circuits.accepts
          finiteSelectiveTwoDetectorSourceIndex
          finiteSelectiveTwoOuterEmptyQueryDatum = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hsourceTrue
    have hcoreTrue :
        FiniteModel.coreReading.equationReading.circuits.accepts
            PUnit.unit ⟨[]⟩ = true := by
      apply (finiteSelectiveTwoCollapseBackwardUpper.accepts_iff
        PUnit.unit ⟨[]⟩).mpr
      simpa only [finiteSelectiveTwoDetectorSourceIndex,
        finiteSelectiveTwoOuterEmptyQueryDatum] using hsourceTrue
    exact Bool.false_ne_true
      (FiniteModel.emptyQueryDatum_rejected.symm.trans hcoreTrue)
  have htargetEmpty :
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.circuits.accepts
          (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.equationMap
            finiteSelectiveTwoDetectorSourceIndex)
          (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.queryMap
            finiteSelectiveTwoOuterEmptyQueryDatum) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro htargetTrue
    have hsourceTrue :=
      (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.accepts_iff
        finiteSelectiveTwoDetectorSourceIndex
        finiteSelectiveTwoOuterEmptyQueryDatum).mpr htargetTrue
    exact Bool.false_ne_true (hsourceEmpty.symm.trans hsourceTrue)
  exact ⟨finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.detectorCode_eq
      finiteSelectiveTwoDetectorSourceIndex,
    hsourceCycle, htargetCycle, hsourceEmpty, htargetEmpty⟩

/-! ## Operation projection and law -/

/--
The assembled operation field maps the genuinely nonidentity outer collapse to
the actual reflected collapse.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_operationMap :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.operationMap
        finiteSelectiveTwoOuterCollapseOperation =
      finiteSelectiveTwoActualReflectedCollapseOperation.{u} ∧
    (let e := finiteSelectiveTwoUpperComputationalOuterInput.hom.doctrineHom.atomEquiv;
      (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
        finiteSelectiveTwoOuterCollapseOperation).atomMap
          (e.symm FiniteModel.FiniteAtom.componentA) ≠
        e.symm FiniteModel.FiniteAtom.componentA) := by
  constructor
  · change
      (finiteGeneratedReflectedSignedExactCoreReadingHom.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase).operationMap
          finiteSelectiveTwoOuterCollapseOperation =
        finiteGeneratedReflectedOperationMap.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoOuterCollapseOperation
    exact finiteGeneratedReflectedSignedExactCoreReadingHom_operationMap.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoOuterCollapseOperation
  · exact finiteSelectiveTwoOuterCollapseOperation_nonidentity

/-- The assembled collapse operation satisfies the full configuration naturality square. -/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_operation_naturality :
    ConfigurationHom.comp
        (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
          (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.operationMap
            finiteSelectiveTwoOuterCollapseOperation))
        (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.configurationMap
          finiteSelectiveTwoCollapseSourceObject) =
      ConfigurationHom.comp
        (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.configurationMap
          finiteSelectiveTwoCollapseTargetObject)
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
          finiteSelectiveTwoOuterCollapseOperation) :=
  finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.operation_naturality
    finiteSelectiveTwoOuterCollapseOperation

/-! ## Invariant and signature projections -/

/-- The rigid singleton invariant index is mapped by the assembled actual-derived field. -/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_invariantMap :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.invariantMap
        finiteSelectiveTwoUpperInvariantIndex =
      finiteSelectiveTwoActualReflectedInvariantIndex.{u} := by
  rfl

/--
The assembled invariant law fires at the fixture's `PUnit` index; its invariant
predicate is rigidly true, so this theorem makes no sensitivity claim.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_invariant_transport :
    Invariant.TransportedAlong
      (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.invariantReading.invariant
        finiteSelectiveTwoUpperInvariantIndex)
      (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.invariantReading.invariant
        (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.invariantMap
          finiteSelectiveTwoUpperInvariantIndex))
      _root_.id
      finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.objectMap :=
  finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.invariant_transport
    finiteSelectiveTwoUpperInvariantIndex

/-- The rigid singleton signature axis is mapped by the assembled actual-derived field. -/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_axisMap :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.axisMap
        finiteSelectiveTwoUpperSignatureAxis =
      finiteSelectiveTwoActualReflectedSignatureAxis.{u} := by
  rfl

/--
The assembled coordinate equivalence sends the concrete nonzero value `3`,
returns it on the inverse round trip, and separates it from zero.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_coordinateEquiv_value_three :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.coordinateEquiv
          finiteSelectiveTwoUpperSignatureAxis
          finiteSelectiveTwoUpperSignatureCoordinateThree =
        finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u} ∧
      (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.coordinateEquiv
          finiteSelectiveTwoUpperSignatureAxis).symm
          finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u} =
        finiteSelectiveTwoUpperSignatureCoordinateThree ∧
      finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.coordinateEquiv
          finiteSelectiveTwoUpperSignatureAxis
          finiteSelectiveTwoUpperSignatureCoordinateThree ≠
        finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.coordinateEquiv
          finiteSelectiveTwoUpperSignatureAxis
          finiteSelectiveTwoUpperSignatureCoordinateZero := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact Equiv.symm_apply_apply
      (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.coordinateEquiv
        finiteSelectiveTwoUpperSignatureAxis)
      finiteSelectiveTwoUpperSignatureCoordinateThree
  · intro equality
    apply finiteSelectiveTwoUpperSignatureCoordinateThree_ne_zero
    exact
      (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.coordinateEquiv
        finiteSelectiveTwoUpperSignatureAxis).injective equality

/--
The assembled selected-axis law fires honestly on the fixture's `PUnit` axis,
where both selected predicates are rigidly true.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_axis_selected_iff :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.signatureReading.selected
        finiteSelectiveTwoUpperSignatureAxis ↔
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.signatureReading.selected
        (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.axisMap
          finiteSelectiveTwoUpperSignatureAxis) :=
  finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.axis_selected_iff
    finiteSelectiveTwoUpperSignatureAxis

/--
The assembled coordinate-read law fires on the nontrivial object and singleton
axis.  This is the fixture's constant-coordinate law, not the nonzero `3`
witness supplied by `coordinateEquiv` above.
-/
theorem finiteSelectiveTwoReflectedSignedExactCoreReadingHom_coordinate_eq_constant_law :
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.coordinateEquiv
        finiteSelectiveTwoUpperSignatureAxis
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.signatureReading.coordinate
          finiteSelectiveTwoNontrivialObject finiteSelectiveTwoUpperSignatureAxis) =
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.signatureReading.coordinate
        (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.objectMap
          finiteSelectiveTwoNontrivialObject)
        (finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.axisMap
          finiteSelectiveTwoUpperSignatureAxis) :=
  finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u}.coordinate_eq
    finiteSelectiveTwoNontrivialObject finiteSelectiveTwoUpperSignatureAxis

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
