import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedPackageTotalHomTriangle
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperAssemblyWitnesses

/-!
# Concrete witness for the reflected package-total triangle

This module applies the reflected package-total producer and its ambient-factor
API to the existing selective-two noninvertible fixture.  The single named
total hom exposes the same complete upper used by the Cycle 24 witness, so all
eighteen previously audited structural and computational observations remain
attached to the upper field of this package-total hom.

The whole triangle lands in the generated outer hom.  That hom is then used as
one concrete ambient competitor, with its hom-lift premise obtained from the
canonical projection lift of that package hom.  The resulting ambient factor,
hom-lift property, and factorization equation are produced by the generic API.
No known low factor, canonical-factor equality, caller comparison certificate,
or uniqueness claim is used here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## The single package-total hom -/

/--
The reflected package-total hom generated from the selective-two high lift and
its genuinely noninvertible prefix.
-/
noncomputable def finiteSelectiveTwoReflectedPackageTotalHom :
    FiniteGeneratedReflectedPackageTotalHomOutput
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessBase :=
  finiteGeneratedReflectedPackageTotalHom.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/-- The total hom's lower field is exactly the selective-two prefix. -/
@[simp]
theorem finiteSelectiveTwoReflectedPackageTotalHom_base_eq :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.base =
      finiteSelectiveTwoObjectContextWitnessBase :=
  finiteGeneratedReflectedPackageTotalHom_base_eq
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/-- Package projection of the total hom is exactly the selective-two prefix. -/
@[simp]
theorem finiteSelectiveTwoReflectedPackageTotalHom_projection_eq :
    (packageProjection FiniteModel.carrier).map
        finiteSelectiveTwoReflectedPackageTotalHom.{u} =
      finiteSelectiveTwoObjectContextWitnessBase :=
  finiteGeneratedReflectedPackageTotalHom_projection_eq
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/-- The total hom is a hom lift of the selective-two prefix. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_isHomLift :
    (packageProjection FiniteModel.carrier).IsHomLift
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoReflectedPackageTotalHom.{u} :=
  finiteGeneratedReflectedPackageTotalHom_isHomLift
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/--
The named lower field identified by the preceding base equality is genuinely
noninvertible.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_base_not_isIso :
    ¬ IsIso finiteSelectiveTwoObjectContextWitnessBase :=
  finiteSelectiveTwoObjectContextWitnessBase_not_isIso

/-- The total hom's upper field is exactly the Cycle 24 assembled upper. -/
@[simp]
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_eq :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper =
      finiteSelectiveTwoReflectedSignedExactCoreReadingHom.{u} :=
  finiteGeneratedReflectedPackageTotalHom_upper
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase

/-- The literal total-hom compatibility field identifies its upper and lower Atom maps. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_atomEquiv_eq :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv =
      finiteSelectiveTwoReflectedPackageTotalHom.{u}.base.doctrineHom.atomEquiv :=
  finiteSelectiveTwoReflectedPackageTotalHom.{u}.atomEquiv_eq

/-! ## Cycle 24 upper observations through the total hom -/

/-- The total hom's upper Atom equivalence separates the two fixture Atoms. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_atomEquiv_nonconstant :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv
        FiniteModel.FiniteAtom.componentA ≠
      finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv
        FiniteModel.FiniteAtom.componentC := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_atomEquiv_nonconstant.{u}

/-- The total hom's upper extraction field transports the generated family. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_extraction_eq :
    finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.family =
      finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.family.transport
        finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_extraction_eq.{u}

/-- Internal finite cover used to fire the empty-family composition control. -/
private theorem finiteSelectiveTwoPackageTotalEmptyFamily_listFinite :
    FiniteModel.emptyFamily.ListFinite := by
  refine ⟨[], ?_⟩
  intro atom hmem
  simp [FiniteModel.emptyFamily] at hmem

/--
The total hom's upper composition field fires on the distinct all and empty
families.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_composition_eq :
    (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.composition.compose
          (FiniteModel.allFamily.transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv)
          (FiniteModel.allFamily_listFinite.transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv) =
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.composition.compose
          FiniteModel.allFamily FiniteModel.allFamily_listFinite).transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv) ∧
      (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.composition.compose
          (FiniteModel.emptyFamily.transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv)
          (finiteSelectiveTwoPackageTotalEmptyFamily_listFinite.transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv) =
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.composition.compose
          FiniteModel.emptyFamily
          finiteSelectiveTwoPackageTotalEmptyFamily_listFinite).transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv) := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_composition_eq.{u}

/-- The total hom's upper object map returns the actual reflected object. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_objectMap :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.objectMap
        finiteSelectiveTwoNontrivialObject =
      finiteSelectiveTwoActualReflectedNontrivialObject.{u} := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_objectMap.{u}

/--
The total hom's upper object-formation field fires on the cyclic and acyclic
fixture configurations.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_object_formation_eq :
    (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.objectMap
          (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.objectReading.object
            FiniteModel.configuration) =
        finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.objectReading.object
          (FiniteModel.configuration.transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv)) ∧
      (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.objectMap
          (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.objectReading.object
            FiniteModel.acyclicConfiguration) =
        finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.objectReading.object
          (FiniteModel.acyclicConfiguration.transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv)) := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_object_formation_eq.{u}

/-- The total hom's upper configuration map is the actual reflected map. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_configurationMap :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.configurationMap
        finiteSelectiveTwoNontrivialObject =
      finiteGeneratedReflectedConfigurationMap.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoNontrivialObject := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_configurationMap.{u}

/-- The concrete upper configuration map uses the total hom's Atom map. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_configurationMap_atomMap :
    (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.configurationMap
      finiteSelectiveTwoNontrivialObject).atomMap =
        finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_configurationMap_atomMap.{u}

/-- The concrete upper object configuration is exact Atom transport. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_configuration_eq :
    (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.objectMap
      finiteSelectiveTwoNontrivialObject).configuration =
        finiteSelectiveTwoNontrivialObject.configuration.transport
          finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_configuration_eq.{u}

/-! ## Equation, detector, and operation observations -/

/-- The total hom's equation field is the fired seven-field exact transport. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_equationTransport :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.equationTransport =
      finiteSelectiveTwoReflectedEquationSystemExactTransport.{u} := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_equationTransport.{u}

/--
The total hom's detector field is connected to both accepted and rejected data
on the source and assembled target codes.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_detectorCode_eq :
    (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.circuits.code
          (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.equationMap
            finiteSelectiveTwoDetectorSourceIndex) =
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.circuits.code
          finiteSelectiveTwoDetectorSourceIndex).transport
            finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.atomEquiv) ∧
      (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.circuits.code
          finiteSelectiveTwoDetectorSourceIndex).eval
            finiteSelectiveTwoOuterCycleQueryDatum = true ∧
      (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.circuits.code
          (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.equationMap
            finiteSelectiveTwoDetectorSourceIndex)).eval
        (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.queryMap
          finiteSelectiveTwoOuterCycleQueryDatum) = true ∧
      (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.algebra.circuits.code
          finiteSelectiveTwoDetectorSourceIndex).eval
            finiteSelectiveTwoOuterEmptyQueryDatum = false ∧
      (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.circuits.code
          (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.equationMap
            finiteSelectiveTwoDetectorSourceIndex)).eval
        (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.queryMap
          finiteSelectiveTwoOuterEmptyQueryDatum) = false := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_detectorCode_eq.{u}

/--
The total hom's upper operation map sends the nonidentity outer collapse to the
actual reflected collapse and retains the moved-Atom control.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_operationMap :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.operationMap
        finiteSelectiveTwoOuterCollapseOperation =
      finiteSelectiveTwoActualReflectedCollapseOperation.{u} ∧
    (let e := finiteSelectiveTwoUpperComputationalOuterInput.hom.doctrineHom.atomEquiv;
      (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
        finiteSelectiveTwoOuterCollapseOperation).atomMap
          (e.symm FiniteModel.FiniteAtom.componentA) ≠
        e.symm FiniteModel.FiniteAtom.componentA) := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_operationMap.{u}

/-- The total hom's upper collapse satisfies the full naturality square. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_operation_naturality :
    ConfigurationHom.comp
        (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
          (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.operationMap
            finiteSelectiveTwoOuterCollapseOperation))
        (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.configurationMap
          finiteSelectiveTwoCollapseSourceObject) =
      ConfigurationHom.comp
        (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.configurationMap
          finiteSelectiveTwoCollapseTargetObject)
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
          finiteSelectiveTwoOuterCollapseOperation) := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_operation_naturality.{u}

/-! ## Invariant and signature observations -/

/-- The total hom's rigid invariant index is the actual reflected index. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_invariantMap :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.invariantMap
        finiteSelectiveTwoUpperInvariantIndex =
      finiteSelectiveTwoActualReflectedInvariantIndex.{u} := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_invariantMap.{u}

/--
The total hom's invariant law fires at the fixture's rigid `PUnit` index without
claiming sensitivity.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_invariant_transport :
    Invariant.TransportedAlong
      (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.invariantReading.invariant
        finiteSelectiveTwoUpperInvariantIndex)
      (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.invariantReading.invariant
        (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.invariantMap
          finiteSelectiveTwoUpperInvariantIndex))
      _root_.id
      finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.objectMap := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_invariant_transport.{u}

/-- The total hom's rigid signature axis is the actual reflected axis. -/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_axisMap :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.axisMap
        finiteSelectiveTwoUpperSignatureAxis =
      finiteSelectiveTwoActualReflectedSignatureAxis.{u} := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_axisMap.{u}

/--
The total hom's dependent coordinate equivalence sends `3` to the actual
reflected value, returns it, and separates it from zero.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_coordinateEquiv_value_three :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.coordinateEquiv
          finiteSelectiveTwoUpperSignatureAxis
          finiteSelectiveTwoUpperSignatureCoordinateThree =
        finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u} ∧
      (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.coordinateEquiv
          finiteSelectiveTwoUpperSignatureAxis).symm
          finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u} =
        finiteSelectiveTwoUpperSignatureCoordinateThree ∧
      finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.coordinateEquiv
          finiteSelectiveTwoUpperSignatureAxis
          finiteSelectiveTwoUpperSignatureCoordinateThree ≠
        finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.coordinateEquiv
          finiteSelectiveTwoUpperSignatureAxis
          finiteSelectiveTwoUpperSignatureCoordinateZero := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_coordinateEquiv_value_three.{u}

/--
The total hom's selected-axis law fires honestly on the fixture's rigid
singleton axis.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_axis_selected_iff :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.signatureReading.selected
        finiteSelectiveTwoUpperSignatureAxis ↔
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.signatureReading.selected
        (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.axisMap
          finiteSelectiveTwoUpperSignatureAxis) := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_axis_selected_iff.{u}

/--
The total hom's coordinate-read law is fired as the fixture's constant law,
separate from the nonzero coordinate-equivalence control above.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_upper_coordinate_eq_constant_law :
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.coordinateEquiv
        finiteSelectiveTwoUpperSignatureAxis
        (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.signatureReading.coordinate
          finiteSelectiveTwoNontrivialObject finiteSelectiveTwoUpperSignatureAxis) =
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.signatureReading.coordinate
        (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.objectMap
          finiteSelectiveTwoNontrivialObject)
        (finiteSelectiveTwoReflectedPackageTotalHom.{u}.upper.axisMap
          finiteSelectiveTwoUpperSignatureAxis) := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom_upper_eq] using
    finiteSelectiveTwoReflectedSignedExactCoreReadingHom_coordinate_eq_constant_law.{u}

/-! ## Whole triangle and a concrete ambient competitor -/

/--
The selective-two total hom followed by the inner generated hom is the outer
generated hom; this is the concrete whole package-total triangle.
-/
theorem finiteSelectiveTwoReflectedPackageTotalHom_fac :
    finiteSelectiveTwoReflectedPackageTotalHom.{u} ≫
        finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.hom =
      finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.hom := by
  simpa only [finiteSelectiveTwoReflectedPackageTotalHom,
    finiteSelectiveTwoUpperComputationalOuterInput] using
      (finiteGeneratedReflectedPackageTotalHom_fac.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase)

/--
The generated outer hom is one concrete ambient competitor for the selective-
two factorization problem.
-/
noncomputable def finiteSelectiveTwoGeneratedAmbientCompetitor :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain ⟶
      FiniteModel.corePackage :=
  finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.hom

/--
The concrete competitor lies over the composite of the total prefix and the
inner generated base; its hom-lift premise is the canonical projection lift
of the named package hom.
-/
theorem finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift :
    (packageProjection FiniteModel.carrier).IsHomLift
      (finiteSelectiveTwoReflectedPackageTotalHom.{u}.base ≫
        finiteSelectiveTwoObjectContextWitnessInput.lowInput.hom)
      finiteSelectiveTwoGeneratedAmbientCompetitor := by
  have houter :
      (packageProjection FiniteModel.carrier).IsHomLift
        finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.hom.base
        finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.hom := by
    change (packageProjection FiniteModel.carrier).IsHomLift
      ((packageProjection FiniteModel.carrier).map
        finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.hom)
      finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.hom
    infer_instance
  simpa only [finiteSelectiveTwoGeneratedAmbientCompetitor,
    finiteSelectiveTwoReflectedPackageTotalHom_base_eq,
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift_base,
    finiteSelectiveTwoUpperComputationalOuterInput,
    FiniteGeneratedLiftInput.lowInput_hom,
    finiteGeneratedOuterInput_hom] using houter

/-- The concrete competitor's lower field is the selective-two composite. -/
@[simp]
theorem finiteSelectiveTwoGeneratedAmbientCompetitor_base_eq :
    finiteSelectiveTwoGeneratedAmbientCompetitor.base =
      finiteSelectiveTwoGeneratedChain.first ≫
        finiteSelectiveTwoGeneratedChain.second := by
  change
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.hom.base = _
  rw [finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift_base]
  rfl

/--
The named composite identified as the competitor's lower field is genuinely
noninvertible.
-/
theorem finiteSelectiveTwoGeneratedAmbientCompetitor_base_not_isIso :
    ¬ IsIso
    (finiteSelectiveTwoGeneratedChain.first ≫
      finiteSelectiveTwoGeneratedChain.second) :=
  finiteSelectiveTwoGeneratedChain_composite_not_isIso

/-! ## The concrete ambient factor -/

/--
The generic reflected ambient-factor producer applied to the concrete outer
competitor.  Its required hom-lift evidence is generated immediately above.
-/
noncomputable def finiteSelectiveTwoReflectedAmbientFactor :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain ⟶
      finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain := by
  letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
  exact finiteGeneratedReflectedAmbientFactor.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
    finiteSelectiveTwoGeneratedAmbientCompetitor

/-- The concrete reflected ambient factor lies over the noninvertible prefix. -/
theorem finiteSelectiveTwoReflectedAmbientFactor_isHomLift :
    (packageProjection FiniteModel.carrier).IsHomLift
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoReflectedAmbientFactor.{u} := by
  letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
  simpa only [finiteSelectiveTwoReflectedAmbientFactor,
    finiteSelectiveTwoReflectedPackageTotalHom_base_eq] using
      (finiteGeneratedReflectedAmbientFactor_isHomLift.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
        finiteSelectiveTwoGeneratedAmbientCompetitor)

/-- The concrete reflected ambient factor satisfies its requested factorization. -/
theorem finiteSelectiveTwoReflectedAmbientFactor_fac :
    finiteSelectiveTwoReflectedAmbientFactor.{u} ≫
        finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.hom =
      finiteSelectiveTwoGeneratedAmbientCompetitor := by
  letI := finiteSelectiveTwoGeneratedAmbientCompetitor_isHomLift.{u}
  exact finiteGeneratedReflectedAmbientFactor_fac.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoReflectedPackageTotalHom.{u}.base
    finiteSelectiveTwoGeneratedAmbientCompetitor

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
