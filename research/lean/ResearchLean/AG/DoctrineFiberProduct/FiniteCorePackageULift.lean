import ResearchLean.AG.DoctrineFiberProduct.FiniteEquationULift

/-!
# Canonical lifted finite-model core package

This module assembles the data-level universe lifts from the preceding layers
into one complete `CoreReading` and `AATCorePackage` over
`finiteModelLiftCarrier`.  The equation reading is the direct NoCycle reading
whose soundness quantifies every lifted architecture object.  No package hom,
cartesian lift, reflection certificate, or nonexistence conclusion is accepted
or produced here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/--
The complete lifted finite-model core reading, assembled only from canonical
component constructors and their generated laws.
-/
noncomputable def finiteModelLiftCoreReading :
    CoreReading finiteModelLiftCarrier.{u} where
  doctrine :=
    finiteModelLiftExtractionDoctrine.{u} FiniteModel.extractionDoctrine
  source := ULift.up FiniteModel.ExtractionSource.withoutComponentC
  family_listFinite := by
    simpa [FiniteModel.allFamily] using
      (finiteModelLiftAtomFamily_listFinite.{u}
        FiniteModel.allFamily_listFinite)
  composition :=
    finiteModelLiftCompositionReading.{u} FiniteModel.compositionReading
  objectReading :=
    finiteModelLiftObjectReading.{u} FiniteModel.objectReading
  equationReading :=
    finiteModelLiftEquationReadingFor.{u}
      (Site.contextMorphismPreorderCategory _)
  invariantReading := finiteModelLiftInvariantFamily.{u}
  signatureReading := finiteModelLiftArchitectureSignature.{u}
  operationReading := finiteModelLiftOperationReading.{u}

/-- The lifted core reading retains the canonically rebased extraction doctrine. -/
@[simp]
theorem finiteModelLiftCoreReading_doctrine :
    finiteModelLiftCoreReading.{u}.doctrine =
      finiteModelLiftExtractionDoctrine.{u} FiniteModel.extractionDoctrine :=
  rfl

/-- The lifted core reading retains the lifted selective extraction source. -/
@[simp]
theorem finiteModelLiftCoreReading_source :
    finiteModelLiftCoreReading.{u}.source =
      ULift.up FiniteModel.ExtractionSource.withoutComponentC :=
  rfl

/-- The lifted core reading uses the generated composition reading. -/
@[simp]
theorem finiteModelLiftCoreReading_composition :
    finiteModelLiftCoreReading.{u}.composition =
      finiteModelLiftCompositionReading.{u} FiniteModel.compositionReading :=
  rfl

/-- The lifted core reading uses the generated object reading. -/
@[simp]
theorem finiteModelLiftCoreReading_objectReading :
    finiteModelLiftCoreReading.{u}.objectReading =
      finiteModelLiftObjectReading.{u} FiniteModel.objectReading :=
  rfl

/-- The lifted core reading retains the direct lifted NoCycle equation reading. -/
@[simp]
theorem finiteModelLiftCoreReading_equationReading :
    finiteModelLiftCoreReading.{u}.equationReading =
      finiteModelLiftEquationReadingFor.{u}
        (Site.contextMorphismPreorderCategory _) :=
  rfl

/-- The lifted core reading retains the direct lifted invariant family. -/
@[simp]
theorem finiteModelLiftCoreReading_invariantReading :
    finiteModelLiftCoreReading.{u}.invariantReading =
      finiteModelLiftInvariantFamily.{u} :=
  rfl

/-- The lifted core reading retains the direct lifted architecture signature. -/
@[simp]
theorem finiteModelLiftCoreReading_signatureReading :
    finiteModelLiftCoreReading.{u}.signatureReading =
      finiteModelLiftArchitectureSignature.{u} :=
  rfl

/-- The lifted core reading retains the all-configuration-hom operation reading. -/
@[simp]
theorem finiteModelLiftCoreReading_operationReading :
    finiteModelLiftCoreReading.{u}.operationReading =
      finiteModelLiftOperationReading.{u} :=
  rfl

/--
The canonical lifted finite-model package is generated from the lifted Atom
axioms and the complete lifted core reading.
-/
noncomputable def finiteModelLiftCorePackage :
    AATCorePackage finiteModelLiftCarrier.{u} :=
  AATCorePackage.generate
    (finiteModelLiftAtomAxiomSystem.{u} FiniteModel.axiomSystem)
    finiteModelLiftCoreReading.{u}

/-- The lifted package exposes exactly the generated lifted Atom axioms. -/
@[simp]
theorem finiteModelLiftCorePackage_axioms :
    finiteModelLiftCorePackage.{u}.axioms =
      finiteModelLiftAtomAxiomSystem.{u} FiniteModel.axiomSystem :=
  rfl

/-- The lifted package exposes exactly the assembled lifted core reading. -/
@[simp]
theorem finiteModelLiftCorePackage_reading :
    finiteModelLiftCorePackage.{u}.reading =
      finiteModelLiftCoreReading.{u} :=
  rfl

/-- The generated lifted package family is the canonical lift of the source family. -/
theorem finiteModelLiftCorePackage_family :
    finiteModelLiftCorePackage.{u}.family =
      finiteModelLiftAtomFamily.{u} FiniteModel.corePackage.family := by
  rfl

/--
The generated lifted package configuration is the canonical lift of the
source finite-model configuration.
-/
theorem finiteModelLiftCorePackage_configuration :
    finiteModelLiftCorePackage.{u}.configuration =
      finiteModelLiftAtomConfiguration.{u}
        FiniteModel.corePackage.configuration := by
  rfl

/--
The generated lifted package object is the one-way canonical lift of the
source finite-model package object.
-/
theorem finiteModelLiftCorePackage_object :
    finiteModelLiftCorePackage.{u}.object =
      finiteModelLiftArchitectureObject.{u} FiniteModel.corePackage.object := by
  rfl

/-- The generated lifted package selects the exact lifted cycle detector. -/
theorem finiteModelLiftCorePackage_circuit_code
    (index : finiteModelLiftCorePackage.{u}.equationSystem.Index) :
    finiteModelLiftCorePackage.{u}.circuitReading.code index =
      .exact finiteModelLiftCycleQueryDatum.{u} := by
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
