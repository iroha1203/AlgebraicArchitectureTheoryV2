import Formal.Arch.Examples.AtomFoundationExamples
import Formal.Arch.Examples.AATMoleculeLawExamples
import Formal.Arch.Examples.AATZeroCurvatureExamples
import Formal.Arch.Examples.AATOperationRepairSynthesisExamples
import Formal.Arch.Examples.ArchMapObservationExamples
import Formal.Arch.Examples.AtomSFTInterfaceExamples

namespace Formal.Arch.AATCoreSmokeExamples

open Formal.Arch.AtomFoundationExamples
open Formal.Arch.AATMoleculeLawExamples
open Formal.Arch.AATZeroCurvatureExamples
open Formal.Arch.AATOperationRepairSynthesisExamples
open Formal.Arch.ArchMapObservationExamples
open Formal.Arch.AtomSFTInterfaceExamples

/-- Smoke test: the root example starts from an Atom axiom system. -/
theorem atom_axiom_system_root_primitive :
    exampleAtomAxiomSystem.Primitive ExampleAtom.apiComponent := by
  exact exampleAtomAxiomSystem_atom_primitive

/-- Smoke test: pure AAT starts from atom axioms, not observation metadata. -/
theorem aat_begins_from_atom_axioms :
    (exampleAtomAxiomSystem : AATFromAtomAxioms).Primitive
      ExampleAtom.apiComponent := by
  exact exampleAAT_begins_from_atom_axioms

/-- Smoke test: molecule / law / circuit examples are rooted in the atom system. -/
theorem molecule_law_circuit_rooted_in_atom_axioms :
    exampleAtomAxiomSystem.Primitive ExampleAtom.apiComponent ∧
      exampleAtomAxiomSystem.noLawCreatesAtoms ∧
      AAT.ObstructionCircuit singletonBadLaw apiMolecule := by
  exact
    ⟨apiMolecule_atom_primitive,
      singletonBadLaw_does_not_create_atoms,
      singletonBadLaw_obstruction⟩

/-- Smoke test: zero curvature is an AATCore package over atom axioms. -/
theorem zero_curvature_package_rooted_in_aatcore :
    AAT.NoRequiredObstructionCircuit noBadLaw requiredApiMolecule ∧
      AAT.LawfulWithinAATCore noBadCore noBadLaw requiredApiMolecule ∧
      exampleAtomAxiomSystem.noLawCreatesAtoms := by
  exact
    ⟨noBadPackage_noRequiredObstructionCircuit,
      noBadPackage_lawfulWithinAATCore,
      noBadPackage_law_does_not_create_atoms⟩

/-- Smoke test: operation / repair / synthesis packages do not create atoms. -/
theorem operation_repair_synthesis_do_not_create_atoms :
    exampleAtomAxiomSystem.noToolOutputCreatesAtoms ∧
      exampleAtomAxiomSystem.noToolOutputCreatesAtoms ∧
      exampleAtomAxiomSystem.noToolOutputCreatesAtoms := by
  exact
    ⟨identityOperation_does_not_create_atoms,
      noBadRepair_does_not_create_atoms,
      noBadSynthesis_does_not_create_atoms⟩

/-- Smoke test: ArchMap is an observation layer outside pure AAT core. -/
theorem archmap_observation_layer_is_outside_pure_core :
    exampleArchMapObservationLayer.observesAtoms ∧
      exampleAtomAxiomSystem.noObservationBoundaryCreatesAtoms ∧
      exampleArchMapObservationLayer.archMapDoesNotDefineAAT := by
  exact
    ⟨archMap_observes_atoms,
      archMap_does_not_create_atoms,
      archMap_does_not_define_aat⟩

/-- Smoke test: SFT / FieldSig read AATCore transitions without forecast correctness. -/
theorem sft_fieldsig_reads_aatcore_transition_without_forecast_correctness :
    exampleAATCoreLocalAlgebraForSFT.noForecastCorrectnessFromAATAlone ∧
      exampleArchSigAATCoreTransition.fieldSigAnalysisBoundary ∧
      exampleSFTForecastStatus.RecordsForecastBoundary := by
  exact
    ⟨exampleAATCoreLocalAlgebra_no_forecast_correctness,
      exampleFieldSig_reads_archsig_transition_as_sft_analysis,
      exampleFieldSig_forecast_correctness_remains_boundary⟩

end Formal.Arch.AATCoreSmokeExamples
