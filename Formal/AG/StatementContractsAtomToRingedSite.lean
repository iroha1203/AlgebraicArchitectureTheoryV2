import Formal.AG.Examples.FiniteModel

noncomputable section

/-!
Executable statement contracts for the Atom-to-ringed-site PRD.

This first implementation slice fixes the SD1 constructor and characterization
surface.  Later PRD slices extend this file with SD2--SD5 contracts without
changing the contracts below.
-/

namespace AAT.AG

universe u

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) : AATCorePackage U :=
  AATCorePackage.generate S r

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : AtomFamily U :=
  core.family

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : AtomConfiguration U :=
  core.configuration

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : ArchitectureObject U :=
  core.object

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : ObjectAlgebra U :=
  core.algebra

example {U : AtomCarrier.{u}}
    (core : AATCorePackage U) : core.algebra.Obj :=
  core.baseObject

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).axioms = S :=
  AATCorePackage.generate_axioms S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).reading = r :=
  AATCorePackage.generate_reading S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).family = r.doctrine.atomize r.source :=
  AATCorePackage.generate_family_eq_atomize S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    r.doctrine.Atomizes r.source (AATCorePackage.generate S r).family :=
  AATCorePackage.generate_family_atomizes S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).family.ListFinite :=
  AATCorePackage.generate_family_listFinite S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {F : AtomFamily U} (hF : r.doctrine.Atomizes r.source F) :
    F = (AATCorePackage.generate S r).family :=
  AATCorePackage.generate_family_unique S r hF

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).configuration.family =
      (AATCorePackage.generate S r).family :=
  AATCorePackage.generate_configuration_family_eq S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).configuration.FamilySupported :=
  AATCorePackage.generate_configuration_familySupported S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).object.configuration =
      (AATCorePackage.generate S r).configuration :=
  AATCorePackage.generate_object_configuration_eq S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).algebra.lawReading = r.lawReading :=
  AATCorePackage.generate_lawReading_eq S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U) :
    (AATCorePackage.generate S r).algebra.object
      (AATCorePackage.generate S r).baseObject =
        (AATCorePackage.generate S r).object :=
  AATCorePackage.generate_algebra_base_object S r

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B) :
    ((AATCorePackage.generate S r).algebra.operation op).source =
      (AATCorePackage.generate S r).algebra.object A :=
  AATCorePackage.generate_algebra_operation_source S r op

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B) :
    ((AATCorePackage.generate S r).algebra.operation op).target =
      (AATCorePackage.generate S r).algebra.object B :=
  AATCorePackage.generate_algebra_operation_target S r op

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    (A : (AATCorePackage.generate S r).algebra.Obj)
    (i : (AATCorePackage.generate S r).algebra.lawReading.lawUniverse.Index)
    (c : (AATCorePackage.generate S r).algebra.Circuit A i) :
    ¬ ((AATCorePackage.generate S r).algebra.lawReading.lawUniverse.law i).holds
      ((AATCorePackage.generate S r).algebra.object A) :=
  AATCorePackage.generate_circuit_sound S r A i c

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a : U.Atom}
    (ha : ((AATCorePackage.generate S r).algebra.object A).configuration.family.mem a) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.family.mem
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a) :=
  AATCorePackage.generate_algebra_operation_maps_family S r op ha

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a b : U.Atom}
    (hab : ((AATCorePackage.generate S r).algebra.object A).configuration.relation a b) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.relation
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap b) :=
  AATCorePackage.generate_algebra_operation_maps_relation S r op hab

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (r : CoreReading U)
    {A B : (AATCorePackage.generate S r).algebra.Obj}
    (op : (AATCorePackage.generate S r).algebra.Op A B)
    {a b : U.Atom}
    (hab : ((AATCorePackage.generate S r).algebra.object A).configuration.identification a b) :
    ((AATCorePackage.generate S r).algebra.object B).configuration.identification
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap a)
      (((AATCorePackage.generate S r).algebra.configurationMap op).atomMap b) :=
  AATCorePackage.generate_algebra_operation_maps_identification S r op hab

example :
    ∃ A B : FiniteModel.corePackage.algebra.Obj,
      A ≠ B ∧ Nonempty (FiniteModel.corePackage.algebra.Op A B) :=
  FiniteModel.nonidentity_reachable_operation_fires

example :
    FiniteModel.coreReading.lawReading.circuits.accepts PUnit.unit
      FiniteModel.cycleQueryDatum = true :=
  FiniteModel.cycleQueryDatum_accepted

example :
    FiniteModel.coreReading.lawReading.circuits.accepts PUnit.unit ⟨[]⟩ = false :=
  FiniteModel.emptyQueryDatum_rejected

example :
    ¬ (FiniteModel.corePackage.algebra.lawReading.lawUniverse.law PUnit.unit).holds
      (FiniteModel.corePackage.algebra.object FiniteModel.corePackage.baseObject) :=
  FiniteModel.generatedCycleCircuit_sound

end AAT.AG
