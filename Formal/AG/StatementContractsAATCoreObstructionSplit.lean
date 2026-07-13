import Formal.AG.Examples.CoreObstructionCounterexample

noncomputable section

/-!
Executable statement contracts for the unconditional AAT core and the
law-failure-relative obstruction extension.
-/

namespace AAT.AG

universe u

example {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (F : AtomFamily U)
    (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hconfiguration : C.family = F)
    (hobject : A.configuration = C)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (Sig : ArchitectureSignature U) : AATCorePackage U :=
  AATCorePackage.ofComponents S F C A hconfiguration hobject Inv LU Sig

example {U : AtomCarrier.{u}}
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (A : ArchitectureObject U) (Sig : ArchitectureSignature U) :
    (AATCorePackage.objectAlgebraOfComponents Inv LU A Sig).Ob =
      AATCorePackage.EmptyObstructionIndex :=
  AATCorePackage.objectAlgebraOfComponents_obstruction_empty Inv LU A Sig

example {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    ObstructedAATCorePackage core :=
  ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
    relation_supported familyFinite failure

example {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
      relation_supported familyFinite failure).lawIndex = lawIndex :=
  ObstructedAATCorePackage.ofLawFailure_lawIndex core lawIndex family relation
    relation_supported familyFinite failure

example {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
      relation_supported familyFinite failure).circuit.family = family :=
  ObstructedAATCorePackage.ofLawFailure_family core lawIndex family relation
    relation_supported familyFinite failure

example {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
      relation_supported familyFinite failure).circuit.relation = relation :=
  ObstructedAATCorePackage.ofLawFailure_relation core lawIndex family relation
    relation_supported familyFinite failure

example {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    ∀ {a b},
      (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
        relation_supported familyFinite failure).circuit.relation a b ->
      (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
        relation_supported familyFinite failure).circuit.family.mem a ∧
      (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
        relation_supported familyFinite failure).circuit.family.mem b :=
  ObstructedAATCorePackage.ofLawFailure_relation_supported core lawIndex family
    relation relation_supported familyFinite failure

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (obstructed : ObstructedAATCorePackage core) :
    obstructed.circuit.ListFinite :=
  ObstructedAATCorePackage.listFinite obstructed

example {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
      relation_supported familyFinite failure).circuit.ListFinite :=
  ObstructedAATCorePackage.ofLawFailure_listFinite core lawIndex family relation
    relation_supported familyFinite failure

example {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (obstructed : ObstructedAATCorePackage core) :
    ¬ (core.lawUniverse.law obstructed.lawIndex).holds core.object :=
  ObstructedAATCorePackage.law_failure obstructed

example {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    ¬ (core.lawUniverse.law
      (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
        relation_supported familyFinite failure).lawIndex).holds core.object :=
  ObstructedAATCorePackage.ofLawFailure_law_failure core lawIndex family relation
    relation_supported familyFinite failure

example {U : AtomCarrier.{u}} (A : ArchitectureObject U) :
    ¬ Nonempty
      (ObstructionCircuit (CoreObstructionCounterexample.allHoldingLaw U) A) :=
  CoreObstructionCounterexample.allHoldingLaw_has_no_obstructionCircuit A

end AAT.AG
