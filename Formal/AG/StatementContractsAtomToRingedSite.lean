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

/-! SD1 fixed definition signatures. -/

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Source -> U.Atom -> Prop :=
  D.extracts

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Source -> AtomFamily U :=
  D.atomize

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Source -> AtomFamily U -> Prop :=
  D.Atomizes

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Vocabulary -> U.Atom -> Prop :=
  D.vocabularyAllows

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.SemanticReading -> D.Source -> U.Atom -> Prop :=
  D.semanticAllows

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Resolution -> D.Source -> U.Atom -> Prop :=
  D.resolutionAllows

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    D.Source -> U.Atom -> Prop :=
  D.sourceSemantics

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) : D.Source -> D.Source :=
  D.normalize

example {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) : Nonempty U.Atom :=
  S.primitiveExistence

example {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) :
    ∀ a b, SameCoordinates U a b ↔ a = b :=
  S.predicateStability

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (source : D.Source) : D.Atomizes source (D.atomize source) :=
  D.atomize_holds source

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (source : D.Source) {F G : AtomFamily U}
    (hF : D.Atomizes source F) (hG : D.Atomizes source G) : F = G :=
  D.atomize_unique source hF hG

example {U : AtomCarrier.{u}} (D : ExtractionDoctrine U)
    (source : D.Source) {F : AtomFamily U} (hF : D.Atomizes source F) :
    F = D.atomize source :=
  D.eq_atomize source hF

example {U : AtomCarrier.{u}} (R : CompositionReading U) :
    (F : AtomFamily U) -> F.ListFinite -> AtomConfiguration U :=
  R.compose

example {U : AtomCarrier.{u}} (R : CompositionReading U) :
    ∀ F hfinite, (R.compose F hfinite).family = F :=
  R.family_eq

example {U : AtomCarrier.{u}} (R : CompositionReading U) :
    ∀ F hfinite, (R.compose F hfinite).FamilySupported :=
  R.family_supported

example {U : AtomCarrier.{u}} (R : ObjectReading U) :
    AtomConfiguration U -> ArchitectureObject U :=
  R.object

example {U : AtomCarrier.{u}} (R : ObjectReading U) :
    ∀ C, (R.object C).configuration = C :=
  R.configuration_eq

example {U : AtomCarrier.{u}} (q : CircuitQuery U) :
    ArchitectureObject U -> Prop :=
  q.Holds

example {U : AtomCarrier.{u}} (Q : FiniteCircuitDatum U) :
    ArchitectureObject U -> Prop :=
  Q.Matches

example {U : AtomCarrier.{u}} (code : CircuitDetectorCode U) :
    FiniteCircuitDatum U -> Bool :=
  code.eval

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU) :
    LU.Index -> FiniteCircuitDatum U -> Bool :=
  R.accepts

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU) :
    (i : LU.Index) -> CircuitDetectorCode U :=
  R.code

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU) :
    ∀ (i : LU.Index) (A : ArchitectureObject U) (Q : FiniteCircuitDatum U),
      Q.Matches A -> (R.code i).eval Q = true -> ¬ (LU.law i).holds A :=
  R.sound

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU)
    (A : ArchitectureObject U) (i : LU.Index) : Type u :=
  R.Circuit A i

example {U : AtomCarrier.{u}} {LU : LawUniverse U} (R : CircuitReading LU) : Prop :=
  R.RequiredComplete

example {U : AtomCarrier.{u}} (R : LawReading U) : LawUniverse U :=
  R.lawUniverse

example {U : AtomCarrier.{u}} (R : LawReading U) : CircuitReading R.lawUniverse :=
  R.circuits

example {U : AtomCarrier.{u}} (C : AtomConfiguration U) : ConfigurationHom C C :=
  ConfigurationHom.id C

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (f : ConfigurationHom C D) : U.Atom -> U.Atom :=
  f.atomMap

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (f : ConfigurationHom C D) :
    ∀ {a}, C.family.mem a -> D.family.mem (f.atomMap a) :=
  f.maps_family

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (f : ConfigurationHom C D) :
    ∀ {a b}, C.relation a b -> D.relation (f.atomMap a) (f.atomMap b) :=
  f.maps_relation

example {U : AtomCarrier.{u}} {C D : AtomConfiguration U}
    (f : ConfigurationHom C D) :
    ∀ {a b}, C.identification a b ->
      D.identification (f.atomMap a) (f.atomMap b) :=
  f.maps_identification

example {U : AtomCarrier.{u}} {C D E : AtomConfiguration U}
    (g : ConfigurationHom D E) (f : ConfigurationHom C D) :
    ConfigurationHom C E :=
  ConfigurationHom.comp g f

example {U : AtomCarrier.{u}} (R : OperationReading U)
    {A B : ArchitectureObject U} (op : R.Op A B) : Operation U :=
  R.operation op

example {U : AtomCarrier.{u}} (R : OperationReading U) :
    (A B : ArchitectureObject U) -> Type u :=
  R.Op

example {U : AtomCarrier.{u}} (R : OperationReading U) :
    ∀ {A B}, R.Op A B -> ConfigurationHom A.configuration B.configuration :=
  R.configurationMap

example {U : AtomCarrier.{u}} (R : OperationReading U)
    (base : ArchitectureObject U) : ArchitectureObject U -> Prop :=
  R.Reachable base

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) (A : K.Obj)
    (i : K.lawReading.lawUniverse.Index) : Type u :=
  K.Circuit A i

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) {A B : K.Obj}
    (op : K.Op A B) : Operation U :=
  K.operation op

example {U : AtomCarrier.{u}} (r : CoreReading U) : ExtractionDoctrine U :=
  r.doctrine

example {U : AtomCarrier.{u}} (r : CoreReading U) : r.doctrine.Source :=
  r.source

example {U : AtomCarrier.{u}} (r : CoreReading U) :
    (r.doctrine.atomize r.source).ListFinite :=
  r.family_listFinite

example {U : AtomCarrier.{u}} (r : CoreReading U) : CompositionReading U :=
  r.composition

example {U : AtomCarrier.{u}} (r : CoreReading U) : ObjectReading U :=
  r.objectReading

example {U : AtomCarrier.{u}} (r : CoreReading U) : LawReading U :=
  r.lawReading

example {U : AtomCarrier.{u}} (r : CoreReading U) : InvariantFamily U :=
  r.invariantReading

example {U : AtomCarrier.{u}} (r : CoreReading U) : ArchitectureSignature U :=
  r.signatureReading

example {U : AtomCarrier.{u}} (r : CoreReading U) : OperationReading U :=
  r.operationReading

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : K.Obj -> ArchitectureObject U :=
  K.object

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : K.Obj -> K.Obj -> Type u :=
  K.Op

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) :
    ∀ {A B}, K.Op A B ->
      ConfigurationHom (K.object A).configuration (K.object B).configuration :=
  K.configurationMap

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : InvariantFamily U :=
  K.invariantReading

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : LawReading U :=
  K.lawReading

example {U : AtomCarrier.{u}} (K : ObjectAlgebra U) : ArchitectureSignature U :=
  K.signatureReading

example {U : AtomCarrier.{u}} (core : AATCorePackage U) : AtomAxiomSystem U :=
  core.axioms

example {U : AtomCarrier.{u}} (core : AATCorePackage U) : CoreReading U :=
  core.reading

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

example : FiniteModel.corePackage.family.mem FiniteModel.FiniteAtom.componentA :=
  FiniteModel.corePackage_componentA_mem

example : ¬ FiniteModel.corePackage.family.mem FiniteModel.FiniteAtom.componentC :=
  FiniteModel.corePackage_componentC_not_mem

example :
    (FiniteModel.corePackage.algebra.configurationMap
      FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.componentA =
        FiniteModel.FiniteAtom.componentB ∧
      FiniteModel.FiniteAtom.componentA ≠ FiniteModel.FiniteAtom.componentB :=
  FiniteModel.collapseOperation_atomMap_nonidentity

example :
    FiniteModel.collapsedObject.configuration.family.mem
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.componentA) :=
  FiniteModel.collapseOperation_transports_family

example :
    FiniteModel.collapsedObject.configuration.relation
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.dependsAB)
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.dependsBC) :=
  FiniteModel.collapseOperation_transports_relation

example :
    FiniteModel.collapsedObject.configuration.identification
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.componentA)
      ((FiniteModel.corePackage.algebra.configurationMap
        FiniteModel.collapseOperation).atomMap FiniteModel.FiniteAtom.componentB) :=
  FiniteModel.collapseOperation_transports_identification

example :
    FiniteModel.coreReading.lawReading.circuits.accepts PUnit.unit
      FiniteModel.cycleQueryDatum = true :=
  FiniteModel.cycleQueryDatum_accepted

example : FiniteModel.cycleQueryDatum.Matches FiniteModel.corePackage.object :=
  FiniteModel.cycleQueryDatum_matches_core

example : ¬ FiniteModel.componentAAbsentDatum.Matches FiniteModel.corePackage.object :=
  FiniteModel.componentAAbsentDatum_not_matches_core

example :
    FiniteModel.coreReading.lawReading.circuits.accepts PUnit.unit ⟨[]⟩ = false :=
  FiniteModel.emptyQueryDatum_rejected

example :
    ¬ (FiniteModel.corePackage.algebra.lawReading.lawUniverse.law PUnit.unit).holds
      (FiniteModel.corePackage.algebra.object FiniteModel.corePackage.baseObject) :=
  FiniteModel.generatedCycleCircuit_sound

end AAT.AG
