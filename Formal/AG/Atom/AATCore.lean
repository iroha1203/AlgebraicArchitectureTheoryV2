import Formal.AG.Atom.Axioms
import Formal.AG.Atom.ObjectAlgebra

/-!
# AAT core and failure-relative obstruction data

The unconditional core does not require an obstruction: a selected law may
hold on every object, so an actual `ObstructionCircuit` cannot be manufactured
uniformly. Obstruction data is therefore a dependent extension indexed by a
law from the core law universe. The extension stores concrete list-finiteness;
an internal always-failing law or the legacy free `finite : Prop` marker would
not establish the finite circuit required by Part I, Definition 8.2.
-/

namespace AAT.AG

universe u

/--
I.定理10.5: AAT Core package built from the Part I Atom tower.

The package records that an Atom carrier satisfying A0-A8 can be read together
with the R1-R7 components and the R9 object-algebra surface. It does not claim
that concrete graph/category/algebra/diagram/state-transition instances or
finite examples have been constructed.
-/
structure AATCorePackage (U : AtomCarrier.{u}) where
  axioms : AtomAxiomSystem U
  family : AtomFamily U
  configuration : AtomConfiguration U
  object : ArchitectureObject U
  configuration_family_eq : configuration.family = family
  object_configuration_eq : object.configuration = configuration
  lawUniverse : LawUniverse U
  signature : ArchitectureSignature U
  algebra : ObjectAlgebra U
  algebraObject : algebra.Obj
  algebraOperation : algebra.Op
  algebra_object_eq : algebra.object algebraObject = object
  algebra_operation_source_eq : (algebra.operation algebraOperation).source = object
  algebra_operation_target_eq : (algebra.operation algebraOperation).target = object
  algebra_lawUniverse_eq : algebra.lawUniverse = lawUniverse
  algebra_signature_eq : algebra.signature = signature

namespace AATCorePackage

/-- A universe-polymorphic empty index for unconditional obstruction data. -/
def EmptyObstructionIndex : Type u :=
  ULift.{u} Empty

/--
peer-review hardening I-2: a realization tying the abstract `AtomAxiomSystem` tower to the
actual Part I Lean tower. The maps are explicit, so later examples can show how
`S.configurationOf` feeds an `AtomConfiguration` without changing the frozen
`AtomAxiomSystem` record.
-/
structure AtomTowerRealization {U : AtomCarrier.{u}} (S : AtomAxiomSystem U) where
  familyToken : S.Family
  configurationToken : S.Configuration
  familyOf : S.Family -> AtomFamily U
  configurationOf : S.Configuration -> AtomConfiguration U
  family : AtomFamily U
  configuration : AtomConfiguration U
  family_eq : familyOf familyToken = family
  configuration_eq : configurationOf configurationToken = configuration
  configurationToken_eq : S.configurationOf familyToken = configurationToken
  configuration_family_eq : configuration.family = family

namespace AtomTowerRealization

/-- peer-review hardening I-2: the selected configuration is obtained from the selected axiom family token. -/
theorem realized_configuration_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    (R : AtomTowerRealization S) :
    R.configurationOf (S.configurationOf R.familyToken) = R.configuration := by
  rw [R.configurationToken_eq, R.configuration_eq]

/-- peer-review hardening I-2: the selected family is obtained from the selected axiom family token. -/
theorem realized_family_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    (R : AtomTowerRealization S) :
    R.familyOf R.familyToken = R.family :=
  R.family_eq

end AtomTowerRealization

/-- I.定理10.5: the identity operation used by the singleton core algebra. -/
def identityOperation {U : AtomCarrier.{u}} (A : ArchitectureObject U) :
    Operation U where
  source := A
  target := A
  Evidence := PUnit
  evidence := PUnit.unit
  objectMap := fun source target => source = A ∧ target = A
  objectMap_holds := ⟨rfl, rfl⟩
  configurationMap := fun source target =>
    source = A.configuration ∧ target = A.configuration
  configurationMap_holds := ⟨rfl, rfl⟩

/--
I.定理10.5: build the singleton object algebra from the selected Part I
components.
-/
def objectAlgebraOfComponents {U : AtomCarrier.{u}}
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (A : ArchitectureObject U) (Sig : ArchitectureSignature U) :
    ObjectAlgebra U where
  Obj := PUnit
  object := fun _ => A
  Op := PUnit
  operation := fun _ => identityOperation A
  operationSource := fun _ => PUnit.unit
  operationTarget := fun _ => PUnit.unit
  operation_source_eq := by
    intro op
    cases op
    rfl
  operation_target_eq := by
    intro op
    cases op
    rfl
  Inv := Inv
  lawUniverse := LU
  Ob := EmptyObstructionIndex
  obstructionLaw := fun obstruction => nomatch obstruction.down
  obstructionObject := fun obstruction => nomatch obstruction.down
  obstructionCircuit := fun obstruction => nomatch obstruction.down
  signature := Sig

/-- The unconditional singleton algebra has an empty obstruction index. -/
theorem objectAlgebraOfComponents_obstruction_empty {U : AtomCarrier.{u}}
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (A : ArchitectureObject U) (Sig : ArchitectureSignature U) :
    (objectAlgebraOfComponents Inv LU A Sig).Ob = EmptyObstructionIndex :=
  rfl

/--
Compatibility constructor for an object algebra carrying one selected
obstruction. The unconditional AAT core uses `objectAlgebraOfComponents`, whose
obstruction index is empty.
-/
def objectAlgebraWithObstructionOfComponents {U : AtomCarrier.{u}}
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (L : Law U) (A : ArchitectureObject U)
    (O : ObstructionCircuit L A) (Sig : ArchitectureSignature U) :
    ObjectAlgebra U where
  Obj := PUnit
  object := fun _ => A
  Op := PUnit
  operation := fun _ => identityOperation A
  operationSource := fun _ => PUnit.unit
  operationTarget := fun _ => PUnit.unit
  operation_source_eq := by
    intro op
    cases op
    rfl
  operation_target_eq := by
    intro op
    cases op
    rfl
  Inv := Inv
  lawUniverse := LU
  Ob := PUnit
  obstructionLaw := fun _ => L
  obstructionObject := fun _ => A
  obstructionCircuit := fun _ => O
  signature := Sig

/-- I.定理10.5: construct the AAT Core package from the Part I tower. -/
def ofComponents {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (F : AtomFamily U)
    (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hconfiguration : C.family = F)
    (hobject : A.configuration = C)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (Sig : ArchitectureSignature U) : AATCorePackage U where
  axioms := S
  family := F
  configuration := C
  object := A
  configuration_family_eq := hconfiguration
  object_configuration_eq := hobject
  lawUniverse := LU
  signature := Sig
  algebra := objectAlgebraOfComponents Inv LU A Sig
  algebraObject := PUnit.unit
  algebraOperation := PUnit.unit
  algebra_object_eq := rfl
  algebra_operation_source_eq := rfl
  algebra_operation_target_eq := rfl
  algebra_lawUniverse_eq := rfl
  algebra_signature_eq := rfl

/--
peer-review hardening I-2: construct the core package from an explicit realization of the
`AtomAxiomSystem` tower. This additive constructor makes the use of `S` visible
through `AtomTowerRealization`, while preserving the original constructor for
Research imports.
-/
def ofAxiomRealization {U : AtomCarrier.{u}} (S : AtomAxiomSystem U)
    (R : AtomTowerRealization S)
    (A : ArchitectureObject U)
    (hobject : A.configuration = R.configuration)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (Sig : ArchitectureSignature U) : AATCorePackage U :=
  ofComponents S R.family R.configuration A R.configuration_family_eq hobject
    Inv LU Sig

/-- I.定理10.5: an AAT Core package exists for any selected Part I tower. -/
theorem exists_ofComponents {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (F : AtomFamily U)
    (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hconfiguration : C.family = F)
    (hobject : A.configuration = C)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (Sig : ArchitectureSignature U) :
    ∃ core : AATCorePackage U,
      core.axioms = S ∧
        core.family = F ∧
          core.configuration = C ∧
            core.object = A ∧
              core.configuration.family = core.family ∧
                core.object.configuration = core.configuration ∧
                  core.lawUniverse = LU ∧
                    core.signature = Sig :=
  ⟨ofComponents S F C A hconfiguration hobject Inv LU Sig,
    rfl, rfl, rfl, rfl, hconfiguration, hobject, rfl, rfl⟩

/-- A direct existence statement for the selected Part I tower. -/
theorem exists_ofComponents_noHEq {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (F : AtomFamily U)
    (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hconfiguration : C.family = F)
    (hobject : A.configuration = C)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (Sig : ArchitectureSignature U) :
    ∃ core : AATCorePackage U,
      core.axioms = S ∧
        core.family = F ∧
          core.configuration = C ∧
            core.object = A ∧
              core.configuration.family = core.family ∧
                core.object.configuration = core.configuration ∧
                  core.lawUniverse = LU ∧
                    core.signature = Sig :=
  exists_ofComponents S F C A hconfiguration hobject Inv LU Sig

/--
peer-review hardening I-2: HEq-free existence statement from an explicit axiom-system
realization.
-/
theorem exists_ofAxiomRealization_noHEq {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (R : AtomTowerRealization S)
    (A : ArchitectureObject U)
    (hobject : A.configuration = R.configuration)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (Sig : ArchitectureSignature U) :
    ∃ core : AATCorePackage U,
      core.axioms = S ∧
        core.family = R.family ∧
          core.configuration = R.configuration ∧
            core.object = A ∧
              core.configuration.family = core.family ∧
                core.object.configuration = core.configuration ∧
                  core.lawUniverse = LU ∧
                    core.signature = Sig :=
  exists_ofComponents_noHEq S R.family R.configuration A R.configuration_family_eq
    hobject Inv LU Sig

/-- I.定理10.5: read the selected Atom A0-A8 system. -/
theorem axioms_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU Sig).axioms = S :=
  rfl

/-- I.定理10.5: read the selected Atom family component. -/
theorem family_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU Sig).family = F :=
  rfl

/-- I.定理10.5: read the selected configuration component. -/
theorem configuration_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU Sig).configuration = C :=
  rfl

/-- I.定理10.5: read the selected architecture object component. -/
theorem object_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU Sig).object = A :=
  rfl

/-- I.定理10.5: the selected configuration belongs to the selected family. -/
theorem configuration_family {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    core.configuration.family = core.family :=
  core.configuration_family_eq

/-- I.定理10.5: the selected object is built over the selected configuration. -/
theorem object_configuration {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    core.object.configuration = core.configuration :=
  core.object_configuration_eq

/-- I.定理10.5: read the selected law universe component. -/
theorem lawUniverse_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU Sig).lawUniverse = LU :=
  rfl

/-- I.定理10.5: read the selected architecture signature component. -/
theorem signature_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU Sig).signature = Sig :=
  rfl

/-- I.定理10.5: read the selected object algebra component. -/
theorem algebra_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU Sig).algebra =
      objectAlgebraOfComponents Inv LU A Sig :=
  rfl

/-- The unconditional singleton algebra has no selected obstruction index. -/
theorem algebra_obstruction_index_eq {U : AtomCarrier.{u}}
    {S : AtomAxiomSystem U} {F : AtomFamily U}
    {C : AtomConfiguration U} {A : ArchitectureObject U}
    {Inv : InvariantFamily U} {hconfiguration : C.family = F}
    {hobject : A.configuration = C} {LU : LawUniverse U}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU Sig).algebra.Ob =
      EmptyObstructionIndex :=
  rfl

/-- I.定理10.5: the generated object algebra contains the selected object. -/
theorem algebra_object {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    core.algebra.object core.algebraObject = core.object :=
  core.algebra_object_eq

/-- I.定理10.5: the generated object algebra contains the selected law universe. -/
theorem algebra_lawUniverse {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    core.algebra.lawUniverse = core.lawUniverse :=
  core.algebra_lawUniverse_eq

/-- I.定理10.5: the generated object algebra contains the selected signature. -/
theorem algebra_signature {U : AtomCarrier.{u}} (core : AATCorePackage U) :
    core.algebra.signature = core.signature :=
  core.algebra_signature_eq

/-- I.定理10.5: the generated object algebra contains a selected operation. -/
theorem algebra_operation_source {U : AtomCarrier.{u}}
    (core : AATCorePackage U) :
    (core.algebra.operation core.algebraOperation).source = core.object :=
  core.algebra_operation_source_eq

/-- I.定理10.5: the selected operation targets the selected object. -/
theorem algebra_operation_target {U : AtomCarrier.{u}}
    (core : AATCorePackage U) :
    (core.algebra.operation core.algebraOperation).target = core.object :=
  core.algebra_operation_target_eq

end AATCorePackage

/--
An obstruction is additional data over an unconditional AAT core. Its law is
selected from the core law universe, and its circuit witnesses failure on the
core object.
-/
structure ObstructedAATCorePackage {U : AtomCarrier.{u}}
    (core : AATCorePackage U) where
  lawIndex : core.lawUniverse.Index
  circuit :
    ObstructionCircuit (core.lawUniverse.law lawIndex) core.object
  circuit_listFinite : circuit.ListFinite

namespace ObstructedAATCorePackage

/--
Construct an obstruction extension from finite supported circuit data and
failure of the selected law.
-/
def ofLawFailure {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    ObstructedAATCorePackage core where
  lawIndex := lawIndex
  circuit := {
    family := family
    relation := relation
    relation_supported := relation_supported
    finite := family.ListFinite
    finite_holds := familyFinite
    law_failure := failure
  }
  circuit_listFinite := familyFinite

/-- The selected law index of `ofLawFailure`, without unfolding the constructor. -/
theorem ofLawFailure_lawIndex {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ofLawFailure core lawIndex family relation relation_supported familyFinite
      failure).lawIndex = lawIndex :=
  rfl

/-- The constructor preserves the selected circuit family without unfolding. -/
theorem ofLawFailure_family {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ofLawFailure core lawIndex family relation relation_supported familyFinite
      failure).circuit.family = family :=
  rfl

/-- The constructor preserves the selected circuit relation without unfolding. -/
theorem ofLawFailure_relation {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ofLawFailure core lawIndex family relation relation_supported familyFinite
      failure).circuit.relation = relation :=
  rfl

/-- The stored relation remains supported on the stored circuit family. -/
theorem ofLawFailure_relation_supported {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    ∀ {a b},
      (ofLawFailure core lawIndex family relation relation_supported familyFinite
        failure).circuit.relation a b ->
      (ofLawFailure core lawIndex family relation relation_supported familyFinite
        failure).circuit.family.mem a ∧
      (ofLawFailure core lawIndex family relation relation_supported familyFinite
        failure).circuit.family.mem b :=
  (ofLawFailure core lawIndex family relation relation_supported familyFinite
    failure).circuit.relation_supported

/-- Every obstruction extension carries concrete list-finiteness. -/
theorem listFinite {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (obstructed : ObstructedAATCorePackage core) :
    obstructed.circuit.ListFinite :=
  obstructed.circuit_listFinite

/-- The constructor records concrete list-finiteness as its finite marker. -/
theorem ofLawFailure_listFinite {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ofLawFailure core lawIndex family relation relation_supported familyFinite
      failure).circuit.ListFinite :=
  listFinite
    (ofLawFailure core lawIndex family relation relation_supported familyFinite
      failure)

/-- An obstruction extension exposes failure of its selected law. -/
theorem law_failure {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (obstructed : ObstructedAATCorePackage core) :
    ¬ (core.lawUniverse.law obstructed.lawIndex).holds core.object :=
  obstructed.circuit.law_failure

/-- The failure proof used by `ofLawFailure` is available without unfolding. -/
theorem ofLawFailure_law_failure {U : AtomCarrier.{u}}
    (core : AATCorePackage U) (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    ¬ (core.lawUniverse.law
      (ofLawFailure core lawIndex family relation relation_supported familyFinite
        failure).lawIndex).holds core.object :=
  law_failure
    (ofLawFailure core lawIndex family relation relation_supported familyFinite
      failure)

end ObstructedAATCorePackage

end AAT.AG
