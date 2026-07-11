import Formal.AG.Atom.Axioms
import Formal.AG.Atom.ObjectAlgebra

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
  obstructionLaw : Law U
  obstructionCircuit : ObstructionCircuit obstructionLaw object
  signature : ArchitectureSignature U
  algebra : ObjectAlgebra U
  algebraObject : algebra.Obj
  algebraOperation : algebra.Op
  algebraObstruction : algebra.Ob
  algebra_object_eq : algebra.object algebraObject = object
  algebra_operation_source_eq : (algebra.operation algebraOperation).source = object
  algebra_operation_target_eq : (algebra.operation algebraOperation).target = object
  algebra_lawUniverse_eq : algebra.lawUniverse = lawUniverse
  algebra_signature_eq : algebra.signature = signature

namespace AATCorePackage

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
    (L : Law U) (O : ObstructionCircuit L A)
    (Sig : ArchitectureSignature U) : AATCorePackage U where
  axioms := S
  family := F
  configuration := C
  object := A
  configuration_family_eq := hconfiguration
  object_configuration_eq := hobject
  lawUniverse := LU
  obstructionLaw := L
  obstructionCircuit := O
  signature := Sig
  algebra := objectAlgebraOfComponents Inv LU L A O Sig
  algebraObject := PUnit.unit
  algebraOperation := PUnit.unit
  algebraObstruction := PUnit.unit
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
    (L : Law U) (O : ObstructionCircuit L A)
    (Sig : ArchitectureSignature U) : AATCorePackage U :=
  ofComponents S R.family R.configuration A R.configuration_family_eq hobject
    Inv LU L O Sig

/-- I.定理10.5: an AAT Core package exists for any selected Part I tower. -/
theorem exists_ofComponents {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (F : AtomFamily U)
    (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hconfiguration : C.family = F)
    (hobject : A.configuration = C)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (L : Law U) (O : ObstructionCircuit L A)
    (Sig : ArchitectureSignature U) :
    ∃ core : AATCorePackage U,
      core.axioms = S ∧
        core.family = F ∧
          core.configuration = C ∧
            core.object = A ∧
              core.configuration.family = core.family ∧
                core.object.configuration = core.configuration ∧
                  core.lawUniverse = LU ∧
                    core.obstructionLaw = L ∧
                      HEq core.obstructionCircuit O ∧
                        core.signature = Sig :=
  ⟨ofComponents S F C A hconfiguration hobject Inv LU L O Sig,
    rfl, rfl, rfl, rfl, hconfiguration, hobject, rfl, rfl, HEq.rfl, rfl⟩

/--
peer-review hardening I-2: HEq-free existence statement for the selected Part I tower. The
dependent obstruction-circuit equality remains available through the frozen
`exists_ofComponents`; reviewers can use this theorem when they only need the
core tower components.
-/
theorem exists_ofComponents_noHEq {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (F : AtomFamily U)
    (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hconfiguration : C.family = F)
    (hobject : A.configuration = C)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (L : Law U) (O : ObstructionCircuit L A)
    (Sig : ArchitectureSignature U) :
    ∃ core : AATCorePackage U,
      core.axioms = S ∧
        core.family = F ∧
          core.configuration = C ∧
            core.object = A ∧
              core.configuration.family = core.family ∧
                core.object.configuration = core.configuration ∧
                  core.lawUniverse = LU ∧
                    core.obstructionLaw = L ∧
                      core.signature = Sig :=
  ⟨ofComponents S F C A hconfiguration hobject Inv LU L O Sig,
    rfl, rfl, rfl, rfl, hconfiguration, hobject, rfl, rfl, rfl⟩

/--
peer-review hardening I-2: HEq-free existence statement from an explicit axiom-system
realization.
-/
theorem exists_ofAxiomRealization_noHEq {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (R : AtomTowerRealization S)
    (A : ArchitectureObject U)
    (hobject : A.configuration = R.configuration)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (L : Law U) (O : ObstructionCircuit L A)
    (Sig : ArchitectureSignature U) :
    ∃ core : AATCorePackage U,
      core.axioms = S ∧
        core.family = R.family ∧
          core.configuration = R.configuration ∧
            core.object = A ∧
              core.configuration.family = core.family ∧
                core.object.configuration = core.configuration ∧
                  core.lawUniverse = LU ∧
                    core.obstructionLaw = L ∧
                      core.signature = Sig :=
  exists_ofComponents_noHEq S R.family R.configuration A R.configuration_family_eq
    hobject Inv LU L O Sig

/-- I.定理10.5: read the selected Atom A0-A8 system. -/
theorem axioms_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).axioms = S :=
  rfl

/-- I.定理10.5: read the selected Atom family component. -/
theorem family_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).family = F :=
  rfl

/-- I.定理10.5: read the selected configuration component. -/
theorem configuration_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).configuration = C :=
  rfl

/-- I.定理10.5: read the selected architecture object component. -/
theorem object_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).object = A :=
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
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).lawUniverse = LU :=
  rfl

/-- I.定理10.5: read the selected obstruction circuit component. -/
theorem obstructionLaw_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).obstructionLaw =
      L :=
  rfl

/-- I.定理10.5: read the selected obstruction circuit component. -/
theorem obstructionCircuit_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).obstructionCircuit = O :=
  rfl

/-- I.定理10.5: read the selected architecture signature component. -/
theorem signature_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).signature = Sig :=
  rfl

/-- I.定理10.5: read the selected object algebra component. -/
theorem algebra_eq {U : AtomCarrier.{u}} {S : AtomAxiomSystem U}
    {F : AtomFamily U} {C : AtomConfiguration U}
    {A : ArchitectureObject U} {Inv : InvariantFamily U}
    {hconfiguration : C.family = F} {hobject : A.configuration = C}
    {LU : LawUniverse U} {L : Law U} {O : ObstructionCircuit L A}
    {Sig : ArchitectureSignature U} :
    (ofComponents S F C A hconfiguration hobject Inv LU L O Sig).algebra =
      objectAlgebraOfComponents Inv LU L A O Sig :=
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

end AAT.AG
