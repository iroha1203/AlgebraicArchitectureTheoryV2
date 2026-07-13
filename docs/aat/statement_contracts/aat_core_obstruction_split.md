# AAT Core / obstruction split statement contract

この文書は、数学本文の定理10.5に対応する無条件AAT coreと、定義8.2に対応する
law-failure相対のobstructed extensionについて、Lean declarationの固定signatureを定める。
実装状態は記録しない。このcontractは二層のschemaとAPIだけを固定し、Atom公理系からの
core generation全体を`ofComponents`が実装したとは主張しない。

## 無条件core

ここで「無条件」は、selected law failureをpremiseとして要求しないことを指す。
`AATCorePackage`は、Atom tower、law universe、signature、object algebraを保持する。
obstruction lawとobstruction circuitは必須fieldにしない。

```lean
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
  algebra_operation_source_eq :
    (algebra.operation algebraOperation).source = object
  algebra_operation_target_eq :
    (algebra.operation algebraOperation).target = object
  algebra_lawUniverse_eq : algebra.lawUniverse = lawUniverse
  algebra_signature_eq : algebra.signature = signature
```

component constructorはobstructionまたはlaw failureを入力しない。

```lean
def AATCorePackage.ofComponents {U : AtomCarrier.{u}}
    (S : AtomAxiomSystem U) (F : AtomFamily U)
    (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hconfiguration : C.family = F)
    (hobject : A.configuration = C)
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (Sig : ArchitectureSignature U) : AATCorePackage U
```

無条件coreのobject algebraはobstruction indexを空にする。

```lean
def AATCorePackage.EmptyObstructionIndex : Type u

def AATCorePackage.objectAlgebraOfComponents {U : AtomCarrier.{u}}
    (Inv : InvariantFamily U) (LU : LawUniverse U)
    (A : ArchitectureObject U) (Sig : ArchitectureSignature U) :
    ObjectAlgebra U

theorem AATCorePackage.objectAlgebraOfComponents_obstruction_empty
    {U : AtomCarrier.{u}} (Inv : InvariantFamily U)
    (LU : LawUniverse U) (A : ArchitectureObject U)
    (Sig : ArchitectureSignature U) :
    (AATCorePackage.objectAlgebraOfComponents Inv LU A Sig).Ob =
      AATCorePackage.EmptyObstructionIndex
```

## Obstructed extension

obstructed extensionは、coreのlaw universeに属するindexと、そのlawに型付けされたactual
`ObstructionCircuit`を保持する。

```lean
structure ObstructedAATCorePackage {U : AtomCarrier.{u}}
    (core : AATCorePackage U) where
  lawIndex : core.lawUniverse.Index
  circuit :
    ObstructionCircuit (core.lawUniverse.law lawIndex) core.object
  circuit_listFinite : circuit.ListFinite
```

主constructorは生成済みlaw index、finite Atom family、その上にsupportを持つrelation、
同じcore object上でのlaw failureを明示的に要求する。失敗lawを内部生成せず、
`familyFinite`と`failure`は構成されるcircuitの`finite_holds`と`law_failure`に使う。

```lean
def ObstructedAATCorePackage.ofLawFailure
    {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    ObstructedAATCorePackage core
```

constructorと格納されたlaw index / family / relation / support / finiteness / failureの対応を
次のAPIで固定する。

```lean
theorem ObstructedAATCorePackage.ofLawFailure_lawIndex
    {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
      relation_supported familyFinite failure).lawIndex = lawIndex

theorem ObstructedAATCorePackage.ofLawFailure_family
    {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
      relation_supported familyFinite failure).circuit.family = family

theorem ObstructedAATCorePackage.ofLawFailure_relation
    {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
      relation_supported familyFinite failure).circuit.relation = relation

theorem ObstructedAATCorePackage.ofLawFailure_relation_supported
    {U : AtomCarrier.{u}} (core : AATCorePackage U)
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
        relation_supported familyFinite failure).circuit.family.mem b

theorem ObstructedAATCorePackage.listFinite
    {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (obstructed : ObstructedAATCorePackage core) :
    obstructed.circuit.ListFinite

theorem ObstructedAATCorePackage.ofLawFailure_listFinite
    {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
      relation_supported familyFinite failure).circuit.ListFinite

theorem ObstructedAATCorePackage.law_failure
    {U : AtomCarrier.{u}} {core : AATCorePackage U}
    (obstructed : ObstructedAATCorePackage core) :
    ¬ (core.lawUniverse.law obstructed.lawIndex).holds core.object

theorem ObstructedAATCorePackage.ofLawFailure_law_failure
    {U : AtomCarrier.{u}} (core : AATCorePackage U)
    (lawIndex : core.lawUniverse.Index)
    (family : AtomFamily U) (relation : U.Atom -> U.Atom -> Prop)
    (relation_supported :
      ∀ {a b}, relation a b -> family.mem a ∧ family.mem b)
    (familyFinite : family.ListFinite)
    (failure : ¬ (core.lawUniverse.law lawIndex).holds core.object) :
    ¬ (core.lawUniverse.law
        (ObstructedAATCorePackage.ofLawFailure core lawIndex family relation
          relation_supported familyFinite failure).lawIndex).holds
      core.object
```

## All-holding counterexample

すべてのobject上で成り立つlawにはactual obstruction circuitが存在しないことを、
standard axiomsだけで固定する。

```lean
namespace AAT.AG.CoreObstructionCounterexample

def allHoldingLaw (U : AtomCarrier.{u}) : Law U

theorem allHoldingLaw_has_no_obstructionCircuit
    {U : AtomCarrier.{u}} (A : ArchitectureObject U) :
    ¬ Nonempty (ObstructionCircuit (allHoldingLaw U) A)

end AAT.AG.CoreObstructionCounterexample
```

## Material premise

`relation_supported`はcircuit relationが選ばれたAtom family上にあること、`familyFinite`は
そのfamilyのlist witnessを伴うfinitenessを与え、それぞれ定義8.2のstructural dataに使う。
`failure : ¬ (core.lawUniverse.law lawIndex).holds core.object`は定義8.2そのものであり、
obstructed extensionにだけ必要なmaterial premiseである。無条件coreへ移してはならない。
別のcertificate、typeclass、structure fieldからこのpremiseを射影してconstructorを閉じること、
またはconstructor内部でalways-false lawを追加することは、このcontractを満たさない。
