import Formal.AG.Atom.AATCore
import Formal.AG.Atom.LawfulnessZero

namespace AAT.AG

namespace FiniteModel

/-- R10: a small finite Atom universe for AG AAT Part I examples. -/
inductive FiniteAtom where
  | componentA
  | componentB
  | componentC
  | dependsAB
  | dependsBC
  | dependsCA
  | contractBase
  | contractImpl
  | substitutesImplBase
  deriving DecidableEq

namespace FiniteAtom

/-- R10: explicit finite enumeration of the selected Atom universe. -/
def all : List FiniteAtom :=
  [componentA, componentB, componentC, dependsAB, dependsBC, dependsCA,
    contractBase, contractImpl, substitutesImplBase]

/-- R10: the enumeration covers every finite Atom. -/
theorem mem_all (atom : FiniteAtom) : atom ∈ all := by
  cases atom <;> simp [all]

end FiniteAtom

/-- R10: finite Atom carrier with identity coordinate readings. -/
def carrier : AtomCarrier where
  AtomKind := FiniteAtom
  Axis := FiniteAtom
  Subject := FiniteAtom
  Predicate := FiniteAtom
  Payload := FiniteAtom
  Atom := FiniteAtom
  kind := id
  axis := id
  subject := id
  predicate := id
  payload := id

/-- R10: the finite family containing all selected atoms. -/
def allFamily : AtomFamily carrier where
  mem _ := True

/-- R10: the cycle relation of example 8.3. -/
def cycleRelation : carrier.Atom -> carrier.Atom -> Prop
  | FiniteAtom.dependsAB, FiniteAtom.dependsBC => True
  | FiniteAtom.dependsBC, FiniteAtom.dependsCA => True
  | FiniteAtom.dependsCA, FiniteAtom.dependsAB => True
  | _, _ => False

/-- R10: the substitution relation of example 8.4. -/
def substitutionRelation : carrier.Atom -> carrier.Atom -> Prop
  | FiniteAtom.contractImpl, FiniteAtom.contractBase => True
  | FiniteAtom.substitutesImplBase, FiniteAtom.contractImpl => True
  | FiniteAtom.substitutesImplBase, FiniteAtom.contractBase => True
  | _, _ => False

/-- R10: finite configuration containing the selected example atoms. -/
def configuration : AtomConfiguration carrier where
  family := allFamily
  relation a b := cycleRelation a b ∨ substitutionRelation a b
  identification _ _ := False

/-- R10: the finite configuration relation is supported by the finite family. -/
theorem configuration_familySupported :
    AtomConfiguration.FamilySupported configuration := by
  constructor
  · intro a b _h
    exact ⟨trivial, trivial⟩
  · intro a b h
    exact False.elim h

/-- R10: finite architecture object over the selected configuration. -/
def object : ArchitectureObject carrier where
  configuration := configuration
  StructureMaps := PUnit
  SelectedQuantities := PUnit
  structureMaps := PUnit.unit
  selectedQuantities := PUnit.unit

/-- R10: build a finite architecture object over any selected finite configuration. -/
def objectOfConfiguration (C : AtomConfiguration carrier) :
    ArchitectureObject carrier where
  configuration := C
  StructureMaps := PUnit
  SelectedQuantities := PUnit
  structureMaps := PUnit.unit
  selectedQuantities := PUnit.unit

/-- R10 / example 7.4: selected NoCycle law on the finite model. -/
def noCycleLaw : Law carrier where
  holds A := ¬
    (A.configuration.relation FiniteAtom.dependsAB FiniteAtom.dependsBC ∧
      A.configuration.relation FiniteAtom.dependsBC FiniteAtom.dependsCA ∧
        A.configuration.relation FiniteAtom.dependsCA FiniteAtom.dependsAB)

/-- R10 / example 8.4: selected substitution compatibility law. -/
def substitutionLaw : Law carrier where
  holds A := ¬
    (A.configuration.relation FiniteAtom.contractImpl FiniteAtom.contractBase ∧
      A.configuration.relation FiniteAtom.substitutesImplBase
        FiniteAtom.contractBase)

/-- R10: singleton invariant family used by the finite core package. -/
def invariantFamily : InvariantFamily carrier where
  Index := PUnit
  invariant _ := Invariant.predicate { holds := fun _ => True }

/-- R10: singleton required law universe for theorem 9.3 example. -/
def lawUniverse : LawUniverse carrier where
  Index := PUnit
  law _ := noCycleLaw
  role _ := LawRole.required
  witnessFamily := { Witness := PUnit, badWitness := fun _ _ => True }
  SelectedReading := PUnit
  selectedReading := PUnit.unit
  coverageAssumptions := True
  exactnessAssumptions := True

/-- R10: every law in the finite universe is required. -/
theorem lawUniverse_required (index : lawUniverse.Index) :
    lawUniverse.Required index := by
  cases index
  rfl

/-- R10: finite architecture signature with a singleton selected axis. -/
def signature : ArchitectureSignature carrier where
  Axis := PUnit
  Coordinate _ := Nat
  selected _ := True
  coordinate _ _ := 0

/-- R10: Atom A0-A8 system for the finite model. -/
def axiomSystem : AtomAxiomSystem carrier where
  primitiveExistence := ⟨FiniteAtom.componentA⟩
  singleFact _ := True
  singleFact_holds _ := trivial
  predicateStability := by
    intro a b
    constructor
    · intro h
      exact h.1
    · intro h
      cases h
      simp [SameCoordinates, carrier]
  Family := PUnit
  Configuration := PUnit
  compose := fun _ => PUnit.unit
  Law := PUnit
  lawHolds := fun _ _ => True
  ObservationDomain := PUnit
  Observation := PUnit
  observe _ := PUnit.unit
  Operation := PUnit
  operate _ F := F
  Doctrine := PUnit
  doctrine _ :=
    { Source := PUnit, Vocabulary := PUnit, SemanticReading := PUnit,
      Resolution := PUnit, sourceSemantics := fun _ => PUnit,
      normalize := id, atomize := fun _ => PUnit.unit }

/-- R10: A0 non-emptiness for the finite Atom universe. -/
theorem finite_atom_exists : ∃ _atom : carrier.Atom, True :=
  axiomSystem.primitive_exists

/-- R10 / example 8.3: the selected cycle relation contains A -> B. -/
theorem cycle_dependsAB_BC :
    cycleRelation FiniteAtom.dependsAB FiniteAtom.dependsBC :=
  trivial

/-- R10 / example 8.3: the selected cycle relation contains B -> C. -/
theorem cycle_dependsBC_CA :
    cycleRelation FiniteAtom.dependsBC FiniteAtom.dependsCA :=
  trivial

/-- R10 / example 8.3: the selected cycle relation contains C -> A. -/
theorem cycle_dependsCA_AB :
    cycleRelation FiniteAtom.dependsCA FiniteAtom.dependsAB :=
  trivial

/-- R10 / example 8.3: three selected depends atoms form a NoCycle obstruction circuit. -/
def cycleObstructionCircuit : ObstructionCircuit noCycleLaw object where
  family := allFamily
  relation := cycleRelation
  relation_supported := by
    intro a b _h
    exact ⟨trivial, trivial⟩
  finite := ∀ atom : carrier.Atom, atom ∈ FiniteAtom.all
  finite_holds := FiniteAtom.mem_all
  law_failure := by
    intro h
    exact h ⟨Or.inl cycle_dependsAB_BC,
      Or.inl cycle_dependsBC_CA, Or.inl cycle_dependsCA_AB⟩

/-- R10 / example 8.3: the cycle circuit records NoCycle law failure. -/
theorem cycle_obstruction_law_failure :
    ¬ noCycleLaw.holds object :=
  cycleObstructionCircuit.law_failure_holds

/-- R10 / example 8.4: substitution evidence links implementation to base contract. -/
theorem substitution_impl_base :
    substitutionRelation FiniteAtom.substitutesImplBase FiniteAtom.contractBase :=
  trivial

/-- R10 / example 8.4: implementation contract is related to the base contract. -/
theorem substitution_contract_impl_base :
    substitutionRelation FiniteAtom.contractImpl FiniteAtom.contractBase :=
  trivial

/-- R10 / example 8.4: nullable implementation versus non-null base is an obstruction circuit. -/
def substitutionObstructionCircuit :
    ObstructionCircuit substitutionLaw object where
  family := allFamily
  relation := substitutionRelation
  relation_supported := by
    intro a b _h
    exact ⟨trivial, trivial⟩
  finite := ∀ atom : carrier.Atom, atom ∈ FiniteAtom.all
  finite_holds := FiniteAtom.mem_all
  law_failure := by
    intro h
    exact h ⟨Or.inr substitution_contract_impl_base,
      Or.inr substitution_impl_base⟩

/-- R10: the selected object visibly carries the 3-cycle witness. -/
def hasCycleWitness (A : ArchitectureObject carrier) : Prop :=
  A.configuration.relation FiniteAtom.dependsAB FiniteAtom.dependsBC ∧
    A.configuration.relation FiniteAtom.dependsBC FiniteAtom.dependsCA ∧
      A.configuration.relation FiniteAtom.dependsCA FiniteAtom.dependsAB

/-- R10: the finite object has the selected 3-cycle witness. -/
theorem object_hasCycleWitness : hasCycleWitness object :=
  ⟨Or.inl cycle_dependsAB_BC,
    Or.inl cycle_dependsBC_CA, Or.inl cycle_dependsCA_AB⟩

/-- R10 / example 8.4: the substitution circuit records compatibility law failure. -/
theorem substitution_obstruction_law_failure :
    ¬ substitutionLaw.holds object :=
  substitutionObstructionCircuit.law_failure_holds

/-- R10: count-valued obstruction reading for the finite NoCycle example. -/
noncomputable def noCycleOmega (_L : Law carrier)
    (A : ArchitectureObject carrier) : Nat := by
  classical
  exact if hasCycleWitness A then 1 else 0

/-- R10: count-valued obstruction valuation for the finite NoCycle example. -/
noncomputable def noCycleValuation : ObstructionValuation carrier Nat where
  domain := ObstructionValueDomain.nat
  omega := noCycleOmega

/-- R10: zero-reflecting aggregation for the singleton required law universe. -/
def singletonRequiredAggregation :
    ZeroReflectingAggregation Nat noCycleValuation.domain lawUniverse.RequiredIndex where
  aggregate values := values ⟨PUnit.unit, rfl⟩
  zero_reflecting values := by
    constructor
    · intro h index
      cases index with
      | mk index hrequired =>
          cases index
          exact h
    · intro h
      exact h ⟨PUnit.unit, rfl⟩

/-- R10: soundness reads absence of the selected cycle witness as zero valuation. -/
theorem noCycleSound :
    ObstructionSound noCycleValuation noCycleLaw := by
  intro A h
  classical
  have hnot : ¬ hasCycleWitness A := h
  simp [noCycleValuation, noCycleOmega, ObstructionValueDomain.nat, hnot]

/-- R10: completeness reads NoCycle failure as a positive valuation. -/
theorem noCycleComplete :
    ObstructionComplete noCycleValuation noCycleLaw := by
  intro A _h
  classical
  have hcycle : hasCycleWitness A := by
    exact Classical.byContradiction (fun hnot => _h hnot)
  simp [noCycleValuation, noCycleOmega, ObstructionValueDomain.nat, hcycle]

/-- R10: theorem 9.3 instantiated on the finite NoCycle model. -/
theorem finite_lawfulness_iff_omega_zero :
    Lawfulness object lawUniverse ↔
      omegaU noCycleValuation lawUniverse singletonRequiredAggregation object =
        noCycleValuation.domain.zero :=
  lawfulness_iff_omegaU_zero noCycleValuation lawUniverse
    singletonRequiredAggregation
    (fun index => by
      cases index with
      | mk index hrequired =>
          cases index
          exact noCycleSound)
    (fun index => by
      cases index with
      | mk index hrequired =>
          cases index
          exact noCycleComplete)
    object

/-- R10: the finite model feeds the AAT Core theorem package. -/
def corePackage : AATCorePackage carrier :=
  AATCorePackage.ofComponents axiomSystem allFamily configuration object rfl rfl
    invariantFamily lawUniverse noCycleLaw cycleObstructionCircuit signature

/-- R10: the finite core package contains the selected finite object. -/
theorem corePackage_object :
    corePackage.object = object :=
  rfl

end FiniteModel

end AAT.AG
