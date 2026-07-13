import Formal.AG.Atom.AATCore
import Formal.AG.Atom.LawfulnessZero
import Formal.AG.Atom.ThreeReading
import Formal.AG.Site.FinitePoset
import Formal.AG.Site.MinimalContextProfile
import Formal.AG.Site.SheafCategory
import Mathlib.Data.Fintype.Basic

namespace AAT.AG

open CategoryTheory
open Opposite

namespace FiniteModel

universe v

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

/-- peer-review hardening I-3: the selected finite family has an explicit list cover. -/
theorem allFamily_listFinite : allFamily.ListFinite :=
  ⟨FiniteAtom.all, fun atom _hmem => FiniteAtom.mem_all atom⟩

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

/-- peer-review hardening I-1/I-3: acyclic finite configuration over the same nonempty atom family. -/
def acyclicConfiguration : AtomConfiguration carrier where
  family := allFamily
  relation _ _ := False
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

/-- peer-review hardening I-1: acyclic finite architecture object used for concrete three-reading firing. -/
def acyclicObject : ArchitectureObject carrier where
  configuration := acyclicConfiguration
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

/-- peer-review hardening I-1: canonical required-law witness family for the finite NoCycle universe. -/
def concreteNoCycleWitnessFamily : LawWitnessFamily carrier :=
  requiredLawWitnessFamily lawUniverse

/-- peer-review hardening I-1: canonical required-law signature axes for the finite NoCycle universe. -/
def concreteNoCycleSignatureAxes : SignatureAxes carrier :=
  requiredLawSignatureAxes lawUniverse

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

/-- peer-review hardening I-3: the cycle obstruction circuit has explicit finite support. -/
theorem cycleObstructionCircuit_listFinite :
    cycleObstructionCircuit.ListFinite :=
  allFamily_listFinite

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

/-- peer-review hardening I-3: the substitution obstruction circuit has explicit finite support. -/
theorem substitutionObstructionCircuit_listFinite :
    substitutionObstructionCircuit.ListFinite :=
  allFamily_listFinite

/-- R10: the selected object visibly carries the 3-cycle witness. -/
def hasCycleWitness (A : ArchitectureObject carrier) : Prop :=
  A.configuration.relation FiniteAtom.dependsAB FiniteAtom.dependsBC ∧
    A.configuration.relation FiniteAtom.dependsBC FiniteAtom.dependsCA ∧
      A.configuration.relation FiniteAtom.dependsCA FiniteAtom.dependsAB

/-- R10: the finite object has the selected 3-cycle witness. -/
theorem object_hasCycleWitness : hasCycleWitness object :=
  ⟨Or.inl cycle_dependsAB_BC,
    Or.inl cycle_dependsBC_CA, Or.inl cycle_dependsCA_AB⟩

/-- peer-review hardening I-1: the acyclic finite object satisfies the selected NoCycle law. -/
theorem acyclic_noCycleLaw_holds :
    noCycleLaw.holds acyclicObject := by
  intro hcycle
  exact hcycle.1

/-- peer-review hardening I-1: the acyclic finite object is semantically lawful. -/
theorem acyclic_lawfulness :
    Lawfulness acyclicObject lawUniverse := by
  intro index _hrequired
  cases index
  exact acyclic_noCycleLaw_holds

/-- peer-review hardening I-1: the cyclic finite object is not semantically lawful. -/
theorem object_lawfulness_fails :
    ¬ Lawfulness object lawUniverse := by
  intro h
  exact cycle_obstruction_law_failure (h PUnit.unit rfl)

/-- peer-review hardening I-1: the concrete witness family is nondegenerate on the cyclic object. -/
theorem object_hasConcreteNoCycleBadWitness :
    ∃ witness : concreteNoCycleWitnessFamily.Witness,
      concreteNoCycleWitnessFamily.badWitness object witness :=
  ⟨⟨PUnit.unit, rfl⟩, cycle_obstruction_law_failure⟩

/-- peer-review hardening I-1: the acyclic object has no concrete required-law bad witness. -/
theorem acyclic_noConcreteNoCycleBadWitness :
    NoRequiredObstruction acyclicObject concreteNoCycleWitnessFamily :=
  (semanticLawful_iff_noRequiredObstruction_requiredLawWitness
    acyclicObject lawUniverse).mp acyclic_lawfulness

/-- peer-review hardening I-1: the acyclic object has zero on the concrete required-law axis. -/
theorem acyclic_requiredLawAxesZero :
    RequiredSignatureAxesZero acyclicObject concreteNoCycleSignatureAxes :=
  (semanticLawful_iff_requiredSignatureAxesZero_requiredLawAxes
    acyclicObject lawUniverse).mp acyclic_lawfulness

/-- peer-review hardening I-1: the cyclic object has a nonzero concrete required-law axis. -/
theorem object_requiredLawAxesZero_fails :
    ¬ RequiredSignatureAxesZero object concreteNoCycleSignatureAxes := by
  intro hzero
  exact cycle_obstruction_law_failure (hzero ⟨PUnit.unit, rfl⟩ trivial)

/-- peer-review hardening I-1: concrete three-reading agreement fires on the acyclic finite object. -/
theorem acyclic_concreteThreeReadingAgreement :
    (SemanticLawful acyclicObject lawUniverse ↔
        NoRequiredObstruction acyclicObject concreteNoCycleWitnessFamily) ∧
      (NoRequiredObstruction acyclicObject concreteNoCycleWitnessFamily ↔
        RequiredSignatureAxesZero acyclicObject concreteNoCycleSignatureAxes) ∧
        (SemanticLawful acyclicObject lawUniverse ↔
          RequiredSignatureAxesZero acyclicObject concreteNoCycleSignatureAxes) :=
  concreteThreeReadingAgreement acyclicObject lawUniverse

/-- peer-review hardening I-1: concrete three-reading agreement also detects the cyclic failure. -/
theorem object_concreteThreeReadingAgreement_fires :
    (¬ SemanticLawful object lawUniverse) ∧
      (∃ witness : concreteNoCycleWitnessFamily.Witness,
        concreteNoCycleWitnessFamily.badWitness object witness) ∧
        ¬ RequiredSignatureAxesZero object concreteNoCycleSignatureAxes :=
  ⟨object_lawfulness_fails, object_hasConcreteNoCycleBadWitness,
    object_requiredLawAxesZero_fails⟩

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
    invariantFamily lawUniverse signature

/-- R10: the selected NoCycle law fails on the cyclic finite object. -/
theorem noCycleLaw_fails_on_object :
    ¬ noCycleLaw.holds object :=
  cycleObstructionCircuit.law_failure

/--
R10: the cyclic finite model realizes an obstruction over the unconditional
core package, relative to the selected NoCycle law failure.
-/
def obstructedCorePackage : ObstructedAATCorePackage corePackage :=
  ObstructedAATCorePackage.ofLawFailure corePackage PUnit.unit allFamily
    cycleRelation
    (by
      intro a b _h
      exact ⟨trivial, trivial⟩)
    allFamily_listFinite noCycleLaw_fails_on_object

/-- peer-review hardening I-2: the finite model realizes the abstract A0-A8 family/configuration tower. -/
def atomTowerRealization : AATCorePackage.AtomTowerRealization axiomSystem where
  familyToken := PUnit.unit
  configurationToken := PUnit.unit
  familyOf _ := allFamily
  configurationOf _ := configuration
  family := allFamily
  configuration := configuration
  family_eq := rfl
  configuration_eq := rfl
  configurationToken_eq := rfl
  configuration_family_eq := rfl

/-- peer-review hardening I-2: finite model core package using the axiom-system realization bridge. -/
def corePackageFromAxiomRealization : AATCorePackage carrier :=
  AATCorePackage.ofAxiomRealization axiomSystem atomTowerRealization object rfl
    invariantFamily lawUniverse signature

/-- peer-review hardening I-2: the finite realization theorem has no HEq in its conclusion. -/
theorem corePackageFromAxiomRealization_exists_noHEq :
    ∃ core : AATCorePackage carrier,
      core.axioms = axiomSystem ∧
        core.family = allFamily ∧
          core.configuration = configuration ∧
            core.object = object ∧
              core.configuration.family = core.family ∧
                core.object.configuration = core.configuration ∧
                  core.lawUniverse = lawUniverse ∧
                    core.signature = signature :=
  AATCorePackage.exists_ofAxiomRealization_noHEq axiomSystem atomTowerRealization
    object rfl invariantFamily lawUniverse signature

/--
R10: the selected NoCycle law admits the conditional obstruction extension for
the finite core package.
-/
theorem obstructedCorePackage_exists :
    ∃ obstructed : ObstructedAATCorePackage corePackage,
      obstructed.lawIndex = PUnit.unit :=
  ⟨obstructedCorePackage, rfl⟩

/-- R10: the conditional obstruction extension retains the actual law failure. -/
theorem obstructedCorePackage_law_failure :
    ¬ (corePackage.lawUniverse.law obstructedCorePackage.lawIndex).holds
      corePackage.object :=
  obstructedCorePackage.law_failure

/-- R10: the conditional layer retains the concrete finite obstruction support. -/
theorem obstructedCorePackage_listFinite :
    obstructedCorePackage.circuit.ListFinite :=
  allFamily_listFinite

/-- R10: the finite core package contains the selected finite object. -/
theorem corePackage_object :
    corePackage.object = object :=
  rfl

/-!
## Part II finite site example

The following singleton context/site extends the Part I finite model to the
Part II site layer. It is intentionally selected and finite: it does not claim
that every possible `ArchCtx(object)` is finite.
-/

/-- R11 / II.AC16: singleton context over the finite architecture object. -/
def siteContext : Site.ArchCtx object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => True
    supportReads_objectFamily := fun _h => trivial
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- R11 / II.AC16: identity readable morphism for the finite context example. -/
def siteContextIdentityMorphism (W : Site.ArchCtx object) :
    Site.ContextMorphism W W where
  supportMap := id
  axisMap := id
  observableRestrict := id

/--
R11 / peer-review hardening II-3: the singleton finite context reads only atoms from the
selected architecture object's Atom family.
-/
theorem siteContext_supportReads_objectFamily
    {support : siteContext.Support} {atom : carrier.Atom}
    (h : siteContext.minimal.supportReads support atom) :
    object.configuration.family.mem atom :=
  siteContext.supportReads_objectFamily h

/--
R11 / peer-review hardening II-3: the finite model's selected identity morphism fires all
concrete context-morphism role predicates.
-/
theorem siteContextIdentityMorphism_rolesConcrete :
    (siteContextIdentityMorphism siteContext).IsRestriction ∧
      (siteContextIdentityMorphism siteContext).IsProjection ∧
        (siteContextIdentityMorphism siteContext).IsRefinement ∧
          (siteContextIdentityMorphism siteContext).IsBaseChange := by
  let f := siteContextIdentityMorphism siteContext
  let hRestriction : f.IsRestriction :=
    ⟨fun h => h, fun h => h, fun h => h,
      fun h => siteContext.supportReads_objectFamily h⟩
  exact ⟨hRestriction, ⟨hRestriction, fun h => h⟩,
    ⟨hRestriction, ⟨⟨fun h => h, fun h => h⟩, ⟨fun h => h, fun h => h⟩⟩⟩,
    ⟨hRestriction, ⟨⟨fun h => h, fun h => h⟩,
      ⟨fun h => h, fun h => h⟩, fun h => h⟩⟩⟩

/-- R11 / II.AC16: equality preorder on contexts, used by the singleton selected poset. -/
def siteContextPreorder : Site.ContextPreorderCategory object where
  le W V := W = V
  refl W := rfl
  trans hWV hVX := hWV.trans hVX
  readableMorphism := fun h => by
    cases h
    exact siteContextIdentityMorphism _
  readableMorphism_isRestriction := fun {W _V} h => by
    cases h
    exact ⟨fun h => h, fun h => h, fun h => h,
      fun h => W.supportReads_objectFamily h⟩

/-- R11 / II.AC16: singleton selected finite context index. -/
abbrev SiteContextIndex := PUnit

/-- R11 / II.AC16: selected finite context for the singleton poset. -/
def siteContextOf (_i : SiteContextIndex) : Site.ArchCtx object :=
  siteContext

/-- R11 / II.AC16: the selected context poset is finite. -/
theorem siteContextIndex_finite : Finite SiteContextIndex :=
  inferInstance

/-- R11 / II.AC16: selected meet in the singleton context poset. -/
def siteContextMeet (_i _j : SiteContextIndex) : SiteContextIndex :=
  PUnit.unit

/-- R11 / II.AC16: singleton selected context order maps into the site preorder. -/
theorem siteContextLe_sound {i j : SiteContextIndex} (_h : True) :
    siteContextPreorder.le (siteContextOf i) (siteContextOf j) :=
  rfl

/--
R11 / II.AC16: proposition 4.2 quotient finite-meet poset construction fires
for the finite architecture object using the canonical restriction preorder.
-/
noncomputable def siteRestrictionQuotientFiniteMeetPosetCategory :
    Site.QuotientFiniteMeetPosetCategory
      (Site.contextMorphismPreorderCategory object) :=
  Site.quotientFiniteMeetPosetCategoryOf
    (Site.contextMorphismPreorderCategory object)
    (Site.productContextFiniteMeet (A := object))

/--
R11 / II.AC16: example theorem reading proposition 4.2 on the finite model's
canonical restriction preorder.
-/
theorem siteRestrictionQuotientFiniteMeetPosetCategory_fromFiniteMeet :
    ∃ site : Site.QuotientFiniteMeetPosetCategory
        (Site.contextMorphismPreorderCategory object),
      site =
        Site.quotientFiniteMeetPosetCategoryOf
          (Site.contextMorphismPreorderCategory object)
          (Site.productContextFiniteMeet (A := object)) :=
  Site.minimalContextQuotientFiniteMeetPosetCategory_fromFiniteMeet
    (Site.contextMorphismPreorderCategory object)
    (Site.productContextFiniteMeet (A := object))

/-- Issue #3195: finite selected minimal-context profile type. -/
abbrev SiteMinimalContextProfile :=
  Site.MinimalContextProfile object FiniteAtom FiniteAtom

/--
Issue #3195: a nonempty finite profile reading component A, its axis, and the
base contract observable.
-/
def siteComponentAProfile : SiteMinimalContextProfile where
  support := {FiniteAtom.componentA}
  support_le_object := fun {_atom} _h => trivial
  axis := {FiniteAtom.componentA}
  observable := {FiniteAtom.contractBase}

/--
Issue #3195: an independently declared representative of the component-A
profile, used to fire representative independence.
-/
def siteComponentAProfileCopy : SiteMinimalContextProfile where
  support := {FiniteAtom.componentA}
  support_le_object := fun {_atom} _h => trivial
  axis := {FiniteAtom.componentA}
  observable := {FiniteAtom.contractBase}

/--
Issue #3195: a second nonempty finite profile reading component B, its axis,
and the implementation-contract observable.
-/
def siteComponentBProfile : SiteMinimalContextProfile where
  support := {FiniteAtom.componentB}
  support_le_object := fun {_atom} _h => trivial
  axis := {FiniteAtom.componentB}
  observable := {FiniteAtom.contractImpl}

/-- Issue #3195: presentation-level profile type before readable quotienting. -/
abbrev SiteRawMinimalContextProfile :=
  Site.MinimalContextProfile.RawMinimalContextProfile
    object FiniteAtom FiniteAtom

/-- Issue #3195: first nonempty presentation of the component-A readings. -/
def siteComponentARawProfileOne : SiteRawMinimalContextProfile where
  SupportIndex := PUnit
  supportRead := fun _ => FiniteAtom.componentA
  supportRead_objectFamily := fun _ => trivial
  AxisIndex := PUnit
  axisRead := fun _ => FiniteAtom.componentA
  ObservableIndex := PUnit
  observableRead := fun _ => FiniteAtom.contractBase

/--
Issue #3195: a genuinely different presentation with duplicate indices and the
same extensional component-A readings.
-/
def siteComponentARawProfileTwo : SiteRawMinimalContextProfile where
  SupportIndex := Bool
  supportRead := fun _ => FiniteAtom.componentA
  supportRead_objectFamily := fun _ => trivial
  AxisIndex := Bool
  axisRead := fun _ => FiniteAtom.componentA
  ObservableIndex := Bool
  observableRead := fun _ => FiniteAtom.contractBase

/-- Issue #3195: raw presentation one normalizes to the component-A profile. -/
theorem siteComponentARawProfileOne_normalize :
    Site.MinimalContextProfile.RawMinimalContextProfile.normalize
        siteComponentARawProfileOne = siteComponentAProfile := by
  apply Site.MinimalContextProfile.ext <;> ext value <;>
    simp [Site.MinimalContextProfile.RawMinimalContextProfile.normalize,
      siteComponentARawProfileOne, siteComponentAProfile]

/-- Issue #3195: raw presentation two normalizes to the same profile. -/
theorem siteComponentARawProfileTwo_normalize :
    Site.MinimalContextProfile.RawMinimalContextProfile.normalize
        siteComponentARawProfileTwo = siteComponentAProfile := by
  apply Site.MinimalContextProfile.ext <;> ext value <;>
    simp [Site.MinimalContextProfile.RawMinimalContextProfile.normalize,
      siteComponentARawProfileTwo, siteComponentAProfile]

/-- Issue #3195: the two raw presentations are not equal before quotienting. -/
theorem siteComponentARawProfiles_ne :
    siteComponentARawProfileOne ≠ siteComponentARawProfileTwo := by
  intro h
  have hType : PUnit = Bool := congrArg
    (fun W : SiteRawMinimalContextProfile => W.SupportIndex) h
  have hCard := Fintype.card_congr (Equiv.cast hType)
  simp at hCard

/-- Issue #3195: the two raw presentations are mutually readable. -/
theorem siteComponentARawProfiles_readableEquivalent :
    Site.MinimalContextProfile.RawMinimalContextProfile.readableSetoid
      siteComponentARawProfileOne siteComponentARawProfileTwo := by
  apply (Site.MinimalContextProfile.RawMinimalContextProfile.readableEquivalent_iff_normalize_eq
    _ _).mpr
  rw [siteComponentARawProfileOne_normalize,
    siteComponentARawProfileTwo_normalize]

/-- Issue #3195: distinct raw presentations become equal in the quotient. -/
theorem siteComponentARawProfiles_quotient_eq :
    (Quotient.mk _ siteComponentARawProfileOne :
      Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile) =
    Quotient.mk _ siteComponentARawProfileTwo :=
  Quotient.sound siteComponentARawProfiles_readableEquivalent

/--
Issue #3195: descended meet is independent of the two distinct raw
representatives.
-/
theorem siteComponentARawProfiles_quotientInf_independent :
    Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf
        (Quotient.mk _ siteComponentARawProfileOne)
        (Site.MinimalContextProfile.RawMinimalContextProfile.quotientOfNormalized
          siteComponentBProfile) =
      Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf
        (Quotient.mk _ siteComponentARawProfileTwo)
        (Site.MinimalContextProfile.RawMinimalContextProfile.quotientOfNormalized
          siteComponentBProfile) := by
  rw [siteComponentARawProfiles_quotient_eq]

/-- Issue #3195: the raw finite example lives in a finite-limit preorder category. -/
theorem siteRawMinimalContext_hasFiniteLimits :
    Limits.HasFiniteLimits SiteRawMinimalContextProfile :=
  Site.MinimalContextProfile.RawMinimalContextProfile.hasFiniteLimits

/-- Issue #3195: component A is not readable below component B. -/
theorem siteComponentAProfile_not_le_siteComponentBProfile :
    ¬ siteComponentAProfile ≤ siteComponentBProfile := by
  intro h
  have hmem : FiniteAtom.componentA ∈ siteComponentBProfile.support :=
    h.1 (by simp [siteComponentAProfile])
  simp [siteComponentBProfile] at hmem

/-- Issue #3195: component B is not readable below component A. -/
theorem siteComponentBProfile_not_le_siteComponentAProfile :
    ¬ siteComponentBProfile ≤ siteComponentAProfile := by
  intro h
  have hmem : FiniteAtom.componentB ∈ siteComponentAProfile.support :=
    h.1 (by simp [siteComponentBProfile])
  simp [siteComponentAProfile] at hmem

/-- Issue #3195: the two finite profiles are distinct quotient-normal forms. -/
theorem siteComponentAProfile_ne_siteComponentBProfile :
    siteComponentAProfile ≠ siteComponentBProfile := by
  intro h
  apply siteComponentAProfile_not_le_siteComponentBProfile
  rw [h]

/-- Issue #3195: the independently declared A profiles are mutually readable. -/
theorem siteComponentAProfiles_mutuallyReadable :
    siteComponentAProfile ≤ siteComponentAProfileCopy ∧
      siteComponentAProfileCopy ≤ siteComponentAProfile := by
  constructor <;> simp [siteComponentAProfile, siteComponentAProfileCopy]

/-- Issue #3195: no selected hom exists from the A profile to the B profile. -/
theorem siteComponentAProfile_to_siteComponentBProfile_isEmpty :
    IsEmpty (siteComponentAProfile ⟶ siteComponentBProfile) :=
  ⟨fun f => siteComponentAProfile_not_le_siteComponentBProfile f.le⟩

/-- Issue #3195: the actual selected A-to-top context-morphism subtype is inhabited. -/
theorem siteComponentAProfile_to_top_readableContextHom_nonempty :
    Nonempty (Site.MinimalContextProfile.ReadableContextHom
      siteComponentAProfile (⊤ : SiteMinimalContextProfile)) :=
  ⟨Site.MinimalContextProfile.readableContextHomOfLE le_top⟩

/-- Issue #3195: the actual selected A-to-B context-morphism subtype is empty. -/
theorem siteComponentAProfile_to_B_readableContextHom_isEmpty :
    IsEmpty (Site.MinimalContextProfile.ReadableContextHom
      siteComponentAProfile siteComponentBProfile) :=
  ⟨fun f => siteComponentAProfile_not_le_siteComponentBProfile
    (Site.MinimalContextProfile.leOfReadableContextHom f)⟩

/-- Issue #3195: the meet is distinct from component A. -/
theorem siteComponentAProfile_ne_meet :
    siteComponentAProfile ≠ siteComponentAProfile ⊓ siteComponentBProfile := by
  intro h
  apply siteComponentAProfile_not_le_siteComponentBProfile
  have hMeet := inf_le_right (a := siteComponentAProfile) (b := siteComponentBProfile)
  rwa [← h] at hMeet

/-- Issue #3195: the meet is distinct from component B. -/
theorem siteComponentBProfile_ne_meet :
    siteComponentBProfile ≠ siteComponentAProfile ⊓ siteComponentBProfile := by
  intro h
  apply siteComponentBProfile_not_le_siteComponentAProfile
  have hMeet := inf_le_left (a := siteComponentAProfile) (b := siteComponentBProfile)
  rwa [← h] at hMeet

/-- Issue #3195: selected cospan leg from component A to the terminal profile. -/
def siteComponentAProfileToTop : siteComponentAProfile ⟶ (⊤ : SiteMinimalContextProfile) :=
  homOfLE le_top

/-- Issue #3195: selected cospan leg from component B to the terminal profile. -/
def siteComponentBProfileToTop : siteComponentBProfile ⟶ (⊤ : SiteMinimalContextProfile) :=
  homOfLE le_top

/--
Issue #3195: the nontrivial finite cospan has the componentwise meet as its
categorical pullback.
-/
theorem siteComponentProfiles_pullback_eq_meet :
    Limits.pullback siteComponentAProfileToTop siteComponentBProfileToTop =
      siteComponentAProfile ⊓ siteComponentBProfile :=
  Site.MinimalContextProfile.pullback_eq_inf
    siteComponentAProfileToTop siteComponentBProfileToTop

/-- Issue #3195: the selected A cospan leg is an actual legacy restriction. -/
theorem siteComponentAProfileToTop_isRestriction :
    (Site.MinimalContextProfile.homToContextMorphism
      siteComponentAProfileToTop).IsRestriction :=
  Site.MinimalContextProfile.homToContextMorphism_isRestriction
    siteComponentAProfileToTop

/-- Issue #3195: meet is independent of the selected A representative. -/
theorem siteComponentProfiles_meet_representative_independent :
    siteComponentAProfile ⊓ siteComponentBProfile =
      siteComponentAProfileCopy ⊓ siteComponentBProfile :=
  Site.MinimalContextProfile.inf_eq_inf_of_mutual_readability
    siteComponentAProfiles_mutuallyReadable ⟨le_rfl, le_rfl⟩

/--
Issue #3195: nondegenerate proposition 4.2 firing combines distinct profiles,
a third meet object, categorical pullback, actual hom thinness, and legacy
restriction comparison.
-/
theorem siteMinimalContextFiniteMeet_nondegenerate_fires :
    siteComponentARawProfileOne ≠ siteComponentARawProfileTwo ∧
      (Quotient.mk _ siteComponentARawProfileOne :
        Site.MinimalContextProfile.RawMinimalContextProfile.QuotientProfile) =
        Quotient.mk _ siteComponentARawProfileTwo ∧
      Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf
          (Quotient.mk _ siteComponentARawProfileOne)
          (Site.MinimalContextProfile.RawMinimalContextProfile.quotientOfNormalized
            siteComponentBProfile) =
        Site.MinimalContextProfile.RawMinimalContextProfile.quotientInf
          (Quotient.mk _ siteComponentARawProfileTwo)
          (Site.MinimalContextProfile.RawMinimalContextProfile.quotientOfNormalized
            siteComponentBProfile) ∧
      Limits.HasFiniteLimits SiteRawMinimalContextProfile ∧
      siteComponentAProfile ≠ siteComponentBProfile ∧
      siteComponentAProfile ≠ siteComponentAProfile ⊓ siteComponentBProfile ∧
      siteComponentBProfile ≠ siteComponentAProfile ⊓ siteComponentBProfile ∧
      Limits.pullback siteComponentAProfileToTop siteComponentBProfileToTop =
        siteComponentAProfile ⊓ siteComponentBProfile ∧
      Subsingleton (siteComponentAProfile ⟶ (⊤ : SiteMinimalContextProfile)) ∧
      Subsingleton (Site.MinimalContextProfile.ReadableContextHom
        siteComponentAProfile (⊤ : SiteMinimalContextProfile)) ∧
      Nonempty (Site.MinimalContextProfile.ReadableContextHom
        siteComponentAProfile (⊤ : SiteMinimalContextProfile)) ∧
      IsEmpty (Site.MinimalContextProfile.ReadableContextHom
        siteComponentAProfile siteComponentBProfile) ∧
      (Site.MinimalContextProfile.homToContextMorphism
        siteComponentAProfileToTop).IsRestriction :=
  ⟨siteComponentARawProfiles_ne,
    siteComponentARawProfiles_quotient_eq,
    siteComponentARawProfiles_quotientInf_independent,
    siteRawMinimalContext_hasFiniteLimits,
    siteComponentAProfile_ne_siteComponentBProfile,
    siteComponentAProfile_ne_meet,
    siteComponentBProfile_ne_meet,
    siteComponentProfiles_pullback_eq_meet,
    Site.MinimalContextProfile.hom_subsingleton _ _,
    Site.MinimalContextProfile.readableContextHom_subsingleton _ _,
    siteComponentAProfile_to_top_readableContextHom_nonempty,
    siteComponentAProfile_to_B_readableContextHom_isEmpty,
    siteComponentAProfileToTop_isRestriction⟩

/-- R11 / II.AC16: explicit pullback / overlap package for the equality context preorder. -/
def siteOverlap : Site.ContextOverlapPullback siteContextPreorder where
  overlap base _left _right := base
  overlap_le_left := by
    intro base left _right hl _hr
    exact hl.symm
  overlap_le_right := by
    intro base _left right _hl hr
    exact hr.symm
  overlap_le_base := by
    intro _base _left _right _hl _hr
    rfl
  overlap_lift := by
    intro _base left _right X hl _hr hXleft _hXright
    exact hXleft.trans hl

/-- R11 / II.AC16: coverage requirements that make every selected finite datum visible. -/
def siteCoverageRequirements :
    Site.CoverageRequirements object lawUniverse signature where
  selectedReading := lawUniverse.selectedReading
  requiredSupport := fun _ _ => True
  requiredWitness := fun _ _ => True
  requiredAxis := fun _ _ => True
  supportVisibleOn := fun _ _ => True
  witnessVisibleOn := fun _ _ => True
  axisReadableOn := fun _ _ => True
  boundaryVisibleOn := fun _ _ => True

/-- R11 / II.AC16: the finite AAT site over the Part I finite model. -/
def site : Site.AATSite object where
  contextPreorder := siteContextPreorder
  lawUniverse := lawUniverse
  signature := signature
  requirements := siteCoverageRequirements
  overlap := siteOverlap

/-- R11 / II.AC16: the singleton base object of the finite site. -/
def siteBase : site.category :=
  Site.ContextCategoryObject.of siteContextPreorder siteContext

/-- R11 / II.AC16: singleton admissible cover of the finite site. -/
def siteSingletonCover :
    Site.AATCoverageFamily siteCoverageRequirements siteOverlap siteBase where
  Index := PUnit
  patch := fun _ => siteContext
  inclusion := fun _ => rfl
  admissible := {
    atomSupportCoverage := fun _atom _hreq => ⟨PUnit.unit, trivial⟩
    lawWitnessCoverage := fun _witness _hreq => Or.inl ⟨PUnit.unit, trivial⟩
    signatureAxisCoverage := fun _axis _hreq => ⟨PUnit.unit, trivial⟩
    boundaryCoverage := fun _i _j => trivial
    nonGeneration := fun _i {_support} {_atom} _h => trivial
  }

/-- R11 / II.AC16: selected witness ideal requirements for the finite site. -/
def siteAdequacyRequirements :
    Site.UAdequacyRequirements siteContextPreorder siteCoverageRequirements where
  selectedWitnessIdeal := fun _ _ => True
  witnessIdealPreservedBy := fun _h _hideal => trivial

/-- R11 / II.AC16: direct `U`-adequacy of the singleton finite cover. -/
theorem siteSingletonCover_uAdequate :
    Site.UAdequateCover siteAdequacyRequirements siteSingletonCover where
  topologyCover := Site.AATGrothendieckTopology.generate_mem siteSingletonCover
  requiredSupportCovered := fun _atom _hreq => ⟨PUnit.unit, trivial⟩
  requiredWitnessesVisible := fun _witness _hreq => Or.inl ⟨PUnit.unit, trivial⟩
  requiredAxesReadable := fun _axis _hreq => ⟨PUnit.unit, trivial⟩
  boundaryWitnessesVisible := fun _i _j => trivial
  restrictionMapsPreserveWitnessIdeals := fun _i _hbase => trivial

/-- peer-review hardening II-6: every morphism in the singleton finite context site is an isomorphism. -/
theorem siteContextCategoryObject_eq_of_hom {X Y : site.category} (_f : X ⟶ Y) :
    X = Y := by
  cases X
  cases Y
  simp [Site.ContextCategoryObject.instPreorder] at _f
  cases _f.down.down
  rfl

private theorem siteAdmissiblePrecoverage_index_nonempty
    {ι : Type v} {S : site.category} {X : ι -> site.category}
    {f : ∀ i, X i ⟶ S}
    (hR : Presieve.ofArrows X f ∈
      Site.admissiblePrecoverage siteCoverageRequirements siteOverlap S) :
    Nonempty ι := by
  rcases hR with ⟨F, hF⟩
  rcases F.admissible.atomSupportCoverage FiniteAtom.componentA trivial with ⟨i, _hi⟩
  have hmemF : F.presieve (homOfLE (F.inclusion i)) := by
    exact Presieve.ofArrows.mk i
  have hmem :
      Presieve.ofArrows X f (homOfLE (F.inclusion i)) := by
    simpa [hF] using hmemF
  exact ⟨hmem.idx⟩

private theorem siteContextPresieve_ofArrows_eta
    {ι : Type v} {S : site.category} (P : ι -> site.category)
    (p : ∀ i, P i ⟶ S) :
    Presieve.ofArrows P p =
      Presieve.ofArrows
        (fun i => Site.ContextCategoryObject.of siteContextPreorder (P i).ctx)
        (fun i => homOfLE (p i).le) := rfl

private theorem siteContextPresieve_ofArrows_eq_unit
    {ι : Type v} {S : site.category} (P : ι -> site.category)
    (p : ∀ i, P i ⟶ S) [Nonempty ι] :
    Presieve.ofArrows P p =
      Presieve.ofArrows (fun _ : PUnit => S) (fun _ => 𝟙 S) := by
  funext Z h
  apply propext
  constructor
  · intro _hz
    exact Presieve.ofArrows.mk' PUnit.unit
      (siteContextCategoryObject_eq_of_hom h) (Subsingleton.elim _ _)
  · intro _hz
    let i0 : ι := Classical.choice inferInstance
    exact Presieve.ofArrows.mk' i0
      ((siteContextCategoryObject_eq_of_hom h).trans
        (siteContextCategoryObject_eq_of_hom (p i0)).symm)
      (Subsingleton.elim _ _)

/--
peer-review hardening II-6: the singleton finite AAT admissible precoverage has pullbacks.

This is a concrete finite firing instance for the Mathlib `Coverage` bridge:
the selected context category is equality-thin, so every arrow in a covering
presieve is an isomorphism and hence has pullbacks along every base change.
-/
noncomputable instance siteAdmissiblePrecoverage_hasPullbacks :
    Precoverage.HasPullbacks
      (Site.admissiblePrecoverage siteCoverageRequirements siteOverlap) where
  hasPullbacks_of_mem := by
    intro X Y R f _hR
    refine ⟨?_⟩
    intro Z h _hh
    have hIso : IsIso h := by
      have heq : Z = Y := siteContextCategoryObject_eq_of_hom h
      subst Z
      rw [Subsingleton.elim h (𝟙 Y)]
      infer_instance
    exact Limits.hasPullback_of_left_iso h f

/--
peer-review hardening II-6: the singleton finite AAT admissible precoverage is stable under
base change.

The base-changed family uses the pulled-back objects supplied by Mathlib's
`IsPullback` witness.  The finite singleton requirements make admissibility
load-bearing enough to produce a real `AATCoverageFamily`, while still staying
within this selected finite fixture rather than claiming arbitrary
precoverage stability.
-/
noncomputable instance siteAdmissiblePrecoverage_stableUnderBaseChange :
    Precoverage.IsStableUnderBaseChange
      (Site.admissiblePrecoverage siteCoverageRequirements siteOverlap) where
  mem_coverings_of_isPullback := by
    intro ι S X f hR Y _g P p₁ _p₂ _h
    have hNonempty : Nonempty ι := siteAdmissiblePrecoverage_index_nonempty hR
    refine ⟨{
      Index := PUnit
      patch := fun _ => Y.ctx
      inclusion := fun _ => (siteContextPreorder.refl Y.ctx)
      admissible := {
        atomSupportCoverage := fun _atom _hreq => ⟨PUnit.unit, trivial⟩
        lawWitnessCoverage := fun _witness _hreq => Or.inl ⟨PUnit.unit, trivial⟩
        signatureAxisCoverage := fun _axis _hreq => ⟨PUnit.unit, trivial⟩
        boundaryCoverage := fun _i _j => trivial
        nonGeneration := fun _i {_support} {_atom} _h => trivial
      }
    }, ?_⟩
    exact siteContextPresieve_ofArrows_eq_unit P p₁

/--
peer-review hardening II-6: the Mathlib `Coverage.toGrothendieck` bridge fires on the
selected finite singleton site.
-/
theorem siteTopology_eq_coverage_toGrothendieck :
    site.topology =
      (Site.admissiblePrecoverage siteCoverageRequirements siteOverlap).toCoverage.toGrothendieck :=
  Site.AATGrothendieckTopology.eq_coverage_toGrothendieck
    siteCoverageRequirements siteOverlap

/-- R11 / II.AC16: the finite model has finitely many required witnesses. -/
theorem site_requiredWitnessSubtype_finite :
    Finite (Site.RequiredWitnessSubtype siteCoverageRequirements) := by
  change Finite { witness : PUnit // True }
  infer_instance

/-- R11 / II.AC16: witness-closure cover package for the finite model. -/
def siteWitnessClosureCover :
    Site.WitnessClosureCover siteAdequacyRequirements siteOverlap siteBase where
  SeedIndex := PUnit
  seedPatch := fun _ => siteContext
  seedInclusion := fun _ => rfl
  localFiniteRequiredWitnesses := site_requiredWitnessSubtype_finite
  RequiredWitnessSupport := fun _ => siteContext
  requiredWitnessSupport_inclusion := fun _ => rfl
  requiredWitnessSupport_visible := fun _ => trivial
  requiredSupportCovered := fun _atom _hreq => ⟨Sum.inl PUnit.unit, trivial⟩
  readableRequiredAxes := fun _axis _hreq => ⟨Sum.inl PUnit.unit, trivial⟩
  visibleBoundaryWitnesses := fun _i _j => trivial

/-- R11 / II.AC16: example theorem reading lemma 7.2A on the finite model. -/
theorem siteWitnessClosureCover_uAdequate :
    Site.UAdequateCover siteAdequacyRequirements
      siteWitnessClosureCover.toAATCoverageFamily :=
  Site.witnessClosureCover_uAdequate siteWitnessClosureCover

/-- R11 / II.AC16: seed-driven witness-closure cover package for the finite model. -/
def siteSeedWitnessClosureCover :
    Site.SeedWitnessClosureCover siteAdequacyRequirements siteOverlap siteBase where
  SeedIndex := PUnit
  seedPatch := fun _ => siteContext
  seedInclusion := fun _ => rfl
  localFiniteRequiredWitnesses := site_requiredWitnessSubtype_finite
  RequiredWitnessSupport := fun _ => siteContext
  requiredWitnessSupport_inclusion := fun _ => rfl
  requiredWitnessSupport_visible := fun _ => trivial
  seedSupportCovered := fun _atom _hreq => ⟨PUnit.unit, trivial⟩
  seedAxesReadable := fun _axis _hreq => ⟨PUnit.unit, trivial⟩
  boundary_seed_seed := fun _i _j => trivial
  boundary_seed_witness := fun _i _witness => trivial
  boundary_seed_overlap := fun _i _pair => trivial
  boundary_witness_seed := fun _witness _i => trivial
  boundary_witness_witness := fun _witness1 _witness2 => trivial
  boundary_witness_overlap := fun _witness _pair => trivial
  boundary_overlap_seed := fun _pair _i => trivial
  boundary_overlap_witness := fun _pair _witness => trivial
  boundary_overlap_overlap := fun _pair1 _pair2 => trivial

/--
R11 / II.AC16: the seed-driven finite witness closure yields an admissible AAT
coverage family.
-/
theorem siteSeedWitnessClosureCover_admissible :
    Site.AdmissibleCover siteCoverageRequirements siteOverlap
      siteSeedWitnessClosureCover.toAATCoverageFamily.toCoverageFamily :=
  Site.SeedWitnessClosureCover.toAATCoverageFamily_admissible siteSeedWitnessClosureCover

/-- R11 / II.AC16: example theorem reading the seed-driven lemma 7.2A variant. -/
theorem siteSeedWitnessClosureCover_uAdequate :
    Site.UAdequateCover siteAdequacyRequirements
      siteSeedWitnessClosureCover.toAATCoverageFamily :=
  Site.SeedWitnessClosureCover.uAdequate siteSeedWitnessClosureCover

/-- R11 / II.AC16: small coefficient presheaf on the finite site. -/
def siteCoefficient : Site.AATPresheaf site where
  obj _ := PUnit
  map _ x := x
  map_id _ := rfl
  map_comp _ _ := rfl

/-- R11 / II.AC16: selected finite nerve simplices for the singleton cover. -/
def siteNerveSimplex : Nat -> Type
  | 0 => PUnit
  | _ + 1 => Empty

/-- R11 / II.AC16: selected finite poset regime for the finite site. -/
def finitePosetRegime : Site.FinitePosetAATSiteRegime site where
  ContextIndex := SiteContextIndex
  finiteContextIndex := siteContextIndex_finite
  context := siteContextOf
  contextLe := fun _ _ => True
  contextLe_refl := fun _ => trivial
  contextLe_trans := fun _hij _hjk => trivial
  contextLe_antisymm := by
    intro i j _hij _hji
    cases i
    cases j
    rfl
  contextLe_sound := fun h => siteContextLe_sound h
  contextMeet := siteContextMeet
  contextMeet_le_left := fun _ _ => trivial
  contextMeet_le_right := fun _ _ => trivial
  context_le_meet := fun _hik _hjk => trivial
  base := siteBase
  cover := siteSingletonCover
  finiteCoverIndex := by
    change Finite PUnit
    infer_instance
  nerveSimplex := siteNerveSimplex
  finiteNerveSimplex := by
    intro n
    cases n with
    | zero =>
        change Finite PUnit
        infer_instance
    | succ _ =>
        change Finite Empty
        infer_instance
  simplexIndices := by
    intro n simplex _k
    cases n with
    | zero => exact PUnit.unit
    | succ _ => exact Empty.elim simplex
  simplexOverlap := by
    intro n simplex
    cases n with
    | zero => exact siteContext
    | succ _ => exact Empty.elim simplex
  simplexOverlap_le_patch := by
    intro n simplex _k
    cases n with
    | zero => rfl
    | succ _ => exact Empty.elim simplex
  adequacyRequirements := siteAdequacyRequirements
  coverAdequate := siteSingletonCover_uAdequate
  coefficient := siteCoefficient

/-- R11 / II.AC16: example theorem for the selected finite context poset. -/
theorem finitePosetRegime_context_finite :
    Finite finitePosetRegime.ContextIndex :=
  finitePosetRegime.context_index_finite

/-- R11 / II.AC16: example theorem for the selected singleton meet. -/
theorem finitePosetRegime_context_meet_left (i j : finitePosetRegime.ContextIndex) :
    finitePosetRegime.contextLe (finitePosetRegime.contextMeet i j) i :=
  finitePosetRegime.contextMeet_le_left i j

/-- R11 / II.AC16: example theorem for the selected singleton meet. -/
theorem finitePosetRegime_context_meet_right (i j : finitePosetRegime.ContextIndex) :
    finitePosetRegime.contextLe (finitePosetRegime.contextMeet i j) j :=
  finitePosetRegime.contextMeet_le_right i j

/-- R11 / II.AC16: example theorem for the selected singleton meet universal property. -/
theorem finitePosetRegime_context_le_meet {i j k : finitePosetRegime.ContextIndex}
    (hik : finitePosetRegime.contextLe k i) (hjk : finitePosetRegime.contextLe k j) :
    finitePosetRegime.contextLe k (finitePosetRegime.contextMeet i j) :=
  finitePosetRegime.context_le_meet hik hjk

/-- R11 / II.AC16: example theorem for the selected finite context poset antisymmetry. -/
theorem finitePosetRegime_context_antisymm {i j : finitePosetRegime.ContextIndex}
    (hij : finitePosetRegime.contextLe i j) (hji : finitePosetRegime.contextLe j i) :
    i = j :=
  finitePosetRegime.selected_context_le_antisymm hij hji

/-- R11 / II.AC16: the singleton finite site has the top cover. -/
theorem site_top_mem :
    (⊤ : Sieve siteBase) ∈ site.topology siteBase :=
  site.top_mem siteBase

/-- R11 / II.AC16: the singleton cover has nerve dimension zero. -/
theorem finitePosetRegime_nerveDimension_zero :
    Site.FinitePosetNerveDimension finitePosetRegime 0 := by
  intro n hn
  cases n with
  | zero =>
      exact False.elim ((Nat.lt_irrefl 0) hn)
  | succ _ =>
      change IsEmpty Empty
      infer_instance

/-- R11 / II.AC16: selected zero and face-combination data for the singleton finite site. -/
def finitePosetCechAdditiveData :
    Site.FinitePosetCechAdditiveData finitePosetRegime where
  zeroSection := fun _n _simplex => PUnit.unit
  combineFaces := fun _n _simplex _faces => PUnit.unit
  combineFaces_zero := fun _n _simplex => rfl

/-- R11 / II.AC16: selected face maps for the singleton finite site. -/
def finitePosetCechFaceData :
    Site.FinitePosetCechFaceData finitePosetRegime where
  face := by
    intro n simplex _i
    cases n with
    | zero => exact Empty.elim simplex
    | succ _ => exact Empty.elim simplex
  faceOverlap_le := by
    intro n simplex _i
    cases n with
    | zero => exact Empty.elim simplex
    | succ _ => exact Empty.elim simplex

/--
R11 / II.AC16: Čech complex on the singleton finite site.

The differential is the selected face-restriction combination, and all positive
target degrees are empty because the selected cover has nerve dimension zero.
-/
def finitePosetCechComplex : Site.FinitePosetCechComplex finitePosetRegime where
  additive := finitePosetCechAdditiveData
  faces := finitePosetCechFaceData
  differential := by
    intro n _cochain simplex
    cases n with
    | zero => exact Empty.elim simplex
    | succ _ => exact Empty.elim simplex
  differential_eq_restrictions := by
    intro n _cochain simplex
    cases n with
    | zero => exact Empty.elim simplex
    | succ _ => exact Empty.elim simplex
  differential_zero := by
    intro n
    funext simplex
    cases n with
    | zero => exact Empty.elim simplex
    | succ _ => exact Empty.elim simplex
  differential_comp_zero := by
    intro n _cochain
    funext simplex
    cases n with
    | zero => exact Empty.elim simplex
    | succ _ => exact Empty.elim simplex

/-- R11 / II.AC16: equality quotient relation for the singleton finite cohomology. -/
def finitePosetCechCoboundaryRelation (n : Nat) :
    Site.FinitePosetCechCoboundaryRelation finitePosetCechComplex n where
  related := fun left right => left = right
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun hleft hright => hleft.trans hright
  kills_image := by
    intro cocycle himage
    cases n with
    | zero => exact False.elim himage
    | succ _ =>
        apply Subtype.ext
        funext simplex
        exact Empty.elim simplex

/-- R11 / II.AC16: example theorem for finite summands of the Čech complex. -/
theorem finitePosetRegime_cechComplex_finite (n : Nat) :
    Finite (Site.FinitePosetCechSimplex finitePosetRegime n) :=
  Site.finitePosetCechComplex_finite finitePosetRegime n

/--
R11 / II.AC16: example theorem reading proposition 7.2C on the finite model.

The singleton cover has nerve dimension zero, so every positive degree
vanishes in the finite cover-relative Čech vocabulary.
-/
theorem finitePosetRegime_cech_vanishes_above_dimension {n : Nat} (hn : 0 < n) :
    Site.FinitePosetCechCohomologyVanishes finitePosetCechComplex n
      (finitePosetCechCoboundaryRelation n) :=
  Site.finitePosetCechCohomology_vanishes_above_nerveDimension
    finitePosetCechComplex (finitePosetCechCoboundaryRelation n)
    finitePosetRegime_nerveDimension_zero hn

/-!
## peer-review hardening II-5: two-patch finite site firing example

The singleton site above remains as the small compatibility fixture used by
earlier examples.  The following selected finite regime has two patches, an
explicit overlap context, nonempty degree-one nerve data, a concrete descent
success, a sheafification-gap witness, and a nonzero degree-zero Čech
differential calculation.
-/

/-- peer-review hardening II-5: selected contexts for the two-patch finite site. -/
inductive TwoPatchContextIndex where
  | overlap
  | left
  | right
  | base
  deriving DecidableEq

namespace TwoPatchContextIndex

/-- peer-review hardening II-5: explicit finite enumeration of the selected two-patch contexts. -/
def all : List TwoPatchContextIndex :=
  [overlap, left, right, base]

/-- peer-review hardening II-5: the enumeration covers every selected two-patch context. -/
theorem mem_all (i : TwoPatchContextIndex) : i ∈ all := by
  cases i <;> simp [all]

end TwoPatchContextIndex

instance : Fintype TwoPatchContextIndex where
  elems := {TwoPatchContextIndex.overlap, TwoPatchContextIndex.left,
    TwoPatchContextIndex.right, TwoPatchContextIndex.base}
  complete := by
    intro i
    cases i <;> simp

/--
peer-review hardening II-5: selected finite poset order.

`overlap` refines both patches, each patch refines `base`, and `base` is the
selected top context.
-/
def twoPatchContextIndexLe : TwoPatchContextIndex -> TwoPatchContextIndex -> Prop
  | TwoPatchContextIndex.overlap, _ => True
  | TwoPatchContextIndex.left, TwoPatchContextIndex.left => True
  | TwoPatchContextIndex.left, TwoPatchContextIndex.base => True
  | TwoPatchContextIndex.right, TwoPatchContextIndex.right => True
  | TwoPatchContextIndex.right, TwoPatchContextIndex.base => True
  | TwoPatchContextIndex.base, TwoPatchContextIndex.base => True
  | _, _ => False

/-- peer-review hardening II-5: reflexivity of the selected two-patch context order. -/
theorem twoPatchContextIndexLe_refl (i : TwoPatchContextIndex) :
    twoPatchContextIndexLe i i := by
  cases i <;> simp [twoPatchContextIndexLe]

/-- peer-review hardening II-5: transitivity of the selected two-patch context order. -/
theorem twoPatchContextIndexLe_trans {i j k : TwoPatchContextIndex}
    (hij : twoPatchContextIndexLe i j) (hjk : twoPatchContextIndexLe j k) :
    twoPatchContextIndexLe i k := by
  cases i <;> cases j <;> cases k <;>
    simp [twoPatchContextIndexLe] at hij hjk ⊢

/-- peer-review hardening II-5: antisymmetry of the selected two-patch context order. -/
theorem twoPatchContextIndexLe_antisymm {i j : TwoPatchContextIndex}
    (hij : twoPatchContextIndexLe i j) (hji : twoPatchContextIndexLe j i) :
    i = j := by
  cases i <;> cases j <;> simp [twoPatchContextIndexLe] at hij hji ⊢

/-- peer-review hardening II-5: selected meet in the two-patch finite context poset. -/
def twoPatchContextMeet : TwoPatchContextIndex -> TwoPatchContextIndex ->
    TwoPatchContextIndex
  | TwoPatchContextIndex.base, j => j
  | i, TwoPatchContextIndex.base => i
  | TwoPatchContextIndex.left, TwoPatchContextIndex.left => TwoPatchContextIndex.left
  | TwoPatchContextIndex.right, TwoPatchContextIndex.right => TwoPatchContextIndex.right
  | _, _ => TwoPatchContextIndex.overlap

/-- peer-review hardening II-5: the selected meet maps to its left factor. -/
theorem twoPatchContextMeet_le_left (i j : TwoPatchContextIndex) :
    twoPatchContextIndexLe (twoPatchContextMeet i j) i := by
  cases i <;> cases j <;> simp [twoPatchContextMeet, twoPatchContextIndexLe]

/-- peer-review hardening II-5: the selected meet maps to its right factor. -/
theorem twoPatchContextMeet_le_right (i j : TwoPatchContextIndex) :
    twoPatchContextIndexLe (twoPatchContextMeet i j) j := by
  cases i <;> cases j <;> simp [twoPatchContextMeet, twoPatchContextIndexLe]

/-- peer-review hardening II-5: universal property of the selected two-patch meet. -/
theorem twoPatchContext_le_meet {i j k : TwoPatchContextIndex}
    (hik : twoPatchContextIndexLe k i) (hjk : twoPatchContextIndexLe k j) :
    twoPatchContextIndexLe k (twoPatchContextMeet i j) := by
  cases i <;> cases j <;> cases k <;>
    simp [twoPatchContextMeet, twoPatchContextIndexLe] at hik hjk ⊢

/-- peer-review hardening II-5: concrete context over the finite object indexed by the two-patch poset. -/
def twoPatchContext (i : TwoPatchContextIndex) : Site.ArchCtx object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => True
    supportReads_objectFamily := fun _h => trivial
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := TwoPatchContextIndex
  extension := i

/-- peer-review hardening II-5: readable morphism between selected two-patch contexts. -/
def twoPatchContextMorphism (i j : TwoPatchContextIndex) :
    Site.ContextMorphism (twoPatchContext i) (twoPatchContext j) where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- peer-review hardening II-5: selected two-patch morphisms satisfy the concrete restriction role. -/
theorem twoPatchContextMorphism_isRestriction (i j : TwoPatchContextIndex) :
    (twoPatchContextMorphism i j).IsRestriction :=
  ⟨fun h => h, fun h => h, fun h => h,
    fun h => (twoPatchContext j).supportReads_objectFamily h⟩

/-- peer-review hardening II-5: canonical restriction preorder used by the two-patch selected site. -/
noncomputable abbrev twoPatchContextPreorder : Site.ContextPreorderCategory object :=
  Site.contextMorphismPreorderCategory object

/-- peer-review hardening II-5: selected order maps into the canonical restriction preorder. -/
theorem twoPatchContextLe_sound {i j : TwoPatchContextIndex}
    (_h : twoPatchContextIndexLe i j) :
    twoPatchContextPreorder.le (twoPatchContext i) (twoPatchContext j) :=
  ⟨twoPatchContextMorphism i j, twoPatchContextMorphism_isRestriction i j⟩

private theorem twoPatchContext_le_any (i j : TwoPatchContextIndex) :
    twoPatchContextPreorder.le (twoPatchContext i) (twoPatchContext j) :=
  ⟨twoPatchContextMorphism i j, twoPatchContextMorphism_isRestriction i j⟩

/-- peer-review hardening II-5: overlap package inherited from the canonical product meet. -/
noncomputable def twoPatchOverlap :
    Site.ContextOverlapPullback twoPatchContextPreorder :=
  Site.meetOverlapPullback twoPatchContextPreorder Site.productContextFiniteMeet

/-- peer-review hardening II-5: selected cover index with two patches. -/
inductive TwoPatchCoverIndex where
  | left
  | right
  deriving DecidableEq

namespace TwoPatchCoverIndex

/-- peer-review hardening II-5: explicit finite enumeration of the selected two-patch cover. -/
def all : List TwoPatchCoverIndex :=
  [left, right]

/-- peer-review hardening II-5: the enumeration covers both selected patches. -/
theorem mem_all (i : TwoPatchCoverIndex) : i ∈ all := by
  cases i <;> simp [all]

end TwoPatchCoverIndex

instance : Fintype TwoPatchCoverIndex where
  elems := {TwoPatchCoverIndex.left, TwoPatchCoverIndex.right}
  complete := by
    intro i
    cases i <;> simp

/-- peer-review hardening II-5: map cover indices to their selected context indices. -/
def twoPatchCoverContextIndex : TwoPatchCoverIndex -> TwoPatchContextIndex
  | TwoPatchCoverIndex.left => TwoPatchContextIndex.left
  | TwoPatchCoverIndex.right => TwoPatchContextIndex.right

/-- peer-review hardening II-5: selected context carried by each cover patch. -/
def twoPatchCoverPatch (i : TwoPatchCoverIndex) : Site.ArchCtx object :=
  twoPatchContext (twoPatchCoverContextIndex i)

/-- peer-review hardening II-5: the left patch visibly reads `componentA`. -/
def twoPatchSupportVisibleOn (W : Site.ArchCtx object) (atom : carrier.Atom) : Prop :=
  (W = twoPatchContext TwoPatchContextIndex.left ∧
      atom = FiniteAtom.componentA) ∨
    (W = twoPatchContext TwoPatchContextIndex.right ∧
      atom = FiniteAtom.componentB) ∨
      (W = twoPatchContext TwoPatchContextIndex.overlap ∧
        atom = FiniteAtom.dependsAB)

/-- peer-review hardening II-5: selected requirements for the two-patch cover. -/
def twoPatchCoverageRequirements :
    Site.CoverageRequirements object lawUniverse signature where
  selectedReading := lawUniverse.selectedReading
  requiredSupport := fun _ atom =>
    atom = FiniteAtom.componentA ∨ atom = FiniteAtom.componentB
  requiredWitness := fun _ _ => True
  requiredAxis := fun _ _ => True
  supportVisibleOn := twoPatchSupportVisibleOn
  witnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = twoPatchContext TwoPatchContextIndex.left ∨
      W = twoPatchContext TwoPatchContextIndex.right
  boundaryVisibleOn := fun _ _ => True

/-- peer-review hardening II-5: the two-patch AAT site over the finite model. -/
noncomputable def twoPatchSite : Site.AATSite object where
  contextPreorder := twoPatchContextPreorder
  lawUniverse := lawUniverse
  signature := signature
  requirements := twoPatchCoverageRequirements
  overlap := twoPatchOverlap

/-- peer-review hardening II-5: base object of the two-patch finite site. -/
def twoPatchBase : twoPatchSite.category :=
  Site.ContextCategoryObject.of twoPatchContextPreorder
    (twoPatchContext TwoPatchContextIndex.base)

/-- peer-review hardening II-5: admissible cover with two selected patches. -/
noncomputable def twoPatchCover :
    Site.AATCoverageFamily twoPatchCoverageRequirements twoPatchOverlap
      twoPatchBase where
  Index := TwoPatchCoverIndex
  patch := twoPatchCoverPatch
  inclusion := by
    intro i
    cases i
    · exact twoPatchContext_le_any TwoPatchContextIndex.left TwoPatchContextIndex.base
    · exact twoPatchContext_le_any TwoPatchContextIndex.right TwoPatchContextIndex.base
  admissible := {
    atomSupportCoverage := by
      intro atom hreq
      rcases hreq with rfl | rfl
      · exact ⟨TwoPatchCoverIndex.left, by
          simp [twoPatchCoverPatch, twoPatchCoverContextIndex,
            twoPatchCoverageRequirements, twoPatchSupportVisibleOn]⟩
      · exact ⟨TwoPatchCoverIndex.right, by
          simp [twoPatchCoverPatch, twoPatchCoverContextIndex,
            twoPatchCoverageRequirements, twoPatchSupportVisibleOn]⟩
    lawWitnessCoverage := by
      intro _witness _hreq
      exact Or.inl ⟨TwoPatchCoverIndex.left, trivial⟩
    signatureAxisCoverage := by
      intro _axis _hreq
      exact ⟨TwoPatchCoverIndex.left, by
        simp [twoPatchCoverPatch, twoPatchCoverContextIndex,
          twoPatchCoverageRequirements]⟩
    boundaryCoverage := fun _i _j => trivial
    nonGeneration := by
      intro _i _support _atom _h
      exact trivial
  }

/-- peer-review hardening II-5: the generated two-patch cover is a topology cover. -/
theorem twoPatchCover_topologyCover :
    Sieve.generate twoPatchCover.presieve ∈ twoPatchSite.topology twoPatchBase :=
  Site.AATGrothendieckTopology.generate_mem twoPatchCover

/-- peer-review hardening II-5: selected adequacy requirements for the two-patch site. -/
def twoPatchAdequacyRequirements :
    Site.UAdequacyRequirements twoPatchContextPreorder
      twoPatchCoverageRequirements where
  selectedWitnessIdeal := fun _ _ => True
  witnessIdealPreservedBy := fun _h _hideal => trivial

/-- peer-review hardening II-5: direct `U`-adequacy for the two-patch finite cover. -/
theorem twoPatchCover_uAdequate :
    Site.UAdequateCover twoPatchAdequacyRequirements twoPatchCover where
  topologyCover := twoPatchCover_topologyCover
  requiredSupportCovered := twoPatchCover.admissible.atomSupportCoverage
  requiredWitnessesVisible := twoPatchCover.admissible.lawWitnessCoverage
  requiredAxesReadable := twoPatchCover.admissible.signatureAxisCoverage
  boundaryWitnessesVisible := twoPatchCover.admissible.boundaryCoverage
  restrictionMapsPreserveWitnessIdeals := fun _i _hbase => trivial

/-- peer-review hardening II-5: the selected overlap context maps to the left patch. -/
theorem twoPatch_overlap_le_left :
    twoPatchContextPreorder.le
      (twoPatchContext TwoPatchContextIndex.overlap)
      (twoPatchContext TwoPatchContextIndex.left) :=
  twoPatchContext_le_any TwoPatchContextIndex.overlap TwoPatchContextIndex.left

/-- peer-review hardening II-5: the selected overlap context maps to the right patch. -/
theorem twoPatch_overlap_le_right :
    twoPatchContextPreorder.le
      (twoPatchContext TwoPatchContextIndex.overlap)
      (twoPatchContext TwoPatchContextIndex.right) :=
  twoPatchContext_le_any TwoPatchContextIndex.overlap TwoPatchContextIndex.right

/-- peer-review hardening II-5: the selected overlap visibly reads the boundary atom. -/
theorem twoPatch_overlap_reads_boundary :
    twoPatchSupportVisibleOn
      (twoPatchContext TwoPatchContextIndex.overlap) FiniteAtom.dependsAB := by
  simp [twoPatchSupportVisibleOn]

/-- peer-review hardening II-5: coefficient presheaf with nontrivial Boolean sections. -/
def twoPatchBoolCoefficient : Site.AATPresheaf twoPatchSite where
  obj _ := Bool
  map _ x := x
  map_id _ := rfl
  map_comp _ _ := rfl

/-- peer-review hardening II-5: unit-valued sheaf used for the concrete descent success. -/
def twoPatchUnitPresheaf : Site.AATPresheaf twoPatchSite where
  obj _ := PUnit
  map _ x := x
  map_id _ := rfl
  map_comp _ _ := rfl

/-- peer-review hardening II-5: the unit presheaf satisfies the AAT sheaf condition. -/
theorem twoPatchUnit_isSheaf :
    Site.AATSheafCondition twoPatchSite twoPatchUnitPresheaf := by
  intro _base _cover _hcover family _compatible
  refine ⟨PUnit.unit, ?_, ?_⟩
  · intro _Y f hf
    cases family f hf
    rfl
  · intro y _hy
    cases y
    rfl

/-- peer-review hardening II-5: packaged unit sheaf on the two-patch finite site. -/
def twoPatchUnitSheaf : Site.AATSheaf twoPatchSite where
  carrier := twoPatchUnitPresheaf
  isSheaf := twoPatchUnit_isSheaf

/-- peer-review hardening II-5: the two-patch cover satisfies descent for the unit sheaf. -/
theorem twoPatchUnit_descent :
    Site.AATDescent twoPatchSite twoPatchUnitPresheaf
      (Sieve.generate twoPatchCover.presieve) :=
  Site.AATSheafCondition.descent twoPatchUnit_isSheaf
    (Sieve.generate twoPatchCover.presieve) twoPatchCover_topologyCover

/-- peer-review hardening II-5: canonical comparison from raw Boolean data to the unit sheaf. -/
def twoPatchBoolToUnit :
    twoPatchBoolCoefficient ⟶ twoPatchUnitPresheaf where
  app _ _ := PUnit.unit
  naturality _ _ _ := rfl

/--
peer-review hardening II-5: selected sheafification comparison whose canonical map forgets
the Boolean distinction.
-/
def twoPatchSheafificationComparison :
    Site.AATSheafificationComparison twoPatchSite where
  raw := twoPatchBoolCoefficient
  plus := twoPatchUnitSheaf
  canonical := twoPatchBoolToUnit

/-- peer-review hardening II-5: the selected comparison has a concrete sheafification gap. -/
theorem twoPatchSheafificationGap :
    Site.AATSheafificationGap twoPatchSheafificationComparison := by
  refine ⟨twoPatchBase, ?_⟩
  intro hbij
  have htf : true = false := hbij.1 (by rfl)
  cases htf

/-- peer-review hardening II-5: selected nerve simplices for the two-patch cover. -/
def twoPatchNerveSimplex : Nat -> Type
  | 0 => TwoPatchCoverIndex
  | 1 => PUnit
  | _ + 2 => Empty

/-- peer-review hardening II-5: selected cover indices of the two-patch nerve. -/
def twoPatchSimplexIndices :
    ∀ n : Nat, twoPatchNerveSimplex n -> Fin (n + 1) -> TwoPatchCoverIndex
  | 0, simplex, _ => simplex
  | 1, _simplex, k => if k.val = 0 then TwoPatchCoverIndex.left else TwoPatchCoverIndex.right
  | _ + 2, simplex, _ => Empty.elim simplex

/-- peer-review hardening II-5: selected overlap context of each two-patch nerve simplex. -/
def twoPatchSimplexOverlap :
    ∀ n : Nat, twoPatchNerveSimplex n -> Site.ArchCtx object
  | 0, simplex => twoPatchCoverPatch simplex
  | 1, _simplex => twoPatchContext TwoPatchContextIndex.overlap
  | _ + 2, simplex => Empty.elim simplex

/-- peer-review hardening II-5: finite-poset regime for the non-singleton two-patch site. -/
noncomputable def twoPatchFinitePosetRegime :
    Site.FinitePosetAATSiteRegime twoPatchSite where
  ContextIndex := TwoPatchContextIndex
  finiteContextIndex := inferInstance
  context := twoPatchContext
  contextLe := twoPatchContextIndexLe
  contextLe_refl := twoPatchContextIndexLe_refl
  contextLe_trans := fun hij hjk => twoPatchContextIndexLe_trans hij hjk
  contextLe_antisymm := fun hij hji => twoPatchContextIndexLe_antisymm hij hji
  contextLe_sound := fun h => twoPatchContextLe_sound h
  contextMeet := twoPatchContextMeet
  contextMeet_le_left := twoPatchContextMeet_le_left
  contextMeet_le_right := twoPatchContextMeet_le_right
  context_le_meet := fun hik hjk => twoPatchContext_le_meet hik hjk
  base := twoPatchBase
  cover := twoPatchCover
  finiteCoverIndex := by
    change Finite TwoPatchCoverIndex
    infer_instance
  nerveSimplex := twoPatchNerveSimplex
  finiteNerveSimplex := by
    intro n
    cases n with
    | zero =>
        change Finite TwoPatchCoverIndex
        infer_instance
    | succ n =>
        cases n with
        | zero =>
            change Finite PUnit
            infer_instance
        | succ _ =>
            change Finite Empty
            infer_instance
  simplexIndices := twoPatchSimplexIndices
  simplexOverlap := twoPatchSimplexOverlap
  simplexOverlap_le_patch := by
    intro n simplex k
    cases n with
    | zero =>
        cases simplex
        · exact twoPatchContext_le_any TwoPatchContextIndex.left TwoPatchContextIndex.left
        · exact twoPatchContext_le_any TwoPatchContextIndex.right TwoPatchContextIndex.right
    | succ n =>
        cases n with
        | zero =>
            change twoPatchContextPreorder.le
              (twoPatchContext TwoPatchContextIndex.overlap)
              (twoPatchCoverPatch (twoPatchSimplexIndices 1 simplex k))
            unfold twoPatchCoverPatch
            exact ⟨twoPatchContextMorphism _ _, twoPatchContextMorphism_isRestriction _ _⟩
        | succ _ =>
            exact Empty.elim simplex
  adequacyRequirements := twoPatchAdequacyRequirements
  coverAdequate := twoPatchCover_uAdequate
  coefficient := twoPatchBoolCoefficient

/-- peer-review hardening II-5: the two-patch selected context poset has four finite contexts. -/
theorem twoPatchFinitePosetRegime_context_finite :
    Finite twoPatchFinitePosetRegime.ContextIndex :=
  twoPatchFinitePosetRegime.context_index_finite

/-- peer-review hardening II-5: the two-patch selected cover has two finite patches. -/
theorem twoPatchFinitePosetRegime_cover_finite :
    Finite twoPatchFinitePosetRegime.cover.Index :=
  twoPatchFinitePosetRegime.cover_index_finite

/-- peer-review hardening II-5: the two-patch nerve has dimension one. -/
theorem twoPatchFinitePosetRegime_nerveDimension_one :
    Site.FinitePosetNerveDimension twoPatchFinitePosetRegime 1 := by
  intro n hn
  cases n with
  | zero =>
      exact False.elim ((Nat.not_succ_le_zero 1) hn)
  | succ n =>
      cases n with
      | zero =>
          exact False.elim ((Nat.lt_irrefl 1) hn)
      | succ _ =>
          change IsEmpty Empty
          infer_instance

/-- peer-review hardening II-5: selected additive data for the Boolean two-patch Čech surface. -/
def twoPatchCechAdditiveData :
    Site.FinitePosetCechAdditiveData twoPatchFinitePosetRegime where
  zeroSection := by
    intro _n _simplex
    change Bool
    exact false
  combineFaces := by
    intro n _simplex faces
    cases n with
    | zero =>
        change Bool
        exact (show Bool from faces ⟨0, by decide⟩) !=
          (show Bool from faces ⟨1, by decide⟩)
    | succ _ =>
        change Bool
        exact false
  combineFaces_zero := by
    intro n simplex
    cases n with
    | zero =>
        cases simplex
        rfl
    | succ n =>
        cases n with
        | zero => exact Empty.elim simplex
        | succ _ =>
            exact Empty.elim simplex

/-- peer-review hardening II-5: selected face maps for the two-patch nerve. -/
def twoPatchCechFaceData :
    Site.FinitePosetCechFaceData twoPatchFinitePosetRegime where
  face := by
    intro n simplex i
    cases n with
    | zero =>
        exact if i.val = 0 then TwoPatchCoverIndex.left else TwoPatchCoverIndex.right
    | succ n =>
        cases n with
        | zero => exact Empty.elim simplex
        | succ _ => exact Empty.elim simplex
  faceOverlap_le := by
    intro n simplex i
    cases n with
    | zero =>
        change twoPatchContextPreorder.le
          (twoPatchContext TwoPatchContextIndex.overlap)
          (twoPatchSimplexOverlap 0
            (if i.val = 0 then TwoPatchCoverIndex.left else TwoPatchCoverIndex.right))
        exact ⟨twoPatchContextMorphism _ _, twoPatchContextMorphism_isRestriction _ _⟩
    | succ n =>
        cases n with
        | zero => exact Empty.elim simplex
        | succ _ => exact Empty.elim simplex

/-- peer-review hardening II-5: degree-zero Boolean Čech differential for the two-patch cover. -/
def twoPatchCechDifferential :
    ∀ n : Nat,
      Site.FinitePosetCechCochain twoPatchFinitePosetRegime n ->
        Site.FinitePosetCechCochain twoPatchFinitePosetRegime (n + 1)
  | 0, cochain, _simplex =>
      (show Bool from cochain TwoPatchCoverIndex.left) !=
        (show Bool from cochain TwoPatchCoverIndex.right)
  | _ + 1, _cochain, simplex => Empty.elim simplex

/-- peer-review hardening II-5: selected Boolean Čech complex on the two-patch finite site. -/
def twoPatchCechComplex :
    Site.FinitePosetCechComplex twoPatchFinitePosetRegime where
  additive := twoPatchCechAdditiveData
  faces := twoPatchCechFaceData
  differential := twoPatchCechDifferential
  differential_eq_restrictions := by
    intro n cochain simplex
    cases n with
    | zero =>
        cases simplex
        change
          ((show Bool from cochain TwoPatchCoverIndex.left) !=
              (show Bool from cochain TwoPatchCoverIndex.right)) =
            ((show Bool from cochain TwoPatchCoverIndex.left) !=
              (show Bool from cochain TwoPatchCoverIndex.right))
        rfl
    | succ n =>
        cases n with
        | zero => exact Empty.elim simplex
        | succ _ => exact Empty.elim simplex
  differential_zero := by
    intro n
    funext simplex
    cases n with
    | zero =>
        cases simplex
        rfl
    | succ n =>
        cases n with
        | zero => exact Empty.elim simplex
        | succ _ => exact Empty.elim simplex
  differential_comp_zero := by
    intro n _cochain
    funext simplex
    cases n with
    | zero => exact Empty.elim simplex
    | succ _ => exact Empty.elim simplex

/--
peer-review hardening II-5: universal selected image-killing quotient relation for the
two-patch cohomology surface.

The nonzero calculation below is the degree-zero differential value.  This
relation is the selected quotient surface required by the Type-valued finite
Čech API: it kills all differential images rather than claiming an equality
quotient computation.
-/
def twoPatchCechCoboundaryRelation (n : Nat) :
    Site.FinitePosetCechCoboundaryRelation twoPatchCechComplex n where
  related := fun _left _right => True
  refl := fun _ => trivial
  symm := fun _h => trivial
  trans := fun _hleft _hright => trivial
  kills_image := fun _himage => trivial

/-- peer-review hardening II-5: positive degrees above one vanish for the selected two-patch nerve. -/
theorem twoPatchFinitePosetRegime_cech_vanishes_above_one {n : Nat} (hn : 1 < n) :
    Site.FinitePosetCechCohomologyVanishes twoPatchCechComplex n
      (twoPatchCechCoboundaryRelation n) :=
  Site.finitePosetCechCohomology_vanishes_above_nerveDimension
    twoPatchCechComplex (twoPatchCechCoboundaryRelation n)
    twoPatchFinitePosetRegime_nerveDimension_one hn

/-- peer-review hardening II-5: degree-zero cochain separating the two selected patches. -/
def twoPatchSeparatedCochain :
    Site.FinitePosetCechCochain twoPatchFinitePosetRegime 0
  | TwoPatchCoverIndex.left => by
      change Bool
      exact true
  | TwoPatchCoverIndex.right => by
      change Bool
      exact false

/-- peer-review hardening II-5: the separated cochain has nonzero degree-one Čech differential. -/
theorem twoPatchSeparatedCochain_differential_nonzero :
    twoPatchCechComplex.differential 0 twoPatchSeparatedCochain PUnit.unit = true :=
  rfl

end FiniteModel

end AAT.AG
