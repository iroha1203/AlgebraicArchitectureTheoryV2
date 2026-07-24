import Formal.AG.Atom.AATCore
import Formal.AG.Atom.LawfulnessZero
import Formal.AG.Atom.ThreeReading
import Formal.AG.Site.FinitePoset
import Formal.AG.Site.MinimalContextProfile
import Formal.AG.Site.SheafCategory
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic

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

/-- The selected Atom vocabulary is finite. -/
instance : Fintype FiniteAtom :=
  Fintype.ofList all mem_all

end FiniteAtom

/-- R10: source modes for the primary finite extraction doctrine. -/
inductive ExtractionSource where
  | all
  | withoutComponentC
  deriving DecidableEq

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

/-- R10: the selected source-to-Atom extraction doctrine for the finite model. -/
def extractionDoctrine : ExtractionDoctrine carrier where
  Source := ExtractionSource
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ source atom =>
    source = ExtractionSource.all ∨ atom ≠ FiniteAtom.componentC
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- R10: the finite family containing all selected atoms. -/
def allFamily : AtomFamily carrier :=
  extractionDoctrine.atomize ExtractionSource.withoutComponentC

/-- Every atom admitted by the selected vocabulary belongs to the extracted family. -/
theorem allFamily_mem (atom : carrier.Atom)
    (hselected : atom ≠ FiniteAtom.componentC) : allFamily.mem atom := by
  apply (extractionDoctrine.atomize_mem_iff
    ExtractionSource.withoutComponentC atom).mpr
  apply (extractionDoctrine.extracts_iff
    ExtractionSource.withoutComponentC atom).mpr
  exact ⟨trivial, Or.inr hselected, trivial, trivial⟩

/-- The primary doctrine extracts a concrete atom from its selective source. -/
theorem componentA_extracted_withoutComponentC :
    extractionDoctrine.extracts ExtractionSource.withoutComponentC
      FiniteAtom.componentA := by
  apply (extractionDoctrine.extracts_iff
    ExtractionSource.withoutComponentC FiniteAtom.componentA).mpr
  exact ⟨trivial, Or.inr (by simp), trivial, trivial⟩

/-- The primary doctrine rejects a concrete atom from its selective source. -/
theorem componentC_not_extracted_withoutComponentC :
    ¬ extractionDoctrine.extracts ExtractionSource.withoutComponentC
      FiniteAtom.componentC := by
  intro h
  have hread := (extractionDoctrine.extracts_iff
    ExtractionSource.withoutComponentC FiniteAtom.componentC).mp h
  exact hread.2.1.resolve_left (by decide) rfl

/-- The generated family is a positive `Atomizes` instance for the primary doctrine. -/
theorem allFamily_atomizes :
    extractionDoctrine.Atomizes ExtractionSource.withoutComponentC allFamily :=
  extractionDoctrine.atomize_holds ExtractionSource.withoutComponentC

/-- An empty family used to witness failure of the primary atomization predicate. -/
def emptyFamily : AtomFamily carrier where
  mem _ := False

/-- The empty family is a negative `Atomizes` instance for the primary doctrine. -/
theorem emptyFamily_not_atomizes :
    ¬ extractionDoctrine.Atomizes ExtractionSource.withoutComponentC
      emptyFamily := by
  intro h
  have hextracted : extractionDoctrine.extracts ExtractionSource.withoutComponentC
      FiniteAtom.componentA := componentA_extracted_withoutComponentC
  exact (h FiniteAtom.componentA).mpr hextracted

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

/-- R10: composition on every finite family, retaining supported selected relations. -/
def compositionReading : CompositionReading carrier where
  compose F _ := {
    family := F
    relation := fun a b =>
      (cycleRelation a b ∨ substitutionRelation a b) ∧ F.mem a ∧ F.mem b
    identification := fun a b =>
      a = FiniteAtom.componentA ∧ b = FiniteAtom.componentB ∧ F.mem a ∧ F.mem b
  }
  family_eq := by intros; rfl
  family_supported := by
    intro F _
    constructor
    · intro a b h
      exact ⟨h.2.1, h.2.2⟩
    · intro a b h
      exact ⟨h.2.2.1, h.2.2.2⟩

/-- R10: finite configuration containing the selected example atoms. -/
def configuration : AtomConfiguration carrier :=
  compositionReading.compose allFamily allFamily_listFinite

/-- peer-review hardening I-1/I-3: acyclic finite configuration over the same nonempty atom family. -/
def acyclicConfiguration : AtomConfiguration carrier where
  family := allFamily
  relation _ _ := False
  identification _ _ := False

/-- R10: the finite configuration relation is supported by the finite family. -/
theorem configuration_familySupported :
    AtomConfiguration.FamilySupported configuration := by
  exact compositionReading.family_supported allFamily allFamily_listFinite

/-- R10: build a finite architecture object over any selected finite configuration. -/
def objectOfConfiguration (C : AtomConfiguration carrier) :
    ArchitectureObject carrier where
  configuration := C
  StructureMaps := PUnit
  SelectedQuantities := PUnit
  structureMaps := PUnit.unit
  selectedQuantities := PUnit.unit

/-- R10: object formation over every selected finite configuration. -/
def objectReading : ObjectReading carrier where
  object := objectOfConfiguration
  configuration_eq := by intros; rfl

/-- R10: finite architecture object over the selected configuration. -/
def object : ArchitectureObject carrier :=
  objectReading.object configuration

/-- peer-review hardening I-1: acyclic finite architecture object used for concrete three-reading firing. -/
def acyclicObject : ArchitectureObject carrier where
  configuration := acyclicConfiguration
  StructureMaps := PUnit
  SelectedQuantities := PUnit
  structureMaps := PUnit.unit
  selectedQuantities := PUnit.unit

/-- The concrete three-edge dependency cycle detected by the finite fixture. -/
def hasDependencyCycle (A : ArchitectureObject carrier) : Prop :=
  A.configuration.relation FiniteAtom.dependsAB FiniteAtom.dependsBC ∧
    A.configuration.relation FiniteAtom.dependsBC FiniteAtom.dependsCA ∧
      A.configuration.relation FiniteAtom.dependsCA FiniteAtom.dependsAB

/-- The concrete substitution conflict detected by the finite fixture. -/
def hasSubstitutionConflict (A : ArchitectureObject carrier) : Prop :=
  A.configuration.relation FiniteAtom.contractImpl FiniteAtom.contractBase ∧
    A.configuration.relation FiniteAtom.substitutesImplBase FiniteAtom.contractBase

/-- R10: singleton invariant family used by the finite core package. -/
def invariantFamily : InvariantFamily carrier where
  Index := PUnit
  invariant _ := Invariant.predicate { holds := fun _ => True }

/-- R10: finite architecture signature with a singleton selected axis. -/
def signature : ArchitectureSignature carrier where
  Axis := PUnit
  Coordinate _ := Nat
  selected _ := True
  coordinate _ _ := 0

/-- R10: the concrete signed query pattern detecting the selected 3-cycle. -/
def cycleQueryDatum : FiniteCircuitDatum carrier where
  queries := [
    (.relationPresent FiniteAtom.dependsAB FiniteAtom.dependsBC, true),
    (.relationPresent FiniteAtom.dependsBC FiniteAtom.dependsCA, true),
    (.relationPresent FiniteAtom.dependsCA FiniteAtom.dependsAB, true)]

/-- A concrete context used to read the finite equation residual. -/
def equationProbeContext : Site.ArchCtx object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom => atom ≠ FiniteAtom.componentC
    supportReads_objectFamily := fun hselected => allFamily_mem _ hselected
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- The NoCycle equation residual: lawful objects read `0`, cyclic objects read `1`. -/
noncomputable def noCycleResidual (A : ArchitectureObject carrier) : Int := by
  classical
  exact if hasDependencyCycle A then 1 else 0

/--
The finite core equation system over any selected readable context preorder.

Its symbolic witness coordinate is `2 : Int`; the object-dependent residual
is `0` or `1`, so the later generated ideal `(2)` can distinguish the cyclic
fixture in the quotient without storing a membership or quotient certificate.
-/
noncomputable def equationSystem (C : Site.ContextPreorderCategory object) :
    ArchitecturalEquationSystem C where
  Index := PUnit
  role _ := EquationRole.required
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ _ _ => 2
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ A _ _ => noCycleResidual A
  equationResidual_restrict := by intros; rfl

/-- Residual vanishing is exactly absence of the selected dependency cycle. -/
theorem equationHolds_iff_noCycle
    (C : Site.ContextPreorderCategory object) (A : ArchitectureObject carrier) :
    (equationSystem C).EquationHolds PUnit.unit A ↔ ¬ hasDependencyCycle A := by
  constructor
  · intro h hcycle
    have hzero := h (Site.ContextCategoryObject.of C equationProbeContext)
      FiniteAtom.componentA
    simp [equationSystem, noCycleResidual, hcycle] at hzero
  · intro h W atom
    simp [equationSystem, noCycleResidual, hasDependencyCycle] at h ⊢
    exact h

/-- Equation-indexed finite detector reading used by every finite-core context choice. -/
noncomputable def equationCircuitReading
    (C : Site.ContextPreorderCategory object) :
    EquationCircuitReading (equationSystem C) where
  code _ := .exact cycleQueryDatum

/--
The finite NoCycle detector is sound because an accepted matching datum
supplies all three relations that contradict residual vanishing.
-/
theorem equationCircuitReading_sound
    (C : Site.ContextPreorderCategory object) :
    (equationCircuitReading C).Sound := by
  intro index A Q hmatches haccepts
  cases index
  have hdatum : cycleQueryDatum = Q :=
    (CircuitDetectorCode.eval_exact_eq_true_iff cycleQueryDatum Q).mp haccepts
  subst Q
  have hab :
      A.configuration.relation FiniteAtom.dependsAB FiniteAtom.dependsBC :=
    ((hmatches
      (.relationPresent FiniteAtom.dependsAB FiniteAtom.dependsBC) true
      (by simp [cycleQueryDatum])).mpr rfl).2.2
  have hbc :
      A.configuration.relation FiniteAtom.dependsBC FiniteAtom.dependsCA :=
    ((hmatches
      (.relationPresent FiniteAtom.dependsBC FiniteAtom.dependsCA) true
      (by simp [cycleQueryDatum])).mpr rfl).2.2
  have hca :
      A.configuration.relation FiniteAtom.dependsCA FiniteAtom.dependsAB :=
    ((hmatches
      (.relationPresent FiniteAtom.dependsCA FiniteAtom.dependsAB) true
      (by simp [cycleQueryDatum])).mpr rfl).2.2
  intro hequation
  exact (equationHolds_iff_noCycle C A).mp hequation ⟨hab, hbc, hca⟩

/-- Context, equation, and circuit reading used by the generated finite core. -/
noncomputable def equationReading (C : Site.ContextPreorderCategory object) :
    EquationReading object where
  contextPreorder := C
  equationSystem := equationSystem C
  circuits := equationCircuitReading C
  circuitSound := equationCircuitReading_sound C

/-- R10: all actual configuration homomorphisms form the operation reading. -/
def operationReading : OperationReading carrier where
  Op A B := ConfigurationHom A.configuration B.configuration
  configurationMap op := op

/-- R10: admissible reading specialized to a selected generated-object context preorder. -/
noncomputable def coreReadingFor (C : Site.ContextPreorderCategory object) :
    CoreReading carrier where
  doctrine := extractionDoctrine
  source := ExtractionSource.withoutComponentC
  family_listFinite := by
    refine ⟨FiniteAtom.all, ?_⟩
    intro atom _
    exact FiniteAtom.mem_all atom
  composition := compositionReading
  objectReading := objectReading
  equationReading := equationReading C
  invariantReading := invariantFamily
  signatureReading := signature
  operationReading := operationReading

/-- R10: the canonical finite core uses the full readable-context preorder. -/
noncomputable def coreReading : CoreReading carrier :=
  coreReadingFor (Site.contextMorphismPreorderCategory object)

/-- R10: Atom A0-A8 system for the finite model. -/
theorem axiomSystem : AtomAxiomSystem carrier where
  primitiveExistence := ⟨FiniteAtom.componentA⟩
  predicateStability := by
    intro a b
    constructor
    · intro h
      exact h.1
    · intro h
      cases h
      simp [SameCoordinates, carrier]

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

/-- R10 / example 8.4: substitution evidence links implementation to base contract. -/
theorem substitution_impl_base :
    substitutionRelation FiniteAtom.substitutesImplBase FiniteAtom.contractBase :=
  trivial

/-- R10 / example 8.4: implementation contract is related to the base contract. -/
theorem substitution_contract_impl_base :
    substitutionRelation FiniteAtom.contractImpl FiniteAtom.contractBase :=
  trivial

/-- The substitution equation residual: compatible objects read `0`, conflicts read `1`. -/
noncomputable def substitutionResidual (A : ArchitectureObject carrier) : Int := by
  classical
  exact if hasSubstitutionConflict A then 1 else 0

/-- An explicit equation system for the finite substitution-compatibility reading. -/
noncomputable def substitutionEquationSystem
    (C : Site.ContextPreorderCategory object) :
    ArchitecturalEquationSystem C where
  Index := PUnit
  role _ := EquationRole.required
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ _ _ => 3
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ A _ _ => substitutionResidual A
  equationResidual_restrict := by intros; rfl

/-- Substitution-equation fulfillment is exactly absence of the selected conflict. -/
theorem substitutionEquationHolds_iff
    (C : Site.ContextPreorderCategory object) (A : ArchitectureObject carrier) :
    (substitutionEquationSystem C).EquationHolds PUnit.unit A ↔
      ¬ hasSubstitutionConflict A := by
  constructor
  · intro h hconflict
    have hzero := h (Site.ContextCategoryObject.of C equationProbeContext)
      FiniteAtom.componentA
    simp [substitutionEquationSystem, substitutionResidual, hconflict] at hzero
  · intro hconflict W atom
    simp [substitutionEquationSystem, substitutionResidual, hconflict]

/-- The relation-free object fulfills the substitution equation. -/
theorem acyclic_substitutionEquationHolds
    (C : Site.ContextPreorderCategory object) :
    (substitutionEquationSystem C).EquationHolds PUnit.unit acyclicObject :=
  (substitutionEquationHolds_iff C acyclicObject).mpr (fun h => h.1)

/-- The selected implementation/base mismatch violates the substitution equation. -/
theorem object_substitutionEquation_fails
    (C : Site.ContextPreorderCategory object) :
    ¬ (substitutionEquationSystem C).EquationHolds PUnit.unit object := by
  intro hequation
  exact (substitutionEquationHolds_iff C object).mp hequation
    ⟨⟨Or.inr substitution_contract_impl_base,
      allFamily_mem _ (by simp), allFamily_mem _ (by simp)⟩,
      ⟨Or.inr substitution_impl_base, allFamily_mem _ (by simp),
        allFamily_mem _ (by simp)⟩⟩

/-- R10: the selected object visibly carries the 3-cycle witness. -/
def hasCycleWitness (A : ArchitectureObject carrier) : Prop :=
  A.configuration.relation FiniteAtom.dependsAB FiniteAtom.dependsBC ∧
    A.configuration.relation FiniteAtom.dependsBC FiniteAtom.dependsCA ∧
      A.configuration.relation FiniteAtom.dependsCA FiniteAtom.dependsAB

/-- R10: the finite object has the selected 3-cycle witness. -/
theorem object_hasCycleWitness : hasCycleWitness object :=
  ⟨⟨Or.inl cycle_dependsAB_BC, allFamily_mem _ (by simp),
      allFamily_mem _ (by simp)⟩,
    ⟨Or.inl cycle_dependsBC_CA, allFamily_mem _ (by simp),
      allFamily_mem _ (by simp)⟩,
    ⟨Or.inl cycle_dependsCA_AB, allFamily_mem _ (by simp),
      allFamily_mem _ (by simp)⟩⟩

/-- The acyclic object fulfills the selected NoCycle equation. -/
theorem acyclic_noCycleEquationHolds
    (C : Site.ContextPreorderCategory object) :
    (equationSystem C).EquationHolds PUnit.unit acyclicObject :=
  (equationHolds_iff_noCycle C acyclicObject).mpr (fun hcycle => hcycle.1)

/-- The cyclic object violates the selected NoCycle equation. -/
theorem object_noCycleEquation_fails
    (C : Site.ContextPreorderCategory object) :
    ¬ (equationSystem C).EquationHolds PUnit.unit object := by
  intro hequation
  exact (equationHolds_iff_noCycle C object).mp hequation
    (by simpa [hasCycleWitness] using object_hasCycleWitness)

/-- The cyclic object has a semantic obstruction for the NoCycle equation. -/
theorem object_equationSemanticObstruction
    (C : Site.ContextPreorderCategory object) :
    EquationSemanticObstruction (equationSystem C) PUnit.unit object :=
  (EquationSemanticObstruction.iff_not_equationHolds
    (equationSystem C) PUnit.unit object).mpr (object_noCycleEquation_fails C)

/-- The acyclic object has no semantic obstruction for the NoCycle equation. -/
theorem acyclicObject_not_equationSemanticObstruction
    (C : Site.ContextPreorderCategory object) :
    ¬ EquationSemanticObstruction (equationSystem C) PUnit.unit acyclicObject := by
  intro hobstruction
  exact (EquationSemanticObstruction.iff_not_equationHolds
    (equationSystem C) PUnit.unit acyclicObject).mp hobstruction
      (acyclic_noCycleEquationHolds C)

/-- The acyclic object is lawful for all required equations in the finite system. -/
theorem acyclic_equationLawful
    (C : Site.ContextPreorderCategory object) :
    (equationSystem C).EquationLawful acyclicObject := by
  intro index _hrequired
  cases index
  exact acyclic_noCycleEquationHolds C

/-- The cyclic object is not lawful for the required finite equation. -/
theorem object_equationLawful_fails
    (C : Site.ContextPreorderCategory object) :
    ¬ (equationSystem C).EquationLawful object := by
  intro hlawful
  exact object_noCycleEquation_fails C (hlawful PUnit.unit rfl)

/-- Count-valued obstruction reading for the finite NoCycle equation. -/
noncomputable def noCycleEquationOmega (_index : PUnit)
    (A : ArchitectureObject carrier) : Nat := by
  classical
  exact if hasCycleWitness A then 1 else 0

/-- Equation-indexed obstruction valuation for the finite NoCycle example. -/
noncomputable def noCycleEquationValuation
    (C : Site.ContextPreorderCategory object) :
    EquationObstructionValuation (equationSystem C) Nat where
  domain := ObstructionValueDomain.nat
  omega := noCycleEquationOmega

/-- Zero-reflecting aggregation for the singleton required equation family. -/
def singletonRequiredEquationAggregation
    (C : Site.ContextPreorderCategory object) :
    ZeroReflectingAggregation Nat (noCycleEquationValuation C).domain
      (equationSystem C).RequiredIndex where
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

/-- Soundness reads equation fulfillment as zero cycle valuation. -/
theorem noCycleEquationSound
    (C : Site.ContextPreorderCategory object) :
    EquationObstructionSound (noCycleEquationValuation C) PUnit.unit := by
  intro A hequation
  classical
  have hnot : ¬ hasCycleWitness A := by
    simpa [hasCycleWitness, hasDependencyCycle] using
      (equationHolds_iff_noCycle C A).mp hequation
  simp [noCycleEquationValuation, noCycleEquationOmega,
    ObstructionValueDomain.nat, hnot]

/-- Completeness reads equation failure as a positive cycle valuation. -/
theorem noCycleEquationComplete
    (C : Site.ContextPreorderCategory object) :
    EquationObstructionComplete (noCycleEquationValuation C) PUnit.unit := by
  intro A hfailure
  classical
  have hcycle : hasCycleWitness A := by
    exact Classical.byContradiction (fun hnot =>
      hfailure ((equationHolds_iff_noCycle C A).mpr (by
        simpa [hasCycleWitness, hasDependencyCycle] using hnot)))
  simp [noCycleEquationValuation, noCycleEquationOmega,
    ObstructionValueDomain.nat, hcycle]

/-- Theorem 9.3 instantiated on the finite NoCycle equation system. -/
theorem finite_equationLawful_iff_omega_zero
    (C : Site.ContextPreorderCategory object) :
    (equationSystem C).EquationLawful object ↔
      omegaE (noCycleEquationValuation C)
          (singletonRequiredEquationAggregation C) object =
        (noCycleEquationValuation C).domain.zero :=
  equationLawful_iff_omegaE_zero (noCycleEquationValuation C)
    (singletonRequiredEquationAggregation C)
    (fun index => by
      cases index with
      | mk index hrequired =>
          cases index
          exact noCycleEquationSound C)
    (fun index => by
      cases index with
      | mk index hrequired =>
          cases index
          exact noCycleEquationComplete C)
    object

/-- Constant-one valuation used to refute automatic equation soundness. -/
def alwaysOneEquationValuation
    (C : Site.ContextPreorderCategory object) :
    EquationObstructionValuation (equationSystem C) Nat where
  domain := ObstructionValueDomain.nat
  omega _ _ := 1

/-- The constant-one valuation is not sound on the lawful acyclic object. -/
theorem alwaysOneEquationValuation_not_sound
    (C : Site.ContextPreorderCategory object) :
    ¬ EquationObstructionSound (alwaysOneEquationValuation C) PUnit.unit := by
  intro hsound
  have hzero := hsound acyclicObject (acyclic_noCycleEquationHolds C)
  simp [alwaysOneEquationValuation, ObstructionValueDomain.nat] at hzero

/-- Constant-zero valuation used to refute automatic equation completeness. -/
def alwaysZeroEquationValuation
    (C : Site.ContextPreorderCategory object) :
    EquationObstructionValuation (equationSystem C) Nat where
  domain := ObstructionValueDomain.nat
  omega _ _ := 0

/-- The constant-zero valuation is not complete on the cyclic object. -/
theorem alwaysZeroEquationValuation_not_complete
    (C : Site.ContextPreorderCategory object) :
    ¬ EquationObstructionComplete (alwaysZeroEquationValuation C) PUnit.unit := by
  intro hcomplete
  have hpositive := hcomplete object (object_noCycleEquation_fails C)
  simp [alwaysZeroEquationValuation, ObstructionValueDomain.nat] at hpositive

/-- Generate the same finite object with equations on a selected context preorder. -/
noncomputable def corePackageFor (C : Site.ContextPreorderCategory object) :
    AATCorePackage carrier :=
  AATCorePackage.generate axiomSystem (coreReadingFor C)

/-- R10: the finite model generates its Part I core from axioms and reading rules. -/
noncomputable def corePackage : AATCorePackage carrier :=
  corePackageFor (Site.contextMorphismPreorderCategory object)

/-- R10: the generated core object is the selected finite architecture object. -/
theorem corePackage_object : corePackage.object = object := by
  rfl

/--
R10: a nonidentity atom map used by the generated operation example.

The input is intentionally ignored: this constant collapse gives a minimal
explicit nonidentity map whose direct-image configuration makes family and
relation transport observable.
-/
def collapseAtom (_atom : carrier.Atom) : carrier.Atom :=
  FiniteAtom.componentB

/-- R10: direct image of a configuration along the selected atom map. -/
def mappedConfiguration (C : AtomConfiguration carrier) : AtomConfiguration carrier where
  family.mem atom := ∃ source, C.family.mem source ∧ collapseAtom source = atom
  relation a b := ∃ source target,
    C.relation source target ∧ collapseAtom source = a ∧ collapseAtom target = b
  identification a b := ∃ source target,
    C.identification source target ∧ collapseAtom source = a ∧ collapseAtom target = b

/-- R10: the direct-image construction supplies an actual configuration homomorphism. -/
def collapseConfigurationHom (C : AtomConfiguration carrier) :
    ConfigurationHom C (mappedConfiguration C) where
  atomMap := collapseAtom
  maps_family h := ⟨_, h, rfl⟩
  maps_relation h := ⟨_, _, h, rfl, rfl⟩
  maps_identification h := ⟨_, _, h, rfl, rfl⟩

/-- R10: a second architecture object reached by the nonidentity atom map. -/
def collapsedObject : ArchitectureObject carrier :=
  objectOfConfiguration (mappedConfiguration corePackage.object.configuration)

/-- R10: the collapsed object belongs to the operation closure of the generated object. -/
theorem collapsedObject_reachable :
    coreReading.operationReading.Reachable corePackage.object collapsedObject :=
  OperationReading.Reachable.step OperationReading.Reachable.base
    (collapseConfigurationHom corePackage.object.configuration)

/-- R10: the reached object as an index of the generated object algebra. -/
def collapsedAlgebraObject : corePackage.algebra.Obj :=
  ⟨collapsedObject, collapsedObject_reachable⟩

/-- R10: the actual nonidentity operation between the two reachable indices. -/
def collapseOperation :
    corePackage.algebra.Op corePackage.baseObject collapsedAlgebraObject :=
  collapseConfigurationHom corePackage.object.configuration

/-- R10: the operation's atom map is visibly nonidentity. -/
theorem collapseOperation_atomMap_nonidentity :
    (corePackage.algebra.configurationMap collapseOperation).atomMap
      FiniteAtom.componentA = FiniteAtom.componentB ∧
      FiniteAtom.componentA ≠ FiniteAtom.componentB := by
  exact ⟨rfl, by decide⟩

/-- R10: extraction from the selected source is exactly exclusion of component C. -/
theorem extractionDoctrine_extracts_iff_selected (atom : carrier.Atom) :
    extractionDoctrine.extracts ExtractionSource.withoutComponentC atom ↔
      atom ≠ FiniteAtom.componentC := by
  rw [extractionDoctrine.extracts_iff]
  simp [extractionDoctrine]

/-- R10: generated-family membership is exactly the selected extraction predicate. -/
theorem corePackage_family_mem (atom : carrier.Atom) :
    atom ≠ FiniteAtom.componentC -> corePackage.family.mem atom := by
  intro hselected
  exact (corePackage.family_mem_iff_extracts atom).mpr
    ((extractionDoctrine_extracts_iff_selected atom).mpr hselected)

/-- R10: the generated main core contains a concretely selected atom. -/
theorem corePackage_componentA_mem :
    corePackage.family.mem FiniteAtom.componentA :=
  corePackage_family_mem _ (by simp)

/-- R10: the generated main core excludes the atom rejected by its source reading. -/
theorem corePackage_componentC_not_mem :
    ¬ corePackage.family.mem FiniteAtom.componentC := by
  intro h
  exact (extractionDoctrine_extracts_iff_selected FiniteAtom.componentC).mp
    ((corePackage.family_mem_iff_extracts FiniteAtom.componentC).mp h) rfl

/-- R10: configuration relations are the two selected relations on generated-family atoms. -/
theorem corePackage_configuration_relation_iff (a b : carrier.Atom) :
    corePackage.configuration.relation a b ↔
      (cycleRelation a b ∨ substitutionRelation a b) ∧
        corePackage.family.mem a ∧ corePackage.family.mem b := by
  rw [corePackage.configuration_relation_iff_compose]
  rfl

/-- R10: object relations are characterized through the generated configuration API. -/
theorem corePackage_object_relation_iff (a b : carrier.Atom) :
    corePackage.object.configuration.relation a b ↔
      (cycleRelation a b ∨ substitutionRelation a b) ∧
        corePackage.family.mem a ∧ corePackage.family.mem b := by
  rw [corePackage.object_configuration_eq]
  exact corePackage_configuration_relation_iff a b

/-- R10: the generated base configuration contains the first cycle relation. -/
theorem corePackage_cycle_relation :
    corePackage.object.configuration.relation
      FiniteAtom.dependsAB FiniteAtom.dependsBC :=
  (corePackage_object_relation_iff _ _).mpr
    ⟨Or.inl trivial, corePackage_family_mem _ (by simp),
      corePackage_family_mem _ (by simp)⟩

/-- R10: the generated base configuration contains the second cycle relation. -/
theorem corePackage_cycle_relation_two :
    corePackage.object.configuration.relation
      FiniteAtom.dependsBC FiniteAtom.dependsCA :=
  (corePackage_object_relation_iff _ _).mpr
    ⟨Or.inl trivial, corePackage_family_mem _ (by simp),
      corePackage_family_mem _ (by simp)⟩

/-- R10: the generated base configuration contains the third cycle relation. -/
theorem corePackage_cycle_relation_three :
    corePackage.object.configuration.relation
      FiniteAtom.dependsCA FiniteAtom.dependsAB :=
  (corePackage_object_relation_iff _ _).mpr
    ⟨Or.inl trivial, corePackage_family_mem _ (by simp),
      corePackage_family_mem _ (by simp)⟩

/-- R10: the generated base configuration contains a concrete identification. -/
theorem corePackage_componentA_identified_componentB :
    corePackage.object.configuration.identification
      FiniteAtom.componentA FiniteAtom.componentB := by
  rw [corePackage.object_configuration_eq]
  exact ⟨rfl, rfl, corePackage_family_mem _ (by simp),
    corePackage_family_mem _ (by simp)⟩

/-- R10: the nonidentity operation transports concrete family membership. -/
theorem collapseOperation_transports_family :
    collapsedObject.configuration.family.mem
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.componentA) :=
  (corePackage.algebra.configurationMap collapseOperation).maps_family
    ((corePackage.object_family_mem_iff_extracts FiniteAtom.componentA).mpr
      ((extractionDoctrine_extracts_iff_selected FiniteAtom.componentA).mpr (by simp)))

/-- R10: the nonidentity operation transports an actual relation. -/
theorem collapseOperation_transports_relation :
    collapsedObject.configuration.relation
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.dependsAB)
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.dependsBC) :=
  (corePackage.algebra.configurationMap collapseOperation).maps_relation
    corePackage_cycle_relation

/-- R10: the nonidentity operation transports a concrete identification. -/
theorem collapseOperation_transports_identification :
    collapsedObject.configuration.identification
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.componentA)
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.componentB) :=
  (corePackage.algebra.configurationMap collapseOperation).maps_identification
    corePackage_componentA_identified_componentB

/-- R10: the reached object differs from the generated base object. -/
theorem baseObject_ne_collapsedObject :
    corePackage.baseObject ≠ collapsedAlgebraObject := by
  intro h
  have hobject : corePackage.object = collapsedObject :=
    congrArg (fun index : corePackage.algebra.Obj => index.1) h
  have hbase :
      corePackage.object.configuration.family.mem FiniteAtom.componentA := by
    rw [corePackage.object_configuration_eq, corePackage.configuration_family_eq]
    exact corePackage_family_mem _ (by simp)
  have hmem : collapsedObject.configuration.family.mem FiniteAtom.componentA := by
    rw [← hobject]
    exact hbase
  rcases hmem with ⟨source, _hsource, hsource⟩
  cases source <;> cases hsource

/-- R10: the generated algebra has two distinct reachable objects and an operation between them. -/
theorem nonidentity_reachable_operation_fires :
    ∃ A B : corePackage.algebra.Obj,
      A ≠ B ∧ Nonempty (corePackage.algebra.Op A B) :=
  ⟨corePackage.baseObject, collapsedAlgebraObject,
    baseObject_ne_collapsedObject, ⟨collapseOperation⟩⟩

/-- R10: an empty configuration used to refute universal reachability. -/
def unreachableEmptyConfiguration : AtomConfiguration carrier where
  family := emptyFamily
  relation _ _ := False
  identification _ _ := False

/-- R10: an architecture object whose Atom family is empty. -/
def unreachableEmptyObject : ArchitectureObject carrier :=
  objectOfConfiguration unreachableEmptyConfiguration

/-- R10: every object reachable from the generated base retains an Atom witness. -/
theorem reachable_object_family_nonempty
    {A : ArchitectureObject carrier}
    (hreachable : coreReading.operationReading.Reachable corePackage.object A) :
    Nonempty {atom : carrier.Atom // A.configuration.family.mem atom} := by
  induction hreachable with
  | base =>
      exact ⟨⟨FiniteAtom.componentA, by
        rw [corePackage.object_configuration_eq,
          corePackage.configuration_family_eq]
        exact corePackage_componentA_mem⟩⟩
  | step hsource op ih =>
      obtain ⟨⟨atom, hatom⟩⟩ := ih
      exact ⟨⟨op.atomMap atom, op.maps_family hatom⟩⟩

/-- R10: the empty-family object is not in the generated operation closure. -/
theorem unreachableEmptyObject_not_reachable :
    ¬ coreReading.operationReading.Reachable corePackage.object
      unreachableEmptyObject := by
  intro hreachable
  obtain ⟨⟨atom, hatom⟩⟩ := reachable_object_family_nonempty hreachable
  exact hatom

/-- R10: the selected cycle datum matches the generated core object. -/
theorem cycleQueryDatum_matches_core :
    cycleQueryDatum.Matches corePackage.object := by
  intro query expected hmem
  simp [cycleQueryDatum] at hmem
  rcases hmem with h | h | h
  · rcases h with ⟨rfl, rfl⟩
    constructor
    · intro _; rfl
    · intro _
      exact ⟨by simpa [corePackage.object_configuration_eq,
        corePackage.configuration_family_eq] using
          corePackage_family_mem FiniteAtom.dependsAB (by simp),
        by simpa [corePackage.object_configuration_eq,
          corePackage.configuration_family_eq] using
            corePackage_family_mem FiniteAtom.dependsBC (by simp),
        corePackage_cycle_relation⟩
  · rcases h with ⟨rfl, rfl⟩
    constructor
    · intro _; rfl
    · intro _
      exact ⟨by simpa [corePackage.object_configuration_eq,
        corePackage.configuration_family_eq] using
          corePackage_family_mem FiniteAtom.dependsBC (by simp),
        by simpa [corePackage.object_configuration_eq,
          corePackage.configuration_family_eq] using
            corePackage_family_mem FiniteAtom.dependsCA (by simp),
        corePackage_cycle_relation_two⟩
  · rcases h with ⟨rfl, rfl⟩
    constructor
    · intro _; rfl
    · intro _
      exact ⟨by simpa [corePackage.object_configuration_eq,
        corePackage.configuration_family_eq] using
          corePackage_family_mem FiniteAtom.dependsCA (by simp),
        by simpa [corePackage.object_configuration_eq,
          corePackage.configuration_family_eq] using
            corePackage_family_mem FiniteAtom.dependsAB (by simp),
        corePackage_cycle_relation_three⟩

/-- R10: an opposite signed query that does not match the generated core object. -/
def componentAAbsentDatum : FiniteCircuitDatum carrier where
  queries := [(.atomPresent FiniteAtom.componentA, false)]

/-- R10: the component-A presence query holds on the generated core object. -/
theorem componentA_atomPresent_holds_core :
    (CircuitQuery.atomPresent FiniteAtom.componentA).Holds
      corePackage.object :=
  (CircuitQuery.atomPresent_holds_iff _ _).mpr
    ((corePackage.object_family_mem_iff_extracts FiniteAtom.componentA).mpr
      componentA_extracted_withoutComponentC)

/-- R10: the component-C presence query does not hold on the generated core object. -/
theorem componentC_atomPresent_not_holds_core :
    ¬ (CircuitQuery.atomPresent FiniteAtom.componentC).Holds
      corePackage.object := by
  intro hholds
  exact componentC_not_extracted_withoutComponentC
    ((corePackage.object_family_mem_iff_extracts FiniteAtom.componentC).mp
      ((CircuitQuery.atomPresent_holds_iff _ _).mp hholds))

/-- R10: matching is nontrivial on the generated finite object. -/
theorem componentAAbsentDatum_not_matches_core :
    ¬ componentAAbsentDatum.Matches corePackage.object := by
  intro hmatches
  have hiff := hmatches (.atomPresent FiniteAtom.componentA) false
    (by simp [componentAAbsentDatum])
  exact Bool.noConfusion (hiff.mp componentA_atomPresent_holds_core)

/-- R10: the positive component-A query used by the complete exact detector. -/
def componentAPresentDatum : FiniteCircuitDatum carrier where
  queries := [(.atomPresent FiniteAtom.componentA, true)]

/-- R10: the signed datum matches exactly when component A is present. -/
theorem componentAPresentDatum_matches_iff (A : ArchitectureObject carrier) :
    componentAPresentDatum.Matches A ↔
      A.configuration.family.mem FiniteAtom.componentA := by
  constructor
  · intro hmatches
    exact (CircuitQuery.atomPresent_holds_iff _ _).mp
      ((FiniteCircuitDatum.holds_iff_of_matches hmatches
        (by simp [componentAPresentDatum])).mpr rfl)
  · intro hmem query expected hquery
    simp only [componentAPresentDatum, List.mem_singleton] at hquery
    cases hquery
    constructor
    · intro _hholds
      rfl
    · intro _htrue
      exact (CircuitQuery.atomPresent_holds_iff _ _).mpr hmem

/--
Residual for the equation-indexed completeness fixture: component A is absent
exactly when the residual vanishes.
-/
noncomputable def componentAAbsentResidual
    (A : ArchitectureObject carrier) : Int := by
  classical
  exact if A.configuration.family.mem FiniteAtom.componentA then 1 else 0

/--
A singleton required equation whose fulfillment says that component A is
absent. This supplies a direct equation-system fixture rather than passing
through the legacy `Law` display.
-/
noncomputable def componentAAbsentEquationSystem
    (C : Site.ContextPreorderCategory object) :
    ArchitecturalEquationSystem C where
  Index := PUnit
  role _ := EquationRole.required
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ _ _ => 1
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ A _ _ => componentAAbsentResidual A
  equationResidual_restrict := by intros; rfl

/--
The component-A equation holds exactly on objects whose family omits the
selected component.
-/
theorem componentAAbsentEquationHolds_iff
    (C : Site.ContextPreorderCategory object) (A : ArchitectureObject carrier) :
    (componentAAbsentEquationSystem C).EquationHolds PUnit.unit A ↔
      ¬ A.configuration.family.mem FiniteAtom.componentA := by
  constructor
  · intro h hmem
    have hzero := h (Site.ContextCategoryObject.of C equationProbeContext)
      FiniteAtom.componentA
    simp [componentAAbsentEquationSystem, componentAAbsentResidual, hmem] at hzero
  · intro hmem W atom
    simp [componentAAbsentEquationSystem, componentAAbsentResidual, hmem]

/-- Exact positive-query detector for the component-A equation. -/
noncomputable def componentAPresentEquationCircuitReading
    (C : Site.ContextPreorderCategory object) :
    EquationCircuitReading (componentAAbsentEquationSystem C) where
  code _ := .exact componentAPresentDatum

/-- The component-A equation detector selects the exact positive datum. -/
theorem componentAPresentEquationCircuitReading_code
    (C : Site.ContextPreorderCategory object)
    (index : (componentAAbsentEquationSystem C).Index) :
    (componentAPresentEquationCircuitReading C).code index =
      .exact componentAPresentDatum := by
  cases index
  rfl

/--
The positive-query detector is sound by the direct residual characterization.
-/
theorem componentAPresentEquationCircuitReading_sound
    (C : Site.ContextPreorderCategory object) :
    (componentAPresentEquationCircuitReading C).Sound := by
  intro index A Q hmatches haccepts
  cases index
  have hdatum : componentAPresentDatum = Q :=
    (CircuitDetectorCode.eval_exact_eq_true_iff componentAPresentDatum Q).mp haccepts
  subst Q
  intro hequation
  exact (componentAAbsentEquationHolds_iff C A).mp hequation
    ((componentAPresentDatum_matches_iff A).mp hmatches)

/--
Every failure of the required component-A equation has the accepted positive
query, so the equation-indexed completeness predicate fires nonvacuously.
-/
theorem componentAPresentEquationCircuitReading_requiredComplete
    (C : Site.ContextPreorderCategory object) :
    (componentAPresentEquationCircuitReading C).RequiredComplete := by
  intro A index _hrequired hfailure
  cases index
  have hmem : A.configuration.family.mem FiniteAtom.componentA := by
    by_contra habsent
    exact hfailure ((componentAAbsentEquationHolds_iff C A).mpr habsent)
  refine ⟨⟨componentAPresentDatum,
    (componentAPresentDatum_matches_iff A).mpr hmem, ?_⟩⟩
  exact (CircuitDetectorCode.eval_exact_eq_true_iff
    componentAPresentDatum componentAPresentDatum).mpr rfl

/-- Reject-only equation detector used as the negative completeness instance. -/
noncomputable def rejectingEquationCircuitReading
    (C : Site.ContextPreorderCategory object) :
    EquationCircuitReading (componentAAbsentEquationSystem C) where
  code _ := .reject

/-- The negative completeness fixture selects reject at every equation index. -/
theorem rejectingEquationCircuitReading_code
    (C : Site.ContextPreorderCategory object)
    (index : (componentAAbsentEquationSystem C).Index) :
    (rejectingEquationCircuitReading C).code index = .reject := by
  cases index
  rfl

/--
The reject-only equation detector is not required-complete on the generated
component-A object.
-/
theorem rejectingEquationCircuitReading_not_requiredComplete
    (C : Site.ContextPreorderCategory object) :
    ¬ (rejectingEquationCircuitReading C).RequiredComplete := by
  intro hcomplete
  have hfailure :
      ¬ (componentAAbsentEquationSystem C).EquationHolds PUnit.unit
        corePackage.object := by
    intro hequation
    exact (componentAAbsentEquationHolds_iff C corePackage.object).mp hequation
      corePackage_componentA_mem
  obtain ⟨circuit⟩ := hcomplete corePackage.object PUnit.unit rfl hfailure
  have hreject :
      (rejectingEquationCircuitReading C).accepts PUnit.unit circuit.1 = false := by
    simp [EquationCircuitReading.accepts, rejectingEquationCircuitReading,
      CircuitDetectorCode.eval]
  exact Bool.noConfusion (hreject.symm.trans circuit.2.2)

/-- The negative signed component-A query matches the empty-family object. -/
theorem componentAAbsentDatum_matches_unreachableEmptyObject :
    componentAAbsentDatum.Matches unreachableEmptyObject := by
  intro query expected hquery
  simp only [componentAAbsentDatum, List.mem_singleton] at hquery
  cases hquery
  simp [CircuitQuery.Holds, unreachableEmptyObject, objectOfConfiguration,
    unreachableEmptyConfiguration, emptyFamily]

/--
An exact negative-query detector for the same equation, used to refute
vacuous universal soundness.
-/
noncomputable def unsoundEquationCircuitReading
    (C : Site.ContextPreorderCategory object) :
    EquationCircuitReading (componentAAbsentEquationSystem C) where
  code _ := .exact componentAAbsentDatum

/--
The negative-query detector is not sound: it accepts the empty-family object,
where the component-A equation actually holds.
-/
theorem unsoundEquationCircuitReading_not_sound
    (C : Site.ContextPreorderCategory object) :
    ¬ (unsoundEquationCircuitReading C).Sound := by
  intro hSound
  have haccepts :
      (unsoundEquationCircuitReading C).accepts PUnit.unit
        componentAAbsentDatum = true := by
    exact (CircuitDetectorCode.eval_exact_eq_true_iff
      componentAAbsentDatum componentAAbsentDatum).mpr rfl
  have hholds :
      (componentAAbsentEquationSystem C).EquationHolds PUnit.unit
        unreachableEmptyObject :=
    (componentAAbsentEquationHolds_iff C unreachableEmptyObject).mpr
      (by
        simp [unreachableEmptyObject, objectOfConfiguration,
          unreachableEmptyConfiguration, emptyFamily])
  exact hSound PUnit.unit unreachableEmptyObject componentAAbsentDatum
    componentAAbsentDatum_matches_unreachableEmptyObject haccepts hholds

/--
The component-A detector witnesses a concrete failed required equation and a
nonempty accepted circuit fiber on the generated object.
-/
theorem componentAPresentEquationCircuitReading_nonvacuous
    (C : Site.ContextPreorderCategory object) :
    ¬ (componentAAbsentEquationSystem C).EquationHolds PUnit.unit
        corePackage.object ∧
      Nonempty
        ((componentAPresentEquationCircuitReading C).Circuit
          corePackage.object PUnit.unit) := by
  have hfailure :
      ¬ (componentAAbsentEquationSystem C).EquationHolds PUnit.unit
        corePackage.object := by
    intro hequation
    exact (componentAAbsentEquationHolds_iff C corePackage.object).mp hequation
      corePackage_componentA_mem
  exact ⟨hfailure,
    componentAPresentEquationCircuitReading_requiredComplete C
      corePackage.object PUnit.unit rfl hfailure⟩

/--
The generated component-A fixture realizes the three equation, circuit, and
signature readings on a concrete positive object.
-/
theorem componentAAbsent_concreteThreeReadingAgreement
    (C : Site.ContextPreorderCategory object) :
    ((componentAAbsentEquationSystem C).EquationLawful corePackage.object ↔
        NoRequiredEquationCircuit
          (componentAPresentEquationCircuitReading C) corePackage.object) ∧
      (NoRequiredEquationCircuit
          (componentAPresentEquationCircuitReading C) corePackage.object ↔
        RequiredSignatureAxesZero corePackage.object
          (equationResidualSignatureAxes
            (componentAAbsentEquationSystem C))) ∧
      ((componentAAbsentEquationSystem C).EquationLawful corePackage.object ↔
        RequiredSignatureAxesZero corePackage.object
          (equationResidualSignatureAxes
            (componentAAbsentEquationSystem C))) :=
  concreteThreeReadingAgreement
    (componentAPresentEquationCircuitReading C)
    (componentAPresentEquationCircuitReading_sound C)
    (componentAPresentEquationCircuitReading_requiredComplete C)
    (equationResidualSignatureComparison
      (componentAAbsentEquationSystem C))
    corePackage.object

/-- The residual-coordinate signature vanishes on the component-A-absent object. -/
theorem componentAAbsent_signatureAxesZero_unreachableEmptyObject
    (C : Site.ContextPreorderCategory object) :
    RequiredSignatureAxesZero unreachableEmptyObject
      (equationResidualSignatureAxes (componentAAbsentEquationSystem C)) := by
  apply (equationLawful_iff_requiredSignatureAxesZero
    (equationResidualSignatureComparison
      (componentAAbsentEquationSystem C)) unreachableEmptyObject).mp
  intro index _hrequired
  cases index
  exact (componentAAbsentEquationHolds_iff C unreachableEmptyObject).mpr
    (by
      simp [unreachableEmptyObject, objectOfConfiguration,
        unreachableEmptyConfiguration, emptyFamily])

/-- The same residual-coordinate signature is nonzero on the generated core object. -/
theorem componentAAbsent_signatureAxesZero_fails_core
    (C : Site.ContextPreorderCategory object) :
    ¬ RequiredSignatureAxesZero corePackage.object
      (equationResidualSignatureAxes (componentAAbsentEquationSystem C)) := by
  intro hzero
  have hlawful :=
    (equationLawful_iff_requiredSignatureAxesZero
      (equationResidualSignatureComparison
        (componentAAbsentEquationSystem C)) corePackage.object).mpr hzero
  exact (componentAAbsentEquationHolds_iff C corePackage.object).mp
    (hlawful PUnit.unit rfl) corePackage_componentA_mem

/-- R10: the main core reading selects the exact cycle detector template. -/
theorem coreReading_circuit_code
    (i : coreReading.equationReading.equationSystem.Index) :
    coreReading.equationReading.circuits.code i =
      .exact cycleQueryDatum := by
  cases i
  rfl

/-- R10: the finite-template detector accepts the concrete cycle datum. -/
theorem cycleQueryDatum_accepted :
    coreReading.equationReading.circuits.accepts
      PUnit.unit cycleQueryDatum = true :=
  (EquationCircuitReading.accepts_eq_true_iff_of_code_exact
    coreReading.equationReading.circuits
      PUnit.unit cycleQueryDatum cycleQueryDatum
    (coreReading_circuit_code PUnit.unit)).mpr rfl

/-- R10: a distinct empty datum is rejected by the finite-template detector. -/
theorem emptyQueryDatum_rejected :
    coreReading.equationReading.circuits.accepts
      PUnit.unit ⟨[]⟩ = false := by
  apply Bool.eq_false_of_not_eq_true
  intro haccepts
  have heq : cycleQueryDatum = ⟨[]⟩ :=
    (EquationCircuitReading.accepts_eq_true_iff_of_code_exact
      coreReading.equationReading.circuits
        PUnit.unit cycleQueryDatum ⟨[]⟩
      (coreReading_circuit_code PUnit.unit)).mp haccepts
  have hqueries := congrArg FiniteCircuitDatum.queries heq
  simp [cycleQueryDatum] at hqueries

/-- R10: the accepted datum is an element of the generated indexed circuit family. -/
def generatedCycleCircuit :
    corePackage.algebra.Circuit corePackage.baseObject PUnit.unit :=
  ⟨cycleQueryDatum, cycleQueryDatum_matches_core, cycleQueryDatum_accepted⟩

/-- R10: equation failure is derived from detector soundness, not stored in the datum. -/
theorem generatedCycleCircuit_sound :
    ¬ corePackage.algebra.equationSystem.EquationHolds PUnit.unit
      (corePackage.algebra.object corePackage.baseObject) :=
  AATCorePackage.generate_circuit_sound axiomSystem coreReading
    corePackage.baseObject PUnit.unit generatedCycleCircuit

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
    supportReads := fun _ atom => atom ≠ FiniteAtom.componentC
    supportReads_objectFamily := fun hselected => allFamily_mem _ hselected
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

/-- The finite core specialized to the singleton Part II context preorder. -/
noncomputable def siteCorePackage : AATCorePackage carrier :=
  corePackageFor siteContextPreorder

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
  support_le_object := by
    intro atom h
    have hatom : atom = FiniteAtom.componentA := Set.mem_singleton_iff.mp h
    subst atom
    exact allFamily_mem _ (by simp)
  axis := {FiniteAtom.componentA}
  observable := {FiniteAtom.contractBase}

/--
Issue #3195: an independently declared representative of the component-A
profile, used to fire representative independence.
-/
def siteComponentAProfileCopy : SiteMinimalContextProfile where
  support := {FiniteAtom.componentA}
  support_le_object := by
    intro atom h
    have hatom : atom = FiniteAtom.componentA := Set.mem_singleton_iff.mp h
    subst atom
    exact allFamily_mem _ (by simp)
  axis := {FiniteAtom.componentA}
  observable := {FiniteAtom.contractBase}

/--
Issue #3195: a second nonempty finite profile reading component B, its axis,
and the implementation-contract observable.
-/
def siteComponentBProfile : SiteMinimalContextProfile where
  support := {FiniteAtom.componentB}
  support_le_object := by
    intro atom h
    have hatom : atom = FiniteAtom.componentB := Set.mem_singleton_iff.mp h
    subst atom
    exact allFamily_mem _ (by simp)
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
  supportRead_objectFamily := fun _ => allFamily_mem _ (by simp)
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
  supportRead_objectFamily := fun _ => allFamily_mem _ (by simp)
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
    Site.CoverageRequirements object siteCorePackage.equationSystem signature where
  requiredSupport := fun _ => True
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := fun _ _ => True
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun _ _ => True
  boundaryVisibleOn := fun _ _ => True

/-- SD2: selected geometry data typed by the generated finite core. -/
noncomputable def siteSelectedGeometryReading :
    Site.SelectedGeometryReading siteCorePackage where
  requirements := siteCoverageRequirements
  overlap := siteOverlap

/-- R11 / II.AC16: the finite AAT site generated from the selected core geometry. -/
noncomputable def site : Site.AATSite corePackage.object :=
  siteSelectedGeometryReading.toAATSite

/-- Every equation in the generated singleton site is required. -/
theorem site_equation_required (index : site.equationSystem.Index) :
    site.equationSystem.Required index := by
  cases index
  rfl

/-- The generated site equation is exactly absence of the selected cycle. -/
@[simp] theorem site_equationHolds_iff_noCycle
    (A : ArchitectureObject carrier) :
    site.equationSystem.EquationHolds PUnit.unit A ↔ ¬ hasDependencyCycle A := by
  change (equationSystem siteContextPreorder).EquationHolds PUnit.unit A ↔
    ¬ hasDependencyCycle A
  exact equationHolds_iff_noCycle siteContextPreorder A

/-- SD2: the finite site retains the generated core signature reading. -/
theorem site_signature_eq_core :
    site.signature = corePackage.algebra.signatureReading :=
  Site.SelectedGeometryReading.toAATSite_signature siteSelectedGeometryReading

/-- SD2: the finite topology is generated by the selected coverage. -/
theorem site_topology_eq_generated :
    site.topology =
      Site.AATGrothendieckTopology siteSelectedGeometryReading.requirements
        siteSelectedGeometryReading.overlap :=
  Site.SelectedGeometryReading.topology_eq_generated siteSelectedGeometryReading

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
    equationCoordinateCoverage := fun _coordinate _hreq =>
      Or.inl ⟨PUnit.unit, trivial⟩
    violationWitnessCoverage := fun _witness _hreq => Or.inl ⟨PUnit.unit, trivial⟩
    signatureAxisCoverage := fun _axis _hreq => ⟨PUnit.unit, trivial⟩
    boundaryCoverage := fun _i _j => trivial
    nonGeneration := fun _i {_support} {_atom} hselected =>
      allFamily_mem _ hselected
  }

/-- SD2: the singleton admissible cover belongs to the generated core topology. -/
theorem siteSingletonCover_topologyCover :
    Sieve.generate siteSingletonCover.presieve ∈ site.topology siteBase := by
  rw [site_topology_eq_generated]
  exact Site.AATGrothendieckTopology.generate_mem siteSingletonCover

/-- R11 / II.AC16: selected witness ideal requirements for the finite site. -/
def siteAdequacyRequirements :
    Site.UAdequacyRequirements siteContextPreorder siteCoverageRequirements where
  selectedWitnessIdeal := fun _ => True
  witnessIdealPreservedBy := fun _h _hideal => trivial

/-- R11 / II.AC16: direct `U`-adequacy of the singleton finite cover. -/
theorem siteSingletonCover_uAdequate :
    Site.UAdequateCover siteAdequacyRequirements siteSingletonCover where
  topologyCover := siteSingletonCover_topologyCover
  requiredSupportCovered := fun _atom _hreq => ⟨PUnit.unit, trivial⟩
  requiredEquationCoordinatesVisible := fun _coordinate _hreq =>
    Or.inl ⟨PUnit.unit, trivial⟩
  selectedViolationWitnessesVisible := fun _witness _hreq => Or.inl ⟨PUnit.unit, trivial⟩
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
        equationCoordinateCoverage := fun _coordinate _hreq =>
          Or.inl ⟨PUnit.unit, trivial⟩
        violationWitnessCoverage := fun _witness _hreq => Or.inl ⟨PUnit.unit, trivial⟩
        signatureAxisCoverage := fun _axis _hreq => ⟨PUnit.unit, trivial⟩
        boundaryCoverage := fun _i _j => trivial
        nonGeneration := fun _i {_support} {_atom} hread =>
          Y.ctx.minimal.supportReads_objectFamily hread
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
  by
    rw [site_topology_eq_generated]
    exact Site.AATGrothendieckTopology.eq_coverage_toGrothendieck
      siteCoverageRequirements siteOverlap

/-- R11 / II.AC16: the finite model has finitely many required witnesses. -/
theorem site_requiredWitnessSubtype_finite :
    Finite (Site.RequiredWitnessSubtype siteCoverageRequirements) := by
  change Finite { witness : PUnit × FiniteAtom // True }
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
  requiredEquationCoordinatesVisible := fun _coordinate _hreq =>
    Or.inl ⟨Sum.inl PUnit.unit, trivial⟩
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
  seedEquationCoordinatesVisible := fun _coordinate _hreq =>
    ⟨PUnit.unit, trivial⟩
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
    supportReads := fun _ atom => atom ≠ FiniteAtom.componentC
    supportReads_objectFamily := fun hselected => allFamily_mem _ hselected
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

/-- The finite core specialized to the nondegenerate two-patch context preorder. -/
noncomputable def twoPatchCorePackage : AATCorePackage carrier :=
  corePackageFor twoPatchContextPreorder

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
    Site.CoverageRequirements object twoPatchCorePackage.equationSystem signature where
  requiredSupport := fun atom =>
    atom = FiniteAtom.componentA ∨ atom = FiniteAtom.componentB
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := twoPatchSupportVisibleOn
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = twoPatchContext TwoPatchContextIndex.left ∨
      W = twoPatchContext TwoPatchContextIndex.right
  boundaryVisibleOn := fun _ _ => True

/-- SD2: the nondegenerate two-patch geometry is typed by the generated core. -/
noncomputable def twoPatchSelectedGeometryReading :
    Site.SelectedGeometryReading twoPatchCorePackage where
  requirements := twoPatchCoverageRequirements
  overlap := twoPatchOverlap

/-- peer-review hardening II-5: the two-patch AAT site over the generated core. -/
noncomputable def twoPatchSite : Site.AATSite corePackage.object :=
  twoPatchSelectedGeometryReading.toAATSite

/-- SD2: the two-patch topology is generated from its selected coverage. -/
theorem twoPatchSite_topology_eq_generated :
    twoPatchSite.topology =
      Site.AATGrothendieckTopology twoPatchCoverageRequirements twoPatchOverlap :=
  Site.SelectedGeometryReading.topology_eq_generated
    twoPatchSelectedGeometryReading

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
    equationCoordinateCoverage := by
      intro _coordinate _hreq
      exact Or.inl ⟨TwoPatchCoverIndex.left, trivial⟩
    violationWitnessCoverage := by
      intro _witness _hreq
      exact Or.inl ⟨TwoPatchCoverIndex.left, trivial⟩
    signatureAxisCoverage := by
      intro _axis _hreq
      exact ⟨TwoPatchCoverIndex.left, by
        simp [twoPatchCoverPatch, twoPatchCoverContextIndex,
          twoPatchCoverageRequirements]⟩
    boundaryCoverage := fun _i _j => trivial
    nonGeneration := by
      intro _i _support _atom hselected
      exact allFamily_mem _ hselected
  }

/-- peer-review hardening II-5: the generated two-patch cover is a topology cover. -/
theorem twoPatchCover_topologyCover :
    Sieve.generate twoPatchCover.presieve ∈ twoPatchSite.topology twoPatchBase := by
  rw [twoPatchSite_topology_eq_generated]
  exact Site.AATGrothendieckTopology.generate_mem twoPatchCover

/-- peer-review hardening II-5: selected adequacy requirements for the two-patch site. -/
def twoPatchAdequacyRequirements :
    Site.UAdequacyRequirements twoPatchContextPreorder
      twoPatchCoverageRequirements where
  selectedWitnessIdeal := fun _ => True
  witnessIdealPreservedBy := fun _h _hideal => trivial

/-- peer-review hardening II-5: direct `U`-adequacy for the two-patch finite cover. -/
theorem twoPatchCover_uAdequate :
    Site.UAdequateCover twoPatchAdequacyRequirements twoPatchCover where
  topologyCover := twoPatchCover_topologyCover
  requiredSupportCovered := twoPatchCover.admissible.atomSupportCoverage
  requiredEquationCoordinatesVisible :=
    twoPatchCover.admissible.equationCoordinateCoverage
  selectedViolationWitnessesVisible := twoPatchCover.admissible.violationWitnessCoverage
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

/-- The product of two contexts in the selected two-patch finite site. -/
private def twoPatchProductObject
    (X Y : twoPatchSite.category) : twoPatchSite.category :=
  Site.ContextCategoryObject.of twoPatchContextPreorder
    (Site.productContext X.ctx Y.ctx)

/-- First projection from a product context in the selected two-patch site. -/
private noncomputable def twoPatchProductLeft
    (X Y : twoPatchSite.category) : twoPatchProductObject X Y ⟶ X :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx)

/-- Second projection from a product context in the selected two-patch site. -/
private noncomputable def twoPatchProductRight
    (X Y : twoPatchSite.category) : twoPatchProductObject X Y ⟶ Y :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx)

/--
On the selected finite two-patch site, a presheaf with bijective restriction
maps satisfies the generated AAT sheaf condition.
-/
private theorem twoPatchPresheaf_isSheaf_of_bijective
    (P : CategoryTheory.Functor twoPatchSite.categoryᵒᵖ Type)
    (hbij : ∀ {X Y : twoPatchSite.category} (f : X ⟶ Y),
      Function.Bijective (P.map f.op)) :
    Presieve.IsSheaf twoPatchSite.topology P := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  rcases F.admissible.atomSupportCoverage
      FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  let patchObject := Site.ContextCategoryObject.of twoPatchContextPreorder
    (F.patch i)
  let Q := twoPatchProductObject Y patchObject
  let q : Q ⟶ Y := twoPatchProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := twoPatchProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed hinclusion qpatch
    convert hcomp using 1
  rcases (hbij q).2 (family q hq) with ⟨global, hglobal⟩
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    let PQ := twoPatchProductObject Z Q
    let pz : PQ ⟶ Z := twoPatchProductLeft Z Q
    let pq : PQ ⟶ Q := twoPatchProductRight Z Q
    apply (hbij pz).1
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    calc
      P.map pz.op (P.map g.op global) =
          P.map pq.op (P.map q.op global) := by
            rw [← FunctorToTypes.map_comp_apply,
              ← FunctorToTypes.map_comp_apply]
            congr 2
      _ = P.map pq.op (family q hq) := by rw [hglobal]
      _ = P.map pz.op (family g hg) := hcompat.symm
  · intro other hother
    apply (hbij q).1
    rw [hglobal]
    exact hother q hq

/-- `ZMod 2`-valued coefficients with identity restriction on the two-patch site. -/
def twoPatchZMod2Coefficient : Site.AATPresheaf twoPatchSite where
  obj _ := ZMod 2
  map _ x := x
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The nontrivial `ZMod 2` coefficient presheaf is an actual two-patch sheaf. -/
theorem twoPatchZMod2Coefficient_isSheaf :
    Site.AATSheafCondition twoPatchSite twoPatchZMod2Coefficient := by
  apply (Site.AATSheafCondition.iff_presieve_isSheaf twoPatchSite _).2
  apply twoPatchPresheaf_isSheaf_of_bijective
  intro _X _Y _f
  exact Function.bijective_id

/-- Packaged nontrivial `ZMod 2` coefficient sheaf on the two-patch AAT site. -/
def twoPatchZMod2CoefficientSheaf : Site.AATSheaf twoPatchSite where
  carrier := twoPatchZMod2Coefficient
  isSheaf := twoPatchZMod2Coefficient_isSheaf

/-- Replay functions with `ZMod 2` source and target states on the two-patch site. -/
abbrev TwoPatchZMod2ReplayFunction := ZMod 2 → ZMod 2

/--
Translation replay maps on the selected two-patch site.

The coefficient is part of the replay section itself: its evaluation is the
translation `state ↦ state + coefficient`.  Consequently equality of the
coefficient is equality of the replay map, rather than a separate sampled
observation of an arbitrary function.
-/
structure TwoPatchZMod2TranslationReplay where
  /-- The translation parameter that determines the replay map. -/
  coefficient : ZMod 2

namespace TwoPatchZMod2TranslationReplay

/-- Evaluate a translation replay map at a source state. -/
def apply (replay : TwoPatchZMod2TranslationReplay) (state : ZMod 2) : ZMod 2 :=
  state + replay.coefficient

/-- The replay section determines its translation coefficient. -/
theorem ext {left right : TwoPatchZMod2TranslationReplay}
    (h : left.coefficient = right.coefficient) : left = right := by
  cases left
  cases right
  cases h
  rfl

/-- Subtract a degree-zero correction from a translation replay section. -/
def adjust (replay : TwoPatchZMod2TranslationReplay) (correction : ZMod 2) :
    TwoPatchZMod2TranslationReplay where
  coefficient := replay.coefficient - correction

@[simp] theorem coefficient_adjust (replay : TwoPatchZMod2TranslationReplay)
    (correction : ZMod 2) : (adjust replay correction).coefficient =
      replay.coefficient - correction :=
  rfl

end TwoPatchZMod2TranslationReplay

/-- Translation replay sections with identity restriction on the two-patch site. -/
def twoPatchZMod2TranslationReplayPresheaf : Site.AATPresheaf twoPatchSite where
  obj _ := TwoPatchZMod2TranslationReplay
  map _ replay := replay
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Translation replay sections satisfy descent on every selected AAT cover. -/
theorem twoPatchZMod2TranslationReplay_isSheaf :
    Site.AATSheafCondition twoPatchSite twoPatchZMod2TranslationReplayPresheaf := by
  apply (Site.AATSheafCondition.iff_presieve_isSheaf twoPatchSite _).2
  apply twoPatchPresheaf_isSheaf_of_bijective
  intro _X _Y _f
  exact Function.bijective_id

/-- The actual replay-function sheaf for coefficient-reflecting translations. -/
def twoPatchZMod2TranslationReplaySheaf : Site.AATSheaf twoPatchSite where
  carrier := twoPatchZMod2TranslationReplayPresheaf
  isSheaf := twoPatchZMod2TranslationReplay_isSheaf

/-- The actual replay-function presheaf on the selected two-patch AAT site. -/
def twoPatchZMod2ReplayFunctionPresheaf : Site.AATPresheaf twoPatchSite where
  obj _ := TwoPatchZMod2ReplayFunction
  map _ replay := replay
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The `ZMod 2` replay-function presheaf satisfies descent on every AAT cover. -/
theorem twoPatchZMod2ReplayFunction_isSheaf :
    Site.AATSheafCondition twoPatchSite twoPatchZMod2ReplayFunctionPresheaf := by
  apply (Site.AATSheafCondition.iff_presieve_isSheaf twoPatchSite _).2
  apply twoPatchPresheaf_isSheaf_of_bijective
  intro _X _Y _f
  exact Function.bijective_id

/-- Packaged actual replay-function sheaf for the two-patch `ZMod 2` fixture. -/
def twoPatchZMod2ReplayFunctionSheaf : Site.AATSheaf twoPatchSite where
  carrier := twoPatchZMod2ReplayFunctionPresheaf
  isSheaf := twoPatchZMod2ReplayFunction_isSheaf

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

/-- The same selected two-patch site with its actual `ZMod 2` coefficient sheaf. -/
noncomputable def twoPatchZMod2FinitePosetRegime :
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
        | succ _ => exact Empty.elim simplex
  adequacyRequirements := twoPatchAdequacyRequirements
  coverAdequate := twoPatchCover_uAdequate
  coefficient := twoPatchZMod2Coefficient

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

/-- Additive Čech data for the actual `ZMod 2` coefficient sheaf on the two patches. -/
def twoPatchZMod2CechAdditiveData :
    Site.FinitePosetCechAdditiveData twoPatchZMod2FinitePosetRegime where
  zeroSection := by
    intro _n _simplex
    change ZMod 2
    exact 0
  combineFaces := by
    intro n _simplex faces
    cases n with
    | zero =>
        change ZMod 2
        exact (show ZMod 2 from faces ⟨1, by decide⟩) -
          (show ZMod 2 from faces ⟨0, by decide⟩)
    | succ _ =>
        change ZMod 2
        exact 0
  combineFaces_zero := by
    intro n simplex
    cases n with
    | zero =>
        cases simplex
        rfl
    | succ n =>
        cases n with
        | zero => exact Empty.elim simplex
        | succ _ => exact Empty.elim simplex

/-- The actual two-patch `ZMod 2` Čech differential: right restriction minus left restriction. -/
def twoPatchZMod2CechDifferential :
    ∀ n : Nat,
      Site.FinitePosetCechCochain twoPatchZMod2FinitePosetRegime n ->
        Site.FinitePosetCechCochain twoPatchZMod2FinitePosetRegime (n + 1)
  | 0, cochain, _simplex =>
      (show ZMod 2 from cochain TwoPatchCoverIndex.right) -
        (show ZMod 2 from cochain TwoPatchCoverIndex.left)
  | _ + 1, _cochain, simplex => Empty.elim simplex

/-- Actual `ZMod 2` Čech complex on the selected two-patch AAT site. -/
def twoPatchZMod2CechComplex :
    Site.FinitePosetCechComplex twoPatchZMod2FinitePosetRegime where
  additive := twoPatchZMod2CechAdditiveData
  faces := {
    face := by
      intro n simplex i
      cases n with
      | zero => exact if i.val = 0 then TwoPatchCoverIndex.left else TwoPatchCoverIndex.right
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
          | succ _ => exact Empty.elim simplex }
  differential := twoPatchZMod2CechDifferential
  differential_eq_restrictions := by
    intro n cochain simplex
    cases n with
    | zero =>
        cases simplex
        change
          ((show ZMod 2 from cochain TwoPatchCoverIndex.right) -
              (show ZMod 2 from cochain TwoPatchCoverIndex.left)) =
            ((show ZMod 2 from cochain TwoPatchCoverIndex.right) -
              (show ZMod 2 from cochain TwoPatchCoverIndex.left))
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
