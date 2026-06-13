import Formal.AG.Atom.AATCore
import Formal.AG.Atom.LawfulnessZero
import Formal.AG.Site.FinitePoset
import Formal.AG.Site.SheafCategory

namespace AAT.AG

open CategoryTheory

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
  supportReadable := True
  axisReadable := True
  observableFunctorial := True
  nonGenerating := True
  axisForgetting := False
  supportRefinement := True
  axisRefinement := True
  baseChangeCompatible := True

/-- R11 / II.AC16: equality preorder on contexts, used by the singleton selected poset. -/
def siteContextPreorder : Site.ContextPreorderCategory object where
  le W V := W = V
  refl W := rfl
  trans hWV hVX := hWV.trans hVX
  readableMorphism := fun h => by
    cases h
    exact siteContextIdentityMorphism _
  readableMorphism_isRestriction := fun h => by
    cases h
    exact ⟨trivial, trivial, trivial, trivial⟩

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

/-- R11 / II.AC16: the finite AAT site over the PRD-1 finite model. -/
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
    nonGeneration := fun _i => trivial
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

/-- R11 / II.AC16: zero differential Čech complex on the singleton finite site. -/
def finitePosetCechComplex : Site.FinitePosetCechComplex finitePosetRegime Nat where
  differential := fun _n _cochain _simplex => 0
  differential_zero := fun _n => rfl

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
    Site.FinitePosetCechCohomologyVanishes finitePosetRegime Nat n :=
  Site.finitePosetCechCohomology_vanishes_above_nerveDimension
    finitePosetRegime Nat finitePosetCechComplex
    finitePosetRegime_nerveDimension_zero hn

end FiniteModel

end AAT.AG
