import Formal.Arch.Extension.Flatness
import Formal.Arch.Evolution.SFTField
import Formal.Arch.Evolution.SFTForecastCone

namespace Formal.Arch

universe u v w x y z

/--
Atom signature axes.

These axes are coordinates of a selected atomization boundary.  They are not a
global taxonomy of all possible software phenomena.
-/
inductive Axis where
  | static
  | boundary
  | abstraction
  | lsp
  | runtime
  | semantic
  | state
  | security
  | resource
  | field
  | coverage
  deriving DecidableEq, Repr

/-- The role an atom plays inside the selected atomization boundary. -/
inductive Polarity where
  | constructive
  | obstruction
  | coverage
  | repair
  deriving DecidableEq, Repr

/-- Boundary tags explaining why a coverage atom exists. -/
inductive CoverageGapKind where
  | missingEvidence
  | unmeasuredAxis
  | privateUnavailable
  | dynamicBlindSpot
  | outOfScope
  | unknownUnmodeledRemainder
  deriving DecidableEq, Repr

/-- The atom families used by the AAT/SFT atomic layer. -/
inductive AtomKind where
  | component
  | staticEdge
  | runtimeEdge
  | effectEdge
  | port
  | adapter
  | pureRule
  | coordinator
  | stateCell
  | guard
  | forbiddenStaticEdge
  | boundaryLeak
  | abstractionLeak
  | concreteBypass
  | simpleCycle : Nat -> AtomKind
  | projectionFailure
  | lspMismatch
  | fatInterface
  | nonCommutingSquare
  | runtimeExposure
  | effectLeak
  | replayViolation
  | compensationGap
  | complexityTransfer
  | coverageGap : CoverageGapKind -> AtomKind
  deriving DecidableEq, Repr

/--
Measurement status for one atom/signature axis.

`measuredZero` is deliberately different from `unmeasured`, rejected, or
out-of-scope evidence.
-/
inductive MeasurementStatus where
  | measuredZero
  | measuredNonzero
  | unmeasured
  | outOfScope
  | privateUnavailable
  | dynamicBlindSpot
  | rejectedCandidate
  | uncertainCandidate
  deriving DecidableEq, Repr

/--
Finite witness support for an atom.

The fields are predicates rather than lists so the same API covers concrete
components, relation/effect edges, and semantic diagrams.  Finiteness is
supplied by `FiniteSupportUniverse`.
-/
structure Support (C : Type u) (E : Type v) (D : Type w) where
  comps : C -> Prop
  edges : E -> Prop
  diagrams : D -> Prop

namespace Support

variable {C : Type u} {E : Type v} {D : Type w}

/-- Empty support. -/
def empty : Support C E D where
  comps := fun _ => False
  edges := fun _ => False
  diagrams := fun _ => False

/-- Single selected component support. -/
def component (c : C) : Support C E D where
  comps := fun x => x = c
  edges := fun _ => False
  diagrams := fun _ => False

/-- Single selected edge support. -/
def edge (e : E) : Support C E D where
  comps := fun _ => False
  edges := fun x => x = e
  diagrams := fun _ => False

/-- Single selected diagram / observation support. -/
def diagram (d : D) : Support C E D where
  comps := fun _ => False
  edges := fun _ => False
  diagrams := fun x => x = d

end Support

/-- Inclusion between supports. -/
def SupportSubset {C : Type u} {E : Type v} {D : Type w}
    (S T : Support C E D) : Prop :=
  (∀ c, S.comps c -> T.comps c) ∧
  (∀ e, S.edges e -> T.edges e) ∧
  (∀ d, S.diagrams d -> T.diagrams d)

namespace SupportSubset

variable {C : Type u} {E : Type v} {D : Type w}

/-- Support inclusion is reflexive. -/
theorem refl (S : Support C E D) : SupportSubset S S :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Support inclusion is transitive. -/
theorem trans {R S T : Support C E D}
    (hRS : SupportSubset R S) (hST : SupportSubset S T) :
    SupportSubset R T :=
  ⟨fun c h => hST.1 c (hRS.1 c h),
   fun e h => hST.2.1 e (hRS.2.1 e h),
   fun d h => hST.2.2 d (hRS.2.2 d h)⟩

/-- Support inclusion is antisymmetric up to predicate extensionality. -/
theorem antisymm {S T : Support C E D}
    (hST : SupportSubset S T) (hTS : SupportSubset T S) : S = T := by
  rcases S with ⟨Sc, Se, Sd⟩
  rcases T with ⟨Tc, Te, Td⟩
  have hc : Sc = Tc := by
    funext c
    exact propext ⟨fun h => hST.1 c h, fun h => hTS.1 c h⟩
  have he : Se = Te := by
    funext e
    exact propext ⟨fun h => hST.2.1 e h, fun h => hTS.2.1 e h⟩
  have hd : Sd = Td := by
    funext d
    exact propext ⟨fun h => hST.2.2 d h, fun h => hTS.2.2 d h⟩
  cases hc
  cases he
  cases hd
  rfl

end SupportSubset

/-- Proper support inclusion. -/
def ProperSubsupport {C : Type u} {E : Type v} {D : Type w}
    (T S : Support C E D) : Prop :=
  SupportSubset T S ∧ ¬ SupportSubset S T

/-- Predicate-relative minimality on supports. -/
def MinimalSupport {C : Type u} {E : Type v} {D : Type w}
    (P : Support C E D -> Prop) (S : Support C E D) : Prop :=
  P S ∧ ∀ T, ProperSubsupport T S -> ¬ P T

/-- Boundary-relative upward closure for badness predicates. -/
def UpwardClosed {C : Type u} {E : Type v} {D : Type w}
    (P : Support C E D -> Prop) : Prop :=
  ∀ {A S}, SupportSubset A S -> P A -> P S

/--
A finite selected support universe used by atomization theorems.

The `minimalOf` field is the finite-search obligation: every selected support
with property `P` contains a minimal selected support for `P`.
-/
structure FiniteSupportUniverse (C : Type u) (E : Type v) (D : Type w) where
  supports : List (Support C E D)
  minimalOf :
    ∀ (P : Support C E D -> Prop) {S : Support C E D},
      P S -> ∃ A, A ∈ supports ∧ SupportSubset A S ∧ MinimalSupport P A
  coverageBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

namespace FiniteSupportUniverse

variable {C : Type u} {E : Type v} {D : Type w}

/-- A bad selected support contains a predicate-relative minimal bad support. -/
theorem contains_minimal_bad
    (U : FiniteSupportUniverse C E D)
    (Bad : Support C E D -> Prop) {S : Support C E D}
    (hBad : Bad S) :
    ∃ A, A ∈ U.supports ∧ SupportSubset A S ∧ MinimalSupport Bad A :=
  U.minimalOf Bad hBad

/--
For upward-closed badness, the selected bad region is generated by minimal
atoms in the finite support universe.
-/
theorem bad_iff_contains_minimal
    (U : FiniteSupportUniverse C E D)
    (Bad : Support C E D -> Prop) (hUp : UpwardClosed Bad)
    (S : Support C E D) :
    Bad S ↔
      ∃ A, A ∈ U.supports ∧ SupportSubset A S ∧ MinimalSupport Bad A := by
  constructor
  · exact U.contains_minimal_bad Bad
  · rintro ⟨A, _hMem, hSub, hMin⟩
    exact hUp hSub hMin.1

end FiniteSupportUniverse

/-- Future cellular-circuit shape names. -/
structure ArchitectureShape where
  name : String
  axis : Axis
  boundary : Prop
  nonConclusions : Prop
  deriving Repr

/-- A representable carrier cell occurrence. -/
structure ArchitectureCell (C : Type u) (E : Type v) (D : Type w) where
  shape : ArchitectureShape
  support : Support C E D

/-- A finite molecule assembled from selected cells. -/
structure ArchitectureMolecule (C : Type u) (E : Type v) (D : Type w) where
  cells : List (ArchitectureCell C E D)
  support : Support C E D
  incidenceBoundary : Prop

/-- Atomization boundary for one selected architecture-object type. -/
structure AtomizationBoundary
    (Obj : Type x) (C : Type u) (E : Type v) (D : Type w) where
  requiredAxes : List Axis
  selectedAxis : Axis -> Prop
  atomKindAxis : AtomKind -> Axis
  shapePredicate : Obj -> AtomKind -> Support C E D -> Prop
  coverageGapPredicate : Obj -> CoverageGapKind -> Support C E D -> Prop
  theoremBoundary : Prop
  coverageAssumptions : Prop
  exactnessAssumptions : Prop
  classificationPriorityBoundary : Prop
  nonConclusions : Prop

/-- Shape predicate selected by an atomization boundary. -/
def Shape {Obj : Type x} {C : Type u} {E : Type v} {D : Type w}
    (B : AtomizationBoundary Obj C E D) (X : Obj)
    (k : AtomKind) (S : Support C E D) : Prop :=
  B.shapePredicate X k S

/-- A law-indexed circuit is a predicate-relative minimal support. -/
def ArchitectureCircuit {Obj : Type x} {C : Type u} {E : Type v} {D : Type w}
    (B : AtomizationBoundary Obj C E D) (X : Obj)
    (k : AtomKind) (S : Support C E D) : Prop :=
  MinimalSupport (Shape B X k) S

/-- Obstruction circuit spelling for badness predicates. -/
def ObstructionCircuit {C : Type u} {E : Type v} {D : Type w}
    (Bad : Support C E D -> Prop) (S : Support C E D) : Prop :=
  MinimalSupport Bad S

/-- Constructive atom spelling for good-shape predicates. -/
def ConstructiveMinimalGenerator {C : Type u} {E : Type v} {D : Type w}
    (GoodShape : Support C E D -> Prop) (S : Support C E D) : Prop :=
  MinimalSupport GoodShape S

/-- Coverage atoms are minimal coverage gaps, not measured-zero claims. -/
def MinimalCoverageGap {Obj : Type x} {C : Type u} {E : Type v} {D : Type w}
    (B : AtomizationBoundary Obj C E D) (X : Obj)
    (gap : CoverageGapKind) (S : Support C E D) : Prop :=
  MinimalSupport (B.coverageGapPredicate X gap) S

/-- Architecture atom data returned by an atomization surface. -/
structure ArchitectureAtom (C : Type u) (E : Type v) (D : Type w) where
  kind : AtomKind
  axis : Axis
  polarity : Polarity
  support : Support C E D
  status : MeasurementStatus
  evidenceBoundary : Prop
  nonConclusions : Prop

/-- A valid atom is one whose support is a selected minimal circuit or coverage gap. -/
def ValidAtom {Obj : Type x} {C : Type u} {E : Type v} {D : Type w}
    (B : AtomizationBoundary Obj C E D) (X : Obj)
    (a : ArchitectureAtom C E D) : Prop :=
  a.axis = B.atomKindAxis a.kind ∧
    match a.kind with
    | AtomKind.coverageGap gap => MinimalCoverageGap B X gap a.support
    | _ => ArchitectureCircuit B X a.kind a.support

/-- Valid atoms of the same kind form an antichain under proper subsupport. -/
theorem validAtom_antichain_sameKind
    {Obj : Type x} {C : Type u} {E : Type v} {D : Type w}
    {B : AtomizationBoundary Obj C E D} {X : Obj}
    {a b : ArchitectureAtom C E D}
    (hKind : a.kind = b.kind)
    (ha : ValidAtom B X a) (hb : ValidAtom B X b) :
    ¬ ProperSubsupport a.support b.support := by
  intro hProper
  rcases ha with ⟨_haAxis, haMin⟩
  rcases hb with ⟨_hbAxis, hbMin⟩
  rw [hKind] at haMin
  cases hAtomKind : b.kind <;>
    simp [ArchitectureCircuit, MinimalCoverageGap, hAtomKind] at haMin hbMin
  all_goals exact hbMin.2 a.support hProper haMin.1

/-- Single-edge policy violation predicate used by static atom v0. -/
def SingleEdgePolicyViolation {C : Type u} {E : Type v} {D : Type w}
    (edgeBad : E -> Prop) (edge : E) (S : Support C E D) : Prop :=
  S = Support.edge edge ∧ edgeBad edge

/-- A single bad edge is a minimal support for the single-edge predicate. -/
theorem singleEdgePolicyViolation_minimal
    {C : Type u} {E : Type v} {D : Type w}
    (edgeBad : E -> Prop) {edge : E} (hBad : edgeBad edge) :
    MinimalSupport (SingleEdgePolicyViolation (C := C) (D := D) edgeBad edge)
      (Support.edge edge) := by
  constructor
  · exact ⟨rfl, hBad⟩
  · intro T hProper hViolation
    rcases hViolation with ⟨hEq, _⟩
    subst hEq
    exact hProper.2 (SupportSubset.refl _)

/-- Static atom v0 theorem package. -/
structure StaticAtomV0Package (C : Type u) (E : Type v) (D : Type w) where
  forbiddenEdgeBad : E -> Prop
  boundaryLeakBad : E -> Prop
  abstractionLeakBad : E -> Prop
  simpleCycleBad : Support C E D -> Prop
  rankViolationBad : Support C E D -> Prop
  coverageGapBad : Support C E D -> Prop
  forbiddenEdgeMinimal :
    ∀ {e}, forbiddenEdgeBad e ->
      MinimalSupport (SingleEdgePolicyViolation (C := C) (D := D)
        forbiddenEdgeBad e) (Support.edge e)
  boundaryLeakMinimal :
    ∀ {e}, boundaryLeakBad e ->
      MinimalSupport (SingleEdgePolicyViolation (C := C) (D := D)
        boundaryLeakBad e) (Support.edge e)
  abstractionLeakMinimal :
    ∀ {e}, abstractionLeakBad e ->
      MinimalSupport (SingleEdgePolicyViolation (C := C) (D := D)
        abstractionLeakBad e) (Support.edge e)
  simpleCycleMinimal :
    ∀ {S}, simpleCycleBad S -> ObstructionCircuit simpleCycleBad S
  rankViolationMinimal :
    ∀ {S}, rankViolationBad S -> ObstructionCircuit rankViolationBad S
  coverageGapMinimal :
    ∀ {S}, coverageGapBad S -> MinimalSupport coverageGapBad S
  staticZeroNonConclusion : Prop
  noMatroidOrUniqueFactorizationConclusion : Prop

namespace StaticAtomV0Package

variable {C : Type u} {E : Type v} {D : Type w}

/-- Forbidden static edge atoms are minimal single-edge supports. -/
theorem forbiddenStaticEdge_minimal
    (package : StaticAtomV0Package C E D) {e : E}
    (hBad : package.forbiddenEdgeBad e) :
    MinimalSupport (SingleEdgePolicyViolation (C := C) (D := D)
      package.forbiddenEdgeBad e) (Support.edge e) :=
  package.forbiddenEdgeMinimal hBad

/-- Boundary-leak atoms are minimal single-edge supports when the policy is edge-local. -/
theorem boundaryLeak_minimal
    (package : StaticAtomV0Package C E D) {e : E}
    (hBad : package.boundaryLeakBad e) :
    MinimalSupport (SingleEdgePolicyViolation (C := C) (D := D)
      package.boundaryLeakBad e) (Support.edge e) :=
  package.boundaryLeakMinimal hBad

/-- Simple-cycle atoms are obstruction circuits in the selected static universe. -/
theorem simpleCycle_obstructionCircuit
    (package : StaticAtomV0Package C E D) {S : Support C E D}
    (hBad : package.simpleCycleBad S) :
    ObstructionCircuit package.simpleCycleBad S :=
  package.simpleCycleMinimal hBad

/-- Rank-violation atoms are obstruction circuits in the selected static universe. -/
theorem rankViolation_obstructionCircuit
    (package : StaticAtomV0Package C E D) {S : Support C E D}
    (hBad : package.rankViolationBad S) :
    ObstructionCircuit package.rankViolationBad S :=
  package.rankViolationMinimal hBad

/-- Static coverage gaps are minimal supports for the selected coverage predicate. -/
theorem coverageGap_minimal
    (package : StaticAtomV0Package C E D) {S : Support C E D}
    (hBad : package.coverageGapBad S) :
    MinimalSupport package.coverageGapBad S :=
  package.coverageGapMinimal hBad

/-- The package records that static zero is not semantic or runtime safety. -/
def records_staticZeroNonConclusion
    (package : StaticAtomV0Package C E D) :
    Prop :=
  package.staticZeroNonConclusion

end StaticAtomV0Package

/-- Atom valuation on selected axes. -/
structure AtomValuation where
  count : Axis -> Nat
  status : Axis -> MeasurementStatus
  evidenceBoundary : Axis -> Prop
  nonConclusions : Prop

/-- Atom signature is the valuation plus theorem-boundary evidence. -/
structure AtomSignature where
  valuation : AtomValuation
  theoremBoundary : Prop
  coverageBoundary : Prop
  exactnessBoundary : Prop
  atomCoverCompleteness : Prop
  nonConclusions : Prop

/-- There is a measured bad atom on an axis when its valuation count is positive. -/
def HasBadAtomOn (signature : AtomSignature) (axis : Axis) : Prop :=
  0 < signature.valuation.count axis

/-- Selected signature zero is measured-zero status plus zero atom valuation. -/
def SignatureZero (signature : AtomSignature) (axis : Axis) : Prop :=
  signature.valuation.status axis = MeasurementStatus.measuredZero ∧
    signature.valuation.count axis = 0

/-- A zero-valued measured axis has no bad atom on that axis. -/
theorem no_hasBadAtomOn_of_signatureZero
    {signature : AtomSignature} {axis : Axis}
    (hZero : SignatureZero signature axis) :
    ¬ HasBadAtomOn signature axis := by
  intro hBad
  rw [HasBadAtomOn, hZero.2] at hBad
  exact Nat.lt_irrefl 0 hBad

/-- Under measured-zero status, no bad atom is equivalent to signature zero. -/
theorem signatureZero_iff_no_hasBadAtomOn
    {signature : AtomSignature} {axis : Axis}
    (hMeasured : signature.valuation.status axis = MeasurementStatus.measuredZero) :
    SignatureZero signature axis ↔ ¬ HasBadAtomOn signature axis := by
  constructor
  · exact no_hasBadAtomOn_of_signatureZero
  · intro hNo
    refine ⟨hMeasured, ?_⟩
    exact Nat.eq_zero_of_not_pos (by
      intro hPos
      exact hNo hPos)

/-- Atom vanishing bridge with all required exactness boundaries explicit. -/
structure AtomVanishingBridge (signature : AtomSignature) (axis : Axis) where
  witnessComplete : Prop
  axisExact : Prop
  atomCoverComplete : Prop
  measuredStatus : signature.valuation.status axis = MeasurementStatus.measuredZero
  zeroIffNoAtom : SignatureZero signature axis ↔ ¬ HasBadAtomOn signature axis
  noGlobalSafetyConclusion : Prop
  noUnmeasuredAxisConclusion : Prop

/-- Build the measured-zero/no-atom bridge from the measured status hypothesis. -/
def AtomVanishingBridge.ofMeasuredZero
    (signature : AtomSignature) (axis : Axis)
    (hMeasured : signature.valuation.status axis = MeasurementStatus.measuredZero)
    (hWitnessComplete hAxisExact hAtomCoverComplete : Prop)
    (hNoGlobalSafety hNoUnmeasured : Prop) :
    AtomVanishingBridge signature axis where
  witnessComplete := hWitnessComplete
  axisExact := hAxisExact
  atomCoverComplete := hAtomCoverComplete
  measuredStatus := hMeasured
  zeroIffNoAtom := signatureZero_iff_no_hasBadAtomOn hMeasured
  noGlobalSafetyConclusion := hNoGlobalSafety
  noUnmeasuredAxisConclusion := hNoUnmeasured

/-- Classifier abstraction for a selected atomization boundary. -/
structure AtomClassifier
    (Obj : Type x) (C : Type u) (E : Type v) (D : Type w) where
  classify :
    AtomizationBoundary Obj C E D -> Obj -> Support C E D ->
      Option (ArchitectureAtom C E D)
  sound :
    ∀ {B X S a}, classify B X S = some a -> ValidAtom B X a
  rejectedCandidateNotMeasuredZero : Prop
  completenessBoundary : Prop
  nonConclusions : Prop

/-- Classifier soundness theorem. -/
theorem classify_sound
    {Obj : Type x} {C : Type u} {E : Type v} {D : Type w}
    (classifier : AtomClassifier Obj C E D)
    {B : AtomizationBoundary Obj C E D} {X : Obj}
    {S : Support C E D} {a : ArchitectureAtom C E D}
    (h : classifier.classify B X S = some a) :
    ValidAtom B X a :=
  classifier.sound h

/-- Certificate carrying atomization output and its soundness proof. -/
structure AtomizationCertificate
    (Obj : Type x) (C : Type u) (E : Type v) (D : Type w)
    (B : AtomizationBoundary Obj C E D) (X : Obj) where
  atoms : List (ArchitectureAtom C E D)
  allValid : ∀ a, a ∈ atoms -> ValidAtom B X a
  rejectedCandidateBoundary : Prop
  coverageGapBoundary : Prop
  nonConclusions : Prop

/-- Atomizer abstraction returning a sound certificate. -/
structure Atomizer
    (Obj : Type x) (C : Type u) (E : Type v) (D : Type w)
    (B : AtomizationBoundary Obj C E D) where
  atomize :
    (X : Obj) -> AtomizationCertificate Obj C E D B X
  sound :
    ∀ {X a}, a ∈ (atomize X).atoms -> ValidAtom B X a
  completenessBoundary : Prop
  nonConclusions : Prop

/-- Atomizer soundness theorem. -/
theorem atomize_sound
    {Obj : Type x} {C : Type u} {E : Type v} {D : Type w}
    {B : AtomizationBoundary Obj C E D} {X : Obj}
    (atomizer : Atomizer Obj C E D B)
    {a : ArchitectureAtom C E D}
    (hMem : a ∈ (atomizer.atomize X).atoms) :
    ValidAtom B X a :=
  atomizer.sound hMem

/-- Repair atoms are rewrite generators, not `ArchitectureAtom`s. -/
structure RepairAtom (C : Type u) (E : Type v) (D : Type w) where
  name : String
  consumes : ArchitectureAtom C E D -> Prop
  produces : ArchitectureAtom C E D -> Prop
  selectedAxis : Axis
  monotonicityBoundary : Prop
  nonConclusions : Prop

/-- Evolution atoms describe atom changes along a field transition. -/
structure EvolutionAtom
    (Field : Type x) (Operation : Type y)
    (C : Type u) (E : Type v) (D : Type w) where
  source : Field
  operation : Operation
  target : Field
  support : Support C E D
  created : List (ArchitectureAtom C E D)
  removed : List (ArchitectureAtom C E D)
  preserved : List (ArchitectureAtom C E D)
  exposed : List (ArchitectureAtom C E D)
  hidden : List (ArchitectureAtom C E D)
  unknownBoundary : Prop
  nonConclusions : Prop

/-- Atom delta for one transition. -/
structure AtomDelta (C : Type u) (E : Type v) (D : Type w) where
  created : List (ArchitectureAtom C E D)
  removed : List (ArchitectureAtom C E D)
  preserved : List (ArchitectureAtom C E D)
  transformed : List (ArchitectureAtom C E D × ArchitectureAtom C E D)
  hidden : List (ArchitectureAtom C E D)
  exposed : List (ArchitectureAtom C E D)
  unknown : List (CoverageGapKind × Support C E D)
  forecastBoundary : Prop
  nonConclusions : Prop

/-- Atom trace along a selected field path. -/
structure AtomTrace (Field : Type x) (C : Type u) (E : Type v) (D : Type w) where
  states : List Field
  deltas : List (AtomDelta C E D)
  wellTyped : Prop
  boundary : Prop
  nonConclusions : Prop

/-- Safe region determined by forbidding selected atom families. -/
structure AtomSafeRegion (C : Type u) (E : Type v) (D : Type w) where
  forbidden : AtomKind -> Prop
  atoms : List (ArchitectureAtom C E D)
  safe : ∀ a, a ∈ atoms -> ¬ forbidden a.kind
  boundary : Prop
  nonConclusions : Prop

/-- Extension atom formula as incidence refinement, not disjoint factorization. -/
structure ExtensionAtomFormula (C : Type u) (E : Type v) (D : Type w) where
  inherited : List (ArchitectureAtom C E D)
  featureLocal : List (ArchitectureAtom C E D)
  interaction : List (ArchitectureAtom C E D)
  liftingOrFilling : List (ArchitectureAtom C E D)
  complexityTransfer : List (ArchitectureAtom C E D)
  residualCoverage : List (ArchitectureAtom C E D)
  incidenceRefinementBoundary : Prop
  noDisjointPartitionConclusion : Prop

/-- Phase 1 SOLID / Clean atom theorem package. -/
structure SolidCleanAtomPackage (C : Type u) (E : Type v) (D : Type w) where
  portAtoms : List (ArchitectureAtom C E D)
  adapterAtoms : List (ArchitectureAtom C E D)
  pureRuleAtoms : List (ArchitectureAtom C E D)
  coordinatorAtoms : List (ArchitectureAtom C E D)
  fatInterfaceAtoms : List (ArchitectureAtom C E D)
  lspMismatchAtoms : List (ArchitectureAtom C E D)
  projectionFailureAtoms : List (ArchitectureAtom C E D)
  projectionSoundAtomTheorem : Prop
  lspMismatchAtomTheorem : Prop
  dipLocalSoundnessTheorem : Prop
  solidNotGlobalDecomposability : Prop
  nonConclusions : Prop

namespace SolidCleanAtomPackage

variable {C : Type u} {E : Type v} {D : Type w}

def projectionSound_atom_theorem
    (package : SolidCleanAtomPackage C E D) :
    Prop :=
  package.projectionSoundAtomTheorem

def solid_not_global_decomposability
    (package : SolidCleanAtomPackage C E D) :
    Prop :=
  package.solidNotGlobalDecomposability

def lspMismatch_atom_theorem
    (package : SolidCleanAtomPackage C E D) :
    Prop :=
  package.lspMismatchAtomTheorem

def dipLocal_soundness_theorem
    (package : SolidCleanAtomPackage C E D) :
    Prop :=
  package.dipLocalSoundnessTheorem

end SolidCleanAtomPackage

/-- Phase 2 semantic / runtime atom theorem package. -/
structure SemanticRuntimeAtomPackage (C : Type u) (E : Type v) (D : Type w) where
  runtimeEdgeAtoms : List (ArchitectureAtom C E D)
  guardAtoms : List (ArchitectureAtom C E D)
  runtimeExposureAtoms : List (ArchitectureAtom C E D)
  nonCommutingSquareAtoms : List (ArchitectureAtom C E D)
  effectLeakAtoms : List (ArchitectureAtom C E D)
  replayViolationAtoms : List (ArchitectureAtom C E D)
  compensationGapAtoms : List (ArchitectureAtom C E D)
  staticZeroNotSemanticZero : Prop
  runtimeProtectionLocalTheorem : Prop
  nonCommutingSquareWitnessTheorem : Prop
  noGlobalOperationalSafetyConclusion : Prop

namespace SemanticRuntimeAtomPackage

variable {C : Type u} {E : Type v} {D : Type w}

def static_zero_not_semantic_zero
    (package : SemanticRuntimeAtomPackage C E D) :
    Prop :=
  package.staticZeroNotSemanticZero

def non_commuting_square_witness
    (package : SemanticRuntimeAtomPackage C E D) :
    Prop :=
  package.nonCommutingSquareWitnessTheorem

def runtime_protection_local_theorem
    (package : SemanticRuntimeAtomPackage C E D) :
    Prop :=
  package.runtimeProtectionLocalTheorem

def records_no_global_operational_safety
    (package : SemanticRuntimeAtomPackage C E D) :
    Prop :=
  package.noGlobalOperationalSafetyConclusion

end SemanticRuntimeAtomPackage

/-- AAT atoms pulled back to a selected `SoftwareField`. -/
def FieldAtoms
    {FieldState : Type z} {C : Type u} {A : Type v}
    {StaticObs : Type w} {SemanticExpr : Type x} {SemanticObs : Type y}
    {Edge Diagram : Type}
    (B :
      AtomizationBoundary
        (ArchitectureObject C A StaticObs SemanticExpr SemanticObs)
        C Edge Diagram)
    (atomizer :
      Atomizer
        (ArchitectureObject C A StaticObs SemanticExpr SemanticObs)
        C Edge Diagram B)
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs) :
    List (ArchitectureAtom C Edge Diagram) :=
  (atomizer.atomize field.arch).atoms

/-- Soundness of field atoms follows through the architecture projection. -/
theorem field_atom_sound
    {FieldState : Type z} {C : Type u} {A : Type v}
    {StaticObs : Type w} {SemanticExpr : Type x} {SemanticObs : Type y}
    {Edge Diagram : Type}
    (B :
      AtomizationBoundary
        (ArchitectureObject C A StaticObs SemanticExpr SemanticObs)
        C Edge Diagram)
    (atomizer :
      Atomizer
        (ArchitectureObject C A StaticObs SemanticExpr SemanticObs)
        C Edge Diagram B)
    (field : SoftwareField FieldState C A StaticObs SemanticExpr SemanticObs)
    {a : ArchitectureAtom C Edge Diagram}
    (hMem : a ∈ FieldAtoms B atomizer field) :
    ValidAtom B field.arch a := by
  exact atomize_sound atomizer hMem

/-- Atomic SFT bridge theorem package. -/
structure AtomicSFTBridgePackage
    (Field : Type z) (Operation : Type y)
    (C : Type u) (E : Type v) (D : Type w) where
  fieldAtoms : Field -> List (ArchitectureAtom C E D)
  atomDelta : Field -> Operation -> Field -> AtomDelta C E D
  atomTrace : List Field -> AtomTrace Field C E D
  safeRegion : AtomSafeRegion C E D
  fieldAtomSound : Prop
  atomTraceSound : Prop
  atomSafeSupport : Prop
  atomConeNarrowingBoundary : Prop
  fieldUpdateRecordsUnexpectedAtomBoundary : Prop
  noGlobalFutureSafetyConclusion : Prop
  noForecastCorrectnessConclusion : Prop

namespace AtomicSFTBridgePackage

variable {Field : Type z} {Operation : Type y}
variable {C : Type u} {E : Type v} {D : Type w}

def field_atom_sound_boundary
    (package : AtomicSFTBridgePackage Field Operation C E D) :
    Prop :=
  package.fieldAtomSound

def atom_safe_support_boundary
    (package : AtomicSFTBridgePackage Field Operation C E D) :
    Prop :=
  package.atomSafeSupport

def atom_trace_sound_boundary
    (package : AtomicSFTBridgePackage Field Operation C E D) :
    Prop :=
  package.atomTraceSound

def atom_cone_narrowing_boundary
    (package : AtomicSFTBridgePackage Field Operation C E D) :
    Prop :=
  package.atomConeNarrowingBoundary

def field_update_records_unexpected_atom_boundary
    (package : AtomicSFTBridgePackage Field Operation C E D) :
    Prop :=
  package.fieldUpdateRecordsUnexpectedAtomBoundary

def records_no_global_future_safety
    (package : AtomicSFTBridgePackage Field Operation C E D) :
    Prop :=
  package.noGlobalFutureSafetyConclusion

end AtomicSFTBridgePackage

end Formal.Arch
