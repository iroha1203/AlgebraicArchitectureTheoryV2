import Formal.Arch.Evolution.SFTField

namespace Formal.Arch

universe u v w q r s

/--
Atom axes are selected coordinates of architectural observation.

They are not scores, theorem discharges, or extractor completeness claims.
-/
inductive Axis where
  | static
  | semantic
  | runtime
  | boundary
  | dataflow
  | governance
  | evolution
  | policy
  deriving DecidableEq, Repr

/--
Atom v2 uses only primitive atom families here.  Obstructions, gaps, repairs,
and SFT deltas are separate structures, not atom kinds.
-/
inductive AtomKind where
  | component
  | relation
  | capability
  | dataState
  | effect
  | boundaryAuthority
  | observationContract
  | runtimeInteraction
  | evolutionHistory
  | policy
  | semantic
  deriving DecidableEq, Repr

namespace AtomKind

/-- In Atom v2 every `AtomKind` constructor in this file is primitive. -/
def IsPrimitive (_kind : AtomKind) : Prop := True

theorem isPrimitive (kind : AtomKind) : kind.IsPrimitive := by
  trivial

end AtomKind

/--
Measurement status of an observation.

Rejected, uncertain, private, out-of-scope, and blind-spot states are not
measured-zero evidence.
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

namespace MeasurementStatus

/-- Statuses that carry a measurement rather than a boundary/gap marker. -/
def SupportsMeasurement : MeasurementStatus -> Prop
  | measuredZero => True
  | measuredNonzero => True
  | _ => False

theorem rejectedCandidate_not_supportsMeasurement :
    ¬ SupportsMeasurement rejectedCandidate := by
  intro h
  exact h

theorem uncertainCandidate_not_supportsMeasurement :
    ¬ SupportsMeasurement uncertainCandidate := by
  intro h
  exact h

theorem unmeasured_not_measuredZero :
    unmeasured ≠ measuredZero := by
  intro h
  cases h

end MeasurementStatus

/--
Observation status is intentionally separate from atom existence.

An architecture atom may exist as a primitive typed fact while a concrete
tooling surface only observes, infers, rejects, or leaves it missing.
-/
inductive ObservationStatus where
  | observed
  | inferred
  | approximated
  | ambiguous
  | missing
  | contradicted
  | privateUnavailable
  | outOfScope
  | rejectedCandidate
  | uncertainCandidate
  deriving DecidableEq, Repr

/--
Selected finite-support predicate for an atom.

The support is a typed witness boundary.  It does not claim repository-wide
extractor completeness.
-/
structure Support (C : Type u) (E : Type v) (D : Type w) where
  components : C -> Prop
  edges : E -> Prop
  diagrams : D -> Prop
  evidenceBoundary : Prop
  nonConclusions : Prop

namespace Support

/-- Empty selected support. -/
def empty (C : Type u) (E : Type v) (D : Type w) : Support C E D where
  components := fun _ => False
  edges := fun _ => False
  diagrams := fun _ => False
  evidenceBoundary := True
  nonConclusions := True

/-- Component-only support. -/
def component {C : Type u} (E : Type v) (D : Type w) (c : C) :
    Support C E D where
  components := fun x => x = c
  edges := fun _ => False
  diagrams := fun _ => False
  evidenceBoundary := True
  nonConclusions := True

/-- Edge-only support. -/
def edge (C : Type u) {E : Type v} (D : Type w) (e : E) :
    Support C E D where
  components := fun _ => False
  edges := fun x => x = e
  diagrams := fun _ => False
  evidenceBoundary := True
  nonConclusions := True

/-- Diagram-only support. -/
def diagram (C : Type u) (E : Type v) {D : Type w} (d : D) :
    Support C E D where
  components := fun _ => False
  edges := fun _ => False
  diagrams := fun x => x = d
  evidenceBoundary := True
  nonConclusions := True

end Support

/-- Inclusion of selected support predicates. -/
def SupportSubset {C : Type u} {E : Type v} {D : Type w}
    (S T : Support C E D) : Prop :=
  (∀ c, S.components c -> T.components c) ∧
  (∀ e, S.edges e -> T.edges e) ∧
  (∀ d, S.diagrams d -> T.diagrams d)

/-- Proper inclusion of selected support predicates. -/
def ProperSubsupport {C : Type u} {E : Type v} {D : Type w}
    (S T : Support C E D) : Prop :=
  SupportSubset S T ∧ ¬ SupportSubset T S

namespace SupportSubset

theorem refl {C : Type u} {E : Type v} {D : Type w}
    (S : Support C E D) : SupportSubset S S := by
  exact ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem trans {C : Type u} {E : Type v} {D : Type w}
    {S T U : Support C E D}
    (hST : SupportSubset S T) (hTU : SupportSubset T U) :
    SupportSubset S U := by
  exact
    ⟨fun c h => hTU.1 c (hST.1 c h),
      fun e h => hTU.2.1 e (hST.2.1 e h),
      fun d h => hTU.2.2 d (hST.2.2 d h)⟩

end SupportSubset

/--
Primitive architecture atom.

This is a typed architectural fact with support and explicit evidence
boundaries.  It is not an observation gap, atomizer output certificate, repair
step, or SFT forecast.
-/
structure ArchitectureAtom (C : Type u) (E : Type v) (D : Type w) where
  kind : AtomKind
  axis : Axis
  support : Support C E D
  predicate : String
  evidenceBoundary : Prop
  nonConclusions : Prop

/-- Predicate spelling for primitive atoms. -/
def PrimitiveArchitectureAtom {C : Type u} {E : Type v} {D : Type w}
    (atom : ArchitectureAtom C E D) : Prop :=
  atom.kind.IsPrimitive

theorem primitiveArchitectureAtom_constructive
    {C : Type u} {E : Type v} {D : Type w}
    (atom : ArchitectureAtom C E D) :
    PrimitiveArchitectureAtom atom := by
  exact AtomKind.isPrimitive atom.kind

/-- A finite selected molecule/configuration of primitive atoms. -/
structure AtomMolecule (C : Type u) (E : Type v) (D : Type w) where
  atoms : ArchitectureAtom C E D -> Prop
  finiteBoundary : Prop
  nonConclusions : Prop

/-- Inclusion of atom molecules. -/
def AtomMoleculeSubset {C : Type u} {E : Type v} {D : Type w}
    (M N : AtomMolecule C E D) : Prop :=
  ∀ atom, M.atoms atom -> N.atoms atom

/-- Proper molecule inclusion. -/
def ProperAtomSubmolecule {C : Type u} {E : Type v} {D : Type w}
    (M N : AtomMolecule C E D) : Prop :=
  AtomMoleculeSubset M N ∧ ¬ AtomMoleculeSubset N M

/-- Minimal molecule for a badness predicate. -/
def MinimalAtomMolecule {C : Type u} {E : Type v} {D : Type w}
    (Bad : AtomMolecule C E D -> Prop)
    (M : AtomMolecule C E D) : Prop :=
  Bad M ∧ ∀ N, ProperAtomSubmolecule N M -> ¬ Bad N

/-- A design law marks bad atom configurations relative to selected boundaries. -/
structure DesignLaw (C : Type u) (E : Type v) (D : Type w) where
  Bad : AtomMolecule C E D -> Prop
  selectedBoundary : Prop
  nonConclusions : Prop

/-- Atom v2 obstruction circuit: a law-relative minimal bad molecule. -/
def ObstructionCircuit {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D) (M : AtomMolecule C E D) : Prop :=
  MinimalAtomMolecule law.Bad M

theorem obstructionCircuit_bad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D} {M : AtomMolecule C E D}
    (h : ObstructionCircuit law M) :
    law.Bad M :=
  h.1

theorem obstructionCircuit_antichain
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D} {M N : AtomMolecule C E D}
    (h : ObstructionCircuit law M)
    (hProper : ProperAtomSubmolecule N M) :
    ¬ law.Bad N :=
  h.2 N hProper

/-- Upward-closed selected badness for molecule search. -/
def AtomBadUpwardClosed {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D) : Prop :=
  ∀ {M N}, AtomMoleculeSubset M N -> law.Bad M -> law.Bad N

/--
Selected finite molecule universe.

This is a proof-carrying search boundary, not a claim that every possible
architecture fact has been extracted.
-/
structure FiniteAtomMoleculeUniverse {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D) where
  selected : AtomMolecule C E D -> Prop
  minimalOf :
    ∀ M, selected M -> law.Bad M ->
      { N // selected N ∧ ObstructionCircuit law N ∧ AtomMoleculeSubset N M }
  coverageBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

namespace FiniteAtomMoleculeUniverse

theorem contains_minimal_bad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    (U : FiniteAtomMoleculeUniverse law)
    {M : AtomMolecule C E D}
    (hSel : U.selected M) (hBad : law.Bad M) :
    ∃ N, U.selected N ∧ ObstructionCircuit law N ∧ AtomMoleculeSubset N M := by
  rcases U.minimalOf M hSel hBad with ⟨N, hN⟩
  exact ⟨N, hN⟩

theorem bad_iff_contains_obstruction_circuit
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    (U : FiniteAtomMoleculeUniverse law)
    (hUp : AtomBadUpwardClosed law)
    {M : AtomMolecule C E D}
    (hSel : U.selected M) :
    law.Bad M ↔
      ∃ N, U.selected N ∧ ObstructionCircuit law N ∧ AtomMoleculeSubset N M := by
  constructor
  · intro hBad
    exact U.contains_minimal_bad hSel hBad
  · intro h
    rcases h with ⟨N, _hSelN, hCircuit, hSub⟩
    exact hUp hSub hCircuit.1

end FiniteAtomMoleculeUniverse

/-- Tool-facing observation of a primitive atom. -/
structure ObservedAtom (C : Type u) (E : Type v) (D : Type w) where
  atom : ArchitectureAtom C E D
  observationStatus : ObservationStatus
  measurementStatus : MeasurementStatus
  evidenceRef : String
  sourceBoundary : Prop
  nonConclusions : Prop

/-- Observation gap, kept separate from atom existence. -/
structure ObservationGap (C : Type u) (E : Type v) (D : Type w) where
  expectedKind : AtomKind
  expectedAxis : Axis
  support : Support C E D
  measurementStatus : MeasurementStatus
  notMeasuredZero : measurementStatus ≠ MeasurementStatus.measuredZero
  sourceBoundary : Prop
  nonConclusions : Prop

theorem observedAtom_rejected_not_measured
    {C : Type u} {E : Type v} {D : Type w}
    (observed : ObservedAtom C E D)
    (h : observed.measurementStatus = MeasurementStatus.rejectedCandidate) :
    ¬ observed.measurementStatus.SupportsMeasurement := by
  rw [h]
  exact MeasurementStatus.rejectedCandidate_not_supportsMeasurement

theorem observedAtom_uncertain_not_measured
    {C : Type u} {E : Type v} {D : Type w}
    (observed : ObservedAtom C E D)
    (h : observed.measurementStatus = MeasurementStatus.uncertainCandidate) :
    ¬ observed.measurementStatus.SupportsMeasurement := by
  rw [h]
  exact MeasurementStatus.uncertainCandidate_not_supportsMeasurement

theorem observationGap_not_measuredZero
    {C : Type u} {E : Type v} {D : Type w}
    (gap : ObservationGap C E D) :
    gap.measurementStatus ≠ MeasurementStatus.measuredZero :=
  gap.notMeasuredZero

/--
Validated Lean-facing atom presentation.

ArchSig/ArchMap may supply candidates, but only this presentation surface is
read by AAT/SFT theorem packages.
-/
structure AtomPresentation (C : Type u) (E : Type v) (D : Type w) where
  observed : ObservedAtom C E D -> Prop
  gaps : ObservationGap C E D -> Prop
  promotionBoundary : Prop
  validationBoundary : Prop
  rawCandidateBoundary : Prop
  nonConclusions : Prop

/-- Per-atom valuation used by selected signatures. -/
structure AtomValuation (C : Type u) (E : Type v) (D : Type w) where
  atom : ArchitectureAtom C E D
  measurementStatus : MeasurementStatus
  bad : Prop
  evidenceBoundary : Prop
  nonConclusions : Prop

/-- Selected atom signature over a presentation. -/
structure AtomSignature (C : Type u) (E : Type v) (D : Type w) where
  valuation : ArchitectureAtom C E D -> MeasurementStatus
  badOn : ArchitectureAtom C E D -> Prop
  measuredBoundary : Prop
  nonConclusions : Prop

/-- A bad atom measured as nonzero on the selected signature. -/
def HasBadAtomOn {C : Type u} {E : Type v} {D : Type w}
    (signature : AtomSignature C E D)
    (atom : ArchitectureAtom C E D) : Prop :=
  signature.badOn atom ∧
    signature.valuation atom = MeasurementStatus.measuredNonzero

/-- Signature zero means no selected bad atom is measured nonzero. -/
def SignatureZero {C : Type u} {E : Type v} {D : Type w}
    (signature : AtomSignature C E D) : Prop :=
  ∀ atom, ¬ HasBadAtomOn signature atom

theorem no_hasBadAtomOn_of_signatureZero
    {C : Type u} {E : Type v} {D : Type w}
    {signature : AtomSignature C E D}
    (hZero : SignatureZero signature)
    (atom : ArchitectureAtom C E D) :
    ¬ HasBadAtomOn signature atom :=
  hZero atom

theorem signatureZero_iff_no_hasBadAtomOn
    {C : Type u} {E : Type v} {D : Type w}
    (signature : AtomSignature C E D) :
    SignatureZero signature ↔
      ∀ atom, ¬ HasBadAtomOn signature atom :=
  Iff.rfl

/-- Atom presentation bundled with its selected signature. -/
structure PresentedAtomSignature (C : Type u) (E : Type v) (D : Type w) where
  presentation : AtomPresentation C E D
  signature : AtomSignature C E D
  valuationBoundary : Prop
  nonConclusions : Prop

/-- SFT reads field atoms from validated presentation coordinates. -/
def FieldAtomsFromPresentation
    {FieldState : Type s} {C : Type u} {E : Type v}
    {StaticObs : Type w} {SemanticExpr : Type q} {SemanticObs : Type r}
    {D : Type w}
    (_field : SoftwareField FieldState C E StaticObs SemanticExpr SemanticObs)
    (presentation : AtomPresentation C E D) :
    ArchitectureAtom C E D -> Prop :=
  fun atom =>
    ∃ observed, presentation.observed observed ∧ observed.atom = atom

/-- Validated bridge from an SFT field to a Lean-facing atom presentation. -/
structure ValidatedFieldAtomPresentation
    (FieldState : Type s) (C : Type u) (E : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q) (SemanticObs : Type r)
    (D : Type w) where
  field : SoftwareField FieldState C E StaticObs SemanticExpr SemanticObs
  presentation : AtomPresentation C E D
  rawCandidateExcluded : Prop
  validationBoundary : Prop
  nonConclusions : Prop

def validatedFieldAtomPresentation_excludes_raw_candidates
    {FieldState : Type s} {C : Type u} {E : Type v}
    {StaticObs : Type w} {SemanticExpr : Type q} {SemanticObs : Type r}
    {D : Type w}
    (validated :
      ValidatedFieldAtomPresentation
        FieldState C E StaticObs SemanticExpr SemanticObs D) :
    Prop :=
  validated.rawCandidateExcluded

/-- Atom-level delta between selected presentations. -/
structure AtomDelta (C : Type u) (E : Type v) (D : Type w) where
  created : ArchitectureAtom C E D -> Prop
  removed : ArchitectureAtom C E D -> Prop
  preserved : ArchitectureAtom C E D -> Prop
  transformed : ArchitectureAtom C E D -> ArchitectureAtom C E D -> Prop
  hidden : ObservationGap C E D -> Prop
  exposed : ObservedAtom C E D -> Prop
  unknown : ObservationGap C E D -> Prop
  evidenceBoundary : Prop
  nonConclusions : Prop

/-- Atom presentation delta with source/target presentation boundary. -/
structure PresentedAtomDelta (C : Type u) (E : Type v) (D : Type w) where
  before : AtomPresentation C E D
  after : AtomPresentation C E D
  delta : AtomDelta C E D
  validationBoundary : Prop
  nonConclusions : Prop

/-- A selected trace of atom presentation deltas. -/
structure AtomTrace (C : Type u) (E : Type v) (D : Type w) where
  step : Nat -> PresentedAtomDelta C E D -> Prop
  finiteBoundary : Prop
  orderingBoundary : Prop
  nonConclusions : Prop

/-- SFT package reading validated atom presentations and traces. -/
structure AtomicSFTPresentationBridgePackage
    (FieldState : Type s) (C : Type u) (E : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q) (SemanticObs : Type r)
    (D : Type w) where
  validatedPresentation :
    ValidatedFieldAtomPresentation
      FieldState C E StaticObs SemanticExpr SemanticObs D
  fieldAtoms :
    ArchitectureAtom C E D -> Prop
  fieldAtomsSound :
    ∀ atom, fieldAtoms atom ->
      FieldAtomsFromPresentation
        validatedPresentation.field validatedPresentation.presentation atom
  atomTrace : AtomTrace C E D
  rawCandidateExcluded : Prop
  forecastCorrectnessNonConclusion : Prop
  globalFutureSafetyNonConclusion : Prop
  nonConclusions : Prop

namespace AtomicSFTPresentationBridgePackage

def records_raw_candidate_exclusion
    {FieldState : Type s} {C : Type u} {E : Type v}
    {StaticObs : Type w} {SemanticExpr : Type q} {SemanticObs : Type r}
    {D : Type w}
    (package :
      AtomicSFTPresentationBridgePackage
        FieldState C E StaticObs SemanticExpr SemanticObs D) :
    Prop :=
  package.rawCandidateExcluded

def records_no_forecast_correctness
    {FieldState : Type s} {C : Type u} {E : Type v}
    {StaticObs : Type w} {SemanticExpr : Type q} {SemanticObs : Type r}
    {D : Type w}
    (package :
      AtomicSFTPresentationBridgePackage
        FieldState C E StaticObs SemanticExpr SemanticObs D) :
    Prop :=
  package.forecastCorrectnessNonConclusion

end AtomicSFTPresentationBridgePackage

end Formal.Arch
