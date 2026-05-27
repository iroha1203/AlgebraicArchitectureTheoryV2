import Formal.Arch.Evolution.SFTField
import Formal.Arch.Evolution.SFTForecastCone
import Formal.Arch.Law.Projection
import Formal.Arch.Law.Observation
import Formal.Arch.Patterns.SRPDesignPattern

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

/--
In Atom v2 every `AtomKind` constructor in this file is primitive.

This predicate is intentionally small: it records the current Lean-facing atom
grammar, not a claim that the taxonomy is globally complete.
-/
def IsPrimitive (_kind : AtomKind) : Prop := True

theorem isPrimitive (kind : AtomKind) : kind.IsPrimitive := by
  trivial

end AtomKind

/--
Lean-facing policy for extending the atom grammar.

The policy records which currently declared `AtomKind` / `Axis` coordinates are
allowed in a selected presentation and keeps that extension boundary separate
from derived witnesses such as obstruction circuits, observation gaps, repair
steps, and SFT forecasts.
-/
structure AtomGrammarExtensionPolicy where
  permittedKind : AtomKind -> Prop
  permittedAxis : Axis -> Prop
  primitiveKindBoundary :
    ∀ kind, permittedKind kind -> kind.IsPrimitive
  derivedWitnessesSeparated : Prop
  toolingSchemaBoundary : Prop
  noGlobalTaxonomyCompleteness : Prop

namespace AtomGrammarExtensionPolicy

/-- The current policy permits all atom kinds and axes declared in this file. -/
def current : AtomGrammarExtensionPolicy where
  permittedKind := fun _ => True
  permittedAxis := fun _ => True
  primitiveKindBoundary := fun kind _ => AtomKind.isPrimitive kind
  derivedWitnessesSeparated := True
  toolingSchemaBoundary := True
  noGlobalTaxonomyCompleteness := True

theorem current_permits_kind (kind : AtomKind) :
    current.permittedKind kind := by
  trivial

theorem current_permits_axis (axis : Axis) :
    current.permittedAxis axis := by
  trivial

theorem primitive_of_permitted
    (policy : AtomGrammarExtensionPolicy) {kind : AtomKind}
    (h : policy.permittedKind kind) :
    kind.IsPrimitive :=
  policy.primitiveKindBoundary kind h

theorem current_permittedKind_isPrimitive (kind : AtomKind) :
    kind.IsPrimitive :=
  primitive_of_permitted current (current_permits_kind kind)

end AtomGrammarExtensionPolicy

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

namespace ArchitectureAtom

/-- A primitive atom is accepted by a selected grammar policy. -/
def AllowedBy {C : Type u} {E : Type v} {D : Type w}
    (policy : AtomGrammarExtensionPolicy)
    (atom : ArchitectureAtom C E D) : Prop :=
  policy.permittedKind atom.kind ∧ policy.permittedAxis atom.axis

theorem allowedBy_current
    {C : Type u} {E : Type v} {D : Type w}
    (atom : ArchitectureAtom C E D) :
    atom.AllowedBy AtomGrammarExtensionPolicy.current := by
  exact
    ⟨AtomGrammarExtensionPolicy.current_permits_kind atom.kind,
      AtomGrammarExtensionPolicy.current_permits_axis atom.axis⟩

theorem primitive_of_allowedBy
    {C : Type u} {E : Type v} {D : Type w}
    {policy : AtomGrammarExtensionPolicy}
    {atom : ArchitectureAtom C E D}
    (h : atom.AllowedBy policy) :
    PrimitiveArchitectureAtom atom :=
  policy.primitiveKindBoundary atom.kind h.1

end ArchitectureAtom

/-- A finite selected molecule/configuration of primitive atoms. -/
structure AtomMolecule (C : Type u) (E : Type v) (D : Type w) where
  atoms : ArchitectureAtom C E D -> Prop
  finiteBoundary : Prop
  nonConclusions : Prop

/--
Selected atom universe for finite molecule reasoning.

This is a proof-carrying boundary for selected atoms, not an extractor
completeness statement.
-/
structure SelectedAtomUniverse (C : Type u) (E : Type v) (D : Type w) where
  selectedAtom : ArchitectureAtom C E D -> Prop
  finiteBoundary : Prop
  coverageBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

/-- A molecule is supported by a selected atom universe. -/
def AtomMoleculeSupportedBy {C : Type u} {E : Type v} {D : Type w}
    (U : SelectedAtomUniverse C E D)
    (M : AtomMolecule C E D) : Prop :=
  ∀ atom, M.atoms atom -> U.selectedAtom atom

/-- Proof-carrying finite witness for a selected molecule. -/
structure FiniteAtomMoleculeWitness {C : Type u} {E : Type v} {D : Type w}
    (U : SelectedAtomUniverse C E D)
    (M : AtomMolecule C E D) where
  supportedBy : AtomMoleculeSupportedBy U M
  moleculeFiniteBoundary : Prop
  universeFiniteBoundary : Prop
  nonConclusions : Prop

/-- Inclusion of atom molecules. -/
def AtomMoleculeSubset {C : Type u} {E : Type v} {D : Type w}
    (M N : AtomMolecule C E D) : Prop :=
  ∀ atom, M.atoms atom -> N.atoms atom

namespace AtomMoleculeSubset

theorem refl {C : Type u} {E : Type v} {D : Type w}
    (M : AtomMolecule C E D) :
    AtomMoleculeSubset M M := by
  intro atom hAtom
  exact hAtom

theorem trans {C : Type u} {E : Type v} {D : Type w}
    {M N P : AtomMolecule C E D}
    (hMN : AtomMoleculeSubset M N)
    (hNP : AtomMoleculeSubset N P) :
    AtomMoleculeSubset M P := by
  intro atom hAtom
  exact hNP atom (hMN atom hAtom)

end AtomMoleculeSubset

namespace FiniteAtomMoleculeWitness

def ofSubmolecule
    {C : Type u} {E : Type v} {D : Type w}
    {U : SelectedAtomUniverse C E D}
    {M N : AtomMolecule C E D}
    (w : FiniteAtomMoleculeWitness U M)
    (hSub : AtomMoleculeSubset N M) :
    FiniteAtomMoleculeWitness U N where
  supportedBy := by
    intro atom hAtom
    exact w.supportedBy atom (hSub atom hAtom)
  moleculeFiniteBoundary := N.finiteBoundary
  universeFiniteBoundary := w.universeFiniteBoundary
  nonConclusions := w.nonConclusions

end FiniteAtomMoleculeWitness

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

/--
Selected atom-configuration lawfulness.

This is not defined as circuit absence.  It says that every selected molecule is
not bad for the design law.
-/
def LawfulWithinAtomConfiguration
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) : Prop :=
  ∀ M, requiredMolecule M -> ¬ law.Bad M

/-- No required obstruction circuit is observed inside the selected boundary. -/
def NoRequiredObstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) : Prop :=
  ∀ M, requiredMolecule M -> ¬ ObstructionCircuit law M

/--
Bridge assumptions connecting selected lawfulness to obstruction-circuit
absence.

The first field is the substantive witness-completeness assumption: selected
bad molecules must expose a selected minimal obstruction circuit.  Without that
coverage/exactness boundary, no-circuit observations are not promoted to global
lawfulness.
-/
structure AtomLawfulnessBridge
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  badWitnessComplete :
    ∀ M, requiredMolecule M -> law.Bad M ->
      ∃ Ckt, requiredMolecule Ckt ∧ ObstructionCircuit law Ckt
  circuitBad :
    ∀ M, requiredMolecule M -> ObstructionCircuit law M -> law.Bad M
  coverageBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

namespace AtomLawfulnessBridge

theorem lawful_iff_no_obstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (bridge : AtomLawfulnessBridge law requiredMolecule) :
    LawfulWithinAtomConfiguration law requiredMolecule ↔
      NoRequiredObstructionCircuit law requiredMolecule := by
  constructor
  · intro hLawful M hRequired hCircuit
    exact hLawful M hRequired (bridge.circuitBad M hRequired hCircuit)
  · intro hNoCircuit M hRequired hBad
    rcases bridge.badWitnessComplete M hRequired hBad with
      ⟨Ckt, hRequiredCkt, hCircuit⟩
    exact hNoCircuit Ckt hRequiredCkt hCircuit

end AtomLawfulnessBridge

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

/-- A selected required axis predicate lifted to atoms. -/
def RequiredAtomAxis {C : Type u} {E : Type v} {D : Type w}
    (requiredAxis : Axis -> Prop)
    (atom : ArchitectureAtom C E D) : Prop :=
  requiredAxis atom.axis

/--
Required atom signature zero means no selected required atom is measured as a
bad nonzero atom.
-/
def RequiredAtomSignatureZero {C : Type u} {E : Type v} {D : Type w}
    (signature : AtomSignature C E D)
    (requiredAxis : Axis -> Prop) : Prop :=
  ∀ atom, RequiredAtomAxis requiredAxis atom -> ¬ HasBadAtomOn signature atom

/--
Bridge package from a selected atom signature to required-axis vanishing.

This is a measured selected-axis statement.  It does not prove unmeasured axis
safety, global future safety, or zero curvature without the later lawfulness
and observation-coverage bridges.
-/
structure AtomVanishingBridge {C : Type u} {E : Type v} {D : Type w}
    (signature : AtomSignature C E D)
    (requiredAxis : Axis -> Prop) where
  requiredAxisZero : RequiredAtomSignatureZero signature requiredAxis
  measuredBoundary : Prop
  nonConclusions : Prop

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

theorem requiredAtomSignatureZero_of_signatureZero
    {C : Type u} {E : Type v} {D : Type w}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (hZero : SignatureZero signature) :
    RequiredAtomSignatureZero signature requiredAxis := by
  intro atom _hRequired
  exact hZero atom

namespace AtomVanishingBridge

def ofSignatureZero
    {C : Type u} {E : Type v} {D : Type w}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (hZero : SignatureZero signature) :
    AtomVanishingBridge signature requiredAxis where
  requiredAxisZero := requiredAtomSignatureZero_of_signatureZero hZero
  measuredBoundary := signature.measuredBoundary
  nonConclusions := signature.nonConclusions

theorem no_hasBadAtomOn_of_requiredAxis
    {C : Type u} {E : Type v} {D : Type w}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (bridge : AtomVanishingBridge signature requiredAxis)
    (atom : ArchitectureAtom C E D)
    (hRequired : RequiredAtomAxis requiredAxis atom) :
    ¬ HasBadAtomOn signature atom :=
  bridge.requiredAxisZero atom hRequired

end AtomVanishingBridge

/--
AAT-facing theorem package read from a validated atom presentation.

The package separates three surfaces:

* observed atoms and gaps that AAT may read from the presentation,
* selected lawfulness / signature bridges used by AAT statements,
* guardrails saying that raw candidates or validation passes are not theorem
  claims by themselves.
-/
structure AtomPresentationAATPackage
    {C : Type u} {E : Type v} {D : Type w}
    (presentation : AtomPresentation C E D)
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop)
    (signature : AtomSignature C E D)
    (requiredAxis : Axis -> Prop) where
  selectedAtoms : ArchitectureAtom C E D -> Prop
  selectedGaps : ObservationGap C E D -> Prop
  selectedAtomsSound :
    ∀ atom, selectedAtoms atom ->
      ∃ observed,
        presentation.observed observed ∧
        observed.atom = atom ∧
        observed.measurementStatus.SupportsMeasurement
  selectedGapsSound :
    ∀ gap, selectedGaps gap -> presentation.gaps gap
  lawfulnessBridge : AtomLawfulnessBridge law requiredMolecule
  vanishingBridge : AtomVanishingBridge signature requiredAxis
  promotionBoundary : presentation.promotionBoundary
  validationBoundary : presentation.validationBoundary
  rawCandidateBoundary : presentation.rawCandidateBoundary
  nonConclusions : presentation.nonConclusions

namespace AtomPresentationAATPackage

def RawCandidateTheoremClaim
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (_pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis) : Prop :=
  False

def ValidationPassTheoremClaim
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (_pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis) : Prop :=
  False

theorem selectedAtom_from_presentation
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis)
    {atom : ArchitectureAtom C E D}
    (hAtom : pkg.selectedAtoms atom) :
    ∃ observed,
      presentation.observed observed ∧
      observed.atom = atom ∧
      observed.measurementStatus.SupportsMeasurement :=
  pkg.selectedAtomsSound atom hAtom

theorem selectedGap_from_presentation
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis)
    {gap : ObservationGap C E D}
    (hGap : pkg.selectedGaps gap) :
    presentation.gaps gap :=
  pkg.selectedGapsSound gap hGap

theorem lawful_iff_no_required_obstructionCircuit
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis) :
    LawfulWithinAtomConfiguration law requiredMolecule ↔
      NoRequiredObstructionCircuit law requiredMolecule :=
  pkg.lawfulnessBridge.lawful_iff_no_obstructionCircuit

theorem no_hasBadAtomOn_of_requiredAxis
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis)
    (atom : ArchitectureAtom C E D)
    (hRequired : RequiredAtomAxis requiredAxis atom) :
    ¬ HasBadAtomOn signature atom :=
  pkg.vanishingBridge.no_hasBadAtomOn_of_requiredAxis atom hRequired

theorem rawCandidateBoundary_recorded
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis) :
    presentation.rawCandidateBoundary :=
  pkg.rawCandidateBoundary

theorem noRawCandidateTheoremClaim_recorded
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis) :
    ¬ RawCandidateTheoremClaim pkg := by
  intro h
  exact h

theorem noValidationPassTheoremClaim_recorded
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis) :
    ¬ ValidationPassTheoremClaim pkg := by
  intro h
  exact h

theorem nonConclusions_recorded
    {C : Type u} {E : Type v} {D : Type w}
    {presentation : AtomPresentation C E D}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    {signature : AtomSignature C E D}
    {requiredAxis : Axis -> Prop}
    (pkg :
      AtomPresentationAATPackage
        presentation law requiredMolecule signature requiredAxis) :
    presentation.nonConclusions :=
  pkg.nonConclusions

end AtomPresentationAATPackage

/--
Layering read as an atom arrangement law.

This package does not redefine `StrictLayered`; it records the selected
AtomMolecule law whose lawfulness is sufficient to recover the existing AAT
layering invariant.
-/
structure LayeringAtomArrangementLaw
    {C : Type u} {E : Type v} {D : Type w}
    (G : ArchGraph C)
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  lawfulnessImpliesStrictLayered :
    LawfulWithinAtomConfiguration law requiredMolecule -> StrictLayered G
  obstructionCircuitBoundary : Prop
  nonConclusions : Prop

namespace LayeringAtomArrangementLaw

theorem strictLayered_of_lawful
    {C : Type u} {E : Type v} {D : Type w}
    {G : ArchGraph C}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : LayeringAtomArrangementLaw G law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    StrictLayered G :=
  pkg.lawfulnessImpliesStrictLayered hLawful

theorem acyclic_of_lawful
    {C : Type u} {E : Type v} {D : Type w}
    {G : ArchGraph C}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : LayeringAtomArrangementLaw G law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    Acyclic G :=
  strictLayered_acyclic (pkg.strictLayered_of_lawful hLawful)

end LayeringAtomArrangementLaw

/-- Projection soundness read as an atom arrangement law. -/
structure ProjectionAtomArrangementLaw
    {C : Type u} {A : Type q} {E : Type v} {D : Type w}
    (G : ArchGraph C)
    (π : InterfaceProjection C A)
    (GA : AbstractGraph A)
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  lawfulnessImpliesProjectionSound :
    LawfulWithinAtomConfiguration law requiredMolecule ->
      ProjectionSound G π GA
  projectionFailureExposesBadMolecule :
    ∀ edge, ProjectionObstruction G π GA edge ->
      ∃ M, requiredMolecule M ∧ law.Bad M
  obstructionCircuitBoundary : Prop
  nonConclusions : Prop

namespace ProjectionAtomArrangementLaw

theorem projectionSound_of_lawful
    {C : Type u} {A : Type q} {E : Type v} {D : Type w}
    {G : ArchGraph C}
    {π : InterfaceProjection C A}
    {GA : AbstractGraph A}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : ProjectionAtomArrangementLaw G π GA law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    ProjectionSound G π GA :=
  pkg.lawfulnessImpliesProjectionSound hLawful

theorem noProjectionObstruction_of_lawful
    {C : Type u} {A : Type q} {E : Type v} {D : Type w}
    {G : ArchGraph C}
    {π : InterfaceProjection C A}
    {GA : AbstractGraph A}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : ProjectionAtomArrangementLaw G π GA law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    NoProjectionObstruction G π GA :=
  (projectionSound_iff_noProjectionObstruction.mp
    (pkg.projectionSound_of_lawful hLawful))

end ProjectionAtomArrangementLaw

/-- Observation equivalence read as an atom arrangement law. -/
structure ObservationAtomArrangementLaw
    {Impl : Type u} {Obs : Type q} {C : Type v} {E : Type w} {D : Type r}
    (O : Observation Impl Obs)
    (x y : Impl)
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  lawfulnessImpliesObservationEquivalence :
    LawfulWithinAtomConfiguration law requiredMolecule ->
      ObservationallyEquivalent O x y
  observationBoundary : Prop
  nonConclusions : Prop

namespace ObservationAtomArrangementLaw

theorem observationallyEquivalent_of_lawful
    {Impl : Type u} {Obs : Type q} {C : Type v} {E : Type w} {D : Type r}
    {O : Observation Impl Obs}
    {x y : Impl}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : ObservationAtomArrangementLaw O x y law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    ObservationallyEquivalent O x y :=
  pkg.lawfulnessImpliesObservationEquivalence hLawful

end ObservationAtomArrangementLaw

/-- A boundary leak is represented as a law-relative obstruction circuit candidate. -/
structure BoundaryLeakObstructionCandidate
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  molecule : AtomMolecule C E D
  required : requiredMolecule molecule
  circuit : ObstructionCircuit law molecule
  boundaryEvidence : Prop
  nonConclusions : Prop

/-- A concrete bypass is represented as a law-relative obstruction circuit candidate. -/
structure ConcreteBypassObstructionCandidate
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  molecule : AtomMolecule C E D
  required : requiredMolecule molecule
  circuit : ObstructionCircuit law molecule
  bypassEvidence : Prop
  nonConclusions : Prop

/-- A projection failure is represented as a law-relative obstruction circuit candidate. -/
structure ProjectionFailureObstructionCandidate
    {C : Type u} {A : Type q} {E : Type v} {D : Type w}
    (G : ArchGraph C)
    (π : InterfaceProjection C A)
    (GA : AbstractGraph A)
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  edge : C × C
  projectionFailure : ProjectionObstruction G π GA edge
  molecule : AtomMolecule C E D
  required : requiredMolecule molecule
  circuit : ObstructionCircuit law molecule
  nonConclusions : Prop

theorem boundaryLeakCandidate_bad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (candidate :
      BoundaryLeakObstructionCandidate law requiredMolecule) :
    law.Bad candidate.molecule :=
  obstructionCircuit_bad candidate.circuit

theorem concreteBypassCandidate_bad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (candidate :
      ConcreteBypassObstructionCandidate law requiredMolecule) :
    law.Bad candidate.molecule :=
  obstructionCircuit_bad candidate.circuit

theorem projectionFailureCandidate_bad
    {C : Type u} {A : Type q} {E : Type v} {D : Type w}
    {G : ArchGraph C}
    {π : InterfaceProjection C A}
    {GA : AbstractGraph A}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (candidate :
      ProjectionFailureObstructionCandidate
        G π GA law requiredMolecule) :
    law.Bad candidate.molecule :=
  obstructionCircuit_bad candidate.circuit

/-- A responsibility role carried by a selected atom molecule. -/
structure ResponsibilityRole
    {C : Type u} {E : Type v} {D : Type w}
    (R : Type q) where
  role : R
  molecule : AtomMolecule C E D
  carriedBy : C -> Prop
  roleBoundary : Prop
  nonConclusions : Prop

/--
Responsibility molecule coherence against an existing selected responsibility
boundary.

The role is carried by the molecule; it is not a primitive atom and is not
counted as one.
-/
def ResponsibilityMoleculeCoherent
    {C : Type u} {E : Type v} {D : Type w} {R : Type q}
    (boundary : ResponsibilityBoundary C R)
    (role : ResponsibilityRole (C := C) (E := E) (D := D) R) : Prop :=
  ∀ c, role.carriedBy c -> boundary.owns c role.role

/-- SRP coherence is read as coherent responsibility molecules. -/
def SRPResponsibilityMoleculeCoherent
    {C : Type u} {E : Type v} {D : Type w} {R : Type q}
    (boundary : ResponsibilityBoundary C R)
    (selectedRole : ResponsibilityRole (C := C) (E := E) (D := D) R -> Prop) :
    Prop :=
  ∀ role, selectedRole role -> ResponsibilityMoleculeCoherent boundary role

/--
SRP read as an atom arrangement law.

The package connects selected atom-molecule lawfulness to the existing bounded
SRP surface: total/functional responsibility assignment and edge-local
cohesion.
-/
structure SRPAtomArrangementLaw
    {C : Type u} {E : Type v} {D : Type w} {R : Type q}
    (G : ArchGraph C)
    (boundary : ResponsibilityBoundary C R)
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  lawfulnessImpliesBoundaryTotal :
    LawfulWithinAtomConfiguration law requiredMolecule ->
      boundary.Total
  lawfulnessImpliesBoundaryFunctional :
    LawfulWithinAtomConfiguration law requiredMolecule ->
      boundary.Functional
  lawfulnessImpliesLocalCohesion :
    LawfulWithinAtomConfiguration law requiredMolecule ->
      boundary.EdgeCohesive G
  responsibilityMoleculeBoundary : Prop
  nonConclusions : Prop

namespace SRPAtomArrangementLaw

theorem boundaryTotal_of_lawful
    {C : Type u} {E : Type v} {D : Type w} {R : Type q}
    {G : ArchGraph C}
    {boundary : ResponsibilityBoundary C R}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : SRPAtomArrangementLaw G boundary law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    boundary.Total :=
  pkg.lawfulnessImpliesBoundaryTotal hLawful

theorem boundaryFunctional_of_lawful
    {C : Type u} {E : Type v} {D : Type w} {R : Type q}
    {G : ArchGraph C}
    {boundary : ResponsibilityBoundary C R}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : SRPAtomArrangementLaw G boundary law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    boundary.Functional :=
  pkg.lawfulnessImpliesBoundaryFunctional hLawful

theorem localCohesion_of_lawful
    {C : Type u} {E : Type v} {D : Type w} {R : Type q}
    {G : ArchGraph C}
    {boundary : ResponsibilityBoundary C R}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (pkg : SRPAtomArrangementLaw G boundary law requiredMolecule)
    (hLawful : LawfulWithinAtomConfiguration law requiredMolecule) :
    boundary.EdgeCohesive G :=
  pkg.lawfulnessImpliesLocalCohesion hLawful

end SRPAtomArrangementLaw

/-- SRP failure is represented as a law-relative malformed responsibility molecule. -/
structure SRPFailureObstructionCandidate
    {C : Type u} {E : Type v} {D : Type w} {R : Type q}
    (law : DesignLaw C E D)
    (requiredMolecule : AtomMolecule C E D -> Prop) where
  malformedRole : ResponsibilityRole (C := C) (E := E) (D := D) R
  molecule : AtomMolecule C E D
  required : requiredMolecule molecule
  circuit : ObstructionCircuit law molecule
  srpBoundary : Prop
  nonConclusions : Prop

theorem srpFailureCandidate_bad
    {C : Type u} {E : Type v} {D : Type w} {R : Type q}
    {law : DesignLaw C E D}
    {requiredMolecule : AtomMolecule C E D -> Prop}
    (candidate :
      SRPFailureObstructionCandidate
        (R := R) law requiredMolecule) :
    law.Bad candidate.molecule :=
  obstructionCircuit_bad candidate.circuit

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

/-- Law-relative obstruction-circuit delta between selected atom presentations. -/
structure CircuitDelta
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D) where
  created : AtomMolecule C E D -> Prop
  removed : AtomMolecule C E D -> Prop
  preserved : AtomMolecule C E D -> Prop
  transformed :
    AtomMolecule C E D -> AtomMolecule C E D -> Prop
  createdCircuit :
    ∀ molecule, created molecule -> ObstructionCircuit law molecule
  removedCircuit :
    ∀ molecule, removed molecule -> ObstructionCircuit law molecule
  preservedCircuit :
    ∀ molecule, preserved molecule -> ObstructionCircuit law molecule
  evidenceBoundary : Prop
  nonConclusions : Prop

namespace CircuitDelta

theorem created_bad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    (delta : CircuitDelta law)
    {molecule : AtomMolecule C E D}
    (hCreated : delta.created molecule) :
    law.Bad molecule :=
  obstructionCircuit_bad (delta.createdCircuit molecule hCreated)

theorem removed_bad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    (delta : CircuitDelta law)
    {molecule : AtomMolecule C E D}
    (hRemoved : delta.removed molecule) :
    law.Bad molecule :=
  obstructionCircuit_bad (delta.removedCircuit molecule hRemoved)

theorem preserved_bad
    {C : Type u} {E : Type v} {D : Type w}
    {law : DesignLaw C E D}
    (delta : CircuitDelta law)
    {molecule : AtomMolecule C E D}
    (hPreserved : delta.preserved molecule) :
    law.Bad molecule :=
  obstructionCircuit_bad (delta.preservedCircuit molecule hPreserved)

end CircuitDelta

/-- Selected trace of law-relative obstruction-circuit deltas. -/
structure CircuitTrace
    {C : Type u} {E : Type v} {D : Type w}
    (law : DesignLaw C E D) where
  step : Nat -> CircuitDelta law -> Prop
  finiteBoundary : Prop
  lawRelativeBoundary : Prop
  nonConclusions : Prop

/--
Bridge from AtomTrace / CircuitTrace into a selected SFT ForecastCone boundary.

The bridge records that the SFT cone is read together with atom and circuit
traces. It does not assert forecast correctness, probability, calibration, or
global future safety.
-/
structure AtomTraceForecastBoundary
    {Field : Type s} {Operation : Type q}
    {C : Type u} {E : Type v} {D : Type w}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat)
    (target : Field)
    (path : FieldPath support relation source target)
    (law : DesignLaw C E D) where
  coneMember :
    ForecastCone support relation source horizon target path
  atomTrace : AtomTrace C E D
  circuitTrace : CircuitTrace law
  atomTraceBoundary : Prop
  circuitTraceBoundary : Prop
  governedTraceBoundary : Prop
  typedBoundaryFailure : Prop
  governed_or_typedBoundaryFailure :
    governedTraceBoundary ∨ typedBoundaryFailure
  nonConclusions : Prop

namespace AtomTraceForecastBoundary

def ForecastCorrectnessClaim
    {Field : Type s} {Operation : Type q}
    {C : Type u} {E : Type v} {D : Type w}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source : Field} {horizon : Nat}
    {target : Field}
    {path : FieldPath support relation source target}
    {law : DesignLaw C E D}
    (_bridge :
      AtomTraceForecastBoundary
        support relation source horizon target path law) : Prop :=
  False

theorem forecastCone
    {Field : Type s} {Operation : Type q}
    {C : Type u} {E : Type v} {D : Type w}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source : Field} {horizon : Nat}
    {target : Field}
    {path : FieldPath support relation source target}
    {law : DesignLaw C E D}
    (bridge :
      AtomTraceForecastBoundary
        support relation source horizon target path law) :
    ForecastCone support relation source horizon target path :=
  bridge.coneMember

theorem length_le_horizon
    {Field : Type s} {Operation : Type q}
    {C : Type u} {E : Type v} {D : Type w}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source : Field} {horizon : Nat}
    {target : Field}
    {path : FieldPath support relation source target}
    {law : DesignLaw C E D}
    (bridge :
      AtomTraceForecastBoundary
        support relation source horizon target path law) :
    ArchitecturePath.length path <= horizon :=
  ForecastCone.length_le_horizon bridge.coneMember

theorem governed_or_typedBoundaryFailure_recorded
    {Field : Type s} {Operation : Type q}
    {C : Type u} {E : Type v} {D : Type w}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source : Field} {horizon : Nat}
    {target : Field}
    {path : FieldPath support relation source target}
    {law : DesignLaw C E D}
    (bridge :
      AtomTraceForecastBoundary
        support relation source horizon target path law) :
    bridge.governedTraceBoundary ∨ bridge.typedBoundaryFailure :=
  bridge.governed_or_typedBoundaryFailure

theorem records_no_forecast_correctness
    {Field : Type s} {Operation : Type q}
    {C : Type u} {E : Type v} {D : Type w}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source : Field} {horizon : Nat}
    {target : Field}
    {path : FieldPath support relation source target}
    {law : DesignLaw C E D}
    (bridge :
      AtomTraceForecastBoundary
        support relation source horizon target path law) :
    ¬ ForecastCorrectnessClaim bridge := by
  intro h
  exact h

end AtomTraceForecastBoundary

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
