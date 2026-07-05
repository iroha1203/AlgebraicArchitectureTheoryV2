import Formal.AG.Evolution.ReplayDescent

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
PRD-9 R9 / AC18--AC19 force and force-integrability obstruction candidate.

Forces are selected temporal state morphisms inside one selected temporal
site.  Integrability is a selected local-to-global evidence predicate, and the
obstruction theorem is kept as a statement-only candidate whose detection
assumptions are explicit fields.  This file does not prove a general force
integrability theorem and does not forecast unselected transitions.
-/

/--
IX.定義7.1 / AC18: selected force between two temporal states.

The force is represented as a selected cross-point state morphism along a
selected incidence leg of `Tr_E × X`.  The morphism is scoped to the selected
source/target states and does not assert anything about unselected runtime
transitions.
-/
structure Force {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (St : StateTransitionPresheaf T) where
  source : T.Point
  target : T.Point
  sourceState : St.State source
  targetState : St.State target
  incidence : T.IncidenceLeg source target
  stateMorphism : St.State source -> St.State target
  stateMorphism_hits_target : stateMorphism sourceState = targetState
  selectedForce : Prop
  selectedForce_cert : selectedForce

namespace Force

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}

/-- IX.定義7.1 / AC18: read the selected temporal incidence of a force. -/
def selectedIncidence (F : Force St) :
    T.IncidenceLeg F.source F.target :=
  F.incidence

/-- IX.定義7.1 / AC18: the selected force morphism sends source state to target state. -/
theorem maps_source_to_target (F : Force St) :
    F.stateMorphism F.sourceState = F.targetState :=
  F.stateMorphism_hits_target

/-- IX.定義7.1 / AC18: force selection is explicit input data. -/
theorem selected (F : Force St) : F.selectedForce :=
  F.selectedForce_cert

end Force

/--
IX.定義7.1 / AC18: evidence that a force integrates to selected global
temporal law data.

The law data, selected replay descent interface, and global replay transition
are all explicit.  A force is integrable only when the selected force points are
identified with the base source/target of a replay descent package and the
global replay sends the selected source state to the selected target state.
-/
structure ForceIntegrationData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    (F : Force St) where
  globalTemporalLaw : TemporalLaw St
  coefficient : TemporalCoefficient T
  replayData : ReplayDescentData St coefficient globalTemporalLaw
  descentCriterion : TemporalDescentCriterion replayData
  globalReplayTransition : replayData.GlobalReplayTransition
  replaySource_eq : F.source = (replayData.sourceTrace, replayData.cover.baseContext)
  replayTarget_eq : F.target = (replayData.targetTrace, replayData.cover.baseContext)
  globalReplay_hits_force :
    globalReplayTransition (replaySource_eq ▸ F.sourceState) =
      (replayTarget_eq ▸ F.targetState)
  localLawData : Prop
  localLawData_cert : localLawData
  descendsToGlobalTemporalLaw : Prop
  descendsToGlobalTemporalLaw_cert : descendsToGlobalTemporalLaw
  lawWitness : globalTemporalLaw.Witness
  lawSource_eq : globalTemporalLaw.source lawWitness = F.source
  lawTarget_eq : globalTemporalLaw.target lawWitness = F.target
  forceRespectsGlobalLaw :
    globalTemporalLaw.stateEquation lawWitness
      (lawSource_eq.symm ▸ F.sourceState)
      (lawTarget_eq.symm ▸ F.targetState)

/-- IX.定義7.1 / AC18: selected integrability predicate for a force. -/
def IntegrableForce {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    (F : Force St) : Prop :=
  Nonempty (ForceIntegrationData F)

namespace ForceIntegrationData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {F : Force St}

/-- IX.定義7.1 / AC18: integration data witnesses `IntegrableForce`. -/
theorem integrable (D : ForceIntegrationData F) :
    IntegrableForce F :=
  ⟨D⟩

/-- IX.定義7.1 / AC18: read the local law data certificate. -/
theorem local_law_data_holds (D : ForceIntegrationData F) :
    D.localLawData :=
  D.localLawData_cert

/-- IX.定義7.1 / AC18: read the selected global descent/integration certificate. -/
theorem descends_to_global_temporal_law (D : ForceIntegrationData F) :
    D.descendsToGlobalTemporalLaw :=
  D.descendsToGlobalTemporalLaw_cert

/-- IX.定義7.1 / AC18: the R5 theorem-4.2 package yields a global replay transition. -/
theorem temporal_descent_criterion_holds (D : ForceIntegrationData F) :
    Nonempty D.replayData.GlobalReplayTransition :=
  D.descentCriterion.temporal_descent_criterion

/--
IX.定義7.1 / AC18: the selected global replay transition realizes the force on
the selected source/target states.
-/
theorem global_replay_hits_force (D : ForceIntegrationData F) :
    D.globalReplayTransition (D.replaySource_eq ▸ F.sourceState) =
      (D.replayTarget_eq ▸ F.targetState) :=
  D.globalReplay_hits_force

/--
IX.定義7.1 / AC18: the selected force source/target states satisfy the selected
global temporal law equation.
-/
theorem force_respects_global_law (D : ForceIntegrationData F) :
    D.globalTemporalLaw.stateEquation D.lawWitness
      (D.lawSource_eq.symm ▸ F.sourceState)
      (D.lawTarget_eq.symm ▸ F.targetState) :=
  D.forceRespectsGlobalLaw

end ForceIntegrationData

/--
IX.定義7.1 / AC18: force mismatch class.

This ties a selected force to a concrete degree-one temporal mismatch and its
selected temporal cohomology class.  The degree-one condition and construction
soundness are explicit assumptions; a bare nonzero cohomology group is not read
as a force obstruction.
-/
structure ForceMismatchClass {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    (F : Force St) where
  mismatch : TemporalMismatch Coeff Law
  temporalClass : TemporalClass mismatch
  degree_one : mismatch.degree = 1
  traceProductSiteFixed : Prop
  traceProductSiteFixed_cert : traceProductSiteFixed
  mismatchConstructedFromForce : Prop
  mismatchConstructedFromForce_cert : mismatchConstructedFromForce

namespace ForceMismatchClass

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {F : Force St}

/-- IX.定義7.1 / AC18: read the force obstruction class. -/
def obstructionClass (C : ForceMismatchClass (Coeff := Coeff) (Law := Law) F) :
    C.mismatch.bridge.siteComplex.CoverRelativeHn C.mismatch.degree :=
  C.temporalClass.cohomologyClass

/-- IX.定義7.1 / AC18: the selected force mismatch is degree one. -/
theorem mismatch_degree_one
    (C : ForceMismatchClass (Coeff := Coeff) (Law := Law) F) :
    C.mismatch.degree = 1 :=
  C.degree_one

/-- IX.定義7.1 / AC18: the product/incidence site is explicitly fixed. -/
theorem trace_product_site_fixed
    (C : ForceMismatchClass (Coeff := Coeff) (Law := Law) F) :
    C.traceProductSiteFixed :=
  C.traceProductSiteFixed_cert

/-- IX.定義7.1 / AC18: the mismatch construction is explicitly tied to the force. -/
theorem mismatch_constructed_from_force
    (C : ForceMismatchClass (Coeff := Coeff) (Law := Law) F) :
    C.mismatchConstructedFromForce :=
  C.mismatchConstructedFromForce_cert

end ForceMismatchClass

/--
IX.定理候補7.2 / AC18: inhabitable selected data for the force-integrability
obstruction candidate.

This is the candidate-data layer: it records the selected nonzero marker
and detection assumptions, but it does not require or prove the theorem
statement `ob(F) != 0 -> not IntegrableForce F`.
-/
structure ForceIntegrabilityObstructionCandidateData
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    {F : Force St} (C : ForceMismatchClass (Coeff := Coeff) (Law := Law) F) where
  selectedNonzero :
    C.mismatch.bridge.siteComplex.CoverRelativeHn C.mismatch.degree -> Prop
  obstruction_nonzero : selectedNonzero C.obstructionClass
  coefficientExactness : Prop
  coefficientExactness_cert : coefficientExactness
  witnessCoverage : Prop
  witnessCoverage_cert : witnessCoverage
  temporalDescentDetecting : Prop
  temporalDescentDetecting_cert : temporalDescentDetecting
  localToGlobalControlledByDescent : Prop
  localToGlobalControlledByDescent_cert : localToGlobalControlledByDescent

namespace ForceIntegrabilityObstructionCandidateData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {F : Force St}
variable {C : ForceMismatchClass (Coeff := Coeff) (Law := Law) F}

/-- IX.定理候補7.2 / AC18: read the selected nonzero marker data. -/
theorem obstruction_nonzero_holds
    (O : ForceIntegrabilityObstructionCandidateData C) :
    O.selectedNonzero C.obstructionClass :=
  O.obstruction_nonzero

/-- IX.定理候補7.2 / AC18: coefficient exactness is selected candidate data. -/
theorem coefficient_exactness_holds
    (O : ForceIntegrabilityObstructionCandidateData C) :
    O.coefficientExactness :=
  O.coefficientExactness_cert

/-- IX.定理候補7.2 / AC18: witness coverage is selected candidate data. -/
theorem witness_coverage_holds
    (O : ForceIntegrabilityObstructionCandidateData C) :
    O.witnessCoverage :=
  O.witnessCoverage_cert

/-- IX.定理候補7.2 / AC18: temporal descent detection is selected candidate data. -/
theorem temporal_descent_detecting_holds
    (O : ForceIntegrabilityObstructionCandidateData C) :
    O.temporalDescentDetecting :=
  O.temporalDescentDetecting_cert

/--
IX.定理候補7.2 / AC18: the unproved theorem statement associated with the
selected candidate data.
-/
def nonintegrabilityStatement
    (O : ForceIntegrabilityObstructionCandidateData C) : Prop :=
  O.selectedNonzero C.obstructionClass -> ¬ IntegrableForce F

end ForceIntegrabilityObstructionCandidateData

/--
IX.定理候補7.2 / AC19: force integrability obstruction candidate.

The central implication `ob(F) != 0 -> not IntegrableForce F` is a selected
candidate statement.  Its detection power is not proved here; it is an explicit
assumption, together with coefficient exactness, witness coverage, and
local-to-global control by the selected temporal descent interface.
-/
structure ForceIntegrabilityObstructionCandidate
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    {Coeff : TemporalCoefficient T} {Law : TemporalLaw St}
    {F : Force St} (C : ForceMismatchClass (Coeff := Coeff) (Law := Law) F) where
  selectedNonzero :
    C.mismatch.bridge.siteComplex.CoverRelativeHn C.mismatch.degree -> Prop
  obstruction_nonzero : selectedNonzero C.obstructionClass
  coefficientExactness : Prop
  coefficientExactness_cert : coefficientExactness
  witnessCoverage : Prop
  witnessCoverage_cert : witnessCoverage
  temporalDescentDetecting : Prop
  temporalDescentDetecting_cert : temporalDescentDetecting
  localToGlobalControlledByDescent : Prop
  localToGlobalControlledByDescent_cert : localToGlobalControlledByDescent
  nonintegrabilityStatement : Prop
  nonintegrabilityStatement_cert : nonintegrabilityStatement

namespace ForceIntegrabilityObstructionCandidate

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {St : StateTransitionPresheaf T}
variable {Coeff : TemporalCoefficient T}
variable {Law : TemporalLaw St}
variable {F : Force St}
variable {C : ForceMismatchClass (Coeff := Coeff) (Law := Law) F}

/-- IX.定理候補7.2 / AC19: read the selected nonzero obstruction witness. -/
theorem obstruction_nonzero_holds
    (O : ForceIntegrabilityObstructionCandidate C) :
    O.selectedNonzero C.obstructionClass :=
  O.obstruction_nonzero

/-- IX.定理候補7.2 / AC19: coefficient exactness is an explicit candidate assumption. -/
theorem coefficient_exactness_holds
    (O : ForceIntegrabilityObstructionCandidate C) :
    O.coefficientExactness :=
  O.coefficientExactness_cert

/-- IX.定理候補7.2 / AC19: temporal descent detection is an explicit candidate assumption. -/
theorem temporal_descent_detecting_holds
    (O : ForceIntegrabilityObstructionCandidate C) :
    O.temporalDescentDetecting :=
  O.temporalDescentDetecting_cert

/--
IX.定理候補7.2 / AC19: the selected non-integrability statement is recorded
as candidate data.  This does not prove the general implication
`ob(F) != 0 -> not IntegrableForce F`.
-/
theorem candidate_statement_recorded
    (O : ForceIntegrabilityObstructionCandidate C) :
    O.nonintegrabilityStatement :=
  O.nonintegrabilityStatement_cert

end ForceIntegrabilityObstructionCandidate

end Evolution
end AAT.AG
