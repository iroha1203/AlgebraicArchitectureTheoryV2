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

The law data, local evidence, and descent/integration boundary are all explicit.
-/
structure ForceIntegrationData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} {St : StateTransitionPresheaf T}
    (F : Force St) where
  globalTemporalLaw : TemporalLaw St
  localLawData : Prop
  localLawData_cert : localLawData
  descendsToGlobalTemporalLaw : Prop
  descendsToGlobalTemporalLaw_cert : descendsToGlobalTemporalLaw
  forceRespectsGlobalLaw : Prop
  forceRespectsGlobalLaw_cert : forceRespectsGlobalLaw

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
  nonintegrable_of_nonzero :
    selectedNonzero C.obstructionClass -> ¬ IntegrableForce F

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
IX.定理候補7.2 / AC19: statement-only obstruction reading.

Given the selected nonzero obstruction and the candidate detection assumptions,
the package reads non-integrability of the selected force.
-/
theorem candidate_not_integrable_of_obstruction
    (O : ForceIntegrabilityObstructionCandidate C) :
    ¬ IntegrableForce F :=
  O.nonintegrable_of_nonzero O.obstruction_nonzero

end ForceIntegrabilityObstructionCandidate

end Evolution
end AAT.AG
