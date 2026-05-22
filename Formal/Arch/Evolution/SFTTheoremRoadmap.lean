import Formal.Arch.Evolution.SFTArtifactAction
import Formal.Arch.Evolution.SFTEnvelope
import Formal.Arch.Evolution.SFTPolicy
import Formal.Arch.Evolution.SFTReachability
import Formal.Arch.Evolution.SFTDescent
import Formal.Arch.Evolution.SFTFiniteCover
import Formal.Arch.Evolution.SFTDescentObstruction

/-!
Lean entrypoints for `docs/sft/sft_theorem_roadmap_and_research_vision.md`.

The roadmap contains theorem-scale research claims.  This module formalizes
their checked Lean surface in the same style as the rest of the SFT core:
strong claims are never asserted unconditionally.  Each theorem is represented
as explicit hypotheses, boundary records, and proved accessors from those
hypotheses.  The exact shared-clock `ClockedForecastCone` core is implemented
in `SFTClockedCone`; this module keeps the roadmap-scale theorem surfaces and
selected constructor theorems.
-/

namespace Formal.Arch

universe u v w x y z a b

namespace SFTTheoremRoadmap

/-- A small equivalence witness used by roadmap theorem packages. -/
structure BidirectionalEquivalence (α : Type u) (β : Type v) where
  toFun : α -> β
  invFun : β -> α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

namespace BidirectionalEquivalence

/-- The inverse direction of a bidirectional equivalence. -/
def symm {α : Type u} {β : Type v}
    (equiv : BidirectionalEquivalence α β) :
    BidirectionalEquivalence β α where
  toFun := equiv.invFun
  invFun := equiv.toFun
  left_inv := equiv.right_inv
  right_inv := equiv.left_inv

end BidirectionalEquivalence

/-! ## Architecture covers and ForecastCone descent -/

/-- A finite architecture cover, with overlap and boundary assumptions explicit. -/
structure FiniteArchitectureCover (Region : Type u) where
  regions : List Region
  coversGlobal : Prop
  overlapsFinite : Prop
  interfaceBoundary : Prop
  nonConclusions : Prop

namespace FiniteArchitectureCover

/-- The selected cover records that its regions cover the global field. -/
def RecordsCoverage
    {Region : Type u} (cover : FiniteArchitectureCover Region) : Prop :=
  cover.coversGlobal

/-- The selected cover records finite-overlap assumptions. -/
def RecordsFiniteOverlaps
    {Region : Type u} (cover : FiniteArchitectureCover Region) : Prop :=
  cover.overlapsFinite

/-- The selected cover keeps interface-boundary assumptions explicit. -/
def RecordsInterfaceBoundary
    {Region : Type u} (cover : FiniteArchitectureCover Region) : Prop :=
  cover.interfaceBoundary

/-- Cover-level non-conclusions remain explicit. -/
def RecordsNonConclusions
    {Region : Type u} (cover : FiniteArchitectureCover Region) : Prop :=
  cover.nonConclusions

end FiniteArchitectureCover

/--
ForecastCone descent package for a selected clocked cone.

The compatible local family is abstract: later developments can instantiate it
with Cech nerves, binary pullbacks, or implementation-specific cover data.
-/
structure ClockedForecastConeDescentPackage
    {Field : Type u} {Operation : Type v} {Region : Type w}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (cover : FiniteArchitectureCover Region)
    (source : Field) (horizon : Nat) where
  compatibleLocalFamily : Type x
  descentEquiv :
    BidirectionalEquivalence
      (ClockedConePoint support relation source horizon)
      compatibleLocalFamily
  supportDescentBoundary : Prop
  policyDescentBoundary : Prop
  stepDescentBoundary : Prop
  observationBoundary : Prop
  idleBoundary : Prop
  nonConclusions : Prop

namespace ClockedForecastConeDescentPackage

variable {Field : Type u} {Operation : Type v} {Region : Type w}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {cover : FiniteArchitectureCover Region}
variable {source : Field} {horizon : Nat}

/-- The equivalence witness for global clocked cones and compatible local families. -/
def forecastCone_descent_equiv
    (package :
      ClockedForecastConeDescentPackage support relation cover source horizon) :
    BidirectionalEquivalence
      (ClockedConePoint support relation source horizon)
      package.compatibleLocalFamily :=
  package.descentEquiv

/--
Descent witness accessor: the package stores the selected equivalence between
global clocked cones and compatible local families, and this theorem exposes
that witness as a proposition.  It is a theorem-package surface, not an
unconditional derivation of descent.
-/
theorem forecastCone_descent
    (package :
      ClockedForecastConeDescentPackage support relation cover source horizon) :
    Nonempty
      (BidirectionalEquivalence
        (ClockedConePoint support relation source horizon)
        package.compatibleLocalFamily) :=
  ⟨package.descentEquiv⟩

/-- Descent preserves the explicit idle/stutter boundary required by clocked cones. -/
def RecordsIdleBoundary
    (package :
      ClockedForecastConeDescentPackage support relation cover source horizon) :
    Prop :=
  package.idleBoundary

/-- Descent-package non-conclusions stay explicit. -/
def RecordsNonConclusions
    (package :
      ClockedForecastConeDescentPackage support relation cover source horizon) :
    Prop :=
  package.nonConclusions ∧ cover.RecordsNonConclusions ∧
    support.RecordsNonConclusions ∧ relation.RecordsNonConclusions

end ClockedForecastConeDescentPackage

/-- Binary pullback of two cone families over a shared interface cone family. -/
structure BinaryConePullback
    (LeftCone : Type u) (InterfaceCone : Type v) (RightCone : Type w)
    (leftToInterface : LeftCone -> InterfaceCone)
    (rightToInterface : RightCone -> InterfaceCone) where
  left : LeftCone
  right : RightCone
  compatible : leftToInterface left = rightToInterface right

/-- Binary form of ForecastCone descent over `G = A union_I B`. -/
structure BinaryForecastConeDescentPackage
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (source : Field) (horizon : Nat) where
  leftCone : Type w
  interfaceCone : Type x
  rightCone : Type y
  leftToInterface : leftCone -> interfaceCone
  rightToInterface : rightCone -> interfaceCone
  binaryDescentEquiv :
    BidirectionalEquivalence
      (ClockedConePoint support relation source horizon)
      (BinaryConePullback leftCone interfaceCone rightCone
        leftToInterface rightToInterface)
  binaryCoverBoundary : Prop
  nonConclusions : Prop

namespace BinaryForecastConeDescentPackage

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {source : Field} {horizon : Nat}

/-- The binary descent equivalence witness. -/
def forecastCone_binary_descent_equiv
    (package :
      BinaryForecastConeDescentPackage support relation source horizon) :
    BidirectionalEquivalence
      (ClockedConePoint support relation source horizon)
      (BinaryConePullback package.leftCone package.interfaceCone
        package.rightCone package.leftToInterface package.rightToInterface) :=
  package.binaryDescentEquiv

/-- Binary descent theorem: a global clocked cone is equivalent to an interface pullback. -/
theorem forecastCone_binary_descent
    (package :
      BinaryForecastConeDescentPackage support relation source horizon) :
    Nonempty
      (BidirectionalEquivalence
        (ClockedConePoint support relation source horizon)
        (BinaryConePullback package.leftCone package.interfaceCone
          package.rightCone package.leftToInterface package.rightToInterface)) :=
  ⟨package.binaryDescentEquiv⟩

end BinaryForecastConeDescentPackage

/--
Binary descent package existence from concrete step gluing data and endpoint
projection/glue laws.

This is the roadmap-facing surface for the endpoint-law constructor in
`SFTDescent`: it does not assert unconditional descent, and it does not promote
endpoint relatedness to strict dependent path equality.
-/
theorem binaryForecastConeDescent_of_endpoint_laws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    Nonempty (BinarySelectedForecastConeDescentPackage model source horizon) :=
  binaryForecastConeDescentPackage_of_endpoint_laws glueData laws

/--
Binary descent package existence from concrete step gluing data and selected
path-level projection/glue inverse laws.

This is still binary descent, relative to selected path equivalence data.  It is
not finite-cover descent, and it is not the full Fundamental Modularity Theorem.
-/
theorem binaryForecastConeDescent_of_path_laws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat} :
    Nonempty (BinarySelectedForecastConeDescentPackage model source horizon) :=
  binaryForecastConeDescentPackage_of_path_laws glueData pathLaws

/--
Finite-cover selected descent from explicit finite gluing and Cech-style
compatibility laws.

This is finite-cover selected descent.  It is not a proof that every finite
cover satisfies descent.  It is not full Cech cohomology, and it is not the
Fundamental Modularity Theorem.
-/
theorem finiteForecastConeDescent_of_laws
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    (glueData : FiniteClockedGluingData model)
    (laws : FiniteProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    Nonempty (FiniteSelectedForecastConeDescentPackage model source horizon) :=
  finiteForecastConeDescentPackage_of_laws glueData laws

/--
Selected finite descent failure is connected to selected governance cutting.

This assumes classifier completeness and selected governance cutting laws.  It
is not operational governance effectiveness, and it is not the full Fundamental
Modularity Theorem.
-/
theorem finite_governance_cuts_obstruction_of_failure
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    {model : FiniteSFTModel cover OperationG OperationL}
    {source : Global} {horizon : Nat}
    (package :
      FiniteObstructionGovernancePackage model source horizon)
    (failure : FiniteDescentFailure model source horizon)
    (hBadClassified :
      ∀ witness,
        package.obstructionPackage.classifier.classify failure =
          some witness ->
        package.governancePackage.target.bad witness) :
    ∃ witness : FiniteDescentObstructionWitness model source horizon,
      package.obstructionPackage.classifier.classify failure = some witness ∧
        package.governancePackage.cutsBad
          package.governancePackage.selectedIntervention witness :=
  governance_cuts_obstruction_of_finite_failure
    package failure hBadClassified

/-! ## 5.1 Modularity representation -/

/-- The three equivalent readings of an SFT module boundary. -/
structure ModularityRepresentationPackage where
  moduleBoundary : Prop
  forecastConeDescentForAll : Prop
  uniqueCompatiblePathRepresentation : Prop
  boundary_iff_descent :
    moduleBoundary ↔ forecastConeDescentForAll
  descent_iff_uniqueRepresentation :
    forecastConeDescentForAll ↔ uniqueCompatiblePathRepresentation
  theoremBoundary : Prop
  nonConclusions : Prop

namespace ModularityRepresentationPackage

/-- Modularity is equivalent to descent plus unique compatible representation. -/
theorem modularity_representation
    (package : ModularityRepresentationPackage) :
    package.moduleBoundary ↔
      package.forecastConeDescentForAll ∧
        package.uniqueCompatiblePathRepresentation := by
  constructor
  · intro hModule
    have hDescent := package.boundary_iff_descent.mp hModule
    exact ⟨hDescent, package.descent_iff_uniqueRepresentation.mp hDescent⟩
  · intro hBoth
    exact package.boundary_iff_descent.mpr hBoth.1

/-- The sheaf/descent reading of modularity is available directly. -/
theorem modularity_iff_forecastCone_descent
    (package : ModularityRepresentationPackage) :
    package.moduleBoundary ↔ package.forecastConeDescentForAll :=
  package.boundary_iff_descent

end ModularityRepresentationPackage

/-! ## 5.2 Descent obstruction -/

/-- Typed classes of descent failures from the roadmap. -/
inductive DescentFailureKind where
  | hiddenCoupling
  | missingInterfaceInvariant
  | unsupportedGlobalOperation
  | policyConflict
  | observationBoundaryLeak
  | unknownRemainderExpansion
  | surjectivityFailure
  | injectivityFailure
  deriving DecidableEq, Repr

/-- A typed witness explaining how ForecastCone descent failed. -/
structure DescentObstructionWitness (Payload : Type u) where
  kind : DescentFailureKind
  payload : Payload
  boundary : Prop
  nonConclusions : Prop

/-- The global-to-local cone comparison map used to classify descent failures. -/
structure GlobalToLocalConeMap (GlobalCone : Type u) (LocalFamily : Type v) where
  toLocal : GlobalCone -> LocalFamily
  mapBoundary : Prop
  nonConclusions : Prop

/-- Locally compatible futures may fail to lift to a global future. -/
def SurjectivityFailure
    {GlobalCone : Type u} {LocalFamily : Type v}
    (coneMap : GlobalToLocalConeMap GlobalCone LocalFamily) : Prop :=
  ∃ localFamily : LocalFamily,
    ∀ global : GlobalCone, coneMap.toLocal global ≠ localFamily

/-- Globally distinct futures may look identical locally. -/
def InjectivityFailure
    {GlobalCone : Type u} {LocalFamily : Type v}
    (coneMap : GlobalToLocalConeMap GlobalCone LocalFamily) : Prop :=
  ∃ global₁ global₂ : GlobalCone,
    global₁ ≠ global₂ ∧ coneMap.toLocal global₁ = coneMap.toLocal global₂

/-- Descent obstruction theorem package. -/
structure DescentObstructionPackage
    {GlobalCone : Type u} {LocalFamily : Type v}
    (coneMap : GlobalToLocalConeMap GlobalCone LocalFamily)
    (Payload : Type w) where
  witnessOfSurjectivityFailure :
    SurjectivityFailure coneMap -> DescentObstructionWitness Payload
  witnessOfInjectivityFailure :
    InjectivityFailure coneMap -> DescentObstructionWitness Payload
  surjectivityWitnessKind :
    ∀ hFailure,
      (witnessOfSurjectivityFailure hFailure).kind =
        DescentFailureKind.surjectivityFailure
  injectivityWitnessKind :
    ∀ hFailure,
      (witnessOfInjectivityFailure hFailure).kind =
        DescentFailureKind.injectivityFailure
  obstructionBoundary : Prop
  nonConclusions : Prop

namespace DescentObstructionPackage

variable {GlobalCone : Type u} {LocalFamily : Type v}
variable {coneMap : GlobalToLocalConeMap GlobalCone LocalFamily}
variable {Payload : Type w}

/-- A lift failure yields a typed descent-obstruction witness. -/
theorem descent_obstruction_of_surjectivity_failure
    (package : DescentObstructionPackage coneMap Payload)
    (hFailure : SurjectivityFailure coneMap) :
    ∃ witness : DescentObstructionWitness Payload,
      witness.kind = DescentFailureKind.surjectivityFailure :=
  ⟨package.witnessOfSurjectivityFailure hFailure,
    package.surjectivityWitnessKind hFailure⟩

/-- A local-identification failure yields a typed descent-obstruction witness. -/
theorem descent_obstruction_of_injectivity_failure
    (package : DescentObstructionPackage coneMap Payload)
    (hFailure : InjectivityFailure coneMap) :
    ∃ witness : DescentObstructionWitness Payload,
      witness.kind = DescentFailureKind.injectivityFailure :=
  ⟨package.witnessOfInjectivityFailure hFailure,
    package.injectivityWitnessKind hFailure⟩

/-- A concrete no-lift local family is a surjectivity failure. -/
theorem surjectivityFailure_of_localFamilyDoesNotLift
    {GlobalCone : Type u} {LocalFamily : Type v}
    (coneMap : GlobalToLocalConeMap GlobalCone LocalFamily)
    {family : LocalFamily}
    (hNoLift : LocalFamilyDoesNotLift coneMap.toLocal family) :
    SurjectivityFailure coneMap :=
  ⟨family, hNoLift⟩

/-- A concrete local identification is an injectivity failure. -/
theorem injectivityFailure_of_globalPathsLocallyIdentified
    {GlobalCone : Type u} {LocalFamily : Type v}
    (coneMap : GlobalToLocalConeMap GlobalCone LocalFamily)
    {global₁ global₂ : GlobalCone}
    (hIdentified :
      GlobalPathsLocallyIdentified coneMap.toLocal global₁ global₂) :
    InjectivityFailure coneMap :=
  ⟨global₁, global₂, hIdentified⟩

/-- A no-lift local family yields a typed descent obstruction under the selected classifier. -/
theorem obstruction_of_no_lift
    (package : DescentObstructionPackage coneMap Payload)
    {family : LocalFamily}
    (hNoLift : LocalFamilyDoesNotLift coneMap.toLocal family) :
    ∃ witness : DescentObstructionWitness Payload,
      witness.kind = DescentFailureKind.surjectivityFailure :=
  package.descent_obstruction_of_surjectivity_failure
    (surjectivityFailure_of_localFamilyDoesNotLift coneMap hNoLift)

/-- A concrete local identification yields a typed descent obstruction. -/
theorem obstruction_of_local_identification
    (package : DescentObstructionPackage coneMap Payload)
    {global₁ global₂ : GlobalCone}
    (hIdentified :
      GlobalPathsLocallyIdentified coneMap.toLocal global₁ global₂) :
    ∃ witness : DescentObstructionWitness Payload,
      witness.kind = DescentFailureKind.injectivityFailure :=
  package.descent_obstruction_of_injectivity_failure
    (injectivityFailure_of_globalPathsLocallyIdentified coneMap hIdentified)

end DescentObstructionPackage

/-! ## 5.3 Cone cohomology -/

/-- Cech-style cohomology vocabulary for a selected cone presheaf. -/
structure ConeCohomologyPackage where
  H0 : Prop
  H1Vanishes : Prop
  H2Boundary : Prop
  globalReachableFutures : Prop
  allCompatibleLocalFuturesGlue : Prop
  h0_iff_globalReachableFutures : H0 ↔ globalReachableFutures
  h1_vanishes_iff_allCompatibleLocalFuturesGlue :
    H1Vanishes ↔ allCompatibleLocalFuturesGlue
  cohomologyBoundary : Prop
  nonConclusions : Prop

namespace ConeCohomologyPackage

/-- H0 records the selected global reachable futures. -/
theorem h0_global_reachable_futures
    (package : ConeCohomologyPackage) :
    package.H0 ↔ package.globalReachableFutures :=
  package.h0_iff_globalReachableFutures

/-- Vanishing H1 is equivalent to all compatible local futures gluing globally. -/
theorem h1_zero_iff_local_futures_glue
    (package : ConeCohomologyPackage) :
    package.H1Vanishes ↔ package.allCompatibleLocalFuturesGlue :=
  package.h1_vanishes_iff_allCompatibleLocalFuturesGlue

/-- H2 remains the selected higher-compatibility obstruction boundary. -/
def RecordsHigherCompatibilityBoundary
    (package : ConeCohomologyPackage) :
    Prop :=
  package.H2Boundary

end ConeCohomologyPackage

/-! ## 5.4 Evolutionary normal form -/

/-- Normal-form theorem package for supported global evolution paths. -/
structure EvolutionaryNormalFormPackage
    (GlobalPath : Type u) (NormalForm : Type v) where
  forecastConeDescent : Prop
  localCommutationOrConfluence : Prop
  interfaceSynchronizationBoundary : Prop
  normalForm : GlobalPath -> NormalForm
  rewritesTo : GlobalPath -> NormalForm -> Prop
  normalizes :
    forecastConeDescent ->
      localCommutationOrConfluence ->
        ∀ path, rewritesTo path (normalForm path)
  independentPermutationsEquivalent : Prop
  nonConclusions : Prop

namespace EvolutionaryNormalFormPackage

/-- Descent plus local commutation/confluence gives a selected normal form. -/
theorem evolutionary_normal_form
    {GlobalPath : Type u} {NormalForm : Type v}
    (package : EvolutionaryNormalFormPackage GlobalPath NormalForm)
    (hDescent : package.forecastConeDescent)
    (hLocal : package.localCommutationOrConfluence)
    (path : GlobalPath) :
    package.rewritesTo path (package.normalForm path) :=
  package.normalizes hDescent hLocal path

/-- Independent local-step permutations are identified by the selected package. -/
def RecordsIndependentPermutationsEquivalent
    {GlobalPath : Type u} {NormalForm : Type v}
    (package : EvolutionaryNormalFormPackage GlobalPath NormalForm) :
    Prop :=
  package.independentPermutationsEquivalent

end EvolutionaryNormalFormPackage

/-! ## 5.5 Cone-conservative observation -/

/-- An observation is cone-conservative when equal observations imply cone equivalence. -/
def ConeConservativeObservation
    {Field : Type u} {Observation : Type v}
    (observe : Field -> Observation)
    (coneEquivalent : Field -> Field -> Prop) : Prop :=
  ∀ F G, observe F = observe G -> coneEquivalent F G

/-- A collapse witness: two equally observed fields with different future cones. -/
def ConeObservationCollapse
    {Field : Type u} {Observation : Type v}
    (observe : Field -> Observation)
    (coneEquivalent : Field -> Field -> Prop) : Prop :=
  ∃ F G, observe F = observe G ∧ ¬ coneEquivalent F G

/-- If a same-observation cone collapse exists, the observation is not conservative. -/
theorem not_coneConservative_of_observationCollapse
    {Field : Type u} {Observation : Type v}
    {observe : Field -> Observation}
    {coneEquivalent : Field -> Field -> Prop}
    (hCollapse : ConeObservationCollapse observe coneEquivalent) :
    ¬ ConeConservativeObservation observe coneEquivalent := by
  intro hConservative
  rcases hCollapse with ⟨F, G, hSame, hNotEquivalent⟩
  exact hNotEquivalent (hConservative F G hSame)

/-- Classically, failure of cone-conservativity exposes a collapse witness. -/
theorem observationCollapse_of_not_coneConservative
    {Field : Type u} {Observation : Type v}
    {observe : Field -> Observation}
    {coneEquivalent : Field -> Field -> Prop}
    (hNotConservative :
      ¬ ConeConservativeObservation observe coneEquivalent) :
    ConeObservationCollapse observe coneEquivalent := by
  classical
  exact Classical.byContradiction (fun hNoCollapse => by
    apply hNotConservative
    intro F G hSame
    exact Classical.byContradiction (fun hNotEquivalent =>
      hNoCollapse ⟨F, G, hSame, hNotEquivalent⟩))

/-! ## 5.6 Minimal ConsequenceEnvelope -/

/-- A projection is sound when it does not distinguish review-equivalent paths. -/
def DecisionSoundProjection
    {ConePath : Type u} {Envelope : Type v}
    (reviewEquivalent : ConePath -> ConePath -> Prop)
    (projection : ConePath -> Envelope) : Prop :=
  ∀ p q, reviewEquivalent p q -> projection p = projection q

/-- Two cone paths are indistinguishable for a selected decision predicate. -/
def PathIndistinguishableFor
    {ConePath : Type u} {Decision : Type v}
    (Q : ConePath -> Decision -> Prop)
    (p q : ConePath) : Prop :=
  ∀ decision, Q p decision ↔ Q q decision

namespace PathIndistinguishableFor

/-- Decision indistinguishability is reflexive. -/
theorem refl
    {ConePath : Type u} {Decision : Type v}
    (Q : ConePath -> Decision -> Prop)
    (p : ConePath) :
    PathIndistinguishableFor Q p p := by
  intro decision
  exact Iff.rfl

/-- Decision indistinguishability is symmetric. -/
theorem symm
    {ConePath : Type u} {Decision : Type v}
    {Q : ConePath -> Decision -> Prop}
    {p q : ConePath}
    (h : PathIndistinguishableFor Q p q) :
    PathIndistinguishableFor Q q p := by
  intro decision
  exact (h decision).symm

/-- Decision indistinguishability is transitive. -/
theorem trans
    {ConePath : Type u} {Decision : Type v}
    {Q : ConePath -> Decision -> Prop}
    {p q r : ConePath}
    (hpq : PathIndistinguishableFor Q p q)
    (hqr : PathIndistinguishableFor Q q r) :
    PathIndistinguishableFor Q p r := by
  intro decision
  exact Iff.trans (hpq decision) (hqr decision)

end PathIndistinguishableFor

/-- Setoid of paths indistinguishable for a review decision predicate. -/
def ReviewSetoid
    {ConePath : Type u} {Decision : Type v}
    (Q : ConePath -> Decision -> Prop) : Setoid ConePath where
  r := PathIndistinguishableFor Q
  iseqv := by
    constructor
    · exact PathIndistinguishableFor.refl Q
    · intro p q
      exact PathIndistinguishableFor.symm
    · intro p q r
      exact PathIndistinguishableFor.trans

/-- Minimal envelope as the quotient by review indistinguishability. -/
def MinimalEnvelope
    {ConePath : Type u} {Decision : Type v}
    (Q : ConePath -> Decision -> Prop) : Type u :=
  Quotient (ReviewSetoid Q)

/-- A projection respects decision equivalence when it is constant on review classes. -/
def EnvelopeRespectsDecisionEquivalence
    {ConePath : Type u} {Decision : Type v} {Envelope : Type w}
    (Q : ConePath -> Decision -> Prop)
    (projection : ConePath -> Envelope) : Prop :=
  ∀ p q, PathIndistinguishableFor Q p q -> projection p = projection q

/--
An obstruction-aware review projection is constant on the selected review
equivalence classes.

This is a review-envelope boundary predicate, not operational optimality of
the review decision.
-/
def ObstructionAwareReviewEquivalence
    {ConePath : Type u} {Decision : Type v}
    (reviewEquivalent : ConePath -> ConePath -> Prop)
    (obstructionDecision : ConePath -> Decision) : Prop :=
  ∀ p q, reviewEquivalent p q ->
    obstructionDecision p = obstructionDecision q

/-- Obstruction-aware review equivalence is exactly decision-sound projection. -/
theorem decisionSoundProjection_of_obstructionAware
    {ConePath : Type u} {Decision : Type v}
    {reviewEquivalent : ConePath -> ConePath -> Prop}
    {obstructionDecision : ConePath -> Decision}
    (hAware :
      ObstructionAwareReviewEquivalence
        reviewEquivalent obstructionDecision) :
    DecisionSoundProjection reviewEquivalent obstructionDecision :=
  hAware

namespace MinimalEnvelope

/-- The quotient projection is sound for review indistinguishability. -/
theorem minimalEnvelope_sound
    {ConePath : Type u} {Decision : Type v}
    {Q : ConePath -> Decision -> Prop}
    {p q : ConePath}
    (hEquivalent : PathIndistinguishableFor Q p q) :
    Quotient.mk (ReviewSetoid Q) p = Quotient.mk (ReviewSetoid Q) q :=
  Quotient.sound hEquivalent

/-- Quotient equality reflects review indistinguishability. -/
theorem minimalEnvelope_exact
    {ConePath : Type u} {Decision : Type v}
    {Q : ConePath -> Decision -> Prop}
    {p q : ConePath}
    (hEnvelope :
      (Quotient.mk (ReviewSetoid Q) p : MinimalEnvelope Q) =
        Quotient.mk (ReviewSetoid Q) q) :
    PathIndistinguishableFor Q p q :=
  Quotient.exact hEnvelope

/-- Any decision-respecting projection factors through the minimal envelope quotient. -/
def minimalEnvelope_factor
    {ConePath : Type u} {Decision : Type v} {Envelope : Type w}
    (Q : ConePath -> Decision -> Prop)
    (projection : ConePath -> Envelope)
    (hRespects :
      EnvelopeRespectsDecisionEquivalence Q projection) :
    MinimalEnvelope Q -> Envelope :=
  Quotient.lift projection (by
    intro p q hEquivalent
    exact hRespects p q hEquivalent)

/-- The quotient factor computes back to the original projection. -/
theorem minimalEnvelope_factors
    {ConePath : Type u} {Decision : Type v} {Envelope : Type w}
    (Q : ConePath -> Decision -> Prop)
    (projection : ConePath -> Envelope)
    (hRespects :
      EnvelopeRespectsDecisionEquivalence Q projection)
    (path : ConePath) :
    minimalEnvelope_factor Q projection hRespects
      (Quotient.mk (ReviewSetoid Q) path) = projection path :=
  rfl

end MinimalEnvelope

/-- Minimal review envelope package: the quotient-like universal property. -/
structure MinimalConsequenceEnvelopePackage
    (ConePath : Type u) (MinimalEnvelope : Type v) where
  reviewEquivalent : ConePath -> ConePath -> Prop
  projection : ConePath -> MinimalEnvelope
  projection_exact :
    ∀ p q, projection p = projection q ↔ reviewEquivalent p q
  factorsEverySoundEnvelope :
    ∀ (OtherEnvelope : Type w),
      (otherProjection : ConePath -> OtherEnvelope) ->
        DecisionSoundProjection reviewEquivalent otherProjection ->
          ∃ factor : MinimalEnvelope -> OtherEnvelope,
            ∀ path, factor (projection path) = otherProjection path
  envelopeBoundary : Prop
  nonConclusions : Prop

namespace MinimalConsequenceEnvelopePackage

/-- Any other sound review projection factors through the minimal envelope. -/
theorem minimal_consequenceEnvelope_factors
    {ConePath : Type u} {MinimalEnvelope : Type v}
    (package :
      MinimalConsequenceEnvelopePackage.{u, v, w} ConePath MinimalEnvelope)
    {OtherEnvelope : Type w}
    (otherProjection : ConePath -> OtherEnvelope)
    (hSound :
      DecisionSoundProjection package.reviewEquivalent otherProjection) :
    ∃ factor : MinimalEnvelope -> OtherEnvelope,
      ∀ path, factor (package.projection path) = otherProjection path :=
  package.factorsEverySoundEnvelope OtherEnvelope otherProjection hSound

/-- The minimal envelope identifies exactly the selected review-equivalent paths. -/
theorem minimal_consequenceEnvelope_exact
    {ConePath : Type u} {MinimalEnvelope : Type v}
    (package :
      MinimalConsequenceEnvelopePackage ConePath MinimalEnvelope)
    (p q : ConePath) :
    package.projection p = package.projection q ↔
      package.reviewEquivalent p q :=
  package.projection_exact p q

end MinimalConsequenceEnvelopePackage

/-! ## 5.7 Modular attractor -/

/-- Modular attractor theorem package over an existing SFT stable-region core. -/
structure ModularAttractorPackage
    {Field : Type u} {Operation : Type v}
    (support : OperationSupport Field Operation)
    (relation : StepRelation Field Operation)
    (globalTarget : FieldRegion Field) where
  forecastConeDescent : Prop
  localStableTargets : Prop
  overlapCompatibility : Prop
  gluedStableRegion :
    forecastConeDescent ->
      localStableTargets ->
        overlapCompatibility ->
          StableRegion support relation globalTarget
  basinLimitEquivalence : Prop
  nonConclusions : Prop

namespace ModularAttractorPackage

variable {Field : Type u} {Operation : Type v}
variable {support : OperationSupport Field Operation}
variable {relation : StepRelation Field Operation}
variable {globalTarget : FieldRegion Field}

/-- Compatible local stable regions glue to a stable global target region. -/
theorem modular_attractor
    (package :
      ModularAttractorPackage support relation globalTarget)
    (hDescent : package.forecastConeDescent)
    (hLocal : package.localStableTargets)
    (hCompat : package.overlapCompatibility) :
    StableRegion support relation globalTarget :=
  package.gluedStableRegion hDescent hLocal hCompat

/-- The selected basin-limit equivalence boundary is exposed by the package. -/
def RecordsBasinLimitEquivalence
    (package :
      ModularAttractorPackage support relation globalTarget) :
    Prop :=
  package.basinLimitEquivalence

end ModularAttractorPackage

/-! ## 5.8 Governance synthesis -/

/-- A guard family hits every selected bad path. -/
def GuardFamilyHitsBad
    {Path : Type u} {Guard : Type v}
    (bad : Path -> Prop)
    (guardHits : Guard -> Path -> Prop)
    (guardSet : Guard -> Prop) : Prop :=
  ∀ path, bad path -> ∃ guard, guardSet guard ∧ guardHits guard path

/-- A guard family misses every selected desired path. -/
def GuardFamilyMissesDesired
    {Path : Type u} {Guard : Type v}
    (desired : Path -> Prop)
    (guardHits : Guard -> Path -> Prop)
    (guardSet : Guard -> Prop) : Prop :=
  ∀ path, desired path -> ∀ guard, guardSet guard -> ¬ guardHits guard path

/-- Governance synthesis theorem package. -/
structure GovernanceSynthesisPackage
    (Path : Type u) (Guard : Type v) (Intervention : Type w) where
  bad : Path -> Prop
  desired : Path -> Prop
  guardHits : Guard -> Path -> Prop
  interventionPreservesDesired : Intervention -> Prop
  interventionExcludesBad : Intervention -> Prop
  guardFamilySound : (Guard -> Prop) -> Prop
  guardFamilySound_iff_hits_and_misses :
    ∀ guardSet,
      guardFamilySound guardSet ↔
        GuardFamilyHitsBad bad guardHits guardSet ∧
          GuardFamilyMissesDesired desired guardHits guardSet
  synthesisEquivalence :
    (∃ intervention,
      interventionPreservesDesired intervention ∧
        interventionExcludesBad intervention) ↔
      ∃ guardSet : Guard -> Prop, guardFamilySound guardSet
  governanceBoundary : Prop
  nonConclusions : Prop

namespace GovernanceSynthesisPackage

/-- Governance intervention synthesis is equivalent to a separating guard family. -/
theorem governance_synthesis
    {Path : Type u} {Guard : Type v} {Intervention : Type w}
    (package : GovernanceSynthesisPackage Path Guard Intervention) :
    (∃ intervention,
      package.interventionPreservesDesired intervention ∧
        package.interventionExcludesBad intervention) ↔
      ∃ guardSet : Guard -> Prop,
        GuardFamilyHitsBad package.bad package.guardHits guardSet ∧
          GuardFamilyMissesDesired package.desired package.guardHits guardSet := by
  rw [package.synthesisEquivalence]
  constructor
  · intro hGuard
    rcases hGuard with ⟨guardSet, hSound⟩
    exact ⟨guardSet,
      (package.guardFamilySound_iff_hits_and_misses guardSet).mp hSound⟩
  · intro hGuard
    rcases hGuard with ⟨guardSet, hHits, hMisses⟩
    exact ⟨guardSet,
      (package.guardFamilySound_iff_hits_and_misses guardSet).mpr
        ⟨hHits, hMisses⟩⟩

end GovernanceSynthesisPackage

/--
Finite governance synthesis bridge.

The bridge reads an abstract guard/intervention synthesis package over the
sum of finite obstruction witnesses and desired finite cone families as a
selected finite governance cutting package.  It records a selected synthesized
intervention but does not assert real repository governance effectiveness.
-/
structure FiniteGovernanceSynthesisBridge
    {Global : Type u} {Index : Type v} {Local : Type w}
    {cover : UniformFiniteFieldCover Global Index Local}
    {OperationG : Type x} {OperationL : Type y}
    (model : FiniteSFTModel cover OperationG OperationL)
    (source : Global) (horizon : Nat)
    (Guard : Type z) (Intervention : Type a) where
  obstructionPackage :
    FiniteDescentObstructionPackage model source horizon
  target :
    FiniteGovernanceCutTarget model source horizon
  synthesis :
    GovernanceSynthesisPackage
      (Sum
        (FiniteDescentObstructionWitness model source horizon)
        (FiniteLocalClockedConeFamily cover model source horizon))
      Guard Intervention
  guardSet : Guard -> Prop
  guardFamilySound : synthesis.guardFamilySound guardSet
  selectedIntervention : Intervention
  selectedIntervention_synthesized :
    synthesis.interventionPreservesDesired selectedIntervention ∧
      synthesis.interventionExcludesBad selectedIntervention
  bad_matches_target :
    ∀ witness, target.bad witness -> synthesis.bad (Sum.inl witness)
  desired_matches_target :
    ∀ family, target.desiredPreserved family -> synthesis.desired (Sum.inr family)
  synthesisBoundary : Prop
  obstructionToGovernanceBoundary : Prop
  nonConclusions : Prop

namespace FiniteGovernanceSynthesisBridge

variable {Global : Type u} {Index : Type v} {Local : Type w}
variable {cover : UniformFiniteFieldCover Global Index Local}
variable {OperationG : Type x} {OperationL : Type y}
variable {source : Global} {horizon : Nat}
variable {model : FiniteSFTModel cover OperationG OperationL}
variable {Guard : Type z} {Intervention : Type a}

/-- The selected guard family gives an abstract synthesized intervention. -/
theorem synthesized_intervention_of_guard_family
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention) :
    ∃ intervention,
      bridge.synthesis.interventionPreservesDesired intervention ∧
        bridge.synthesis.interventionExcludesBad intervention := by
  exact bridge.synthesis.synthesisEquivalence.mpr
    ⟨bridge.guardSet, bridge.guardFamilySound⟩

/-- The selected guard family records hit/miss completeness. -/
theorem guard_family_hits_and_misses
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention) :
    GuardFamilyHitsBad bridge.synthesis.bad bridge.synthesis.guardHits
        bridge.guardSet ∧
      GuardFamilyMissesDesired bridge.synthesis.desired
        bridge.synthesis.guardHits bridge.guardSet :=
  (bridge.synthesis.guardFamilySound_iff_hits_and_misses
    bridge.guardSet).mp bridge.guardFamilySound

/-- Selected finite bad witnesses are read as abstract bad paths. -/
theorem selected_bad_matches_synthesis_bad
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention)
    (witness : FiniteDescentObstructionWitness model source horizon)
    (hBad : bridge.target.bad witness) :
    bridge.synthesis.bad (Sum.inl witness) :=
  bridge.bad_matches_target witness hBad

/-- Selected desired finite families are read as abstract desired paths. -/
theorem selected_desired_matches_synthesis_desired
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention)
    (family : FiniteLocalClockedConeFamily cover model source horizon)
    (hDesired : bridge.target.desiredPreserved family) :
    bridge.synthesis.desired (Sum.inr family) :=
  bridge.desired_matches_target family hDesired

/-- The selected guard family hits every selected bad finite obstruction. -/
theorem guard_family_hits_selected_bad
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention)
    (witness : FiniteDescentObstructionWitness model source horizon)
    (hBad : bridge.target.bad witness) :
    ∃ guard, bridge.guardSet guard ∧
      bridge.synthesis.guardHits guard (Sum.inl witness) :=
  bridge.guard_family_hits_and_misses.1
    (Sum.inl witness)
    (bridge.selected_bad_matches_synthesis_bad witness hBad)

/-- Read the synthesized intervention as a finite governance cutting package. -/
def governanceCuttingPackage
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention) :
    FiniteGovernanceCuttingPackage model source horizon where
  intervention := Intervention
  target := bridge.target
  cutsBad intervention witness :=
    bridge.synthesis.interventionExcludesBad intervention ∧
      bridge.target.bad witness
  preservesDesired intervention family :=
    bridge.synthesis.interventionPreservesDesired intervention ∧
      bridge.target.desiredPreserved family
  selectedIntervention := bridge.selectedIntervention
  selected_cuts_all_bad := by
    intro witness hBad
    exact ⟨bridge.selectedIntervention_synthesized.2, hBad⟩
  selected_preserves_desired := by
    intro family hDesired
    exact ⟨bridge.selectedIntervention_synthesized.1, hDesired⟩
  governanceBoundary :=
    bridge.synthesisBoundary ∧ bridge.synthesis.governanceBoundary
  nonConclusions :=
    bridge.nonConclusions ∧ bridge.synthesis.nonConclusions ∧
      bridge.target.nonConclusions

/-- Read the synthesized cutting package together with the obstruction package. -/
def obstructionGovernancePackage
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention) :
    FiniteObstructionGovernancePackage model source horizon where
  obstructionPackage := bridge.obstructionPackage
  governancePackage := bridge.governanceCuttingPackage
  obstructionToGovernanceBoundary :=
    bridge.obstructionToGovernanceBoundary
  nonConclusions :=
    bridge.nonConclusions ∧ bridge.obstructionPackage.nonConclusions ∧
      bridge.governanceCuttingPackage.nonConclusions

/-- The synthesized finite package cuts selected bad obstruction witnesses. -/
theorem governanceCuttingPackage_cuts_bad
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention)
    (witness : FiniteDescentObstructionWitness model source horizon)
    (hBad : bridge.target.bad witness) :
    bridge.governanceCuttingPackage.cutsBad
      bridge.governanceCuttingPackage.selectedIntervention witness :=
  finite_governance_cuts_bad_obstruction
    bridge.governanceCuttingPackage witness hBad

/-- The synthesized finite package preserves selected desired cone families. -/
theorem governanceCuttingPackage_preserves_desired
    (bridge :
      FiniteGovernanceSynthesisBridge
        model source horizon Guard Intervention)
    (family : FiniteLocalClockedConeFamily cover model source horizon)
    (hDesired : bridge.target.desiredPreserved family) :
    bridge.governanceCuttingPackage.preservesDesired
      bridge.governanceCuttingPackage.selectedIntervention family :=
  finite_governance_preserves_desired_family
    bridge.governanceCuttingPackage family hDesired

end FiniteGovernanceSynthesisBridge

/-- A support transformation excludes all selected bad paths when after-support admits none of them. -/
def BadPathExcludedBySupportTransformation
    {Path : Type u}
    (bad : Path -> Prop) (afterAdmits : Path -> Prop) : Prop :=
  ∀ path, bad path -> ¬ afterAdmits path

/-- A support transformation preserves all selected desired paths when after-support still admits them. -/
def DesiredPathPreservedBySupportTransformation
    {Path : Type u}
    (desired : Path -> Prop) (afterAdmits : Path -> Prop) : Prop :=
  ∀ path, desired path -> afterAdmits path

/-- A guard basis induces a support restriction when guarded paths are exactly removed. -/
def GuardInducesSupportRestriction
    {Path : Type u} {Guard : Type v}
    (guardHits : Guard -> Path -> Prop)
    (guardSet : Guard -> Prop)
    (beforeAdmits afterAdmits : Path -> Prop) : Prop :=
  ∀ path,
    afterAdmits path ↔
      beforeAdmits path ∧
        ¬ ∃ guard, guardSet guard ∧ guardHits guard path

/-- A complete guard basis excludes all selected bad paths from the after-support. -/
theorem restrictive_governance_excludes_bad
    {Path : Type u} {Guard : Type v}
    {bad beforeAdmits afterAdmits : Path -> Prop}
    {guardHits : Guard -> Path -> Prop}
    {guardSet : Guard -> Prop}
    (hRestricts :
      GuardInducesSupportRestriction guardHits guardSet
        beforeAdmits afterAdmits)
    (hHits :
      GuardFamilyHitsBad bad guardHits guardSet) :
    BadPathExcludedBySupportTransformation bad afterAdmits := by
  intro path hBad hAfter
  have hBeforeAndMiss :=
    (hRestricts path).mp hAfter
  rcases hHits path hBad with ⟨guard, hGuardSet, hHit⟩
  exact hBeforeAndMiss.2 ⟨guard, hGuardSet, hHit⟩

/-- A guard basis preserving desired paths keeps those paths in after-support. -/
theorem restrictive_governance_preserves_desired
    {Path : Type u} {Guard : Type v}
    {desired beforeAdmits afterAdmits : Path -> Prop}
    {guardHits : Guard -> Path -> Prop}
    {guardSet : Guard -> Prop}
    (hRestricts :
      GuardInducesSupportRestriction guardHits guardSet
        beforeAdmits afterAdmits)
    (hDesiredBefore : ∀ path, desired path -> beforeAdmits path)
    (hMisses :
      GuardFamilyMissesDesired desired guardHits guardSet) :
    DesiredPathPreservedBySupportTransformation desired afterAdmits := by
  intro path hDesired
  exact (hRestricts path).mpr
    ⟨hDesiredBefore path hDesired,
      by
        intro hGuard
        rcases hGuard with ⟨guard, hGuardSet, hHit⟩
        exact hMisses path hDesired guard hGuardSet hHit⟩

/-- Guard completeness yields simultaneous bad-path exclusion and desired-path preservation. -/
theorem governance_synthesis_of_guard_basis_complete
    {Path : Type u} {Guard : Type v}
    {bad desired beforeAdmits afterAdmits : Path -> Prop}
    {guardHits : Guard -> Path -> Prop}
    {guardSet : Guard -> Prop}
    (hRestricts :
      GuardInducesSupportRestriction guardHits guardSet
        beforeAdmits afterAdmits)
    (hHits :
      GuardFamilyHitsBad bad guardHits guardSet)
    (hDesiredBefore : ∀ path, desired path -> beforeAdmits path)
    (hMisses :
      GuardFamilyMissesDesired desired guardHits guardSet) :
    BadPathExcludedBySupportTransformation bad afterAdmits ∧
      DesiredPathPreservedBySupportTransformation desired afterAdmits :=
  ⟨restrictive_governance_excludes_bad hRestricts hHits,
    restrictive_governance_preserves_desired
      hRestricts hDesiredBefore hMisses⟩

/-! ## 5.9 Closed-loop calibration fixed point -/

/-- A fixed point of an endomap. -/
def IsFixedPoint {α : Type u} (f : α -> α) (x : α) : Prop :=
  f x = x

/-- Iterated application of an update function. -/
def IteratedUpdate {Estimate : Type u}
    (update : Estimate -> Estimate) : Nat -> Estimate -> Estimate
  | 0, estimate => estimate
  | Nat.succ n, estimate => update (IteratedUpdate update n estimate)

/-- Iterating from an updated estimate is the same as one more iteration. -/
@[simp] theorem iteratedUpdate_from_update
    {Estimate : Type u}
    (update : Estimate -> Estimate) :
    ∀ n estimate,
      IteratedUpdate update n (update estimate) =
        IteratedUpdate update (n + 1) estimate
  | 0, _ => rfl
  | Nat.succ n, estimate => by
      simp [IteratedUpdate, iteratedUpdate_from_update update n estimate]

/-- The update sequence eventually reaches a fixed point or boundary expansion. -/
def EventuallyFixedOrBoundary
    {Estimate : Type u}
    (update : Estimate -> Estimate)
    (boundaryExpansion : Estimate -> Prop)
    (initial : Estimate) : Prop :=
  ∃ n,
    IsFixedPoint update (IteratedUpdate update n initial) ∨
      boundaryExpansion (IteratedUpdate update n initial)

/-- Finite-height progress assumptions for closed-loop calibration. -/
structure FiniteRefinementHeight
    (Estimate : Type u) (update : Estimate -> Estimate) where
  rank : Estimate -> Nat
  boundaryExpansion : Estimate -> Prop
  strictlyRefinesUnlessDone :
    ∀ estimate,
      ¬ IsFixedPoint update estimate ->
        ¬ boundaryExpansion estimate ->
          rank (update estimate) < rank estimate
  evidenceBoundary : Prop
  nonConclusions : Prop

namespace FiniteRefinementHeight

/--
If each non-fixed, non-boundary update strictly decreases a Nat-valued rank,
then the closed loop eventually reaches a fixed point or boundary expansion.
-/
theorem closedLoopCalibration_fixedPoint_or_boundary_of_finiteHeight
    {Estimate : Type u} {update : Estimate -> Estimate}
    (height : FiniteRefinementHeight Estimate update)
    (initial : Estimate) :
    EventuallyFixedOrBoundary update height.boundaryExpansion initial := by
  refine
    Nat.strongRecOn (height.rank initial)
      (motive := fun n =>
        ∀ estimate,
          height.rank estimate = n ->
            EventuallyFixedOrBoundary update height.boundaryExpansion estimate)
      ?_ initial rfl
  intro n ih estimate hEstimateRank
  by_cases hFixed : IsFixedPoint update estimate
  · exact ⟨0, Or.inl hFixed⟩
  · by_cases hBoundary : height.boundaryExpansion estimate
    · exact ⟨0, Or.inr hBoundary⟩
    · have hDecrease :
          height.rank (update estimate) < n := by
        rw [← hEstimateRank]
        exact height.strictlyRefinesUnlessDone
          estimate hFixed hBoundary
      obtain ⟨steps, hDone⟩ :=
        ih (height.rank (update estimate)) hDecrease
          (update estimate) rfl
      refine ⟨steps + 1, ?_⟩
      simpa [iteratedUpdate_from_update update steps estimate]
        using hDone

end FiniteRefinementHeight

/-- Closed-loop calibration theorem package. -/
structure ClosedLoopCalibrationPackage
    (Estimate : Type u) (update : Estimate -> Estimate) where
  refinementLe : Estimate -> Estimate -> Prop
  boundaryExpansionRequirement : Estimate -> Prop
  monotone : Prop
  evidencePreserving : Prop
  boundaryExplicit : Prop
  nonConclusionPreserving : Prop
  forecastErrorRefining : Prop
  reachesFixedPointOrBoundary :
    monotone ->
      evidencePreserving ->
        boundaryExplicit ->
          nonConclusionPreserving ->
            forecastErrorRefining ->
              ∀ initial,
                EventuallyFixedOrBoundary update
                  boundaryExpansionRequirement initial
  calibrationBoundary : Prop
  nonConclusions : Prop

namespace ClosedLoopCalibrationPackage

/-- Under the selected update assumptions, iteration stops at a fixed point or boundary expansion. -/
theorem closedLoop_calibration_fixedPoint_or_boundary
    {Estimate : Type u} {update : Estimate -> Estimate}
    (package : ClosedLoopCalibrationPackage Estimate update)
    (hMonotone : package.monotone)
    (hEvidence : package.evidencePreserving)
    (hBoundary : package.boundaryExplicit)
    (hNonConclusion : package.nonConclusionPreserving)
    (hError : package.forecastErrorRefining)
    (initial : Estimate) :
    EventuallyFixedOrBoundary update package.boundaryExpansionRequirement
      initial :=
  package.reachesFixedPointOrBoundary hMonotone hEvidence hBoundary
    hNonConclusion hError initial

end ClosedLoopCalibrationPackage

/-! ## 5.10 Artifact Yoneda -/

/-- Two fields have equivalent artifact responses when every probe gives the same response. -/
def ArtifactResponsesEquivalent
    {Artifact : Type u} {Field : Type v} {Response : Type w}
    (response : Field -> Artifact -> Response)
    (F G : Field) : Prop :=
  ∀ artifact, response F artifact = response G artifact

/-- A probe family is SFT-separating when response equivalence exactly detects field equivalence. -/
def SFTSeparatingProbeFamily
    {Artifact : Type u} {Field : Type v} {Response : Type w}
    (response : Field -> Artifact -> Response)
    (sftEquivalent : Field -> Field -> Prop) : Prop :=
  ∀ F G, ArtifactResponsesEquivalent response F G ↔ sftEquivalent F G

/-- Yoneda-shaped separating-probe theorem. -/
theorem artifact_yoneda_of_separating_probes
    {Artifact : Type u} {Field : Type v} {Response : Type w}
    {response : Field -> Artifact -> Response}
    {sftEquivalent : Field -> Field -> Prop}
    (hSeparating :
      SFTSeparatingProbeFamily response sftEquivalent)
    (F G : Field) :
    ArtifactResponsesEquivalent response F G ↔ sftEquivalent F G :=
  hSeparating F G

/-- Artifact-Yoneda theorem package for a separating probe family. -/
structure ArtifactYonedaPackage
    (Artifact : Type u) (Field : Type v) (Response : Type w) where
  response : Field -> Artifact -> Response
  sftEquivalent : Field -> Field -> Prop
  sufficientlySeparatingProbes : Prop
  response_equiv_iff_sft_equiv :
    sufficientlySeparatingProbes ->
      ∀ F G,
        ArtifactResponsesEquivalent response F G ↔ sftEquivalent F G
  probeBoundary : Prop
  nonConclusions : Prop

namespace ArtifactYonedaPackage

/-- A sufficiently separating artifact probe family determines SFT equivalence. -/
theorem artifact_yoneda
    {Artifact : Type u} {Field : Type v} {Response : Type w}
    (package : ArtifactYonedaPackage Artifact Field Response)
    (hSeparating : package.sufficientlySeparatingProbes)
    (F G : Field) :
    ArtifactResponsesEquivalent package.response F G ↔
      package.sftEquivalent F G :=
  package.response_equiv_iff_sft_equiv hSeparating F G

end ArtifactYonedaPackage

/-! ## 5.11 Agentic confluence -/

/-- All fair interleavings land in the same selected cone quotient. -/
def FairInterleavingsConverge
    {Interleaving : Type u} {ConeQuotient : Type v}
    (landing : Interleaving -> ConeQuotient) : Prop :=
  ∀ left right, landing left = landing right

/-- A selected normal-form map is unique when all inputs land in one normal form. -/
def UniqueNormalForm
    {Interleaving : Type u} {NormalForm : Type v}
    (normalForm : Interleaving -> NormalForm) : Prop :=
  ∀ left right, normalForm left = normalForm right

/-- Unique local normal forms yield selected agentic confluence after landing in the quotient. -/
theorem agentic_confluence_of_local_normal_forms_and_descent
    {Interleaving : Type u} {ConeQuotient : Type v}
    (landing : Interleaving -> ConeQuotient)
    (hUnique : UniqueNormalForm landing) :
    FairInterleavingsConverge landing :=
  hUnique

/-- Agentic confluence theorem package. -/
structure AgenticConfluencePackage
    (Interleaving : Type u) (ConeQuotient : Type v) where
  landing : Interleaving -> ConeQuotient
  localTermination : Prop
  localConfluence : Prop
  forecastConeDescent : Prop
  interfaceConstraintsPreserved : Prop
  policiesCommutationInvariant : Prop
  fairInterleavingsConverge :
    localTermination ->
      localConfluence ->
        forecastConeDescent ->
          interfaceConstraintsPreserved ->
            policiesCommutationInvariant ->
              FairInterleavingsConverge landing
  agentBoundary : Prop
  nonConclusions : Prop

namespace AgenticConfluencePackage

/-- The selected assumptions make fair accepted-agent interleavings confluent. -/
theorem agentic_confluence
    {Interleaving : Type u} {ConeQuotient : Type v}
    (package : AgenticConfluencePackage Interleaving ConeQuotient)
    (hTermination : package.localTermination)
    (hConfluence : package.localConfluence)
    (hDescent : package.forecastConeDescent)
    (hInterface : package.interfaceConstraintsPreserved)
    (hPolicy : package.policiesCommutationInvariant) :
    FairInterleavingsConverge package.landing :=
  package.fairInterleavingsConverge hTermination hConfluence hDescent
    hInterface hPolicy

end AgenticConfluencePackage

/-! ## 5.12 Lifecycle bifurcation -/

/-- Lifecycle pressure regimes after repair ceases to be the right operation. -/
inductive LifecyclePressureRegime where
  | repair
  | migration
  | contraction
  | deletion
  | endOfLife
  deriving DecidableEq, Repr

/-- Lifecycle bifurcation theorem package. -/
structure LifecycleBifurcationPackage (Field : Type u) where
  obstructionMeasure : Field -> Nat
  threshold : Nat
  repairFeasible : Field -> Prop
  repairOnlyPreservesTarget : Field -> Prop
  pressureRegime : Field -> LifecyclePressureRegime
  repairFeasible_of_lt :
    ∀ F, obstructionMeasure F < threshold -> repairFeasible F
  repairOnly_cannot_preserve_of_ge :
    ∀ F, threshold <= obstructionMeasure F ->
      ¬ repairOnlyPreservesTarget F
  pressureRegime_of_ge :
    ∀ F, threshold <= obstructionMeasure F ->
      pressureRegime F ≠ LifecyclePressureRegime.repair
  lifecycleBoundary : Prop
  nonConclusions : Prop

namespace LifecycleBifurcationPackage

/-- Below the obstruction threshold, repair remains feasible. -/
theorem lifecycle_repair_feasible_below_threshold
    {Field : Type u}
    (package : LifecycleBifurcationPackage Field)
    (F : Field)
    (hLt : package.obstructionMeasure F < package.threshold) :
    package.repairFeasible F :=
  package.repairFeasible_of_lt F hLt

/-- At or above threshold, repair-only intervention cannot preserve the target. -/
theorem lifecycle_bifurcation_above_threshold
    {Field : Type u}
    (package : LifecycleBifurcationPackage Field)
    (F : Field)
    (hGe : package.threshold <= package.obstructionMeasure F) :
    ¬ package.repairOnlyPreservesTarget F :=
  package.repairOnly_cannot_preserve_of_ge F hGe

/-- At or above threshold, the lifecycle regime leaves pure repair. -/
theorem lifecycle_pressure_regime_of_threshold
    {Field : Type u}
    (package : LifecycleBifurcationPackage Field)
    (F : Field)
    (hGe : package.threshold <= package.obstructionMeasure F) :
    package.pressureRegime F ≠ LifecyclePressureRegime.repair :=
  package.pressureRegime_of_ge F hGe

end LifecycleBifurcationPackage

/-! ## 5.13 Field-shaping fixed point -/

/-- Least fixed point relative to a selected order. -/
def IsLeastFixedPoint
    {Transformation : Type u}
    (le : Transformation -> Transformation -> Prop)
    (shape : Transformation -> Transformation)
    (point : Transformation) : Prop :=
  IsFixedPoint shape point ∧
    ∀ other, IsFixedPoint shape other -> le point other

/-- Greatest fixed point relative to a selected order. -/
def IsGreatestFixedPoint
    {Transformation : Type u}
    (le : Transformation -> Transformation -> Prop)
    (shape : Transformation -> Transformation)
    (point : Transformation) : Prop :=
  IsFixedPoint shape point ∧
    ∀ other, IsFixedPoint shape other -> le other point

/-- Field-shaping fixed point theorem package. -/
structure FieldShapingFixedPointPackage
    (Transformation : Type u)
    (shape : Transformation -> Transformation) where
  le : Transformation -> Transformation -> Prop
  supportTransformationsCompleteLattice : Prop
  monotone : Prop
  fixedPointPrinciple :
    supportTransformationsCompleteLattice ->
      monotone ->
        ∃ least greatest,
          IsLeastFixedPoint le shape least ∧
            IsGreatestFixedPoint le shape greatest
  minimalPreservesDesiredAndExcludesBad : Prop
  fieldShapingBoundary : Prop
  nonConclusions : Prop

namespace FieldShapingFixedPointPackage

/-- A monotone field-shaping operator has selected least and greatest fixed points. -/
theorem fieldShaping_fixedPoints
    {Transformation : Type u}
    {shape : Transformation -> Transformation}
    (package : FieldShapingFixedPointPackage Transformation shape)
    (hComplete : package.supportTransformationsCompleteLattice)
    (hMonotone : package.monotone) :
    ∃ least greatest,
      IsLeastFixedPoint package.le shape least ∧
        IsGreatestFixedPoint package.le shape greatest :=
  package.fixedPointPrinciple hComplete hMonotone

/-- The least fixed-point reading records preservation of desired paths and exclusion of bad paths. -/
def RecordsMinimalPreservesDesiredAndExcludesBad
    {Transformation : Type u}
    {shape : Transformation -> Transformation}
    (package : FieldShapingFixedPointPackage Transformation shape) :
    Prop :=
  package.minimalPreservesDesiredAndExcludesBad

end FieldShapingFixedPointPackage

/-! ## 5.14 Evolutionary invariance -/

/-- Evolutionary invariance theorem package. -/
structure EvolutionaryInvariancePackage (Field : Type u) where
  forecastConesNaturallyEquivalent : Field -> Field -> Prop
  evolutionarilyEquivalent : Field -> Field -> Prop
  cone_equivalence_implies_evolutionary_equivalence :
    ∀ F G,
      forecastConesNaturallyEquivalent F G ->
        evolutionarilyEquivalent F G
  invarianceBoundary : Prop
  nonConclusions : Prop

namespace EvolutionaryInvariancePackage

/-- ForecastCone-equivalent fields are equivalent for selected evolution semantics. -/
theorem evolutionary_invariance
    {Field : Type u}
    (package : EvolutionaryInvariancePackage Field)
    (F G : Field)
    (hCone :
      package.forecastConesNaturallyEquivalent F G) :
    package.evolutionarilyEquivalent F G :=
  package.cone_equivalence_implies_evolutionary_equivalence F G hCone

end EvolutionaryInvariancePackage

/-! ## 6. Fundamental modularity theorem -/

/-- Unified theorem package for the roadmap's grand theorem. -/
structure FundamentalModularityTheoremPackage where
  modularity : Prop
  forecastConeDescent : Prop
  technicalDebtMeasuredByDescentObstruction : Prop
  minimalDecisionPreservingEnvelope : Prop
  governanceCompleteByObstructionCutting : Prop
  closedLoopBoundaryExplicitFixedPoint : Prop
  computablyGoverned : Prop
  typedBoundaryFailureWitness : Prop
  modularity_iff_forecastConeDescent :
    modularity ↔ forecastConeDescent
  recordsTechnicalDebtAsObstruction :
    technicalDebtMeasuredByDescentObstruction
  recordsMinimalReviewEnvelope :
    minimalDecisionPreservingEnvelope
  recordsGovernanceCompleteness :
    governanceCompleteByObstructionCutting
  recordsClosedLoopFixedPoint :
    closedLoopBoundaryExplicitFixedPoint
  everyBoundedEvolution_governed_or_typedFailure :
    computablyGoverned ∨ typedBoundaryFailureWitness
  theoremBoundary : Prop
  nonConclusions : Prop

/-- Conservative conclusion shape for the fundamental modularity theorem family. -/
structure FundamentalModularityConclusion where
  modularityAsDescent : Prop
  technicalDebtAsObstruction : Prop
  reviewAsMinimalEnvelope : Prop
  governanceAsObstructionCutting : Prop
  learningAsBoundaryExplicitFixedPoint : Prop
  computablyGoverned : Prop
  typedBoundaryFailureWitness : Prop
  governed_or_failure :
    computablyGoverned ∨ typedBoundaryFailureWitness
  nonConclusions : Prop

namespace FundamentalModularityTheoremPackage

/-- Construct the fundamental package from the selected theorem family components. -/
def ofTheoremFamily
    (conclusion : FundamentalModularityConclusion)
    (_hModularity :
      conclusion.modularityAsDescent)
    (hDebt :
      conclusion.technicalDebtAsObstruction)
    (hReview :
      conclusion.reviewAsMinimalEnvelope)
    (hGovernance :
      conclusion.governanceAsObstructionCutting)
    (hLearning :
      conclusion.learningAsBoundaryExplicitFixedPoint)
    (theoremBoundary : Prop) :
    FundamentalModularityTheoremPackage where
  modularity := conclusion.modularityAsDescent
  forecastConeDescent := conclusion.modularityAsDescent
  technicalDebtMeasuredByDescentObstruction :=
    conclusion.technicalDebtAsObstruction
  minimalDecisionPreservingEnvelope :=
    conclusion.reviewAsMinimalEnvelope
  governanceCompleteByObstructionCutting :=
    conclusion.governanceAsObstructionCutting
  closedLoopBoundaryExplicitFixedPoint :=
    conclusion.learningAsBoundaryExplicitFixedPoint
  computablyGoverned := conclusion.computablyGoverned
  typedBoundaryFailureWitness := conclusion.typedBoundaryFailureWitness
  modularity_iff_forecastConeDescent := Iff.rfl
  recordsTechnicalDebtAsObstruction := hDebt
  recordsMinimalReviewEnvelope := hReview
  recordsGovernanceCompleteness := hGovernance
  recordsClosedLoopFixedPoint := hLearning
  everyBoundedEvolution_governed_or_typedFailure :=
    conclusion.governed_or_failure
  theoremBoundary := theoremBoundary
  nonConclusions := conclusion.nonConclusions

/-- The theorem-family components assemble into the conservative conclusion shape. -/
theorem fundamental_modularity_of_theorem_family
    (conclusion : FundamentalModularityConclusion)
    (hModularity :
      conclusion.modularityAsDescent)
    (hDebt :
      conclusion.technicalDebtAsObstruction)
    (hReview :
      conclusion.reviewAsMinimalEnvelope)
    (hGovernance :
      conclusion.governanceAsObstructionCutting)
    (hLearning :
      conclusion.learningAsBoundaryExplicitFixedPoint) :
    conclusion.modularityAsDescent ∧
      conclusion.technicalDebtAsObstruction ∧
      conclusion.reviewAsMinimalEnvelope ∧
      conclusion.governanceAsObstructionCutting ∧
      conclusion.learningAsBoundaryExplicitFixedPoint ∧
      (conclusion.computablyGoverned ∨
        conclusion.typedBoundaryFailureWitness) :=
  ⟨hModularity, hDebt, hReview, hGovernance, hLearning,
    conclusion.governed_or_failure⟩

/-- Grand theorem component: modularity is ForecastCone descent. -/
theorem fundamental_modularity
    (package : FundamentalModularityTheoremPackage) :
    package.modularity ↔ package.forecastConeDescent :=
  package.modularity_iff_forecastConeDescent

/-- Grand theorem component: bounded evolution is governed or fails with a typed witness. -/
theorem bounded_evolution_governed_or_typed_witness
    (package : FundamentalModularityTheoremPackage) :
    package.computablyGoverned ∨ package.typedBoundaryFailureWitness :=
  package.everyBoundedEvolution_governed_or_typedFailure

/-- Grand theorem component: technical debt is recorded as descent obstruction. -/
theorem technical_debt_as_descent_obstruction
    (package : FundamentalModularityTheoremPackage) :
    package.technicalDebtMeasuredByDescentObstruction :=
  package.recordsTechnicalDebtAsObstruction

/-- Grand theorem component: review is the selected minimal decision-preserving envelope. -/
theorem review_as_minimal_decision_envelope
    (package : FundamentalModularityTheoremPackage) :
    package.minimalDecisionPreservingEnvelope :=
  package.recordsMinimalReviewEnvelope

/-- Grand theorem component: governance completeness is obstruction cutting. -/
theorem governance_as_obstruction_cutting
    (package : FundamentalModularityTheoremPackage) :
    package.governanceCompleteByObstructionCutting :=
  package.recordsGovernanceCompleteness

/-- Grand theorem component: learning is a boundary-explicit closed-loop fixed point. -/
theorem learning_as_closedLoop_fixedPoint
    (package : FundamentalModularityTheoremPackage) :
    package.closedLoopBoundaryExplicitFixedPoint :=
  package.recordsClosedLoopFixedPoint

end FundamentalModularityTheoremPackage

end SFTTheoremRoadmap

end Formal.Arch
