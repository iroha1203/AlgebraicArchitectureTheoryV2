import Formal.AG.RepresentationAnalysis.DistanceFlatnessMass
import Formal.AG.SingularityMonodromyStack
import Formal.AG.LawAlgebra.ClosedEquationalGeometry

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y z

/--
VII.定義12.1: a selected repair route ending in actual lawful geometry.

Implementation notes: operation-distance data remain unchanged, while the
lawful target is represented by one canonical Scheme morphism factorization
rather than separate ring-ideal fields and coherence equations.
-/
structure RepairRoute
    {Obj : ArchitectureObject U}
    (C : DistanceFlatnessMassContext Obj)
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (R : LawAlgebra.ClosedEquationalLawReading raw X E)
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hclosed : LawAlgebra.RequiredClosed raw X R) where
  source : C.operationDistance.GeometryState
  target : C.operationDistance.GeometryState
  flatCandidate : C.distanceToFlatness.FlatCandidate source
  target_eq_flatState : target = C.distanceToFlatness.flatState source flatCandidate
  operationPath : C.operationDistance.operationPath source target
  routeCost : DistanceValue Nat
  routeCost_eq_d_op : routeCost = C.d_op source target
  routeCost_eq_pathCost : routeCost = C.operationDistance.pathCost operationPath
  sectionSource : AlgebraicGeometry.Scheme
  «section» : sectionSource ⟶ X.underlying
  factorization :
    LawAlgebra.FactorsThroughLawfulClosedSubscheme raw X R hR hclosed «section»

namespace RepairRoute

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {C : DistanceFlatnessMassContext Obj}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
variable {E : ArchitecturalEquationSystem S.contextPreorder}
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {X : LawAlgebra.StandardArchitectureScheme raw}
variable {R : LawAlgebra.ClosedEquationalLawReading raw X E}
variable {hR : LawAlgebra.IsClosedEquationalLawReading raw X R}
variable {hclosed : LawAlgebra.RequiredClosed raw X R}

/-- VII.定義12.1: the selected target is the selected flat-candidate state. -/
theorem target_eq_flatState_holds (Q : RepairRoute C raw X R hR hclosed) :
    Q.target = C.distanceToFlatness.flatState Q.source Q.flatCandidate :=
  Q.target_eq_flatState

/-- VII.定義12.1: the route cost reads the selected operation distance. -/
theorem routeCost_eq_d_op_holds (Q : RepairRoute C raw X R hR hclosed) :
    Q.routeCost = C.d_op Q.source Q.target := Q.routeCost_eq_d_op

/-- VII.定義12.1: the route cost is witnessed by the selected operation path. -/
theorem routeCost_eq_pathCost_holds (Q : RepairRoute C raw X R hR hclosed) :
    Q.routeCost = C.operationDistance.pathCost Q.operationPath :=
  Q.routeCost_eq_pathCost

/-- Expose the route's canonical lawful closed-subscheme factorization. -/
def factorization_certificate (Q : RepairRoute C raw X R hR hclosed) :
    LawAlgebra.FactorsThroughLawfulClosedSubscheme
      raw X R hR hclosed Q.«section» :=
  Q.factorization

end RepairRoute

/-- VII.定義12.2: the selected optimization mode for repair profiles. -/
inductive RepairOptimizationMode where
  | shortest
  | safest
  | structural
  | stable
  deriving DecidableEq

/--
VII.定義12.2: selected repair profiles.

Shortest and safest are profile predicates over AC12 route / margin data.
Structural and stable profiles carry explicit selected Part VI / Part IV--6
readings as data rather than deriving global correctness.

Implementation notes: the profile is indexed by an already constructed
`RepairRoute`; it does not duplicate the route's Scheme or factorization data.
-/
structure RepairProfileReading {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {E : ArchitecturalEquationSystem S.contextPreorder}
    {rawR0 : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {schemeR0 : LawAlgebra.StandardArchitectureScheme rawR0}
    {readingR0 : LawAlgebra.ClosedEquationalLawReading rawR0 schemeR0 E}
    {readingClosedR0 : LawAlgebra.IsClosedEquationalLawReading rawR0 schemeR0 readingR0}
    {requiredClosedR0 : LawAlgebra.RequiredClosed rawR0 schemeR0 readingR0}
    {C : DistanceFlatnessMassContext Obj}
    (route : RepairRoute C rawR0 schemeR0 readingR0 readingClosedR0 requiredClosedR0) where
  mode : RepairOptimizationMode
  shortest : Prop
  shortest_holds : mode = .shortest -> shortest
  safest : Prop
  safest_holds : mode = .safest -> safest
  normalConeReading : Type z
  normalConeDirectionReading : normalConeReading -> Type z
  selectedNormalConeReading : normalConeReading
  selectedNormalConeDirection : normalConeDirectionReading selectedNormalConeReading
  structural : Prop
  structural_holds : mode = .structural -> structural
  cohomologyControlReading : Type z
  derivedConflictControlReading : Type z
  monodromyDebtControlReading : Type z
  stable : Prop
  stable_holds : mode = .stable -> stable

namespace RepairProfileReading

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {E : ArchitecturalEquationSystem S.contextPreorder}
    {rawR0 : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {schemeR0 : LawAlgebra.StandardArchitectureScheme rawR0}
    {readingR0 : LawAlgebra.ClosedEquationalLawReading rawR0 schemeR0 E}
    {readingClosedR0 : LawAlgebra.IsClosedEquationalLawReading rawR0 schemeR0 readingR0}
    {requiredClosedR0 : LawAlgebra.RequiredClosed rawR0 schemeR0 readingR0}
variable {C : DistanceFlatnessMassContext Obj}
variable {route : RepairRoute C rawR0 schemeR0 readingR0 readingClosedR0 requiredClosedR0}

/-- VII.定義12.2: shortest repair certificate, when the selected mode is shortest. -/
theorem shortest_certificate
    (P : RepairProfileReading route) (h : P.mode = .shortest) :
    P.shortest :=
  P.shortest_holds h

/-- VII.定義12.2: safest repair certificate, when the selected mode is safest. -/
theorem safest_certificate
    (P : RepairProfileReading route) (h : P.mode = .safest) :
    P.safest :=
  P.safest_holds h

/-- VII.定義12.2: structural repair certificate, when the selected mode is structural. -/
theorem structural_certificate
    (P : RepairProfileReading route) (h : P.mode = .structural) :
    P.structural :=
  P.structural_holds h

/-- VII.定義12.2: stable repair certificate, when the selected mode is stable. -/
theorem stable_certificate
    (P : RepairProfileReading route) (h : P.mode = .stable) :
    P.stable :=
  P.stable_holds h

end RepairProfileReading

/--
VII.定義12.3: selected margin reading.

`margin(A)` is the selected distance from `A` to the selected boundary relative to
a safe-region predicate.  This file only defines the reading; theorem 12.5 is
left to AC14.
-/
structure MarginProfile {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    (C : DistanceFlatnessMassContext Obj) where
  SafeRegion : Set C.operationDistance.GeometryState
  UnsafeBoundary : Set C.operationDistance.GeometryState
  boundaryDistance :
    C.operationDistance.GeometryState -> C.operationDistance.GeometryState -> DistanceValue Nat
  margin : C.operationDistance.GeometryState -> DistanceValue Nat
  margin_reading :
    ∀ A, ∃ B, B ∈ UnsafeBoundary ∧ margin A = boundaryDistance A B
  safeRegionMembership : C.operationDistance.GeometryState -> Prop
  safeRegionMembership_iff_mem :
    ∀ A, safeRegionMembership A ↔ A ∈ SafeRegion

namespace MarginProfile

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {C : DistanceFlatnessMassContext Obj}

/-- VII.定義12.3: selected margin `margin(A)`. -/
def Margin (M : MarginProfile C)
    (A : C.operationDistance.GeometryState) : DistanceValue Nat :=
  M.margin A

/-- VII.定義12.3: `margin(A)` is read from a selected boundary point. -/
theorem margin_has_boundary_witness
    (M : MarginProfile C) (A : C.operationDistance.GeometryState) :
    ∃ B, B ∈ M.UnsafeBoundary ∧ M.Margin A = M.boundaryDistance A B :=
  M.margin_reading A

/-- VII.定義12.3: selected safe-region membership is exactly set membership. -/
theorem safeRegionMembership_iff
    (M : MarginProfile C) (A : C.operationDistance.GeometryState) :
    M.safeRegionMembership A ↔ A ∈ M.SafeRegion :=
  M.safeRegionMembership_iff_mem A

end MarginProfile

/--
VII.定理12.5: explicit assumptions for margin stability.

The theorem is not a global metric theorem.  It is relative to the selected
path length, endpoint-distance bound, margin budget, and the profile-specific
rule that such a bound preserves the selected safe region.
-/
structure MarginStabilityProfile {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    {C : DistanceFlatnessMassContext Obj} (M : MarginProfile C) where
  start : C.operationDistance.GeometryState
  endpoint : C.operationDistance.GeometryState
  pathLength : Nat
  endpointDistance : Nat
  marginBudget : Nat
  marginBudget_reads_margin : M.Margin start = DistanceValue.measured marginBudget
  boundaryDistanceNat :
    C.operationDistance.GeometryState -> C.operationDistance.GeometryState -> Nat
  boundaryDistance_reads_nat :
    ∀ A B, M.boundaryDistance A B = DistanceValue.measured (boundaryDistanceNat A B)
  start_safe : M.safeRegionMembership start
  endpointDistance_le_pathLength : endpointDistance ≤ pathLength
  pathLength_lt_margin : pathLength < marginBudget
  margin_le_boundaryDistance :
    ∀ B, B ∈ M.UnsafeBoundary -> marginBudget ≤ boundaryDistanceNat start B
  triangle_boundaryDistance :
    ∀ B, B ∈ M.UnsafeBoundary ->
      boundaryDistanceNat start B ≤ endpointDistance + boundaryDistanceNat endpoint B
  boundary_self_distance_zero :
    ∀ B, B ∈ M.UnsafeBoundary -> boundaryDistanceNat B B = 0
  safeRegion_avoids_boundary :
    ∀ A, M.safeRegionMembership A -> A ∉ M.UnsafeBoundary
  safeRegion_of_avoids_boundary :
    ∀ A, A ∉ M.UnsafeBoundary -> M.safeRegionMembership A

namespace MarginStabilityProfile

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {C : DistanceFlatnessMassContext Obj}
variable {M : MarginProfile C}

/-- VII.定理12.5: endpoint distance is within the selected margin budget. -/
theorem endpointDistance_lt_margin
    (P : MarginStabilityProfile M) :
    P.endpointDistance < P.marginBudget :=
  Nat.lt_of_le_of_lt P.endpointDistance_le_pathLength P.pathLength_lt_margin

/-- VII.定理12.5: the selected margin budget is read from `margin(start)`. -/
theorem marginBudget_reads_margin_holds
    (P : MarginStabilityProfile M) :
    M.Margin P.start = DistanceValue.measured P.marginBudget :=
  P.marginBudget_reads_margin

/--
VII.定理12.5: if the endpoint were on the selected boundary, triangle and
margin lower-bound assumptions would force a strict self-contradiction.
-/
theorem marginStability_no_boundary_crossing
    (P : MarginStabilityProfile M) :
    P.endpoint ∉ M.UnsafeBoundary := by
  intro hboundary
  have hmargin_le :
      P.marginBudget ≤ P.boundaryDistanceNat P.start P.endpoint :=
    P.margin_le_boundaryDistance P.endpoint hboundary
  have htriangle :
      P.boundaryDistanceNat P.start P.endpoint ≤
        P.endpointDistance + P.boundaryDistanceNat P.endpoint P.endpoint :=
    P.triangle_boundaryDistance P.endpoint hboundary
  have hself :
      P.boundaryDistanceNat P.endpoint P.endpoint = 0 :=
    P.boundary_self_distance_zero P.endpoint hboundary
  have hboundary_le_endpoint :
      P.boundaryDistanceNat P.start P.endpoint ≤ P.endpointDistance := by
    simpa [hself] using htriangle
  have hbudget_le_endpoint : P.marginBudget ≤ P.endpointDistance :=
    Nat.le_trans hmargin_le hboundary_le_endpoint
  have hendpoint_lt_budget : P.endpointDistance < P.marginBudget :=
    P.endpointDistance_lt_margin
  exact (Nat.not_lt_of_ge hbudget_le_endpoint) hendpoint_lt_budget

/--
VII.定理12.5: Margin Stability.

Under the explicit path-length, endpoint-distance, triangle-inequality, and
margin-definition assumptions, the endpoint remains in the selected safe region.
-/
theorem marginStability_endpoint_safe
    (P : MarginStabilityProfile M) :
    M.safeRegionMembership P.endpoint :=
  P.safeRegion_of_avoids_boundary P.endpoint P.marginStability_no_boundary_crossing

end MarginStabilityProfile

/--
VII.定義12.4: architectural Dehn function interface.

The presentation two-complex is a selected Part VI carrier.  The Dehn function is
defined only relative to selected loops and filling-area readings.
-/
structure ArchitecturalDehnProfile where
  PresentationTwoComplexReading : Type u
  selectedPresentation : PresentationTwoComplexReading
  Loop : Type u
  Filling : Loop -> Type u
  fillingArea : ∀ loop, Filling loop -> Nat
  dehnFunction : Nat -> Nat
  loopSize : Loop -> Nat
  dehn_bounds_selected_fillings :
    ∀ loop (filling : Filling loop), fillingArea loop filling ≤ dehnFunction (loopSize loop)

namespace ArchitecturalDehnProfile

/-- VII.定義12.4: selected architectural Dehn value. -/
def δ_AAT (D : ArchitecturalDehnProfile.{u}) (n : Nat) : Nat :=
  D.dehnFunction n

/-- VII.定義12.4: selected fillings are bounded by the selected Dehn function. -/
theorem fillingArea_le_dehn
    (D : ArchitecturalDehnProfile.{u}) (loop : D.Loop) (filling : D.Filling loop) :
    D.fillingArea loop filling ≤ D.δ_AAT (D.loopSize loop) :=
  D.dehn_bounds_selected_fillings loop filling

end ArchitecturalDehnProfile

/--
VII.定理12.7: explicit observation-gap lower-bound assumptions.

The primary assumptions expose an integer Lipschitz estimate
`observationGap <= lipschitzConstant * fillCost`.  The namespace then derives
the selected Nat-division lower-bound surface `observationGap / L <= fillCost`
under the explicit positive-Lipschitz hypothesis.
-/
structure ObservationGapLowerBoundProfile where
  Path : Type u
  Filler : Type u
  observationGap : Path -> Path -> Nat
  loopFromPair : Path -> Path -> Type u
  selectedLoop : ∀ P Q, loopFromPair P Q
  fillerForLoop : ∀ P Q, loopFromPair P Q -> Filler
  fillCost : Filler -> Nat
  generatorCost : Filler -> Nat
  lipschitzConstant : Nat
  lipschitzConstant_pos : 0 < lipschitzConstant
  observationMapLipschitz :
    ∀ P Q,
      observationGap P Q ≤
        lipschitzConstant * generatorCost (fillerForLoop P Q (selectedLoop P Q))
  generatorCost_le_fillCost :
    ∀ P Q,
      generatorCost (fillerForLoop P Q (selectedLoop P Q)) ≤
        fillCost (fillerForLoop P Q (selectedLoop P Q))
  quotientLowerBound : Nat -> Nat -> Prop
  quotientLowerBound_holds :
    ∀ P Q,
      observationGap P Q ≤
        lipschitzConstant * fillCost (fillerForLoop P Q (selectedLoop P Q)) ->
      quotientLowerBound (observationGap P Q)
        (fillCost (fillerForLoop P Q (selectedLoop P Q)))

namespace ObservationGapLowerBoundProfile

/-- VII.定理12.7: selected filling for the pair loop `P . Q^{-1}`. -/
def selectedFiller
    (G : ObservationGapLowerBoundProfile.{u}) (P Q : G.Path) : G.Filler :=
  G.fillerForLoop P Q (G.selectedLoop P Q)

/--
VII.定理12.7: Lipschitz observation gap gives the selected filling-cost lower
bound in multiplication form.
-/
theorem observationGap_le_lipschitz_fillCost
    (G : ObservationGapLowerBoundProfile.{u}) (P Q : G.Path) :
    G.observationGap P Q ≤
      G.lipschitzConstant * G.fillCost (G.selectedFiller P Q) := by
  exact Nat.le_trans (G.observationMapLipschitz P Q)
    (Nat.mul_le_mul_left G.lipschitzConstant (G.generatorCost_le_fillCost P Q))

/--
VII.定理12.7: selected Nat-division observation-gap lower bound.

This is the Lean reading of `fillCost(P . Q^{-1}) >= observationGap(P,Q) / L`
for the selected loop and selected filler, with Nat division rounded down.
-/
theorem observationGap_div_lipschitz_le_fillCost
    (G : ObservationGapLowerBoundProfile.{u}) (P Q : G.Path) :
    G.observationGap P Q / G.lipschitzConstant ≤
      G.fillCost (G.selectedFiller P Q) := by
  rw [Nat.div_le_iff_le_mul_add_pred G.lipschitzConstant_pos]
  exact Nat.le_trans (G.observationGap_le_lipschitz_fillCost P Q) (by omega)

/--
VII.定理12.7: selected quotient-style lower-bound reading, supplied explicitly
for downstream variants that choose a stronger or domain-specific predicate.
-/
theorem quotientLowerBound_certificate
    (G : ObservationGapLowerBoundProfile.{u}) (P Q : G.Path) :
    G.quotientLowerBound (G.observationGap P Q)
      (G.fillCost (G.selectedFiller P Q)) :=
  G.quotientLowerBound_holds P Q (G.observationGap_le_lipschitz_fillCost P Q)

end ObservationGapLowerBoundProfile

/--
VII.定義12.8: selected bi-Lipschitz representation profile.

The inequalities are over selected comparable state pairs.  No completeness over
all states or semantic universes is asserted.
-/
structure BiLipschitzRepresentationProfile where
  DomainState : Type u
  AnalyticState : Type u
  comparable : DomainState -> DomainState -> Prop
  representation : DomainState -> AnalyticState
  structuralDistance : DomainState -> DomainState -> Nat
  analyticDistance : AnalyticState -> AnalyticState -> Nat
  lowerConstant : Nat
  upperConstant : Nat
  lower_le_upper : lowerConstant ≤ upperConstant
  lower_bound :
    ∀ {A B}, comparable A B ->
      lowerConstant * structuralDistance A B ≤
        analyticDistance (representation A) (representation B)
  upper_bound :
    ∀ {A B}, comparable A B ->
      analyticDistance (representation A) (representation B) ≤
        upperConstant * structuralDistance A B

namespace BiLipschitzRepresentationProfile

/-- VII.定義12.8: the selected lower Lipschitz bound. -/
theorem lower_bound_holds
    (P : BiLipschitzRepresentationProfile.{u})
    {A B : P.DomainState} (h : P.comparable A B) :
    P.lowerConstant * P.structuralDistance A B ≤
      P.analyticDistance (P.representation A) (P.representation B) :=
  P.lower_bound h

/-- VII.定義12.8: the selected upper Lipschitz bound. -/
theorem upper_bound_holds
    (P : BiLipschitzRepresentationProfile.{u})
    {A B : P.DomainState} (h : P.comparable A B) :
    P.analyticDistance (P.representation A) (P.representation B) ≤
      P.upperConstant * P.structuralDistance A B :=
  P.upper_bound h

end BiLipschitzRepresentationProfile

/--
VII.定義13.1: singularity profile as an analytic reading of Part VI
singularity data.

The profile bundles a selected stratum, tangent/deformation interface, normal
cone reading, lifting-failure witness, derived-conflict concentration, and
repair-difficulty reading.  It is a reading layer; it does not construct a
general normal cone or deformation theory, and it does not emit a measurement
verdict.
-/
structure SingularityProfile {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    {S : Site.AATSite Obj}
    {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type v} [CommRing k]
    (X : SingularityMonodromyStack.ArchitectureStratum.{u, v, w, x, y} P k)
    (L : SingularityMonodromyStack.CotangentData.{u, v, w, x, y, z} X)
    (T : SingularityMonodromyStack.TangentData.{u, v, w, x, y, z} X L)
    (D : SingularityMonodromyStack.DeformationObstructionTheory.{u, v, w, x, y, z} T)
    (N : SingularityMonodromyStack.NormalConeReading.{u, v, w, x, y, z} X) where
  selectedPoint : X.Point
  selectedPoint_mem : X.Mem selectedPoint
  selectedTest : D.DeformationTest
  selectedObstruction_nonzero : D.ob selectedTest ≠ T.zeroObstruction
  selectedNormalCone : N.normalCone
  selectedNormalCone_overFlat : N.normalConeOverFlat selectedNormalCone
  DerivedConflictConcentration : Type z
  selectedDerivedConflict : DerivedConflictConcentration
  derivedConflictSupportedOnNormalCone :
    DerivedConflictConcentration -> N.normalCone -> Prop
  selectedDerivedConflict_supported :
    derivedConflictSupportedOnNormalCone selectedDerivedConflict selectedNormalCone
  RepairDifficulty : Type z
  selectedRepairDifficulty : RepairDifficulty
  repairDifficultyReadsSingularity : RepairDifficulty -> Prop
  selectedRepairDifficulty_holds :
    repairDifficultyReadsSingularity selectedRepairDifficulty
  measurementVerdictReserved : Type z

namespace SingularityProfile

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj}
variable {P : SingularityMonodromyStack.StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : SingularityMonodromyStack.ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : SingularityMonodromyStack.CotangentData.{u, v, w, x, y, z} X}
variable {T : SingularityMonodromyStack.TangentData.{u, v, w, x, y, z} X L}
variable {D : SingularityMonodromyStack.DeformationObstructionTheory.{u, v, w, x, y, z} T}
variable {N : SingularityMonodromyStack.NormalConeReading.{u, v, w, x, y, z} X}

/-- VII.定義13.1: expose the selected stratum membership certificate. -/
theorem selectedPoint_mem_holds
    (P : SingularityProfile.{u, v, w, x, y, z} X L T D N) :
    X.Mem P.selectedPoint :=
  P.selectedPoint_mem

/-- VII.定義13.1: nonzero selected obstruction refutes the selected lift/fill. -/
theorem liftingFailure
    (P : SingularityProfile.{u, v, w, x, y, z} X L T D N) :
    ¬ D.LiftFill P.selectedTest :=
  SingularityMonodromyStack.DeformationObstructionTheory.not_liftFill_of_ob_ne_zero D
    P.selectedObstruction_nonzero

/-- VII.定義13.1: expose selected support of the derived conflict on the normal cone. -/
theorem selectedDerivedConflict_supported_holds
    (P : SingularityProfile.{u, v, w, x, y, z} X L T D N) :
    P.derivedConflictSupportedOnNormalCone P.selectedDerivedConflict P.selectedNormalCone :=
  P.selectedDerivedConflict_supported

/-- VII.定義13.1: expose the selected repair-difficulty reading. -/
theorem selectedRepairDifficulty_certificate
    (P : SingularityProfile.{u, v, w, x, y, z} X L T D N) :
    P.repairDifficultyReadsSingularity P.selectedRepairDifficulty :=
  P.selectedRepairDifficulty_holds

end SingularityProfile

/--
VII.定義13.2: bounded monodromy index as an analytic reading of Part VI
monodromy data.

The index is relative to one selected loop `gamma` and a supplied Part VI
`MonodromyAction`.  It records the obstruction / semantic / effect actions,
period change, loop residue, and an underlying finite AMI-style bounded
reading.  Measurement verdicts remain reserved for later measurement-facing
work.
-/
structure MonodromyIndex {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    {S : Site.AATSite Obj}
    {P : SingularityMonodromyStack.StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : SingularityMonodromyStack.ArchitectureStratum.{u, v, w, x, y} P k}
    {G : SingularityMonodromyStack.OperationCategoryData.{u, v, w, x, y, z} X}
    {R : SingularityMonodromyStack.RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : SingularityMonodromyStack.HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    {base : G.State}
    {Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z}
      H base}
    (M : SingularityMonodromyStack.MonodromyAction.{u, v, w, x, y, z} Pi)
    (gamma : Pi.pi1AAT) where
  monodromyAction : SingularityMonodromyStack.CoefficientAutomorphism M.coefficient
  monodromyAction_eq_Mon_gamma : monodromyAction = M.Mon_gamma gamma
  obstructionAction : M.coefficient.Ob ≃ M.coefficient.Ob
  obstructionAction_eq :
    obstructionAction = M.obstructionMonodromy gamma
  semanticAction : M.coefficient.Sem ≃ M.coefficient.Sem
  semanticAction_eq : semanticAction = (M.Mon_gamma gamma).semAut
  effectAction : M.coefficient.Eff ≃ M.coefficient.Eff
  effectAction_eq : effectAction = (M.Mon_gamma gamma).effAut
  PeriodReading : Type z
  periodBefore : PeriodReading
  periodAfter : PeriodReading
  PeriodChange : PeriodReading -> PeriodReading -> Type z
  selectedPeriodChange : PeriodChange periodBefore periodAfter
  LoopResidue : Type z
  selectedLoopResidue : LoopResidue
  loopResidueBound : LoopResidue -> Nat
  residueBound : Nat
  loopResidueBound_le :
    loopResidueBound selectedLoopResidue ≤ residueBound
  architecturalMonodromyIndex :
    SingularityMonodromyStack.ArchitecturalMonodromyIndex.{z}
  boundedReading : Prop
  boundedReading_holds : boundedReading
  measurementVerdictReserved : Type z

namespace MonodromyIndex

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj}
variable {P : SingularityMonodromyStack.StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : SingularityMonodromyStack.ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : SingularityMonodromyStack.OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : SingularityMonodromyStack.RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : SingularityMonodromyStack.HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {base : G.State}
variable {Pi : SingularityMonodromyStack.PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z}
  H base}
variable {M : SingularityMonodromyStack.MonodromyAction.{u, v, w, x, y, z} Pi}
variable {gamma : Pi.pi1AAT}

/-- VII.定義13.2: expose the selected Part VI monodromy action. -/
theorem monodromyAction_eq_Mon_gamma_holds
    (I : MonodromyIndex.{u, v, w, x, y, z} M gamma) :
    I.monodromyAction = M.Mon_gamma gamma :=
  I.monodromyAction_eq_Mon_gamma

/-- VII.定義13.2: expose the obstruction action reading. -/
theorem obstructionAction_eq_holds
    (I : MonodromyIndex.{u, v, w, x, y, z} M gamma) :
    I.obstructionAction = M.obstructionMonodromy gamma :=
  I.obstructionAction_eq

/-- VII.定義13.2: expose the semantic action reading. -/
theorem semanticAction_eq_holds
    (I : MonodromyIndex.{u, v, w, x, y, z} M gamma) :
    I.semanticAction = (M.Mon_gamma gamma).semAut :=
  I.semanticAction_eq

/-- VII.定義13.2: expose the effect action reading. -/
theorem effectAction_eq_holds
    (I : MonodromyIndex.{u, v, w, x, y, z} M gamma) :
    I.effectAction = (M.Mon_gamma gamma).effAut :=
  I.effectAction_eq

/-- VII.定義13.2: expose the selected loop-residue bound. -/
theorem loopResidueBound_le_holds
    (I : MonodromyIndex.{u, v, w, x, y, z} M gamma) :
    I.loopResidueBound I.selectedLoopResidue ≤ I.residueBound :=
  I.loopResidueBound_le

/-- VII.定義13.2: expose the selected bounded-reading certificate. -/
theorem boundedReading_certificate
    (I : MonodromyIndex.{u, v, w, x, y, z} M gamma) :
    I.boundedReading :=
  I.boundedReading_holds

/-- VII.定義13.2: expose the underlying Part VI finite AMI weighted-sum reading. -/
theorem architecturalMonodromyIndex_value_eq_weighted_sum
    (I : MonodromyIndex.{u, v, w, x, y, z} M gamma) :
    I.architecturalMonodromyIndex.value =
      ∑ square : I.architecturalMonodromyIndex.Square,
        I.architecturalMonodromyIndex.weight square *
          I.architecturalMonodromyIndex.mu square
            I.architecturalMonodromyIndex.selectedAxis :=
  SingularityMonodromyStack.ArchitecturalMonodromyIndex.value_eq_weighted_sum_holds
    I.architecturalMonodromyIndex

end MonodromyIndex

/--
VII.R9 / AC13: combined repair, margin, Dehn, and bi-Lipschitz surface.

Implementation notes: the context aggregates independently constructed
profiles and indexes the repair profile by the same canonical repair route.
-/
structure RepairMarginDehnContext {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {E : ArchitecturalEquationSystem S.contextPreorder}
    {rawR0 : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {schemeR0 : LawAlgebra.StandardArchitectureScheme rawR0}
    {readingR0 : LawAlgebra.ClosedEquationalLawReading rawR0 schemeR0 E}
    {readingClosedR0 : LawAlgebra.IsClosedEquationalLawReading rawR0 schemeR0 readingR0}
    {requiredClosedR0 : LawAlgebra.RequiredClosed rawR0 schemeR0 readingR0}
    (C : DistanceFlatnessMassContext Obj) where
  route : RepairRoute C rawR0 schemeR0 readingR0 readingClosedR0 requiredClosedR0
  repairProfile : RepairProfileReading route
  marginProfile : MarginProfile C
  dehnProfile : ArchitecturalDehnProfile.{u}
  biLipschitzProfile : BiLipschitzRepresentationProfile.{u}

namespace RepairMarginDehnContext

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {E : ArchitecturalEquationSystem S.contextPreorder}
    {rawR0 : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {schemeR0 : LawAlgebra.StandardArchitectureScheme rawR0}
    {readingR0 : LawAlgebra.ClosedEquationalLawReading rawR0 schemeR0 E}
    {readingClosedR0 : LawAlgebra.IsClosedEquationalLawReading rawR0 schemeR0 readingR0}
    {requiredClosedR0 : LawAlgebra.RequiredClosed rawR0 schemeR0 readingR0}
variable {C : DistanceFlatnessMassContext Obj}

/-- VII.R9 / AC13: expose the selected repair route. -/
def selectedRoute (R : RepairMarginDehnContext
    (rawR0 := rawR0) (schemeR0 := schemeR0) (readingR0 := readingR0)
    (readingClosedR0 := readingClosedR0) (requiredClosedR0 := requiredClosedR0) C) :
    RepairRoute C rawR0 schemeR0 readingR0 readingClosedR0 requiredClosedR0 :=
  R.route

/-- VII.R9 / AC13: expose the selected margin value. -/
def margin (R : RepairMarginDehnContext
    (rawR0 := rawR0) (schemeR0 := schemeR0) (readingR0 := readingR0)
    (readingClosedR0 := readingClosedR0) (requiredClosedR0 := requiredClosedR0) C)
    (A : C.operationDistance.GeometryState) : DistanceValue Nat :=
  R.marginProfile.Margin A

/-- VII.R9 / AC13: expose the selected architectural Dehn value. -/
def dehnValue (R : RepairMarginDehnContext
    (rawR0 := rawR0) (schemeR0 := schemeR0) (readingR0 := readingR0)
    (readingClosedR0 := readingClosedR0) (requiredClosedR0 := requiredClosedR0) C)
    (n : Nat) : Nat :=
  R.dehnProfile.δ_AAT n

end RepairMarginDehnContext

end RepresentationAnalysis
end AAT.AG
