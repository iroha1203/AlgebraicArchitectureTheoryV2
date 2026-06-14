import Formal.AG.RepresentationAnalysis.DistanceFlatnessMass
import Formal.AG.SingularityMonodromyStack

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w z

/--
VII.定義12.1: selected repair route from a state to a flat candidate.

The route is relative to the AC12 operation-distance / distance-to-flatness
context.  The PRD-3 lawful-locus factorization is carried as explicit selected
section data; no global repair existence theorem is asserted here.
-/
structure RepairRoute {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    (C : DistanceFlatnessMassContext Obj) where
  source : C.operationDistance.GeometryState
  target : C.operationDistance.GeometryState
  flatCandidate : C.distanceToFlatness.FlatCandidate source
  target_eq_flatState : target = C.distanceToFlatness.flatState source flatCandidate
  operationPath : C.operationDistance.operationPath source target
  routeCost : DistanceValue Nat
  routeCost_eq_d_op : routeCost = C.d_op source target
  routeCost_eq_pathCost : routeCost = C.operationDistance.pathCost operationPath
  LawCoordinateAlgebra : Type v
  lawCoordinateCommRing : CommRing LawCoordinateAlgebra
  obstructionIdeal : Ideal LawCoordinateAlgebra
  lawfulSection :
    LawAlgebra.LawfulLocus.LawfulSectionData.{v, w} LawCoordinateAlgebra obstructionIdeal
  factorsThroughLawfulLocus :
    lawfulSection.FactorsThroughLawfulLocus

attribute [instance] RepairRoute.lawCoordinateCommRing

namespace RepairRoute

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {C : DistanceFlatnessMassContext Obj}

/-- VII.定義12.1: the selected target is the selected flat-candidate state. -/
theorem target_eq_flatState_holds (R : RepairRoute.{u, v, w} C) :
    R.target = C.distanceToFlatness.flatState R.source R.flatCandidate :=
  R.target_eq_flatState

/-- VII.定義12.1: the route cost reads the selected operation distance. -/
theorem routeCost_eq_d_op_holds (R : RepairRoute.{u, v, w} C) :
    R.routeCost = C.d_op R.source R.target :=
  R.routeCost_eq_d_op

/-- VII.定義12.1: the route cost is witnessed by the selected operation path. -/
theorem routeCost_eq_pathCost_holds (R : RepairRoute.{u, v, w} C) :
    R.routeCost = C.operationDistance.pathCost R.operationPath :=
  R.routeCost_eq_pathCost

/-- VII.定義12.1: expose the PRD-3 lawful-locus factorization certificate. -/
theorem factorsThroughLawfulLocus_certificate
    (R : RepairRoute.{u, v, w} C) :
    R.lawfulSection.FactorsThroughLawfulLocus :=
  R.factorsThroughLawfulLocus

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
Structural and stable profiles carry explicit selected PRD-6 / PRD-4--6
readings as data rather than deriving global correctness.
-/
structure RepairProfileReading {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    {C : DistanceFlatnessMassContext Obj} (route : RepairRoute.{u, v, w} C) where
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
variable {C : DistanceFlatnessMassContext Obj}
variable {route : RepairRoute.{u, v, w} C}

/-- VII.定義12.2: shortest repair certificate, when the selected mode is shortest. -/
theorem shortest_certificate
    (P : RepairProfileReading.{u, v, w, z} route) (h : P.mode = .shortest) :
    P.shortest :=
  P.shortest_holds h

/-- VII.定義12.2: safest repair certificate, when the selected mode is safest. -/
theorem safest_certificate
    (P : RepairProfileReading.{u, v, w, z} route) (h : P.mode = .safest) :
    P.safest :=
  P.safest_holds h

/-- VII.定義12.2: structural repair certificate, when the selected mode is structural. -/
theorem structural_certificate
    (P : RepairProfileReading.{u, v, w, z} route) (h : P.mode = .structural) :
    P.structural :=
  P.structural_holds h

/-- VII.定義12.2: stable repair certificate, when the selected mode is stable. -/
theorem stable_certificate
    (P : RepairProfileReading.{u, v, w, z} route) (h : P.mode = .stable) :
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
VII.定義12.4: architectural Dehn function interface.

The presentation two-complex is a selected PRD-6 carrier.  The Dehn function is
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

/-- VII.R9 / AC13: combined repair, margin, Dehn, and bi-Lipschitz surface. -/
structure RepairMarginDehnContext {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    (C : DistanceFlatnessMassContext Obj) where
  route : RepairRoute.{u, v, w} C
  repairProfile : RepairProfileReading.{u, v, w, z} route
  marginProfile : MarginProfile C
  dehnProfile : ArchitecturalDehnProfile.{u}
  biLipschitzProfile : BiLipschitzRepresentationProfile.{u}

namespace RepairMarginDehnContext

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {C : DistanceFlatnessMassContext Obj}

/-- VII.R9 / AC13: expose the selected repair route. -/
def selectedRoute (R : RepairMarginDehnContext.{u, v, w, z} C) :
    RepairRoute.{u, v, w} C :=
  R.route

/-- VII.R9 / AC13: expose the selected margin value. -/
def margin (R : RepairMarginDehnContext.{u, v, w, z} C)
    (A : C.operationDistance.GeometryState) : DistanceValue Nat :=
  R.marginProfile.Margin A

/-- VII.R9 / AC13: expose the selected architectural Dehn value. -/
def dehnValue (R : RepairMarginDehnContext.{u, v, w, z} C) (n : Nat) : Nat :=
  R.dehnProfile.δ_AAT n

end RepairMarginDehnContext

end RepresentationAnalysis
end AAT.AG
