import Formal.AG.RepresentationAnalysis.Metric
import Formal.AG.LawAlgebra.LawfulLocus

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w

/--
VII.定義10.1: operation distance profile.

The profile is relative to selected operation cost, path length, and homotopy
filling-cost readings.  It does not assert that the distance determines
lawfulness or flatness.
-/
structure OperationDistanceProfile {U : AtomCarrier.{u}}
    (Obj : ArchitectureObject U) where
  operationCost : OperationCost Obj
  pathLength : PathLength operationCost
  homotopyFillingCost : HomotopyFillingCost Obj
  GeometryState : Type u
  operationPath : GeometryState -> GeometryState -> Type u
  pathCost : ∀ {A B : GeometryState}, operationPath A B -> DistanceValue Nat
  pathLengthValue :
    ∀ {A B : GeometryState}, operationPath A B -> DistanceValue Nat
  fillingCostValue :
    ∀ {A B : GeometryState}, operationPath A B -> DistanceValue Nat
  distance : GeometryState -> GeometryState -> DistanceValue Nat
  distance_reading :
    ∀ A B, ∃ path : operationPath A B, distance A B = pathCost path

namespace OperationDistanceProfile

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}

/-- VII.定義10.1: operation distance `d_op(A,B)`. -/
def d_op (P : OperationDistanceProfile Obj)
    (A B : P.GeometryState) : DistanceValue Nat :=
  P.distance A B

/-- VII.定義10.1: expose the selected operation-path witness for `d_op`. -/
theorem d_op_has_path_witness (P : OperationDistanceProfile Obj)
    (A B : P.GeometryState) :
    ∃ path : P.operationPath A B, P.d_op A B = P.pathCost path :=
  P.distance_reading A B

end OperationDistanceProfile

/-- VII.定義10.2: selected infimum interface for distance-to-flatness. -/
structure CostInfimumDomain (Cost : Type u) where
  infimum : {Index : Type u} -> (Index -> Cost) -> Cost
  isLowerBound : {Index : Type u} -> (Index -> Cost) -> Cost -> Prop
  isGreatestLowerBound : {Index : Type u} -> (Index -> Cost) -> Cost -> Prop
  infimum_isGreatestLowerBound :
    {Index : Type u} -> (values : Index -> Cost) ->
      isGreatestLowerBound values (infimum values)

namespace CostInfimumDomain

variable {Cost : Type u}

/-- VII.定義10.2: expose the selected greatest-lower-bound certificate. -/
theorem infimum_glb (D : CostInfimumDomain Cost)
    {Index : Type u} (values : Index -> Cost) :
    D.isGreatestLowerBound values (D.infimum values) :=
  D.infimum_isGreatestLowerBound values

end CostInfimumDomain

/--
VII.定義10.2: distance to selected flatness candidates.

`dist_flat_U(A)` is an infimum reading over selected candidates `F` satisfying
the chosen flatness/factorization predicate.  This definition alone does not
reflect lawfulness from zero distance.
-/
structure DistanceToFlatnessProfile {U : AtomCarrier.{u}}
    {Obj : ArchitectureObject U}
    (operationDistance : OperationDistanceProfile Obj) where
  Cost : Type u
  costDomain : CostInfimumDomain Cost
  costToDistanceValue : Cost -> DistanceValue Nat
  FlatCandidate : operationDistance.GeometryState -> Type u
  flatState :
    ∀ A, FlatCandidate A -> operationDistance.GeometryState
  factorsThroughFlat :
    ∀ A, FlatCandidate A -> Prop
  candidateDistance :
    ∀ A, FlatCandidate A -> Cost
  candidateDistance_reads_d_op :
    ∀ A (candidate : FlatCandidate A),
      costToDistanceValue (candidateDistance A candidate) =
        operationDistance.d_op A (flatState A candidate)
  candidateFactorsThroughFlat :
    ∀ A (candidate : FlatCandidate A), factorsThroughFlat A candidate

namespace DistanceToFlatnessProfile

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {operationDistance : OperationDistanceProfile Obj}

/-- VII.定義10.2: `dist_flat_U(A)` as the selected infimum reading. -/
def dist_flat (P : DistanceToFlatnessProfile operationDistance)
    (A : operationDistance.GeometryState) : P.Cost :=
  P.costDomain.infimum (P.candidateDistance A)

/-- VII.定義10.2: distance-to-flatness as an enriched `DistanceValue`. -/
def dist_flat_value (P : DistanceToFlatnessProfile operationDistance)
    (A : operationDistance.GeometryState) : DistanceValue Nat :=
  P.costToDistanceValue (P.dist_flat A)

/-- VII.定義10.2: the selected infimum certificate for `dist_flat_U(A)`. -/
theorem dist_flat_isGreatestLowerBound
    (P : DistanceToFlatnessProfile operationDistance)
    (A : operationDistance.GeometryState) :
    P.costDomain.isGreatestLowerBound (P.candidateDistance A) (P.dist_flat A) :=
  P.costDomain.infimum_glb (P.candidateDistance A)

/--
VII.定義10.2: each selected flat-candidate cost reads the corresponding
operation distance `d_op(A,F)`.
-/
theorem candidateDistance_reads_d_op_certificate
    (P : DistanceToFlatnessProfile operationDistance)
    (A : operationDistance.GeometryState)
    (candidate : P.FlatCandidate A) :
    P.costToDistanceValue (P.candidateDistance A candidate) =
      operationDistance.d_op A (P.flatState A candidate) :=
  P.candidateDistance_reads_d_op A candidate

/--
VII.定義10.2 boundary: zero distance reflecting factorization is an explicit
predicate, not a theorem supplied by `dist_flat`.
-/
def DistanceZeroReflectsFactorization
    (P : DistanceToFlatnessProfile operationDistance) : Prop :=
  ∀ A,
    P.dist_flat_value A = DistanceValue.measuredZero ->
      ∃ candidate : P.FlatCandidate A, P.factorsThroughFlat A candidate

end DistanceToFlatnessProfile

/-- VII.定義11.1: selected obstruction measure readings `mu_Ob` and `mu_I`. -/
structure SelectedObstructionMeasure {U : AtomCarrier.{u}}
    (Obj : ArchitectureObject U) where
  ObstructionSupport : Type u
  IdealSupport : Type u
  mu_Ob : ObstructionSupport -> DistanceValue Nat
  mu_I : IdealSupport -> DistanceValue Nat
  selectedObstructionSupport : Set ObstructionSupport
  selectedIdealSupport : Set IdealSupport
  muObSupported :
    ∀ obstruction, obstruction ∈ selectedObstructionSupport ->
      (mu_Ob obstruction).IsMeasured
  muISupported :
    ∀ ideal, ideal ∈ selectedIdealSupport -> (mu_I ideal).IsMeasured

namespace SelectedObstructionMeasure

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}

/-- VII.定義11.1: expose selected obstruction-measure support. -/
theorem muOb_supported (M : SelectedObstructionMeasure Obj)
    {obstruction : M.ObstructionSupport}
    (h : obstruction ∈ M.selectedObstructionSupport) :
    (M.mu_Ob obstruction).IsMeasured :=
  M.muObSupported obstruction h

/-- VII.定義11.1: expose selected ideal-measure support. -/
theorem muI_supported (M : SelectedObstructionMeasure Obj)
    {ideal : M.IdealSupport}
    (h : ideal ∈ M.selectedIdealSupport) :
    (M.mu_I ideal).IsMeasured :=
  M.muISupported ideal h

end SelectedObstructionMeasure

/--
VII.定義11.2: finite-support obstruction mass.

The finite support list, measured contribution, and integral/sum interface are
explicit selected data.  General measure theory is not constructed here.
-/
structure FiniteSupportObstructionMass {U : AtomCarrier.{u}}
    {Obj : ArchitectureObject U}
    (measure : SelectedObstructionMeasure Obj)
    (EvaluationPoint : Type u) where
  finiteSupport : EvaluationPoint -> List measure.ObstructionSupport
  supportCoversSelected :
    ∀ A obstruction, obstruction ∈ measure.selectedObstructionSupport ->
      obstruction ∈ finiteSupport A
  measuredContribution : EvaluationPoint -> measure.ObstructionSupport -> Nat
  measuredContribution_eq_zero_of_not_mem :
    ∀ A obstruction, obstruction ∉ finiteSupport A ->
      measuredContribution A obstruction = 0
  finiteSum : EvaluationPoint -> (measure.ObstructionSupport -> Nat) -> Nat
  finiteIntegral : EvaluationPoint -> (measure.ObstructionSupport -> Nat) -> Nat
  mass : EvaluationPoint -> Nat
  mass_eq_finiteSum :
    ∀ A, mass A = finiteSum A (measuredContribution A)
  finiteIntegral_eq_finiteSum :
    ∀ A,
      finiteIntegral A (measuredContribution A) =
        finiteSum A (measuredContribution A)

namespace FiniteSupportObstructionMass

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {measure : SelectedObstructionMeasure Obj}
variable {EvaluationPoint : Type u}

/-- VII.定義11.2: selected obstruction mass `Mass_U(A)`. -/
def Mass_U (M : FiniteSupportObstructionMass measure EvaluationPoint)
    (A : EvaluationPoint) : Nat :=
  M.mass A

/-- VII.定義11.2: mass is read by the selected finite sum. -/
theorem mass_eq_sum (M : FiniteSupportObstructionMass measure EvaluationPoint)
    (A : EvaluationPoint) :
    M.Mass_U A = M.finiteSum A (M.measuredContribution A) :=
  M.mass_eq_finiteSum A

/-- VII.定義11.2: finite integral agrees with the selected finite sum. -/
theorem finiteIntegral_eq_sum
    (M : FiniteSupportObstructionMass measure EvaluationPoint)
    (A : EvaluationPoint) :
    M.finiteIntegral A (M.measuredContribution A) =
      M.finiteSum A (M.measuredContribution A) :=
  M.finiteIntegral_eq_finiteSum A

/-- VII.定義11.2: support list covers selected obstruction support. -/
theorem mem_finiteSupport_of_selected
    (M : FiniteSupportObstructionMass measure EvaluationPoint)
    (A : EvaluationPoint)
    {obstruction : measure.ObstructionSupport}
    (h : obstruction ∈ measure.selectedObstructionSupport) :
    obstruction ∈ M.finiteSupport A :=
  M.supportCoversSelected A obstruction h

/-- VII.定義11.2: outside finite support, contribution is zero. -/
theorem contribution_zero_of_not_mem
    (M : FiniteSupportObstructionMass measure EvaluationPoint)
    (A : EvaluationPoint)
    {obstruction : measure.ObstructionSupport}
    (h : obstruction ∉ M.finiteSupport A) :
    M.measuredContribution A obstruction = 0 :=
  M.measuredContribution_eq_zero_of_not_mem A obstruction h

end FiniteSupportObstructionMass

/-- VII.定義10.1-11.2: combined R8 analytic distance / mass context. -/
structure DistanceFlatnessMassContext {U : AtomCarrier.{u}}
    (Obj : ArchitectureObject U) where
  operationDistance : OperationDistanceProfile Obj
  distanceToFlatness : DistanceToFlatnessProfile operationDistance
  obstructionMeasure : SelectedObstructionMeasure Obj
  obstructionMass :
    FiniteSupportObstructionMass obstructionMeasure operationDistance.GeometryState

namespace DistanceFlatnessMassContext

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}

/-- VII.定義10.1: context-level operation distance. -/
def d_op (C : DistanceFlatnessMassContext Obj)
    (A B : C.operationDistance.GeometryState) : DistanceValue Nat :=
  C.operationDistance.d_op A B

/-- VII.定義10.2: context-level distance to flatness. -/
def dist_flat (C : DistanceFlatnessMassContext Obj)
    (A : C.operationDistance.GeometryState) : C.distanceToFlatness.Cost :=
  C.distanceToFlatness.dist_flat A

/-- VII.定義11.2: context-level obstruction mass. -/
def Mass_U (C : DistanceFlatnessMassContext Obj)
    (A : C.operationDistance.GeometryState) : Nat :=
  C.obstructionMass.Mass_U A

end DistanceFlatnessMassContext

end RepresentationAnalysis
end AAT.AG
