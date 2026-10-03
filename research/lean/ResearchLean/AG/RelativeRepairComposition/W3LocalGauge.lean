import ResearchLean.AG.RelativeRepairComposition.W3LocalFullLabels

/-! # Actual W3 local gauge equations on the entire A

These formulas evaluate the original affine conjugation on e and f. For
arbitrary independent local repairs the full value at zero characterizes
equality of their entire actual operations.
-/
namespace AAT.AG.RelativeRepairComposition.W3LocalGauge
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3AuthoredOperations
open W3ActualRepairs W3LocalRepairs W3LocalLabels W3LocalOperationCoordinates W3LocalFullLabels
attribute [local instance] localAction

/-- Actual local e conjugation changes its whole correction by b_t-b_s. -/
theorem left_gauge_zero (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : LocalLabels sheared leftRegion S) (R : LocalRepairs sheared leftRegion S) :
    (b +ᵥ R).operation leftEdge.2.2 0 = R.operation leftEdge.2.2 0 + b.1 leftT - b.1 leftS := by
  change (NativeAffine.gauge (ClosedRegion.presentation leftRegion)
    (restrictOperations leftRegion (reference sheared)) (restrictOperations leftRegion (reference sheared))
    (fun f => comparison f.1) (restricted_faces leftRegion (reference sheared) (linear_faces sheared))
    (ClosedRegion.restrictedVertices leftRegion fixedRegion.vertices)
    (ClosedRegion.restrictedEdges leftRegion (fixedEdges S)) b R).operation leftEdge.2.2 0 = _
  rw [NativeAffine.gauge_value]
  change b.1 leftT + R.operation leftEdge.2.2 (-b.1 leftS + 0) = _
  rw [add_zero,left_operation_apply]
  abel_nf

/-- Actual local f conjugation changes its whole correction by b_s-T b_t. -/
theorem right_gauge_zero (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : LocalLabels sheared rightRegion S) (R : LocalRepairs sheared rightRegion S) :
    (b +ᵥ R).operation rightEdge.2.2 0 =
      R.operation rightEdge.2.2 0 + b.1 rightS - linearAction sheared (b.1 rightT) := by
  change (NativeAffine.gauge (ClosedRegion.presentation rightRegion)
    (restrictOperations rightRegion (reference sheared)) (restrictOperations rightRegion (reference sheared))
    (fun f => comparison f.1) (restricted_faces rightRegion (reference sheared) (linear_faces sheared))
    (ClosedRegion.restrictedVertices rightRegion fixedRegion.vertices)
    (ClosedRegion.restrictedEdges rightRegion (fixedEdges S)) b R).operation rightEdge.2.2 0 = _
  rw [NativeAffine.gauge_value]
  change b.1 rightS + R.operation rightEdge.2.2 (-b.1 rightT + 0) = _
  rw [add_zero,right_operation_apply,map_neg]
  abel_nf

/-- Whole actual U gauge equality is precisely its entire original e correction equation. -/
theorem left_gauge_eq (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : LocalLabels sheared leftRegion S) (R Q : LocalRepairs sheared leftRegion S) :
    b +ᵥ R = Q ↔ R.operation leftEdge.2.2 0 + b.1 leftT - b.1 leftS = Q.operation leftEdge.2.2 0 := by
  constructor
  · intro h
    exact (left_gauge_zero sheared S b R).symm.trans
      (congrArg (fun R : LocalRepairs sheared leftRegion S => R.operation leftEdge.2.2 0) h)
  · intro h
    apply NativeAffine.Repair.ext
    intro i j e
    apply AffineEquiv.ext
    intro x
    rw [left_operation_apply sheared S (b +ᵥ R) e x,
      left_operation_apply sheared S Q e x,left_gauge_zero,h]

/-- Whole actual V gauge equality is precisely its entire original f correction equation with full T. -/
theorem right_gauge_eq (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : LocalLabels sheared rightRegion S) (R Q : LocalRepairs sheared rightRegion S) :
    b +ᵥ R = Q ↔ R.operation rightEdge.2.2 0 + b.1 rightS - linearAction sheared (b.1 rightT) =
      Q.operation rightEdge.2.2 0 := by
  constructor
  · intro h
    exact (right_gauge_zero sheared S b R).symm.trans
      (congrArg (fun R : LocalRepairs sheared rightRegion S => R.operation rightEdge.2.2 0) h)
  · intro h
    apply NativeAffine.Repair.ext
    intro i j e
    apply AffineEquiv.ext
    intro x
    rw [right_operation_apply sheared S (b +ᵥ R) e x,
      right_operation_apply sheared S Q e x,right_gauge_zero,h]

/-- The unchanged original reference has zero whole correction on every selected actual edge. -/
theorem local_reference_zero (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) {i j : (ClosedRegion.presentation U).Vertex}
    (e : (ClosedRegion.presentation U).Edge i j) :
    (localReferenceRepair sheared U S).operation e 0 = 0 :=
  reference_zero sheared e.1

end AAT.AG.RelativeRepairComposition.W3LocalGauge
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3LocalGauge
