import ResearchLean.AG.RelativeRepairComposition.W3LocalLabels
import ResearchLean.AG.RelativeRepairComposition.W3AuthoredOperations

/-! # Entire independent W3 local affine operations

Each original one-edge patch operation is determined on the whole A by
its actual linear part and full value at zero, for every permission. The
original overlap has no edge and its independent object is unique for all S.
-/
namespace AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3AuthoredOperations
open W3ActualRepairs W3LocalRepairs W3LocalLabels

/-- Every selected U edge keeps the same original typed e name. -/
theorem left_name (e : EdgeName (K := ClosedRegion.presentation leftRegion)) :
    (ClosedRegion.edgeNameEquiv leftRegion e).1 = name edgeE :=
  (ClosedRegion.edgeNameEquiv leftRegion e).2

/-- Every selected V edge keeps the same original typed f name. -/
theorem right_name (e : EdgeName (K := ClosedRegion.presentation rightRegion)) :
    (ClosedRegion.edgeNameEquiv rightRegion e).1 = name edgeF :=
  (ClosedRegion.edgeNameEquiv rightRegion e).2

/-- The whole selected U typed edge family consists of its actual original e. -/
theorem left_typed_name (e : EdgeName (K := ClosedRegion.presentation leftRegion)) : e = leftEdge := by
  apply (ClosedRegion.edgeNameEquiv leftRegion).injective
  exact Subtype.ext (left_name e)

/-- The whole selected V typed edge family consists of its actual original f. -/
theorem right_typed_name (e : EdgeName (K := ClosedRegion.presentation rightRegion)) : e = rightEdge := by
  apply (ClosedRegion.edgeNameEquiv rightRegion).injective
  exact Subtype.ext (right_name e)

/-- Every independent actual U operation keeps the identity linear part and its whole correction vector. -/
theorem left_operation_apply (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (R : LocalRepairs sheared leftRegion S) {i j : (ClosedRegion.presentation leftRegion).Vertex}
    (e : (ClosedRegion.presentation leftRegion).Edge i j) (x : A) :
    R.operation e x = x + R.operation leftEdge.2.2 0 := by
  rw [NativeAffine.operation_apply,R.linear]
  have hr : (restrictOperations leftRegion (reference sheared) e).linear x = x := by
    exact congrArg (fun e : EdgeName (K := geometry) => (reference sheared e.2.2).linear x)
      (left_name ⟨i,j,e⟩)
  have hz : R.operation e 0 = R.operation leftEdge.2.2 0 :=
    congrArg (fun e : EdgeName (K := ClosedRegion.presentation leftRegion) => R.operation e.2.2 0)
      (left_typed_name ⟨i,j,e⟩)
  rw [hr,hz]

/-- Every independent actual V operation keeps the original full T and its whole correction vector. -/
theorem right_operation_apply (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (R : LocalRepairs sheared rightRegion S) {i j : (ClosedRegion.presentation rightRegion).Vertex}
    (e : (ClosedRegion.presentation rightRegion).Edge i j) (x : A) :
    R.operation e x = linearAction sheared x + R.operation rightEdge.2.2 0 := by
  rw [NativeAffine.operation_apply,R.linear]
  have hr : (restrictOperations rightRegion (reference sheared) e).linear x = linearAction sheared x := by
    exact congrArg (fun e : EdgeName (K := geometry) => (reference sheared e.2.2).linear x)
      (right_name ⟨i,j,e⟩)
  have hz : R.operation e 0 = R.operation rightEdge.2.2 0 :=
    congrArg (fun e : EdgeName (K := ClosedRegion.presentation rightRegion) => R.operation e.2.2 0)
      (right_typed_name ⟨i,j,e⟩)
  rw [hr,hz]

/-- The original overlap has one entire actual repair object for every S. -/
theorem overlap_unique (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (R : LocalRepairs sheared overlap S) : R = localReferenceRepair sheared overlap S := by
  apply NativeAffine.Repair.ext
  intro i j e
  exact (overlap_no_edge ⟨i,j,e⟩).elim

/-- The whole original overlap object family has both inverse point coordinates for every S. -/
noncomputable def overlapObjectEquiv (sheared : Bool) (S : Set (EdgeName (K := geometry))) :
    LocalRepairs sheared overlap S ≃ Unit where
  toFun _ := ()
  invFun _ := localReferenceRepair sheared overlap S
  left_inv R := (overlap_unique sheared S R).symm
  right_inv _ := rfl

end AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3LocalOperationCoordinates
