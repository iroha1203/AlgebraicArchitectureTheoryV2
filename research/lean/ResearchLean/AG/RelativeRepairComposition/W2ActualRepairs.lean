import ResearchLean.AG.RelativeRepairComposition.W2Regions

/-!
# Independent actual affine repairs on W2 and its original patches

Repair families contain the original full affine operations and actual fixed
edge equalities. Empty permission fixes both candidate operations but keeps
the original physical vertex set. The same independent families restrict to
each original patch, including the edge-free overlap.
-/
namespace AAT.AG.RelativeRepairComposition.W2ActualRepairs
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W2AffineInput W2Regions

/-- Independent actual global repairs retain all original full affine edge values. -/
abbrev RealRepairs (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Repair geometry reference comparison (fixedEdges S)

/-- Actual global arrows retain the physical endpoints and all original permitted labels. -/
abbrev ActualCategory (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Groupoid geometry reference reference comparison linear_faces
    fixedRegion.vertices (fixedEdges S)

/-- The native original repair category uses the same original physical and candidate conditions. -/
abbrev NativeCategory (S : Set (EdgeName (K := geometry))) :=
  RepairGroupoid originalTower fixedRegion.vertices (fixedEdges S)

/-- The unchanged actual references are repairs for every permission set. -/
def referenceRepair (S : Set (EdgeName (K := geometry))) : RealRepairs S where
  operation := reference
  linear _ := rfl
  face f := f.elim
  fixed_value _ _ := rfl

/-- Empty permission determines every actual original edge operation. -/
theorem empty_operation (R : RealRepairs ∅) {i j : geometry.Vertex} (e : geometry.Edge i j) :
    R.operation e = reference e :=
  R.fixed_value ⟨i,j,e⟩ (by rw [fixed_empty]; exact Set.mem_univ _)

/-- The original unchanged actual repair is the only global object under empty permission. -/
theorem empty_unique (R : RealRepairs ∅) : R = referenceRepair ∅ := by
  apply NativeAffine.Repair.ext
  intro i j e
  exact empty_operation R e

/-- Full actual global objects under empty permission have mutually inverse point coordinates. -/
def emptyObjectEquiv : RealRepairs ∅ ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => referenceRepair ∅
  left_inv R := (empty_unique R).symm
  right_inv _ := rfl

/-- Original full actual repair objects and every original native arrow have a whole affine equivalence. -/
noncomputable def wholeAffineEquivalence (S : Set (EdgeName (K := geometry))) :
    NativeCategory S ≌ ActualCategory S :=
  NativeAffine.groupoidEquivalence geometry reference reference comparison linear_faces
    fixedRegion.vertices (fixedEdges S)

/-- Each local independent repair uses the same original selected actual edge values. -/
abbrev LocalRepairs (U : ClosedRegion geometry) (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Repair (ClosedRegion.presentation U) (restrictOperations U reference)
    (fun f => comparison f.1) (ClosedRegion.restrictedEdges U (fixedEdges S))

/-- Each original local groupoid retains complete physical restrictions and full original labels. -/
abbrev LocalCategory (U : ClosedRegion geometry) (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Groupoid (ClosedRegion.presentation U) (restrictOperations U reference)
    (restrictOperations U reference) (fun f => comparison f.1)
    (restricted_faces U reference linear_faces)
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U (fixedEdges S))

/-- Restricting the actual original reference gives the unchanged local repair. -/
noncomputable def localReferenceRepair (U : ClosedRegion geometry) (S : Set (EdgeName (K := geometry))) :
    LocalRepairs U S := restrictAffineRepair U reference comparison (fixedEdges S) (referenceRepair S)

/-- Empty permission fixes every selected original edge in every original patch. -/
theorem local_fixed_all (U : ClosedRegion geometry)
    (e : EdgeName (K := ClosedRegion.presentation U)) :
    e ∈ ClosedRegion.restrictedEdges U (fixedEdges ∅) := by
  change (ClosedRegion.edgeNameEquiv U e).1 ∈ fixedEdges ∅
  rw [fixed_empty]
  exact Set.mem_univ _

/-- Every actual local operation is its unchanged selected original reference. -/
theorem local_empty_operation (U : ClosedRegion geometry) (R : LocalRepairs U ∅)
    {i j : (ClosedRegion.presentation U).Vertex} (e : (ClosedRegion.presentation U).Edge i j) :
    R.operation e = restrictOperations U reference e :=
  R.fixed_value ⟨i,j,e⟩ (local_fixed_all U ⟨i,j,e⟩)

/-- Each original patch, including the original overlap, has a unique unchanged actual object. -/
theorem local_empty_unique (U : ClosedRegion geometry) (R : LocalRepairs U ∅) :
    R = localReferenceRepair U ∅ := by
  apply NativeAffine.Repair.ext
  intro i j e
  exact local_empty_operation U R e

/-- Full independent local objects have point coordinates with both inverses. -/
noncomputable def localEmptyObjectEquiv (U : ClosedRegion geometry) : LocalRepairs U ∅ ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => localReferenceRepair U ∅
  left_inv R := (local_empty_unique U R).symm
  right_inv _ := rfl

/-- The actual global restriction functor preserves every original selected operation and full label. -/
noncomputable def actualRestriction (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) : ActualCategory S ⥤ LocalCategory U S :=
  affineRestrictionFunctor U reference reference comparison linear_faces (fixedEdges S) fixedRegion.vertices

/-- Original actual repair restriction keeps every original selected edge exactly. -/
theorem restriction_operation (U : ClosedRegion geometry) (S : Set (EdgeName (K := geometry)))
    (R : ActualCategory S) {i j : (ClosedRegion.presentation U).Vertex}
    (e : (ClosedRegion.presentation U).Edge i j) :
    letI := gaugeAddAction geometry reference reference comparison linear_faces
      fixedRegion.vertices (fixedEdges S)
    letI := gaugeAddAction (ClosedRegion.presentation U) (restrictOperations U reference)
      (restrictOperations U reference) (fun f => comparison f.1)
      (restricted_faces U reference linear_faces)
      (ClosedRegion.restrictedVertices U fixedRegion.vertices)
      (ClosedRegion.restrictedEdges U (fixedEdges S))
    ((actualRestriction U S).obj R).back.operation e = R.back.operation e.1 := rfl

end AAT.AG.RelativeRepairComposition.W2ActualRepairs
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W2ActualRepairs
