import ResearchLean.AG.RelativeRepairComposition.W3ActualArrows

/-! # W3's independent actual local repairs and original restrictions

Every local family uses the selected original edge operations and physical
vertices. Empty permission fixes every selected edge, including the two
one-edge patches, while retaining every permitted original vertex label.
-/
namespace AAT.AG.RelativeRepairComposition.W3LocalRepairs
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3ActualRepairs W3ActualArrows
attribute [local instance] actualAction

/-- Independent full affine repairs on any original closed patch. -/
abbrev LocalRepairs (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Repair (ClosedRegion.presentation U) (restrictOperations U (reference sheared))
    (fun f => comparison f.1) (ClosedRegion.restrictedEdges U (fixedEdges S))

/-- Every actual local arrow retains the same original physical and forbidden conditions. -/
abbrev LocalCategory (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Groupoid (ClosedRegion.presentation U) (restrictOperations U (reference sheared))
    (restrictOperations U (reference sheared)) (fun f => comparison f.1)
    (restricted_faces U (reference sheared) (linear_faces sheared))
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U (fixedEdges S))

/-- All original affine translation labels on each selected patch. -/
noncomputable abbrev LocalLabels (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.gaugeLabels (ClosedRegion.presentation U) (restrictOperations U (reference sheared))
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U (fixedEdges S))

/-- The unchanged original reference restricts to each actual local repair family. -/
noncomputable def localReferenceRepair (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) : LocalRepairs sheared U S :=
  restrictAffineRepair U (reference sheared) comparison (fixedEdges S) (referenceRepair sheared S)

/-- Empty permission fixes every selected original edge. -/
theorem local_fixed_all (U : ClosedRegion geometry)
    (e : EdgeName (K := ClosedRegion.presentation U)) :
    e ∈ ClosedRegion.restrictedEdges U (fixedEdges ∅) := by
  change (ClosedRegion.edgeNameEquiv U e).1 ∈ fixedEdges ∅
  rw [fixed_empty]
  exact Set.mem_univ _

/-- Every local operation under empty permission is the same selected original reference. -/
theorem local_empty_operation (sheared : Bool) (U : ClosedRegion geometry)
    (R : LocalRepairs sheared U ∅)
    {i j : (ClosedRegion.presentation U).Vertex} (e : (ClosedRegion.presentation U).Edge i j) :
    R.operation e = restrictOperations U (reference sheared) e :=
  R.fixed_value ⟨i,j,e⟩ (local_fixed_all U ⟨i,j,e⟩)

/-- Every original restricted patch has one entire unchanged actual repair object. -/
theorem local_empty_unique (sheared : Bool) (U : ClosedRegion geometry)
    (R : LocalRepairs sheared U ∅) : R = localReferenceRepair sheared U ∅ := by
  apply NativeAffine.Repair.ext
  intro i j e
  exact local_empty_operation sheared U R e

/-- Whole original local repair families have both inverse point coordinates. -/
noncomputable def localEmptyObjectEquiv (sheared : Bool) (U : ClosedRegion geometry) :
    LocalRepairs sheared U ∅ ≃ Unit where
  toFun _ := ()
  invFun _ := localReferenceRepair sheared U ∅
  left_inv R := (local_empty_unique sheared U R).symm
  right_inv _ := rfl

/-- The actual global-to-local restriction keeps the selected operations and every full vertex label. -/
noncomputable def actualRestriction (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) : ActualCategory sheared S ⥤ LocalCategory sheared U S :=
  affineRestrictionFunctor U (reference sheared) (reference sheared) comparison (linear_faces sheared)
    (fixedEdges S) fixedRegion.vertices

/-- Each patch's original full affine gauge action. -/
noncomputable local instance localAction (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) :
    AddAction (LocalLabels sheared U S) (LocalRepairs sheared U S) :=
  gaugeAddAction (ClosedRegion.presentation U) (restrictOperations U (reference sheared))
    (restrictOperations U (reference sheared)) (fun f => comparison f.1)
    (restricted_faces U (reference sheared) (linear_faces sheared))
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U (fixedEdges S))

/-- Actual restriction evaluates to the very same selected original edge operation. -/
theorem restriction_operation (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) (R : ActualCategory sheared S)
    {i j : (ClosedRegion.presentation U).Vertex} (e : (ClosedRegion.presentation U).Edge i j) :
    ((actualRestriction sheared U S).obj R).back.operation e = R.back.operation e.1 := rfl

/-- Actual restriction keeps every complete original vertex-label vector. -/
theorem restriction_label (sheared : Bool) (U : ClosedRegion geometry)
    (S : Set (EdgeName (K := geometry))) {R Q : ActualCategory sheared S} (f : R ⟶ Q)
    (v : (ClosedRegion.presentation U).Vertex) :
    ((actualRestriction sheared U S).map f).1.toAdd.1 v = f.1.toAdd.1 v.1 := rfl

end AAT.AG.RelativeRepairComposition.W3LocalRepairs
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3LocalRepairs
