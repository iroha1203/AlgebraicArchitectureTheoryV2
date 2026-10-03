import ResearchLean.AG.RelativeRepairComposition.W1IndexedCover
import ResearchLean.AG.RelativeRepairComposition.W1FiniteCoefficients
import ResearchLean.AG.RelativeRepairComposition.NativeAffineSubdivision
import ResearchLean.AG.RelativeRepairComposition.SubdivisionPublicNames
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSharedValues

/-!
# The specified actual W1 internal factorization on the same full affine tower

The chosen original always edge is a, private to V and outside the shared W.
The primitive full affine factors are t+1 and -t+1. Their actual product is the
same original a operation. The new vertex is free; both actual factor names
remain private in V and every original shared and candidate name remains public.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1IndexedCover
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

/-- The chosen original internal always edge is the same a name. -/
def chosen : EdgeName (K := geometry) := name edgeA

/-- The complete first real affine factor is translation by one. -/
noncomputable def first : Op := translation (k := ZMod 3) 1

/-- The complete second real affine factor has the specified nonidentity linear part. -/
noncomputable def second : Op := translation (k := ZMod 3) 1 * W1AffineInput.flip

/-- The complete first factor evaluates as t+1 at every point. -/
theorem first_apply (t : ZMod 3) : first t = t + 1 := by
  simp only [first, translation_apply, add_comm]

/-- The whole second factor evaluates as -t+1 at every point. -/
theorem second_apply (t : ZMod 3) : second t = -t + 1 := by
  simp only [second, AffineEquiv.coe_mul, Function.comp_apply, translation_apply, W1AffineInput.flip_apply, add_comm]

/-- The actual factor product is the same full original a operation. -/
theorem factor_product : second * first = W1AffineInput.flip := by
  ext t
  simp only [AffineEquiv.coe_mul, Function.comp_apply, first_apply, second_apply, W1AffineInput.flip_apply]
  abel

/-- The designated factors recover the original selected reference for every symbolic input value. -/
theorem factor_reference (x y : ZMod 3) : second * first = reference true x y chosen.2.2 := by
  rw [factor_product]
  simp [chosen, name, reference, linearA]

/-- Primitive full affine factors generate strongness and whole-kernel transport bijectivity on the same input tower. -/
noncomputable def factors (x y : ZMod 3) : Subdivision.Factorization (originalTower true x y) chosen :=
  NativeAffine.subdivisionFactors geometry (reference true x y) (reference true x y)
    comparison (linear_faces true x y) chosen first second (factor_reference x y)

/-- The independently defined subdivided tower retains every original face and original actual operation. -/
noncomputable abbrev splitTower (x y : ZMod 3) :=
  Subdivision.originalTower (originalTower true x y) chosen (factors x y)

/-- The chosen original a is exactly an always private variable in V. -/
theorem chosen_private : chosen ∈ ClosedRegion.privateAlwaysEdges regions fixedRegion candidates true := by
  rw [private_right]
  exact rfl

/-- All original permission masks leave the chosen a unfixed. -/
theorem chosen_not_fixed (S : Set (EdgeName (K := geometry))) : chosen ∉ fixedEdges S :=
  (always_not_fixed S).2

/-- The chosen original edge is outside the original fixed part. -/
theorem chosen_not_P : chosen ∉ fixedRegion.edges := by
  simp [geometry, chosen, fixedRegion, name, edgeA, edgeRx, edgeRy]

/-- The chosen edge is outside both distinct original candidate names. -/
theorem chosen_not_candidate : chosen ∉ candidates := by
  simp [geometry, chosen, candidates, name, edgeA, edgeB, edgeC]

/-- The chosen original a lies outside the actual shared W. -/
theorem chosen_not_W : chosen ∉ overlap.edges := by
  rw [overlap_edges]
  simp [geometry, chosen, name, edgeA, edgeE, edgeB]

/-- The complete expanded original U,V cover includes every new original cell. -/
theorem split_cover : ClosedRegion.IndexedCover
    (fun j => Subdivision.expandedRegion geometry chosen (regions j)) :=
  Subdivision.expanded_indexed_cover geometry chosen regions indexed_cover

/-- The first complete factor remains private in V. -/
theorem first_private : Subdivision.firstEdgeName geometry chosen ∈ ClosedRegion.privateAlwaysEdges
    (fun j => Subdivision.expandedRegion geometry chosen (regions j))
    (Subdivision.expandedRegion geometry chosen fixedRegion)
    (Subdivision.oldEdgeSet geometry chosen candidates) true :=
  (Subdivision.first_private_iff geometry chosen regions fixedRegion candidates chosen_not_candidate true).mpr chosen_private

/-- The second full factor also remains private in V, retaining the whole independent correction. -/
theorem second_private : Subdivision.secondEdgeName geometry chosen ∈ ClosedRegion.privateAlwaysEdges
    (fun j => Subdivision.expandedRegion geometry chosen (regions j))
    (Subdivision.expandedRegion geometry chosen fixedRegion)
    (Subdivision.oldEdgeSet geometry chosen candidates) true :=
  (Subdivision.second_private_iff geometry chosen regions fixedRegion candidates chosen_not_candidate true).mpr chosen_private

/-- The new vertex is absent from the physical fixed original part. -/
theorem fresh_not_P : (Sum.inr () : (Subdivision.presentation geometry chosen).Vertex) ∉
    (Subdivision.expandedRegion geometry chosen fixedRegion).vertices := by
  change ¬ chosen ∈ fixedRegion.edges
  exact chosen_not_P

/-- The new vertex is absent from the actual shared original W and remains a free gauge coordinate. -/
theorem fresh_not_W : (Sum.inr () : (Subdivision.presentation geometry chosen).Vertex) ∉
    (Subdivision.expandedRegion geometry chosen overlap).vertices := by
  change ¬ chosen ∈ overlap.edges
  exact chosen_not_W

end AAT.AG.RelativeRepairComposition.W1SubdivisionInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionInput
