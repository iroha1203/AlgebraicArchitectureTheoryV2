import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionCoordinates
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSharedValues

/-!
# The same full original W1 shared boundary survives internal subdivision

The chosen a is proved outside the actual W=e,b overlap. Every original shared
choice is retained literally, for all candidate permissions, all actual old
repairs, all full fresh values and every independently supplied external family.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionSharedBoundary
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1SubdivisionInput W1SubdivisionRepairs
universe uX
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
variable (x y : ZMod 3)
local notation "T" => W1AffineInput.originalTower true x y
local notation "F" => factors x y

/-- The complete actual overlap choice family is preserved by collapse of every actual new repair. -/
theorem collapse_shared (R : Solution (splitTower x y)) :
    Subdivision.sharedOld (T) overlap (Subdivision.collapseSolution (T) chosen (F) R) =
      Subdivision.sharedNew (T) chosen (F) overlap chosen_not_W R :=
  Subdivision.shared_collapse (T) chosen (F) overlap chosen_not_W R

/-- Every entire fresh kernel value preserves every original complete shared choice during restoration. -/
theorem restore_shared (R : Solution (T)) (r : ZMod 3) :
    Subdivision.sharedNew (T) chosen (F) overlap chosen_not_W
      (Subdivision.expandSolution (T) chosen (F) R ((middleCoefficient x y).symm r)) =
      Subdivision.sharedOld (T) overlap R :=
  Subdivision.shared_expand (T) chosen (F) overlap chosen_not_W R ((middleCoefficient x y).symm r)

/-- Every original permission set has exactly the same realized full actual shared relation after subdivision. -/
theorem shared_relation (S : Set (EdgeName (K := geometry))) :
    Set.range (fun R : SupportedRepair (splitTower x y) (Subdivision.oldEdgeSet geometry chosen (fixedEdges S)) =>
      Subdivision.sharedNew (T) chosen (F) overlap chosen_not_W R.1) =
    Set.range (fun R : SupportedRepair (T) (fixedEdges S) => Subdivision.sharedOld (T) overlap R.1) :=
  Subdivision.shared_relation (T) chosen (F) overlap chosen_not_W (fixedEdges S) (chosen_not_fixed S)

/-- Every independently specified external family obeys the same literal full shared compatibility test in every original range. -/
theorem external_join (S : Set (EdgeName (K := geometry))) {X : Type uX}
    (boundary : X → Subdivision.SharedValues (T) overlap) :
    Nonempty (ContextRelations.StrictJoin
      (fun R : SupportedRepair (splitTower x y) (Subdivision.oldEdgeSet geometry chosen (fixedEdges S)) =>
        Subdivision.sharedNew (T) chosen (F) overlap chosen_not_W R.1) boundary) ↔
    Nonempty (ContextRelations.StrictJoin
      (fun R : SupportedRepair (T) (fixedEdges S) => Subdivision.sharedOld (T) overlap R.1) boundary) :=
  Subdivision.external_strict_join (T) chosen (F) overlap chosen_not_W (fixedEdges S) (chosen_not_fixed S) boundary

end AAT.AG.RelativeRepairComposition.W1SubdivisionSharedBoundary
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionSharedBoundary
