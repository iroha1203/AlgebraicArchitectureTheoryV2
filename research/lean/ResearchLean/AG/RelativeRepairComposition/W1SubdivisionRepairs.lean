import ResearchLean.AG.RelativeRepairComposition.W1SubdivisionInput
import ResearchLean.AG.RelativeRepairComposition.W1RepairCounts
import ResearchLean.AG.RelativeRepairComposition.SubdivisionEquivalence
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedSolutions

/-!
# All independent W1 repairs after the specified internal edge subdivision

Both factor corrections and the fresh vertex use the whole native kernel.
The independently defined new repair set is equivalent to all original actual
repairs times the entire F3 first-factor correction, for every x,y and every S.
The whole native equivalence retains full arrows and its actual natural comparisons.
-/
namespace AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1ActualRepairs W1NativeLabels W1RepairCounts W1SubdivisionInput
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096

variable (x y : ZMod 3) (S : Set (EdgeName (K := geometry)))
local notation "T" => W1AffineInput.originalTower true x y
local notation "F" => factors x y

/-- Every element of the actual entire intermediate categorical kernel has its full F3 coordinate. -/
noncomputable def middleCoefficient :
    Additive (Kernel (GroupExtension.projection (projection (k := ZMod 3) (A := ZMod 3)))
      (GroupExtension.terminal (ZMod 3 ≃ₗ[ZMod 3] ZMod 3)) (F).middle) ≃+ ZMod 3 :=
  NativeAffine.coefficient geometry (reference true x y) (reference true x y)
    comparison (linear_faces true x y) ()

/-- The complete independent new native repair type fixes exactly the retained physical and forbidden original names. -/
abbrev NewRepairs := SupportedRepair (splitTower x y) (Subdivision.oldEdgeSet geometry chosen (fixedEdges S))

/-- The full independent new repair set has all original actual repairs and an arbitrary entire first correction, with both inverse maps. -/
noncomputable def repairEquiv : NewRepairs x y S ≃ RealRepairs true x y S × ZMod 3 :=
  (Subdivision.supportedSolutionEquiv (T) chosen (F) (fixedEdges S) (chosen_not_fixed S)).trans
    (Equiv.prodCongr
      (NativeAffine.repairEquivalence geometry (reference true x y) (reference true x y)
        comparison (linear_faces true x y) (fixedEdges S)) (middleCoefficient x y).toEquiv)

/-- The full new repair count is three times the count of all original actual repairs, for every original permission set. -/
theorem repair_card : Nat.card (NewRepairs x y S) = Nat.card (RealRepairs true x y S) * 3 := by
  have ht : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [Nat.card_congr (repairEquiv x y S), Nat.card_prod, ht]

/-- The unchanged empty-range count is nine at zero d and zero at nonzero d, including all first corrections. -/
theorem empty_card : Nat.card (NewRepairs x y ∅) = if y - x = 0 then 9 else 0 := by
  rw [repair_card, negative_empty_card]
  split <;> rfl

/-- The complete b-only new actual repair set has nine elements. -/
theorem b_card : Nat.card (NewRepairs x y {name edgeB}) = 9 := by
  rw [repair_card, negative_b_card]

/-- The complete c-only new actual repair set has nine elements. -/
theorem c_card : Nat.card (NewRepairs x y {name edgeC}) = 9 := by
  rw [repair_card, negative_c_card]

/-- Both candidate permissions retain all twenty-seven new actual repairs. -/
theorem full_card : Nat.card (NewRepairs x y candidates) = 27 := by
  rw [repair_card, negative_full_card]

/-- The whole native new repair groupoid fixes the old vertex and leaves the fresh vertex free. -/
abbrev NewCategory := RepairGroupoid (splitTower x y) (Sum.inl '' fixedRegion.vertices)
  (Subdivision.oldEdgeSet geometry chosen (fixedEdges S))

/-- All actual old and new repairs and their full label arrows are equivalent on the same original permission set. -/
noncomputable def nativeEquivalence : NativeCategory true x y S ≌ NewCategory x y S :=
  Subdivision.equivalence (T) chosen (F) fixedRegion.vertices (fixedEdges S) (chosen_not_fixed S)

/-- The new natural comparison label is zero at the original fixed vertex and carries the actual entire first correction at the fresh vertex. -/
theorem counit_full_label (R : NewCategory x y S) :
    (((nativeEquivalence x y S).counitIso.hom.app R).1.toAdd.1 (.inl ())) = 0 ∧
      (((nativeEquivalence x y S).counitIso.hom.app R).1.toAdd.1 (.inr ())) =
        Subdivision.firstCorrection (T) chosen (F) R.back.1 :=
  ⟨Subdivision.equivalence_counit_old (T) chosen (F) fixedRegion.vertices (fixedEdges S) (chosen_not_fixed S) R (),
    Subdivision.equivalence_counit_fresh (T) chosen (F) fixedRegion.vertices (fixedEdges S) (chosen_not_fixed S) R⟩

/-- No native automorphism label is discarded: the full new hom-set has at most one arrow. -/
theorem hom_unique {R Q : NewCategory x y S} (f g : R ⟶ Q) : f = g := by
  apply (Subdivision.collapseHomEquiv (T) chosen (F) fixedRegion.vertices
    (fixedEdges S) (chosen_not_fixed S) R Q).injective
  exact W1NativeLabels.hom_unique _ _

/-- Every native new automorphism is the identity arrow with its full original label. -/
theorem aut_identity (R : NewCategory x y S) (f : R ⟶ R) : f = 𝟙 R := hom_unique x y S f (𝟙 R)

end AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1SubdivisionRepairs
