import ResearchLean.AG.RelativeRepairComposition.SubdivisionFixedPublicValues
import ResearchLean.AG.RelativeRepairComposition.C20SubdivisionCoverRegression

/-!
# A fixed original edge is physically public with prescribed zero correction

## Implementation notes

This additional input uses the same original W4 geometry, full affine tower and
actual factors, with b fixed and no candidates. The authored face is retained
in the complete member. Both zero and nonzero whole-kernel public values are
examined: zero satisfies the physical fixed condition, while translation by
one fails it. This tests the previously empty fixed-edge case without changing
the specified W4 or adding fixed edges as free finite variables.
-/
namespace AAT.AG.RelativeRepairComposition.C20FixedPublicRegression
open TransportCoherence Subdivision C17SubdivisionInput
open C20SubdivisionCoverRegression

/-- A closed part fixes the actual old b edge and its old endpoints. -/
def fixedB : ClosedRegion geometry where
  vertices := Set.univ
  edges := {candidate}
  faces := ∅
  triples := ∅
  edge_closed := by intro _ _; exact ⟨trivial,trivial⟩
  face_closed := by intro _ h; exact h.elim
  triple_closed := by intro _ h; exact h.elim

/-- This input has no candidate edges, while a remains private in the full member. -/
theorem chosen_private_fixed : chosen ∈ ClosedRegion.privateAlwaysEdges regions fixedB ∅ false := by
  refine ⟨trivial,?_,fun h => h,?_⟩
  · exact chosen_ne_candidate
  · rintro ⟨j,hj,he⟩
    cases j
    · exact hj rfl
    · exact he

/-- The original fixed b is a full public name despite its prescribed correction. -/
theorem fixed_public : candidate ∈ CompletePublic.publicEdges geometry regions fixedB ∅ false :=
  CompletePublic.fixed_public geometry regions fixedB ∅ false candidate trivial rfl

/-- Fixed b is absent from the finite free public coordinates. -/
theorem fixed_not_free_public : candidate ∉ publicEdges geometry regions fixedB ∅ false :=
  fun h => h.2.1 rfl

/-- The retained fixed b is in the independently generated complete new public family. -/
theorem split_fixed_public : oldEdgeName geometry chosen candidate chosen_ne_candidate.symm ∈
    CompletePublic.publicEdges (presentation geometry chosen)
      (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedB)
      (oldEdgeSet geometry chosen ∅) false := by
  rw [CompletePublic.expanded_public_edges geometry chosen regions fixedB ∅ (fun h => h)]
  exact fixed_public

/-- The new public comparison reads exactly the full original fixed b name. -/
theorem fixed_name_value :
    (CompletePublic.publicNameEquiv geometry chosen regions fixedB ∅ false chosen_private_fixed false
      ⟨oldEdgeName geometry chosen candidate chosen_ne_candidate.symm,split_fixed_public⟩).1 = candidate := rfl

/-- The independently generated fixed part contains this same retained full b name. -/
theorem split_fixed_membership : oldEdgeName geometry chosen candidate chosen_ne_candidate.symm ∈
    (expandedRegion geometry chosen fixedB).edges := rfl

/-- A zero correction at every full public name meets every actual fixed condition. -/
theorem zero_physical : CompletePublic.PublicKernels.fixedZero geometry regions fixedB ∅ originalTower false
    (fun _ => 0) := fun _ _ => rfl

/-- Translation by one is an actual full-kernel value at each full public name. -/
noncomputable def nonzeroValues (e : CompletePublic.publicEdges geometry regions fixedB ∅ false) :
    originalTower.toTower.localCoefficients.A e.1.2.1 :=
  (NativeAffine.coefficient geometry reference reference comparison linear_faces e.1.2.1).symm 1

/-- The nonzero original fixed value is rejected by the independently defined physical condition. -/
theorem nonzero_not_physical :
    ¬ CompletePublic.PublicKernels.fixedZero geometry regions fixedB ∅ originalTower false nonzeroValues := by
  intro h
  have hz := h ⟨candidate,fixed_public⟩ rfl
  have hv := congrArg (NativeAffine.coefficient geometry reference reference comparison linear_faces ()) hz
  change NativeAffine.coefficient geometry reference reference comparison linear_faces ()
    ((NativeAffine.coefficient geometry reference reference comparison linear_faces ()).symm 1) = _ at hv
  rw [AddEquiv.apply_symm_apply,map_zero] at hv
  exact (one_ne_zero : (1 : ZMod 3) ≠ 0) hv

/-- All physical data have both inverse compositions under the general full actual comparison. -/
noncomputable def physicalValuesEquiv :=
  CompletePublic.PublicKernels.physicalFamilyEquiv geometry chosen regions fixedB ∅
    originalTower factors false chosen_private_fixed false

/-- The comparison retains the actual prescribed zero at the original fixed b edge. -/
theorem physical_fixed_value
    (x : {x : ∀ a : CompletePublic.publicEdges (presentation geometry chosen)
      (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedB)
      (oldEdgeSet geometry chosen ∅) false, splitTower.toTower.localCoefficients.A a.1.2.1 //
      CompletePublic.PublicKernels.fixedZero (presentation geometry chosen)
        (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedB)
        (oldEdgeSet geometry chosen ∅) splitTower false x}) :
    (physicalValuesEquiv x).1 ⟨candidate,fixed_public⟩ = 0 :=
  (physicalValuesEquiv x).2 ⟨candidate,fixed_public⟩ rfl

/-- New and old independently imposed physical predicates agree on every full public family. -/
theorem fixed_condition_iff
    (x : ∀ a : CompletePublic.publicEdges (presentation geometry chosen)
      (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedB)
      (oldEdgeSet geometry chosen ∅) false, splitTower.toTower.localCoefficients.A a.1.2.1) :
    CompletePublic.PublicKernels.fixedZero (presentation geometry chosen)
      (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedB)
      (oldEdgeSet geometry chosen ∅) splitTower false x ↔
    CompletePublic.PublicKernels.fixedZero geometry regions fixedB ∅ originalTower false
      (CompletePublic.PublicKernels.familyEquiv geometry chosen regions fixedB ∅
        originalTower factors false chosen_private_fixed false x) :=
  CompletePublic.PublicKernels.fixedZero_iff geometry chosen regions fixedB ∅
    originalTower factors false chosen_private_fixed false x

/-- The independently generated new fixed condition also accepts the whole zero family. -/
theorem split_zero_physical :
    CompletePublic.PublicKernels.fixedZero (presentation geometry chosen)
      (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedB)
      (oldEdgeSet geometry chosen ∅) splitTower false (fun _ => 0) := fun _ _ => rfl

/-- Restore every whole actual value of the rejected old family along the full name inverse. -/
noncomputable def splitNonzeroValues :=
  (CompletePublic.PublicKernels.familyEquiv geometry chosen regions fixedB ∅
    originalTower factors false chosen_private_fixed false).symm nonzeroValues

/-- The same nonzero original fixed value is rejected after actual subdivision. -/
theorem split_nonzero_not_physical :
    ¬ CompletePublic.PublicKernels.fixedZero (presentation geometry chosen)
      (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedB)
      (oldEdgeSet geometry chosen ∅) splitTower false splitNonzeroValues := by
  intro h
  apply nonzero_not_physical
  have hh := (fixed_condition_iff splitNonzeroValues).mp h
  simpa only [splitNonzeroValues,Equiv.apply_symm_apply] using hh

/-- Every new permission set has the same empty forbidden candidate condition at the fixed edge. -/
theorem fixed_mask (S : Set (EdgeName (K := geometry))) :
    oldEdgeName geometry chosen candidate chosen_ne_candidate.symm ∉ oldEdgeSet geometry chosen (∅ \ S) := by
  rw [CompletePublic.retained_forbidden_mask geometry chosen ∅ (fun h => h)]
  exact fun h => h.1

end AAT.AG.RelativeRepairComposition.C20FixedPublicRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C20FixedPublicRegression
