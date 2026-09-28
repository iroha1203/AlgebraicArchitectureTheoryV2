import ResearchLean.AG.ProtocolHolonomy.TwoVertexSecondCycle
import Formal.Util.AssertStandardAxioms

/-!
# Every specified visible change lifts in the two-vertex example

The original C1 liftable subgroup is the range of the actual A2 projection.
Cycle 79 proved this projection reaches both elements of the chosen H.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- The second fixed example has `H_lift = H`, for the original input and
original change-group projection. -/
theorem twoVertex_liftableVisible_eq_top :
    twoVertexData.LiftableVisible twoVertexInput.H = ⊤ := by
  exact MonoidHom.range_eq_top.mpr twoVertex_projection_surjective

/-- In particular every element of the selected visible group has an
original A1 solution, not merely an abstract extension element. -/
theorem twoVertex_all_visible_lift (g : twoVertexInput.H) :
    Nonempty (twoVertexData.Lift g.1) := by
  rw [← twoVertexData.mem_liftableVisible_iff_lift]
  rw [twoVertex_liftableVisible_eq_top]
  trivial

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertex_liftableVisible_eq_top
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_all_visible_lift
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
