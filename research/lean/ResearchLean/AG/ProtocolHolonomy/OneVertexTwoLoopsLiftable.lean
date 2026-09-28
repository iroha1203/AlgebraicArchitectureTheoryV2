import ResearchLean.AG.ProtocolHolonomy.OneVertexTwoLoopsCentralizer
import ResearchLean.AG.ProtocolHolonomy.LiftableVisible
import Formal.Util.AssertStandardAxioms

/-!
# The actual liftable visible image in the first fixed example

The visible group is C₂, but only its identity has an original A1 lift.
The result concerns the image of the actual A2 change-group projection.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- The actual projection image H_lift for the exact first-example primitive
input is the identity subgroup. -/
theorem oneLoop_H_lift_eq_bot :
    oneLoopData.LiftableVisible oneLoopInput.H = ⊥ := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    have hLift : Nonempty (oneLoopData.Lift g.1) :=
      (oneLoopData.mem_liftableVisible_iff_lift oneLoopInput.H g).mp hg
    rcases oneLoop_H_exact g with hid | hswap
    · exact Subgroup.mem_bot.mpr (Subtype.ext hid)
    · have hs : Nonempty (oneLoopData.Lift oneLoopSwap) := by
        simpa [hswap] using hLift
      exact (oneLoopSwap_noLift.false hs.some).elim
  · intro hg
    have hid : g = 1 := Subgroup.mem_bot.mp hg
    subst g
    exact Subgroup.one_mem _

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.oneLoop_H_lift_eq_bot
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
