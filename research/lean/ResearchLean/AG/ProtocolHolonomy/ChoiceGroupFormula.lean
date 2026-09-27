import ResearchLean.AG.ProtocolHolonomy.ChoiceGroup
import Formal.Util.AssertStandardAxioms

namespace AAT.AG.ProtocolHolonomy
open AAT.AG.RealizationReconstruction
universe u v w
namespace ReversibleData
variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- The original A2 formula evaluated in C1 coordinates at every root. -/
theorem rootPair_mul_rootFiber (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (a b : D.RootPair R H) (j : FixedFComponent Q)
    (x : D.Fiber (R.root j)) :
    (a * b).2.rootFiber j x =
      (a.2.toLift D R).fiber (b.1.1.vertex (R.root j))
        (b.2.rootFiber j x) := by
  rcases a with ⟨ga, ra⟩
  rcases b with ⟨gb, rb⟩
  let aa : D.LiftPair H := ⟨ga, ra.toLift D R⟩
  let bb : D.LiftPair H := ⟨gb, rb.toLift D R⟩
  change (((D.liftPairEquivRootPair R H)
      (aa * bb)).2.rootFiber j) x = _
  change (aa * bb).2.fiber (R.root j) x =
    aa.2.fiber (bb.1.1.vertex (R.root j)) (rb.rootFiber j x)
  rw [← rb.reconstructedFiber_root D R j]
  exact D.liftPair_mul_fiber_apply aa bb (R.root j) x

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootPair_mul_rootFiber
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
