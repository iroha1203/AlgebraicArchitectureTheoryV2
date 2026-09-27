import ResearchLean.AG.ProtocolHolonomy.HolonomyChoice
import ResearchLean.AG.ProtocolHolonomy.ChoiceChange
import Formal.Util.AssertStandardAxioms

/-!
# Root coordinate changes preserve the original right lift action

The coordinate action is read from literal multiplication in the original
state-change group. Its root value is the requested right composition of
fiber maps, and changing roots gives the same original A1 lift.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- The C1 root coordinates of the actual right vertical action. -/
noncomputable def rootRightAction (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (b : D.RootSolutions R g.1.1)
    (c : D.RootCentralizers R) : D.RootSolutions R g.1.1 :=
  (D.verticalRightAction H g (b.toLift D R)
    (D.reconstructVertical R c)).toRootSolutions D R

/-- At each root, the coordinate action is the original right composition
`(φ·α)_r = φ_r ∘ α_r`. -/
theorem rootRightAction_rootFiber (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (b : D.RootSolutions R g.1.1)
    (c : D.RootCentralizers R) (j : FixedFComponent Q) :
    (D.rootRightAction R H g b c).rootFiber j =
      (c j).1.trans (b.rootFiber j) := by
  apply Equiv.ext
  intro x
  change (D.verticalRightAction H g (b.toLift D R)
      (D.reconstructVertical R c)).fiber (R.root j) x = _
  rw [D.verticalRightAction_fiber_apply H g]
  rw [← b.reconstructedFiber_root D R j]
  have hc := congrFun (D.verticalRootEvaluation_reconstruct R c) j
  have hc' := congrArg Subtype.val hc
  change (D.reconstructVertical R c).fiber (R.root j) = (c j).1 at hc'
  rw [hc']
  rfl

/-- Root changes commute with C's actual right torsor action, including
the changed centralizer coordinates. -/
theorem liftChoiceChange_rootRightAction (R R' : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (g : D.LiftableVisible H) (b : D.RootSolutions R g.1.1)
    (c : D.RootCentralizers R) :
    D.liftChoiceChange R R' g.1.1 (D.rootRightAction R H g b c) =
      D.rootRightAction R' H g
        (D.liftChoiceChange R R' g.1.1 b)
        (D.verticalChoiceChange R R' c) := by
  apply (D.liftEquivRootSolutions R' g.1.1).symm.injective
  change (D.liftChoiceChange R R' g.1.1
      (D.rootRightAction R H g b c)).toLift D R' =
    (D.rootRightAction R' H g
      (D.liftChoiceChange R R' g.1.1 b)
      (D.verticalChoiceChange R R' c)).toLift D R'
  rw [D.liftChoiceChange_reconstruct R R']
  simp only [rootRightAction, Lift.toRootSolutions_toLift]
  rw [D.liftChoiceChange_reconstruct R R',
    D.verticalChoiceChange_reconstruct R R']

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootRightAction
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootRightAction_rootFiber
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftChoiceChange_rootRightAction
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
