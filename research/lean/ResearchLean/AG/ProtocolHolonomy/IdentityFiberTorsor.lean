import ResearchLean.AG.ProtocolHolonomy.IdentitySplitExact
import ResearchLean.AG.ProtocolHolonomy.LiftFiberTorsor
import Formal.Util.AssertStandardAxioms

/-!
# Original right torsors over every identity-operation visible change

Every element of the supplied H is liftable by an identity-hidden A1 lift.
The original C3 vertical group therefore acts on every H-fiber, with its
actual right-composition formula and unique displacement.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- Put every original visible element into the actual liftable image
using its explicit identity-fiber A1 lift. -/
def identityLiftableVisible
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H) :
    (identityReversibleData Q K).LiftableVisible H :=
  ⟨g, ((identityReversibleData Q K).mem_liftableVisible_iff_lift H g).2
    ⟨identityLift Q K g.1⟩⟩

/-- The original C3 right action specialized to every visible element of
the supplied H, with no selected lift built into the fiber. -/
noncomputable def identityRightAction
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H)
    (a : (identityReversibleData Q K).Lift g.1)
    (α : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q)) :
    (identityReversibleData Q K).Lift g.1 :=
  (identityReversibleData Q K).verticalRightAction H
    (identityLiftableVisible Q K H g) a α

theorem identityRightAction_one
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H)
    (a : (identityReversibleData Q K).Lift g.1) :
    identityRightAction Q K H g a 1 = a :=
  (identityReversibleData Q K).verticalRightAction_one H
    (identityLiftableVisible Q K H g) a

theorem identityRightAction_mul
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H)
    (a : (identityReversibleData Q K).Lift g.1)
    (α β : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q)) :
    identityRightAction Q K H g
      (identityRightAction Q K H g a α) β =
      identityRightAction Q K H g a (α * β) :=
  (identityReversibleData Q K).verticalRightAction_mul H
    (identityLiftableVisible Q K H g) a α β

/-- Every pair of original A1 lifts over every `g∈H` differs by exactly
one original vertical element on the right. -/
theorem identityRightAction_existsUnique
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H)
    (a b : (identityReversibleData Q K).Lift g.1) :
    ∃! α : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q),
      identityRightAction Q K H g a α = b :=
  (identityReversibleData Q K).verticalRightAction_existsUnique H
    (identityLiftableVisible Q K H g) a b

/-- The action is literal right composition at each original vertex. -/
theorem identityRightAction_fiber_apply
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H)
    (a : (identityReversibleData Q K).Lift g.1)
    (α : (identityReversibleData Q K).Lift
      (1 : FixedFGraphAutomorphism Q))
    (v : Q.Vertex) (x : K) :
    (identityRightAction Q K H g a α).fiber v x =
      a.fiber v (α.fiber v x) :=
  (identityReversibleData Q K).verticalRightAction_fiber_apply H
    (identityLiftableVisible Q K H g) a α v x

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityLiftableVisible
#print axioms AAT.AG.ProtocolHolonomy.identityRightAction
#print axioms AAT.AG.ProtocolHolonomy.identityRightAction_one
#print axioms AAT.AG.ProtocolHolonomy.identityRightAction_mul
#print axioms AAT.AG.ProtocolHolonomy.identityRightAction_existsUnique
#print axioms AAT.AG.ProtocolHolonomy.identityRightAction_fiber_apply
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
