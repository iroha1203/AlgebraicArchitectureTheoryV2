import ResearchLean.AG.ProtocolHolonomy.SemanticGroup
import ResearchLean.AG.ProtocolHolonomy.LiftFiberTorsor
import Formal.Util.AssertStandardAxioms

/-!
# The original vertical right action on semantic isomorphism fibers

Each semantic fiber is the entire space of natural isomorphisms over one
liftable visible change. The action is read through the proven A1/semantic
equivalence and the literal right action of the original vertical group.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction CategoryTheory

universe u v w

namespace FiniteProtocolInput

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (P : FiniteProtocolInput.{u, v, w} Q)

/-- Right action of an original vertical lift on a genuine semantic
isomorphism over the same visible change. -/
noncomputable def semanticVerticalRightAction
    (g : P.data.LiftableVisible P.H)
    (i : P.realization ≅ P.renamedRealization g.1.1 g.1.2)
    (α : P.data.Lift (1 : FixedFGraphAutomorphism Q)) :
    P.realization ≅ P.renamedRealization g.1.1 g.1.2 :=
  P.liftIso g.1.1 g.1.2
    (P.data.verticalRightAction P.H g
      (P.isoToLift g.1.1 g.1.2 i) α)

theorem semanticVerticalRightAction_one
    (g : P.data.LiftableVisible P.H)
    (i : P.realization ≅ P.renamedRealization g.1.1 g.1.2) :
    P.semanticVerticalRightAction g i 1 = i := by
  simp [semanticVerticalRightAction, P.data.verticalRightAction_one,
    P.liftIso_isoToLift]

theorem semanticVerticalRightAction_mul
    (g : P.data.LiftableVisible P.H)
    (i : P.realization ≅ P.renamedRealization g.1.1 g.1.2)
    (α β : P.data.Lift (1 : FixedFGraphAutomorphism Q)) :
    P.semanticVerticalRightAction g
      (P.semanticVerticalRightAction g i α) β =
      P.semanticVerticalRightAction g i (α * β) := by
  simp [semanticVerticalRightAction, P.isoToLift_liftIso,
    P.data.verticalRightAction_mul]

theorem semanticVerticalRightAction_free
    (g : P.data.LiftableVisible P.H)
    (i : P.realization ≅ P.renamedRealization g.1.1 g.1.2) :
    Function.Injective (fun α : P.data.Lift (1 : FixedFGraphAutomorphism Q) =>
      P.semanticVerticalRightAction g i α) := by
  intro α β h
  apply P.data.verticalRightAction_free P.H g
    (P.isoToLift g.1.1 g.1.2 i)
  exact (P.liftEquivSemanticIso g.1.1 g.1.2).injective h

theorem semanticVerticalRightAction_transitive
    (g : P.data.LiftableVisible P.H)
    (i j : P.realization ≅ P.renamedRealization g.1.1 g.1.2) :
    ∃ α : P.data.Lift (1 : FixedFGraphAutomorphism Q),
      P.semanticVerticalRightAction g i α = j := by
  obtain ⟨α, hα⟩ := P.data.verticalRightAction_transitive P.H g
    (P.isoToLift g.1.1 g.1.2 i)
    (P.isoToLift g.1.1 g.1.2 j)
  refine ⟨α, ?_⟩
  change P.liftIso g.1.1 g.1.2
      (P.data.verticalRightAction P.H g
        (P.isoToLift g.1.1 g.1.2 i) α) = j
  rw [hα, P.liftIso_isoToLift]

/-- The semantic right action has exactly the requested pointwise fiber
formula `(φ·α)_v = φ_v ∘ α_v`. -/
theorem semanticVerticalRightAction_fiber_apply
    (g : P.data.LiftableVisible P.H)
    (i : P.realization ≅ P.renamedRealization g.1.1 g.1.2)
    (α : P.data.Lift (1 : FixedFGraphAutomorphism Q))
    (v : Q.Vertex) (x : P.data.Fiber v) :
    (P.isoFiber g.1.1 g.1.2
      (P.semanticVerticalRightAction g i α) v) x =
      (P.isoFiber g.1.1 g.1.2 i v) (α.fiber v x) := by
  change (P.data.verticalRightAction P.H g
      (P.isoToLift g.1.1 g.1.2 i) α).fiber v x =
    (P.isoToLift g.1.1 g.1.2 i).fiber v (α.fiber v x)
  exact P.data.verticalRightAction_fiber_apply P.H g
    (P.isoToLift g.1.1 g.1.2 i) α v x

end FiniteProtocolInput
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticVerticalRightAction
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticVerticalRightAction_one
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticVerticalRightAction_mul
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticVerticalRightAction_free
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticVerticalRightAction_transitive
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.semanticVerticalRightAction_fiber_apply
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
