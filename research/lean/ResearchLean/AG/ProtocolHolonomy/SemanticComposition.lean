import ResearchLean.AG.ProtocolHolonomy.RenameComposition
import ResearchLean.AG.ProtocolHolonomy.LiftBridge
import Formal.Util.AssertStandardAxioms

/-!
# A2 composition on the independent semantic realization

The two original A1 lifts act as genuine natural isomorphisms on every
quotient execution. Their reindexed composite retains the original A2
fiber map at each vertex.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction CategoryTheory

universe u v w

namespace FiniteProtocolInput

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (P : FiniteProtocolInput.{u, v, w} Q)

/-- The renamed semantic target for a product is the iterated rename of the
same original execution functor. -/
theorem renamedFunctor_mul
    (g h : FixedFGraphAutomorphism Q)
    (hg : g ∈ P.H) (hh : h ∈ P.H) :
    (P.renamedRealization (g * h) (P.H.mul_mem hg hh)).toFunctor =
      P.renameExecutionFunctor h hh ⋙
        (P.renamedRealization g hg).toFunctor := by
  change P.renameExecutionFunctor (g * h) (P.H.mul_mem hg hh) ⋙
      P.executionFunctor =
    P.renameExecutionFunctor h hh ⋙
      (P.renameExecutionFunctor g hg ⋙ P.executionFunctor)
  rw [P.renameExecutionFunctor_mul g h hg hh]
  rfl

/-- The semantic natural isomorphism of an A2 product has the literal
vertexwise composite from the two original A1 lifts. -/
theorem liftIso_comp_vertex
    (g h : FixedFGraphAutomorphism Q)
    (hg : g ∈ P.H) (hh : h ∈ P.H)
    (a : P.data.Lift g) (b : P.data.Lift h)
    (s : Q.Vertex) (x : P.data.Fiber s) :
    ((P.liftIso (g * h) (P.H.mul_mem hg hh) (a.comp b)).hom.toNatTrans.app
      (P.schema.vertexObject (ULift.up s)) (ULift.up x)).down =
    ((P.liftIso g hg a).hom.toNatTrans.app
      (P.schema.vertexObject (ULift.up (h.vertex s)))
        ((P.liftIso h hh b).hom.toNatTrans.app
          (P.schema.vertexObject (ULift.up s)) (ULift.up x))).down := by
  exact a.comp_fiber_apply b s x

/-- Compose the two genuine semantic natural isomorphisms after reindexing
the first by the second original visible change. The target identification
uses the proved quotient-execution functor composition law. -/
def liftIsoSemanticComposite
    (g h : FixedFGraphAutomorphism Q)
    (hg : g ∈ P.H) (hh : h ∈ P.H)
    (a : P.data.Lift g) (b : P.data.Lift h) :
    P.realization.toFunctor ⟶
      (P.renamedRealization (g * h) (P.H.mul_mem hg hh)).toFunctor :=
  (P.liftIso h hh b).hom.toNatTrans ≫
    (P.renameExecutionFunctor h hh).whiskerLeft
      (P.liftIso g hg a).hom.toNatTrans ≫
    eqToHom (P.renamedFunctor_mul g h hg hh).symm

/-- The composed semantic natural transformation is exactly the one
constructed from the original A2 product, on all quotient executions. -/
theorem liftIsoSemanticComposite_eq
    (g h : FixedFGraphAutomorphism Q)
    (hg : g ∈ P.H) (hh : h ∈ P.H)
    (a : P.data.Lift g) (b : P.data.Lift h) :
    P.liftIsoSemanticComposite g h hg hh a b =
      (P.liftIso (g * h) (P.H.mul_mem hg hh) (a.comp b)).hom.toNatTrans := by
  ext q x
  cases q with
  | mk z =>
    cases z with
    | up s =>
      cases x with
      | up y =>
          simp [liftIsoSemanticComposite]
          change ULift.up (a.fiber (h.vertex s) (b.fiber s y)) =
            ULift.up ((a.comp b).fiber s y)
          exact congrArg ULift.up (a.comp_fiber_apply b s y).symm

end FiniteProtocolInput
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renamedFunctor_mul
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftIso_comp_vertex
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftIsoSemanticComposite
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.liftIsoSemanticComposite_eq
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
