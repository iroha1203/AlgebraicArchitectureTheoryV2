import ResearchLean.AG.RealizationReconstruction.FixedFAllAutomorphismGroup
import Formal.Util.AssertStandardAxioms

/-!
# Reversible named operations on varying fibers

This file starts the source-side construction for G-127.  The edge action is
input data; the state equivalence and its inverse are constructed from a
family of fiber equivalences.  No existence of lifts is assumed.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- A named graph with a possibly different state type at each vertex and a
reversible operation for each named edge. -/
structure ReversibleData (Q : FixedFDirectedMultigraph.{u, v}) where
  Fiber : Q.Vertex → Type w
  edgeEquiv : (e : Q.Edge) → Fiber (Q.source e) ≃ Fiber (Q.target e)

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}} (D : ReversibleData Q)

/-- A renamed edge action, with the endpoint equalities supplied by the graph
automorphism used solely to transport the source and target types. -/
def renamedEdgeEquiv (g : FixedFGraphAutomorphism Q) (e : Q.Edge) :
    D.Fiber (g.vertex (Q.source e)) ≃
      D.Fiber (g.vertex (Q.target e)) :=
  Equiv.cast (congrArg D.Fiber (g.source_rename e).symm) |>.trans
    ((D.edgeEquiv (g.edge e)).trans
      (Equiv.cast (congrArg D.Fiber (g.target_rename e))))

/-- Fiberwise reversible changes satisfying the named operation square. -/
structure Lift (g : FixedFGraphAutomorphism Q) where
  fiber : (x : Q.Vertex) → D.Fiber x ≃ D.Fiber (g.vertex x)
  edge_naturality : ∀ (e : Q.Edge) (x : D.Fiber (Q.source e)),
    fiber (Q.target e) (D.edgeEquiv e x) =
      D.renamedEdgeEquiv g e (fiber (Q.source e) x)

namespace Lift

variable {D} {g : FixedFGraphAutomorphism Q}

@[ext] theorem ext {a b : D.Lift g}
    (h : ∀ x y, a.fiber x y = b.fiber x y) : a = b := by
  cases a with
  | mk af an =>
    cases b with
    | mk bf bn =>
      have hf : af = bf := by
        funext x
        apply Equiv.ext
        exact h x
      cases hf
      rfl

/-- The total state change induced by all vertex fibers. -/
def stateEquiv (a : D.Lift g) :
    (Σ x, D.Fiber x) ≃ (Σ x, D.Fiber x) :=
  Equiv.sigmaCongr g.vertex a.fiber

@[simp] theorem stateEquiv_apply (a : D.Lift g)
    (x : Q.Vertex) (y : D.Fiber x) :
    a.stateEquiv ⟨x, y⟩ = ⟨g.vertex x, a.fiber x y⟩ := rfl

/-- The total state change preserves the vertex observation. -/
theorem stateEquiv_observation (a : D.Lift g)
    (x : Q.Vertex) (y : D.Fiber x) :
    (a.stateEquiv ⟨x, y⟩).1 = g.vertex x := rfl

/-- Its state map remembers every component of the lift. -/
theorem stateEquiv_injective :
    Function.Injective (fun a : D.Lift g => a.stateEquiv) := by
  intro a b h
  apply ext
  intro x y
  have hp := congrArg (fun f : (Σ x, D.Fiber x) ≃ (Σ x, D.Fiber x) =>
    f ⟨x, y⟩) h
  change (⟨g.vertex x, a.fiber x y⟩ : Σ x, D.Fiber x) =
    ⟨g.vertex x, b.fiber x y⟩ at hp
  exact eq_of_heq (Sigma.mk.inj_iff.mp hp).2

end Lift
end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.Lift.stateEquiv
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.Lift.stateEquiv_injective
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
