import ResearchLean.AG.ProtocolHolonomy.FiniteRootedPaths
import ResearchLean.AG.ProtocolHolonomy.LiftableVisible
import Formal.Util.AssertStandardAxioms

/-!
# Enumerate the liftable visible subgroup from finite original tables

Scan the supplied finite list of actual visible changes. For each change,
the input-generated root paths and simultaneous named-edge C1 test decide
whether an original A1 lift exists. The accepted entries are exactly the
actual visible image `LiftableVisible H`; a successful search also returns
one original lift for that entry. The named spanning-forest construction and
all-lifts output remain separate finite obligations.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
    (D : ReversibleData.{u, v, w} Q)
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- The finite list of precisely those visible inputs with a C1 solution. -/
def finiteLiftableVisible
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) : List H :=
  visible.values.filter fun g =>
    (D.findFiniteRootLift g.1 vertices edges fibers).isSome

/-- The executable scan equals the actual visible projection image. -/
theorem mem_finiteLiftableVisible_iff
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) (g : H) :
    g ∈ D.finiteLiftableVisible H visible vertices edges fibers ↔
      g ∈ D.LiftableVisible H := by
  rw [finiteLiftableVisible, List.mem_filter]
  simp only [visible.complete g, true_and]
  exact (D.findFiniteRootLift_isSome_iff g.1 vertices edges fibers).trans
    (D.mem_liftableVisible_iff_lift H g).symm

/-- For every accepted visible change the same C1 run returns an original
A1 lift; membership in the list is the exact success certificate. -/
theorem finiteLiftableVisible_lift_iff
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) (g : H) :
    g ∈ D.finiteLiftableVisible H visible vertices edges fibers ↔
      ∃ a : D.Lift g.1,
        D.findFiniteRootLift g.1 vertices edges fibers = some a := by
  rw [D.mem_finiteLiftableVisible_iff H visible vertices edges fibers g]
  rw [D.mem_liftableVisible_iff_lift H g]
  constructor
  · rintro ⟨a⟩
    have h := (D.findFiniteRootLift_isSome_iff g.1 vertices edges fibers).mpr ⟨a⟩
    cases hs : D.findFiniteRootLift g.1 vertices edges fibers with
    | none => simp [hs] at h
    | some b => exact ⟨b, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a⟩

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteLiftableVisible
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.mem_finiteLiftableVisible_iff
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteLiftableVisible_lift_iff
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
