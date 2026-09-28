import ResearchLean.AG.ProtocolHolonomy.FiniteSelectedVerticalLifts
import ResearchLean.AG.ProtocolHolonomy.FiniteLiftableVisible
import Formal.Util.AssertStandardAxioms

/-!
# C1 and the actual liftable visible image from the selected forest

Run the simultaneous original named-edge C1 search with root paths computed
inside the generated forest. Its success is equivalent to the nonemptiness
of the original A1 lift fiber and the C1 root solution fiber. Scan the finite
visible input to enumerate precisely the original liftable visible image.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
    (D : ReversibleData.{u, v, w} Q)
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- C1 search using roots and actual selected-tree paths generated from the
original finite input tables. -/
def findSelectedRootLift
    (g : FixedFGraphAutomorphism Q)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    Option (D.Lift g) :=
  D.findRootLift (finiteSelectedRootedPaths Q vertices edges)
    g vertices edges fibers

/-- The selected-forest C1 decision is exact for the original A1 lift fiber. -/
theorem findSelectedRootLift_isSome_iff
    (g : FixedFGraphAutomorphism Q)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    (D.findSelectedRootLift g vertices edges fibers).isSome = true ↔
      Nonempty (D.Lift g) :=
  D.findRootLift_isSome_iff
    (finiteSelectedRootedPaths Q vertices edges) g vertices edges fibers

/-- The same selected-forest decision tests the genuine C1 root equations. -/
theorem findSelectedRootLift_isSome_iff_rootSolutions
    (g : FixedFGraphAutomorphism Q)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    (D.findSelectedRootLift g vertices edges fibers).isSome = true ↔
      Nonempty (D.RootSolutions
        (finiteSelectedRootedPaths Q vertices edges) g) :=
  D.findRootLift_isSome_iff_rootSolutions
    (finiteSelectedRootedPaths Q vertices edges) g vertices edges fibers

/-- Scan the complete finite visible input and keep exactly successful C1
changes computed with the same selected-tree paths. -/
def finiteSelectedLiftableVisible
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) : List H :=
  visible.values.filter fun g =>
    (D.findSelectedRootLift g.1 vertices edges fibers).isSome

/-- The computed success list is precisely the actual original visible
image of A1 lifts. -/
theorem mem_finiteSelectedLiftableVisible_iff
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) (g : H) :
    g ∈ D.finiteSelectedLiftableVisible H visible vertices edges fibers ↔
      g ∈ D.LiftableVisible H := by
  rw [finiteSelectedLiftableVisible, List.mem_filter]
  simp only [visible.complete g, true_and]
  exact (D.findSelectedRootLift_isSome_iff g.1 vertices edges fibers).trans
    (D.mem_liftableVisible_iff_lift H g).symm

/-- Membership also exposes the original successful A1 lift returned by
the same selected-forest C1 computation. -/
theorem finiteSelectedLiftableVisible_lift_iff
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (visible : ExplicitEnumeration H)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) (g : H) :
    g ∈ D.finiteSelectedLiftableVisible H visible vertices edges fibers ↔
      ∃ a : D.Lift g.1,
        D.findSelectedRootLift g.1 vertices edges fibers = some a := by
  rw [D.mem_finiteSelectedLiftableVisible_iff H visible vertices edges fibers g]
  rw [D.mem_liftableVisible_iff_lift H g]
  constructor
  · rintro ⟨a⟩
    have h := (D.findSelectedRootLift_isSome_iff
      g.1 vertices edges fibers).mpr ⟨a⟩
    cases hs : D.findSelectedRootLift g.1 vertices edges fibers with
    | none => simp [hs] at h
    | some b => exact ⟨b, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a⟩

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findSelectedRootLift
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findSelectedRootLift_isSome_iff
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findSelectedRootLift_isSome_iff_rootSolutions
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteSelectedLiftableVisible
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.mem_finiteSelectedLiftableVisible_iff
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteSelectedLiftableVisible_lift_iff
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
