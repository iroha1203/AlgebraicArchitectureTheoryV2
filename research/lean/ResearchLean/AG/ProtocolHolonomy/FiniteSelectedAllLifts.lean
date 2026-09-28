import ResearchLean.AG.ProtocolHolonomy.FiniteSelectedLiftability
import ResearchLean.AG.ProtocolHolonomy.FiniteAllLifts
import Formal.Util.AssertStandardAxioms

/-!
# All original lifts from the generated named forest

The selected-forest C1 search yields one original A1 lift when possible.
Compose it with every original vertical A1 lift enumerated from the B2
centralizers of that same forest. The C3 right torsor proves the resulting
finite list exhausts precisely the original lift fiber.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
    (D : ReversibleData.{u, v, w} Q)
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]

/-- Return every original A1 lift over a visible change, using the same
finite-table-generated forest for C1 and B2. -/
def finiteSelectedAllLifts
    (g : FixedFGraphAutomorphism Q)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    List (D.Lift g) :=
  match D.findSelectedRootLift g vertices edges fibers with
  | none => []
  | some a =>
      (D.finiteSelectedVerticalLifts vertices edges fibers).values.map
        (D.composeVertical g a)

/-- Every original A1 lift is among the selected-forest C1/B2/C3 output. -/
theorem mem_finiteSelectedAllLifts
    (g : FixedFGraphAutomorphism Q)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x))
    (b : D.Lift g) :
    b ∈ D.finiteSelectedAllLifts g vertices edges fibers := by
  have hsuccess :=
    (D.findSelectedRootLift_isSome_iff g vertices edges fibers).mpr ⟨b⟩
  cases hfind : D.findSelectedRootLift g vertices edges fibers with
  | none => simp [hfind] at hsuccess
  | some a =>
      let H : Subgroup (FixedFGraphAutomorphism Q) := ⊤
      let g' : D.LiftableVisible H := ⟨⟨g, trivial⟩,
        (D.mem_liftableVisible_iff_lift H ⟨g, trivial⟩).mpr ⟨a⟩⟩
      obtain ⟨α, hα⟩ := D.verticalRightAction_transitive H g' a b
      have hcomp : D.composeVertical g a α = b := by
        rw [D.composeVertical_eq_rightAction H g' a α]
        exact hα
      unfold finiteSelectedAllLifts
      rw [hfind]
      apply List.mem_map.mpr
      exact ⟨α,
        (D.finiteSelectedVerticalLifts vertices edges fibers).complete α,
        hcomp⟩

/-- The output is empty exactly when no original A1 lift exists. In the
successful branch it lists all of them via the actual C3 right action. -/
theorem finiteSelectedAllLifts_eq_nil_iff
    (g : FixedFGraphAutomorphism Q)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    D.finiteSelectedAllLifts g vertices edges fibers = [] ↔
      IsEmpty (D.Lift g) := by
  constructor
  · intro h
    constructor
    intro a
    have hm := D.mem_finiteSelectedAllLifts g vertices edges fibers a
    simp [h] at hm
  · intro h
    cases hs : D.finiteSelectedAllLifts g vertices edges fibers with
    | nil => rfl
    | cons a rest => exact (h.false a).elim

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteSelectedAllLifts
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.mem_finiteSelectedAllLifts
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteSelectedAllLifts_eq_nil_iff
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
