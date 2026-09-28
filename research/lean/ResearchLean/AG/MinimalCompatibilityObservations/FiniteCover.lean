import ResearchLean.AG.MinimalCompatibilityObservations.FiniteMinimum
import Formal.Util.AssertStandardAxioms

/-!
# G-128: finite compatibility as set cover

The uncovered universe consists exactly of incompatible changes. A point
detects such a change when the point is moved by it.
-/

namespace AAT.AG.MinimalCompatibilityObservations

open AAT.AG.ProtocolHolonomy

variable {G X : Type*} [Group G] [MulAction G X]
variable [DecidableEq G] [DecidableEq X]
variable (Gamma : Subgroup G) [DecidablePred (· ∈ Gamma)]
variable (EG : ExplicitEnumeration G)

/-- The finite universe of incompatible changes. -/
def incompatibleSet : Finset G :=
  letI : Fintype G := EG.toFintype
  Finset.univ.filter fun g => g ∉ Gamma

@[simp] theorem mem_incompatibleSet (g : G) :
    g ∈ incompatibleSet Gamma EG ↔ g ∉ Gamma := by
  simp [incompatibleSet]

/-- The incompatible changes detected by observing the point `x`. -/
def detectedSet (x : X) : Finset G :=
  (incompatibleSet Gamma EG).filter fun g => g • x ≠ x

@[simp] theorem mem_detectedSet (g : G) (x : X) :
    g ∈ detectedSet Gamma EG x ↔ g ∉ Gamma ∧ g • x ≠ x := by
  simp [detectedSet]

theorem cover_subset_incompatible (B : Finset X) :
    B.biUnion (detectedSet Gamma EG) ⊆ incompatibleSet Gamma EG := by
  intro g hg
  obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hg
  exact (Finset.mem_filter.mp hx).1

/-- Exact set-cover criterion for the original point-stabilizer inclusion. -/
theorem sufficient_iff_cover (B : Finset X) :
    Sufficient Gamma B ↔
      B.biUnion (detectedSet Gamma EG) = incompatibleSet Gamma EG := by
  constructor
  · intro hS
    apply Finset.Subset.antisymm (cover_subset_incompatible Gamma EG B)
    intro g hg
    by_contra hnot
    have hfix : ∀ x ∈ B, g • x = x := by
      intro x hx
      by_contra hmove
      exact hnot (Finset.mem_biUnion.mpr
        ⟨x, hx, (mem_detectedSet Gamma EG g x).mpr
          ⟨(mem_incompatibleSet Gamma EG g).mp hg, hmove⟩⟩)
    exact (mem_incompatibleSet Gamma EG g).mp hg (hS hfix)
  · intro hcover g hfix
    by_contra hbad
    have hg : g ∈ incompatibleSet Gamma EG :=
      (mem_incompatibleSet Gamma EG g).mpr hbad
    obtain ⟨x, hx, hmove⟩ := Finset.mem_biUnion.mp (hcover.symm ▸ hg)
    exact (mem_detectedSet Gamma EG g x).mp hmove |>.2 (hfix x hx)

end AAT.AG.MinimalCompatibilityObservations

#assert_standard_axioms_only AAT.AG.MinimalCompatibilityObservations
