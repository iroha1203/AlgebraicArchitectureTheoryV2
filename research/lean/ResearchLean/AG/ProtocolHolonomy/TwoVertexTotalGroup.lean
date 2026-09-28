import ResearchLean.AG.ProtocolHolonomy.TwoVertexSwapFiber
import ResearchLean.AG.ProtocolHolonomy.LiftableVisible
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Formal.Util.AssertStandardAxioms

/-!
# The actual total change group is C₄

The actual visible projection is onto the two-element H. Its genuine
kernel is the two-element vertical A1 group. Thus the total A2 change
group has four elements, and the previously proved order-four swap lift
generates all of them.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

private abbrev twoVertexA : Type :=
  twoVertexData.ChangeGroup twoVertexInput.H

private def twoVertexProjection : twoVertexA →* twoVertexInput.H :=
  ReversibleData.ChangeGroup.projection (D := twoVertexData)
    (H := twoVertexInput.H)

/-- The actual A2 visible projection reaches both elements of the specified
H, via the identity and the explicit original swap lift. -/
theorem twoVertex_projection_surjective :
    Function.Surjective twoVertexProjection := by
  intro g
  rcases twoVertex_H_exact g with hid | hswap
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [twoVertexProjection] using hid.symm
  · refine ⟨twoVertexCycleChange, ?_⟩
    apply Subtype.ext
    simpa [twoVertexProjection, twoVertexCycleChange] using hswap.symm

/-- The kernel is the same actual identity-visible group classified above. -/
theorem twoVertex_projection_kernel_card_two :
    Nat.card twoVertexProjection.ker = 2 := by
  have hker := twoVertexData.projectionToLiftable_ker twoVertexInput.H
  change (twoVertexData.projectionToLiftable twoVertexInput.H).ker =
    twoVertexProjection.ker at hker
  rw [← hker]
  calc
    Nat.card (twoVertexData.projectionToLiftable twoVertexInput.H).ker =
        Nat.card (twoVertexData.Lift
          (1 : FixedFGraphAutomorphism twoVertexGraph)) :=
      Nat.card_congr
        (twoVertexData.verticalLiftEquivLiftableKernel
          twoVertexInput.H).symm.toEquiv
    _ = 2 := twoVertex_vertical_card_two

theorem twoVertex_projection_range_card_two :
    Nat.card twoVertexProjection.range = 2 := by
  rw [MonoidHom.range_eq_top.mpr twoVertex_projection_surjective,
    Subgroup.card_top]
  exact twoVertex_H_card_two

/-- The actual A2 group contains exactly four operation-preserving changes. -/
theorem twoVertex_changeGroup_card_four : Nat.card twoVertexA = 4 := by
  calc
    Nat.card twoVertexA =
        Nat.card twoVertexProjection.ker * twoVertexProjection.ker.index :=
      (Subgroup.card_mul_index _).symm
    _ = 2 * 2 := by
      rw [twoVertex_projection_kernel_card_two, Subgroup.index_ker,
        twoVertex_projection_range_card_two]
    _ = 4 := by norm_num

/-- The chosen original swap lift generates every actual A2 change. -/
theorem twoVertexCycleChange_generates :
    Subgroup.zpowers twoVertexCycleChange = ⊤ := by
  haveI : Finite twoVertexA := Nat.finite_of_card_ne_zero (by
    rw [twoVertex_changeGroup_card_four]
    norm_num)
  apply (Subgroup.card_eq_iff_eq_top
    (Subgroup.zpowers twoVertexCycleChange)).mp
  rw [Nat.card_zpowers, twoVertexCycleChange_order_four,
    twoVertex_changeGroup_card_four]

theorem twoVertex_changeGroup_isCyclic : IsCyclic twoVertexA := by
  exact ⟨twoVertexCycleChange, by
    intro g
    have hg : g ∈ Subgroup.zpowers twoVertexCycleChange := by
      rw [twoVertexCycleChange_generates]
      trivial
    exact hg⟩

/-- An explicit cyclic-four presentation of the actual A2 change group. -/
noncomputable def twoVertexC4 :
    Multiplicative (ZMod 4) ≃* twoVertexA := by
  rw [← twoVertex_changeGroup_card_four]
  exact zmodCyclicMulEquiv twoVertex_changeGroup_isCyclic

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.twoVertex_projection_surjective
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_projection_kernel_card_two
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_projection_range_card_two
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_changeGroup_card_four
#print axioms AAT.AG.ProtocolHolonomy.twoVertexCycleChange_generates
#print axioms AAT.AG.ProtocolHolonomy.twoVertex_changeGroup_isCyclic
#print axioms AAT.AG.ProtocolHolonomy.twoVertexC4
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
