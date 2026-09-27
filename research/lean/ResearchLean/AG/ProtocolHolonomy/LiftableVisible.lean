import ResearchLean.AG.ProtocolHolonomy.LiftRootReconstruction
import ResearchLean.AG.ComparisonInformationLoss.GroupHomRestriction
import Formal.Util.AssertStandardAxioms

/-!
# The visible image of actual reversible protocol changes

The C1 solution test describes exactly the range of the actual visible
projection. Restricting the codomain to this range gives the C3 surjection.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction
open AAT.AG.ComparisonInformationLoss

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- The actual subgroup of visible changes that have a lift. -/
def LiftableVisible (H : Subgroup (FixedFGraphAutomorphism Q)) : Subgroup H :=
  (ChangeGroup.projection (D := D) (H := H)).range

theorem mem_liftableVisible_iff_lift
    (H : Subgroup (FixedFGraphAutomorphism Q)) (g : H) :
    g ∈ D.LiftableVisible H ↔ Nonempty (D.Lift g.1) := by
  constructor
  · rintro ⟨c, hc⟩
    cases hc
    exact ⟨c.1.toLift⟩
  · rintro ⟨a⟩
    refine ⟨⟨a.toStateChange, g.property⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- C1 has a solution precisely for the visible image of the actual
operation-preserving change group. -/
theorem mem_liftableVisible_iff_rootSolutions
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (R : RootedPaths Q) (g : H) :
    g ∈ D.LiftableVisible H ↔ Nonempty (D.RootSolutions R g.1) := by
  rw [D.mem_liftableVisible_iff_lift H g]
  exact (D.liftEquivRootSolutions R g.1).nonempty_congr

/-- The actual visible projection with its codomain restricted to its image. -/
def projectionToLiftable
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.ChangeGroup H →* D.LiftableVisible H where
  toFun a := ⟨ChangeGroup.projection a,
    ⟨a, rfl⟩⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' _ _ := by apply Subtype.ext; simp

theorem projectionToLiftable_surjective
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    Function.Surjective (D.projectionToLiftable H) := by
  rintro ⟨g, hg⟩
  rcases hg with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

/-- The restricted projection has the same actual kernel as the original. -/
theorem projectionToLiftable_ker
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    (D.projectionToLiftable H).ker =
      (ChangeGroup.projection (D := D) (H := H)).ker := by
  ext a
  change (D.projectionToLiftable H a = 1) ↔
    (ChangeGroup.projection a = 1)
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

/-- C3's literal inclusion of the actual kernel. -/
def liftableKernelInclusion
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    (D.projectionToLiftable H).ker →* D.ChangeGroup H :=
  (D.projectionToLiftable H).ker.subtype

/-- The actual change group, actual kernel, and liftable visible image form
a short exact sequence. Identifying the kernel with Aut_Q(F) is a further
structural step. -/
theorem liftable_actualKernel_shortExact
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    IsGroupShortExact (D.liftableKernelInclusion H)
      (D.projectionToLiftable H) := by
  refine ⟨Subtype.val_injective, ?_, D.projectionToLiftable_surjective H⟩
  rw [MonoidHom.mulExact_iff]
  exact ((D.projectionToLiftable H).ker.range_subtype).symm

/-- The vertical actual state changes and the kernel of the restricted
visible projection are the same group with the H-membership proof restored. -/
def verticalStateEquivLiftableKernel
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.VerticalStateGroup ≃* (D.projectionToLiftable H).ker where
  toFun a := ⟨⟨a.1, by
    have ha : a.1.visible = 1 := (MonoidHom.mem_ker).mp a.2
    change a.1.visible ∈ H
    rw [ha]
    exact H.one_mem⟩, by
      rw [D.projectionToLiftable_ker H]
      apply (MonoidHom.mem_ker).mpr
      apply Subtype.ext
      exact (MonoidHom.mem_ker).mp a.2⟩
  invFun b := ⟨b.1.1, by
    apply (MonoidHom.mem_ker).mpr
    have hb : b.1 ∈ (ChangeGroup.projection (D := D) (H := H)).ker := by
      rw [← D.projectionToLiftable_ker H]
      exact b.2
    exact congrArg Subtype.val ((MonoidHom.mem_ker).mp hb)⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Identify `Aut_Q(F)` with the actual kernel of the visible projection. -/
noncomputable def verticalLiftEquivLiftableKernel
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.Lift (1 : FixedFGraphAutomorphism Q) ≃*
      (D.projectionToLiftable H).ker :=
  (D.liftMulEquivVerticalStateGroup).trans
    (D.verticalStateEquivLiftableKernel H)

/-- C3's inclusion of vertical A1 lifts into the actual change group. -/
noncomputable def verticalLiftInclusion
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.Lift (1 : FixedFGraphAutomorphism Q) →* D.ChangeGroup H :=
  (D.liftableKernelInclusion H).comp
    (D.verticalLiftEquivLiftableKernel H).toMonoidHom

/-- C3: the literal vertical lift group, actual changes, and liftable
visible subgroup form a short exact sequence. -/
theorem liftable_shortExact
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    IsGroupShortExact (D.verticalLiftInclusion H)
      (D.projectionToLiftable H) := by
  refine ⟨?_, ?_, D.projectionToLiftable_surjective H⟩
  · intro a b h
    exact (D.verticalLiftEquivLiftableKernel H).injective
      (Subtype.val_injective h)
  · rw [MonoidHom.mulExact_iff]
    apply le_antisymm
    · intro c hc
      let k : (D.projectionToLiftable H).ker := ⟨c, hc⟩
      refine ⟨(D.verticalLiftEquivLiftableKernel H).symm k, ?_⟩
      change ((D.verticalLiftEquivLiftableKernel H)
        ((D.verticalLiftEquivLiftableKernel H).symm k)).1 = c
      have h := (D.verticalLiftEquivLiftableKernel H).apply_symm_apply k
      exact congrArg Subtype.val h
    · rintro c ⟨a, ha⟩
      rw [← ha]
      exact (D.verticalLiftEquivLiftableKernel H a).2

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.mem_liftableVisible_iff_rootSolutions
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.projectionToLiftable_surjective
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftable_actualKernel_shortExact
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
