import ResearchLean.AG.ProtocolHolonomy.ChoiceTorsor
import Formal.Util.AssertStandardAxioms

/-!
# Group law and projection in root coordinates

The group structure on root solutions is read from the original A2 change
group. Coordinate changes preserve this group law and the visible projection.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- Every visible change in H paired with its C1 coordinates at R. -/
def RootPair (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :=
  Σ g : H, D.RootSolutions R g.1

/-- Root coordinates are equivalent to the original A1 lift pairs. -/
def liftPairEquivRootPair (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.LiftPair H ≃ D.RootPair R H where
  toFun p := ⟨p.1, p.2.toRootSolutions D R⟩
  invFun p := ⟨p.1, p.2.toLift D R⟩
  left_inv p := by
    rcases p with ⟨g, a⟩
    change (⟨g, (a.toRootSolutions D R).toLift D R⟩ : D.LiftPair H) = ⟨g, a⟩
    rw [a.toRootSolutions_toLift D R]
  right_inv p := by
    rcases p with ⟨g, b⟩
    change (⟨g, (b.toLift D R).toRootSolutions D R⟩ : D.RootPair R H) = ⟨g, b⟩
    rw [b.toLift_toRootSolutions D R]

/-- The root presentation inherits the actual A2 group, not an independently
postulated coordinate law. -/
noncomputable instance (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    Group (D.RootPair R H) :=
  (D.liftPairEquivRootPair R H).symm.group

/-- The original A2 group and its root-coordinate presentation coincide. -/
noncomputable def liftPairMulEquivRootPair (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.LiftPair H ≃* D.RootPair R H where
  toEquiv := D.liftPairEquivRootPair R H
  map_mul' a b := by
    let E := D.liftPairEquivRootPair R H
    change E (a * b) = E (E.symm (E a) * E.symm (E b))
    simp

/-- The root-coordinate group retains the original visible projection. -/
noncomputable def rootPairProjection (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.RootPair R H →* H :=
  (D.liftPairProjection H).comp
    (D.liftPairMulEquivRootPair R H).symm.toMonoidHom

@[simp] theorem rootPairProjection_apply (R : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (a : D.RootPair R H) :
    D.rootPairProjection R H a = a.1 := by
  rcases a with ⟨g, b⟩
  change D.liftPairProjection H ⟨g, b.toLift D R⟩ = g
  exact D.liftPairProjection_apply _

/-- Two root presentations are isomorphic through the same original A2
group; this map preserves the visible projection. -/
noncomputable def rootPairChoiceChange (R R' : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q)) :
    D.RootPair R H ≃* D.RootPair R' H :=
  (D.liftPairMulEquivRootPair R H).symm.trans
    (D.liftPairMulEquivRootPair R' H)

theorem rootPairChoiceChange_projection (R R' : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (a : D.RootPair R H) :
    D.rootPairProjection R' H (D.rootPairChoiceChange R R' H a) =
      D.rootPairProjection R H a := by
  rw [D.rootPairProjection_apply R' H,
    D.rootPairProjection_apply R H]
  rcases a with ⟨g, b⟩
  rfl

/-- At a fixed visible change this group-level map is the C1 choice change
already computed from the original A1 lift. -/
theorem rootPairChoiceChange_fiber (R R' : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (a : D.RootPair R H) :
    (D.rootPairChoiceChange R R' H a).2 =
      D.liftChoiceChange R R' a.1.1 a.2 := by
  rcases a with ⟨g, b⟩
  rfl

/-- The literal kernels of the visible projections correspond under root
choice change. -/
theorem rootPairChoiceChange_mem_ker_iff (R R' : RootedPaths Q)
    (H : Subgroup (FixedFGraphAutomorphism Q))
    (a : D.RootPair R H) :
    D.rootPairChoiceChange R R' H a ∈ (D.rootPairProjection R' H).ker ↔
      a ∈ (D.rootPairProjection R H).ker := by
  simp only [MonoidHom.mem_ker]
  rw [D.rootPairChoiceChange_projection R R' H a]

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftPairEquivRootPair
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftPairMulEquivRootPair
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootPairProjection
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootPairChoiceChange
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootPairChoiceChange_projection
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootPairChoiceChange_fiber
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootPairChoiceChange_mem_ker_iff
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
