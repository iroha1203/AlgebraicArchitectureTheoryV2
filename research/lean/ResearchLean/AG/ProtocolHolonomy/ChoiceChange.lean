import ResearchLean.AG.ProtocolHolonomy.LiftFiberTorsor
import Formal.Util.AssertStandardAxioms

/-!
# Change of root coordinates for reversible protocols

Both coordinate systems are read from the same original family of fiber
equivalences. This gives coherent changes between arbitrary normalized rooted
path choices, including different roots and different selected trees.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- Change the centralizer coordinates through the original A1 vertical
change, so their group law remains the original state composition. -/
noncomputable def verticalChoiceChange (R R' : RootedPaths Q) :
    D.RootCentralizers R ≃* D.RootCentralizers R' :=
  (D.verticalRootMulEquiv R).symm.trans (D.verticalRootMulEquiv R')

/-- Change C1 coordinates through the actual original A1 lift. -/
def liftChoiceChange (R R' : RootedPaths Q)
    (g : FixedFGraphAutomorphism Q) :
    D.RootSolutions R g ≃ D.RootSolutions R' g :=
  (D.liftEquivRootSolutions R g).symm.trans
    (D.liftEquivRootSolutions R' g)

@[simp] theorem verticalChoiceChange_refl (R : RootedPaths Q)
    (a : D.RootCentralizers R) : D.verticalChoiceChange R R a = a := by
  simp [verticalChoiceChange]

@[simp] theorem liftChoiceChange_refl (R : RootedPaths Q)
    (g : FixedFGraphAutomorphism Q) (b : D.RootSolutions R g) :
    D.liftChoiceChange R R g b = b := by
  simp [liftChoiceChange]

/-- Direct and successive changes give exactly the same centralizer
coordinates for three choices. -/
theorem verticalChoiceChange_comp (R₁ R₂ R₃ : RootedPaths Q)
    (a : D.RootCentralizers R₁) :
    D.verticalChoiceChange R₂ R₃
      (D.verticalChoiceChange R₁ R₂ a) =
      D.verticalChoiceChange R₁ R₃ a := by
  simp [verticalChoiceChange]

/-- The corresponding coherence law for all C1 root solutions. -/
theorem liftChoiceChange_comp (R₁ R₂ R₃ : RootedPaths Q)
    (g : FixedFGraphAutomorphism Q) (b : D.RootSolutions R₁ g) :
    D.liftChoiceChange R₂ R₃ g
      (D.liftChoiceChange R₁ R₂ g b) =
      D.liftChoiceChange R₁ R₃ g b := by
  simp [liftChoiceChange]

/-- Changing centralizer coordinates reconstructs the same original
vertical fiber equivalence at every vertex. -/
theorem verticalChoiceChange_reconstruct (R R' : RootedPaths Q)
    (a : D.RootCentralizers R) :
    D.reconstructVertical R' (D.verticalChoiceChange R R' a) =
      D.reconstructVertical R a := by
  simp [verticalChoiceChange, verticalRootMulEquiv, verticalRootEquiv]
  exact D.reconstructVertical_evaluation R' _

/-- Changing C1 coordinates reconstructs the same original A1 lift. -/
theorem liftChoiceChange_reconstruct (R R' : RootedPaths Q)
    (g : FixedFGraphAutomorphism Q) (b : D.RootSolutions R g) :
    (D.liftChoiceChange R R' g b).toLift D R' = b.toLift D R := by
  simp [liftChoiceChange, liftEquivRootSolutions]
  exact Lift.toRootSolutions_toLift D R' _

/-- The canonical signed path from the old root to the new root, using the
old chosen paths. Its original edge names and directions are retained. -/
def oldRootToNewRoot (R R' : RootedPaths Q)
    (j : FixedFComponent Q) : SignedPath Q (R.root j) (R'.root j) :=
  R.path j (R'.root j) (R'.root_component j)

/-- At the new root, vertical coordinates are conjugated by the actual
transport from the old root. -/
theorem verticalChoiceChange_root_formula (R R' : RootedPaths Q)
    (a : D.RootCentralizers R) (j : FixedFComponent Q) :
    (D.verticalChoiceChange R R' a j).1 =
      ((D.transport (oldRootToNewRoot R R' j)).symm.trans (a j).1).trans
        (D.transport (oldRootToNewRoot R R' j)) := by
  let z := D.reconstructVertical R a
  have hnat := D.vertical_transport_naturality z (oldRootToNewRoot R R' j)
  have ha : z.fiber (R.root j) = (a j).1 := by
    have h := congrFun (D.verticalRootEvaluation_reconstruct R a) j
    exact congrArg Subtype.val h
  change (z.fiber (R'.root j)) = _
  rw [← ha]
  apply Equiv.ext
  intro x
  have h := congrArg
    (fun f : D.Fiber (R.root j) ≃ D.Fiber (R'.root j) =>
      f ((D.transport (oldRootToNewRoot R R' j)).symm x)) hnat
  simpa [Equiv.trans_apply] using h

/-- C1 coordinates at a new root use the old-to-new transport and its
renamed counterpart, with the same original A1 lift underneath. -/
theorem liftChoiceChange_root_formula (R R' : RootedPaths Q)
    (g : FixedFGraphAutomorphism Q) (b : D.RootSolutions R g)
    (j : FixedFComponent Q) :
    (D.liftChoiceChange R R' g b).rootFiber j =
      ((D.transport (oldRootToNewRoot R R' j)).symm.trans
        (b.rootFiber j)).trans
          (D.transport (renameSigned g (oldRootToNewRoot R R' j))) := by
  let z := b.toLift D R
  have hnat := z.signed_path_naturality D (oldRootToNewRoot R R' j)
  have hb : z.fiber (R.root j) = b.rootFiber j :=
    b.reconstructedFiber_root D R j
  change z.fiber (R'.root j) = _
  rw [← hb]
  apply Equiv.ext
  intro x
  have h := congrArg
    (fun f : D.Fiber (R.root j) ≃ D.Fiber (g.vertex (R'.root j)) =>
      f ((D.transport (oldRootToNewRoot R R' j)).symm x)) hnat
  simpa [Equiv.trans_apply] using h

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.verticalChoiceChange
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftChoiceChange
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.verticalChoiceChange_comp
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftChoiceChange_comp
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.verticalChoiceChange_reconstruct
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftChoiceChange_reconstruct
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.verticalChoiceChange_root_formula
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.liftChoiceChange_root_formula
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
