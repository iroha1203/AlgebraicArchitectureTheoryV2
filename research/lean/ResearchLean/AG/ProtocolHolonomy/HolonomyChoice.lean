import ResearchLean.AG.ProtocolHolonomy.ChoiceChange
import Formal.Util.AssertStandardAxioms

/-!
# Holonomy under a change of component roots

The original named path between two roots transports all root-loop actions
by conjugation. The proof uses the accepted equality between table-generated
holonomy and all signed named root-loop transports.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)

/-- Conjugate permutations along an equivalence between two possibly
different root fibers. -/
def permutationConjugation {A B : Type*} (q : A ≃ B) :
    Equiv.Perm A ≃* Equiv.Perm B where
  toFun a := (q.symm.trans a).trans q
  invFun b := (q.trans b).trans q.symm
  left_inv := by
    intro a
    apply Equiv.ext
    intro x
    simp [Equiv.trans_apply]
  right_inv := by
    intro b
    apply Equiv.ext
    intro x
    simp [Equiv.trans_apply]
  map_mul' := by
    intro a b
    apply Equiv.ext
    intro x
    simp [Equiv.Perm.mul_def, Equiv.trans_apply]

/-- A root-loop transport conjugated along any original signed named
root-to-root path is a loop transport at the destination root. -/
theorem rootLoopTransport_conjugate_mem
    (R R' : RootedPaths Q) (j : FixedFComponent Q)
    (k : SignedPath Q (R.root j) (R'.root j))
    {m : Equiv.Perm (D.Fiber (R.root j))}
    (hm : m ∈ D.holonomy R j) :
    permutationConjugation (D.transport k) m ∈ D.holonomy R' j := by
  rw [D.holonomy_eq_rootedLoopTransportGroup R j] at hm
  rw [D.holonomy_eq_rootedLoopTransportGroup R' j]
  obtain ⟨p, rfl⟩ := hm
  refine ⟨signedComp Q (signedReverse Q k) (signedComp Q p k), ?_⟩
  simp [permutationConjugation, transport_comp, transport_reverse,
    Equiv.trans_assoc]

/-- B1 holonomy at two chosen roots is exactly conjugate by transport
along the original named root-to-root path, in both directions. -/
theorem holonomy_change_iff
    (R R' : RootedPaths Q) (j : FixedFComponent Q)
    (k : SignedPath Q (R.root j) (R'.root j))
    (m : Equiv.Perm (D.Fiber (R.root j))) :
    m ∈ D.holonomy R j ↔
      permutationConjugation (D.transport k) m ∈ D.holonomy R' j := by
  constructor
  · exact D.rootLoopTransport_conjugate_mem R R' j k
  · intro h
    have h' := D.rootLoopTransport_conjugate_mem R' R j
      (signedReverse Q k) h
    have heq : permutationConjugation
        (D.transport (signedReverse Q k))
        (permutationConjugation (D.transport k) m) = m := by
      apply Equiv.ext
      intro x
      simp [permutationConjugation, transport_reverse, Equiv.trans_apply]
    rw [heq] at h'
    exact h'

/-- The particular root path used by the D coordinate change conjugates
the complete original table-generated holonomy subgroups. -/
theorem holonomy_choice_iff
    (R R' : RootedPaths Q) (j : FixedFComponent Q)
    (m : Equiv.Perm (D.Fiber (R.root j))) :
    m ∈ D.holonomy R j ↔
      permutationConjugation
        (D.transport (oldRootToNewRoot R R' j)) m ∈
          D.holonomy R' j :=
  D.holonomy_change_iff R R' j (oldRootToNewRoot R R' j) m

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.permutationConjugation
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootLoopTransport_conjugate_mem
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.holonomy_change_iff
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.holonomy_choice_iff
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
