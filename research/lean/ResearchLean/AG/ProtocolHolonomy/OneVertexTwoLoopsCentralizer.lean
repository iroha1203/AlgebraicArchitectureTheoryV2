import ResearchLean.AG.ProtocolHolonomy.OneVertexTwoLoopsHolonomy
import ResearchLean.AG.ProtocolHolonomy.VerticalCentralizer
import Formal.Util.AssertStandardAxioms

/-!
# B2 centralizer for the first fixed example

The exact B2 map evaluates actual vertical A1 state changes at the unique
component root. Its holonomy centralizer is the entire two-point
permutation group.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

theorem oneLoop_component_unique (j : FixedFComponent oneLoopGraph) :
    j = oneLoopComponent := by
  induction j using Quotient.inductionOn with
  | _ x => cases x; rfl

/-- Every permutation of the Bool fiber centralizes the actual B1 holonomy
in the one-component fixed example. -/
theorem oneLoop_holonomy_centralizer_top :
    Subgroup.centralizer
      (oneLoopData.holonomy oneLoopRootedPaths oneLoopComponent :
        Set (Equiv.Perm (oneLoopData.Fiber
          (oneLoopRootedPaths.root oneLoopComponent)))) = ⊤ := by
  have hcard : Nat.card (Equiv.Perm Bool) = 2 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_bool]
    decide
  letI : IsCyclic (Equiv.Perm Bool) := isCyclic_of_prime_card hcard
  letI : CommGroup (Equiv.Perm Bool) := IsCyclic.commGroup
  have hcomm : ∀ a b : Equiv.Perm Bool, a * b = b * a :=
    fun a b => mul_comm a b
  rw [oneLoop_original_holonomy_top]
  apply Subgroup.ext
  intro p
  constructor
  · intro _; trivial
  · intro _
    apply (Subgroup.mem_centralizer_iff).mpr
    intro m hm
    exact hcomm m p

/-- The centralizer calculation applies at every root of the same original
graph, since it has exactly one component. -/
theorem oneLoop_holonomy_centralizer_top_every
    (j : FixedFComponent oneLoopGraph) :
    Subgroup.centralizer
      (oneLoopData.holonomy oneLoopRootedPaths j :
        Set (Equiv.Perm (oneLoopData.Fiber (oneLoopRootedPaths.root j)))) = ⊤ := by
  rw [oneLoop_component_unique j]
  exact oneLoop_holonomy_centralizer_top

/-- B2 for this exact example: actual vertical A1 changes, with their A2
group law, are the product of its calculated holonomy centralizers. -/
noncomputable def oneLoopB2 :
    oneLoopData.Lift (1 : FixedFGraphAutomorphism oneLoopGraph) ≃*
      oneLoopData.RootCentralizers oneLoopRootedPaths :=
  oneLoopData.verticalRootMulEquiv oneLoopRootedPaths

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.oneLoop_component_unique
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_holonomy_centralizer_top
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_holonomy_centralizer_top_every
#print axioms AAT.AG.ProtocolHolonomy.oneLoopB2
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
