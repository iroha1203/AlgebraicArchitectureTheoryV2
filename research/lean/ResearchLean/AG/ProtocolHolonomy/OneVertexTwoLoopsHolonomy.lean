import ResearchLean.AG.ProtocolHolonomy.OneVertexTwoLoopsVisibleGroup
import ResearchLean.AG.ProtocolHolonomy.HolonomyGenerators
import ResearchLean.AG.ProtocolHolonomy.NaturalIsomorphism
import Formal.Util.AssertStandardAxioms

/-!
# Holonomy before and after exchanging the first example's two names

Both computations use the same original graph and the same chosen root and
paths. The renamed edge action is the original action at the renamed edge,
as in the actual visible renamed realization.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- The unique component's root and its empty path. -/
def oneLoopRootedPaths : RootedPaths oneLoopGraph where
  root := fun _ => PUnit.unit
  root_component := by
    intro j
    induction j using Quotient.inductionOn with
    | _ x => cases x; rfl
  path := by
    intro j x hx
    cases x
    exact signedNil oneLoopGraph PUnit.unit
  path_root := by intro j; rfl

def oneLoopComponent : FixedFComponent oneLoopGraph :=
  fixedFComponentMk oneLoopGraph PUnit.unit

/-- Read the name-swapped operation table on the same one-vertex graph. -/
def oneLoopRenamedData : ReversibleData oneLoopGraph where
  Fiber := fun _ => Bool
  edgeEquiv := fun e => oneLoopData.renamedEdgeEquiv oneLoopSwap e

/-- This table is exactly the action of each original named edge in the
independently built visible-renamed realization. -/
theorem oneLoop_renamed_semantic_edge (e : Bool) (x : Bool) :
    ((oneLoopInput.renamedRealization oneLoopSwap oneLoopSwap_mem_H).edgeAction
      (ULift.up (⟨e, rfl, rfl⟩ : TypedEdge oneLoopGraph PUnit.unit PUnit.unit))
      (ULift.up x)).down = oneLoopRenamedData.edgeEquiv e x := by
  simpa [oneLoopRenamedData, ReversibleData.renamedEdgeEquiv,
    ReversibleData.typedEdgeEquiv] using
    (oneLoopInput.renamed_edgeAction_down oneLoopSwap oneLoopSwap_mem_H
      (⟨e, rfl, rfl⟩ : TypedEdge oneLoopGraph PUnit.unit PUnit.unit) x)

/-- The B1 generator is the original named edge action because each root
path is empty. -/
theorem oneLoop_original_monodromy (e : Bool) :
    oneLoopData.edgeMonodromyAt oneLoopRootedPaths oneLoopComponent e rfl =
      oneLoopData.edgeEquiv e := by
  apply Equiv.ext
  intro x
  cases e <;> cases x <;> rfl

/-- The changed generator reads the genuinely renamed original edge. -/
theorem oneLoop_renamed_monodromy (e : Bool) :
    oneLoopRenamedData.edgeMonodromyAt oneLoopRootedPaths oneLoopComponent e rfl =
      oneLoopData.renamedEdgeEquiv oneLoopSwap e := by
  apply Equiv.ext
  intro x
  cases e <;> cases x <;> rfl

private theorem oneLoop_perm_eq_one_or_swap (p : Equiv.Perm Bool) :
    p = 1 ∨ p = Equiv.swap false true := by
  rcases oneLoop_visible_eq_one_or_swap (oneLoopGraphAutOfPerm p) with h | h
  · exact Or.inl (congrArg
      (fun g : FixedFGraphAutomorphism oneLoopGraph => g.edge) h)
  · exact Or.inr (congrArg
      (fun g : FixedFGraphAutomorphism oneLoopGraph => g.edge) h)

/-- The original named `true` loop supplies the transposition generator,
while the other original loop supplies the identity. -/
theorem oneLoop_original_holonomy_top :
    oneLoopData.holonomy oneLoopRootedPaths oneLoopComponent = ⊤ := by
  have hswap : (Equiv.swap false true : Equiv.Perm Bool) ∈
      oneLoopData.holonomy oneLoopRootedPaths oneLoopComponent := by
    have h := oneLoopData.edgeMonodromyAt_mem_holonomy
      oneLoopRootedPaths oneLoopComponent true rfl
    simpa [oneLoop_original_monodromy, oneLoopData] using h
  apply Subgroup.ext
  intro p
  constructor
  · intro _; trivial
  · intro _
    rcases oneLoop_perm_eq_one_or_swap p with h | h
    · subst p; exact Subgroup.one_mem _
    · subst p; exact hswap

/-- After the actual visible name exchange, the original `false` loop
supplies the transposition generator. -/
theorem oneLoop_renamed_holonomy_top :
    oneLoopRenamedData.holonomy oneLoopRootedPaths oneLoopComponent = ⊤ := by
  have hswap : (Equiv.swap false true : Equiv.Perm Bool) ∈
      oneLoopRenamedData.holonomy oneLoopRootedPaths oneLoopComponent := by
    have h := oneLoopRenamedData.edgeMonodromyAt_mem_holonomy
      oneLoopRootedPaths oneLoopComponent false rfl
    simpa [oneLoop_renamed_monodromy, oneLoopData, oneLoopSwap,
      ReversibleData.renamedEdgeEquiv] using h
  apply Subgroup.ext
  intro p
  constructor
  · intro _; trivial
  · intro _
    rcases oneLoop_perm_eq_one_or_swap p with h | h
    · subst p; exact Subgroup.one_mem _
    · subst p; exact hswap

theorem oneLoop_original_holonomy_card_two :
    Nat.card (oneLoopData.holonomy oneLoopRootedPaths oneLoopComponent) = 2 := by
  rw [oneLoop_original_holonomy_top]
  have hcard : Nat.card (Equiv.Perm Bool) = 2 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_bool]
    decide
  calc
    Nat.card (⊤ : Subgroup (Equiv.Perm Bool)) =
        Nat.card (Equiv.Perm Bool) :=
      Nat.card_congr (Subgroup.topEquiv :
        (⊤ : Subgroup (Equiv.Perm Bool)) ≃* Equiv.Perm Bool).toEquiv
    _ = 2 := hcard

theorem oneLoop_renamed_holonomy_card_two :
    Nat.card (oneLoopRenamedData.holonomy oneLoopRootedPaths oneLoopComponent) = 2 := by
  rw [oneLoop_renamed_holonomy_top]
  have hcard : Nat.card (Equiv.Perm Bool) = 2 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_bool]
    decide
  calc
    Nat.card (⊤ : Subgroup (Equiv.Perm Bool)) =
        Nat.card (Equiv.Perm Bool) :=
      Nat.card_congr (Subgroup.topEquiv :
        (⊤ : Subgroup (Equiv.Perm Bool)) ≃* Equiv.Perm Bool).toEquiv
    _ = 2 := hcard

theorem oneLoop_original_holonomy_isCyclic :
    IsCyclic (oneLoopData.holonomy oneLoopRootedPaths oneLoopComponent) :=
  isCyclic_of_prime_card oneLoop_original_holonomy_card_two

theorem oneLoop_renamed_holonomy_isCyclic :
    IsCyclic (oneLoopRenamedData.holonomy oneLoopRootedPaths oneLoopComponent) :=
  isCyclic_of_prime_card oneLoop_renamed_holonomy_card_two

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.oneLoopRootedPaths
#print axioms AAT.AG.ProtocolHolonomy.oneLoopRenamedData
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_renamed_semantic_edge
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_original_monodromy
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_renamed_monodromy
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_original_holonomy_top
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_renamed_holonomy_top
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_original_holonomy_card_two
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_renamed_holonomy_card_two
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_original_holonomy_isCyclic
#print axioms AAT.AG.ProtocolHolonomy.oneLoop_renamed_holonomy_isCyclic
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
