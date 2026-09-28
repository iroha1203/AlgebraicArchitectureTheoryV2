import ResearchLean.AG.ProtocolHolonomy.OneVertexTwoLoops
import Formal.Util.AssertStandardAxioms

/-!
# Full primitive input for the first fixed example

The named one-vertex graph has no authored path equations. Its visible
group is the full automorphism group of this two-name graph; the explicit
identification with C₂ is a separate proof obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

/-- The fixed example has no authored path equations. -/
def oneLoopEmptyEquations : PathEquations oneLoopGraph where
  Index := PEmpty
  finiteIndex := inferInstance
  source := PEmpty.elim
  target := PEmpty.elim
  left := fun r => PEmpty.elim r
  right := fun r => PEmpty.elim r

/-- The complete finite A-side input, with all visible permutations of the
two named loops admitted. -/
def oneLoopInput : FiniteProtocolInput oneLoopGraph where
  data := oneLoopData
  finiteVertex := by change Finite PUnit; infer_instance
  finiteEdge := by change Finite Bool; infer_instance
  finiteFiber := by
    intro x
    change Finite Bool
    infer_instance
  equations := oneLoopEmptyEquations
  satisfies := fun r => PEmpty.elim r
  H := ⊤
  renaming_preserves := fun _ _ r => PEmpty.elim r

theorem oneLoopSwap_mem_H : oneLoopSwap ∈ oneLoopInput.H := by
  trivial

theorem oneLoopInput_no_equations : IsEmpty oneLoopInput.equations.Index := by
  change IsEmpty PEmpty
  infer_instance

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.oneLoopEmptyEquations
#print axioms AAT.AG.ProtocolHolonomy.oneLoopInput
#print axioms AAT.AG.ProtocolHolonomy.oneLoopSwap_mem_H
#print axioms AAT.AG.ProtocolHolonomy.oneLoopInput_no_equations
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
