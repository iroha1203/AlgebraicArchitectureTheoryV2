import ResearchLean.AG.OperationRepair.Universal

/-!
# Combining repair requests

The generated lower endpoint preserves unions of request families. The upper
endpoint is fixed by the operation system and observation, so joint repair is
equivalent to repair of each request.
-/

namespace AAT.AG.OperationRepair

universe u v w i

variable {S : Type u} {E : Type v} {O : Type w} {I : Type i}
variable (T : OperationSystem S E) (observe : S → O)

/-- A family of requests combined by union. -/
def requestUnion (Rs : I → S → S → Prop) (x y : S) : Prop :=
  ∃ index, Rs index x y

/-- GOAL C: generating the union of requests equals the join of the generated
operation congruences. This also applies to an empty family. -/
theorem generated_requestUnion (Rs : I → S → S → Prop) :
    generated T (requestUnion Rs) = ⨆ index, generated T (Rs index) := by
  apply le_antisymm
  · apply (generated_le_iff T _).mpr
    intro x y h
    obtain ⟨index, hi⟩ := h
    exact (le_iSup (fun j => generated T (Rs j)) index)
      (generated_contains T hi)
  · apply iSup_le
    intro index
    apply (generated_le_iff T _).mpr
    intro x y hi
    exact generated_contains T ⟨index, hi⟩

/-- The empty request generates equality, including on an empty state type. -/
theorem generated_empty :
    generated T (fun _ _ => False) = ⊥ := by
  apply le_antisymm
  · apply (generated_le_iff T _).mpr
    intro x y h
    exact False.elim h
  · exact bot_le

/-- GOAL C: a union is repairable exactly when every constituent request is
repairable. No finiteness condition is needed for this lattice statement. -/
theorem repairable_requestUnion_iff (Rs : I → S → S → Prop) :
    generated T (requestUnion Rs) ≤ behavior T observe ↔
      ∀ index, generated T (Rs index) ≤ behavior T observe := by
  rw [generated_requestUnion]
  exact iSup_le_iff

#assert_standard_axioms_only AAT.AG.OperationRepair

end AAT.AG.OperationRepair
