import ResearchLean.AG.RepairObservationDuality.PrimitiveQueries

/-!
# G-131 E: total output maps preserve primitive query traces

## Implementation notes

A known fresh coordinate can extend a numerical answer without being a
bijection onto all extended answers. This API therefore uses arbitrary total
maps. Backward execution retains an existential original answer, rather than
pretending that a fixed-coordinate extension has an inverse on all outputs.
The same repeated question list proves exact cost preservation.
-/
namespace AAT.AG.RepairObservationDuality.PrimitiveOutputMap
open PrimitiveQueries
variable {V J K A B : Type*} (eval : V → J → K) (f : A → B)

/-- Map only the complete output, leaving every primitive request untouched. -/
def transport (next : Procedure J K A) : Procedure J K B := fun hist => Sum.map f id (next hist)

/-- The mapped step is its full output map or the unchanged original question. -/
theorem transport_apply (next : Procedure J K A) (hist : History J K) :
    transport f next hist = Sum.map f id (next hist) := rfl

/-- Mapping an output preserves the complete ordered primitive run. -/
theorem run_forward {next : Procedure J K A} {v hist a qs}
    (hr : Run eval next v hist a qs) : Run eval (transport f next) v hist (f a) qs := by
  induction hr with
  | halt h => exact Run.halt (by rw [transport_apply,h]; rfl)
  | ask h _ ih => exact Run.ask (by rw [transport_apply,h]; rfl) ih

/-- Every mapped run comes from an original full answer with exactly the same repeated questions. -/
theorem run_backward {next : Procedure J K A} {v hist b qs}
    (hr : Run eval (transport f next) v hist b qs) :
    ∃ a, Run eval next v hist a qs ∧ f a = b := by
  induction hr with
  | @halt hist b h =>
    rw [transport_apply] at h
    cases he : next hist with
    | inl a => exact ⟨a,Run.halt he,Sum.inl.inj (by simpa only [he,Sum.map_inl] using h)⟩
    | inr j => rw [he] at h; cases h
  | @ask hist b j qs h _ ih =>
    obtain ⟨a,ha,hb⟩ := ih
    refine ⟨a,Run.ask ?_ ha,hb⟩
    rw [transport_apply] at h
    cases he : next hist with
    | inl a => rw [he] at h; cases h
    | inr i => exact congrArg Sum.inr (Sum.inr.inj (by simpa only [he,Sum.map_inr,id_eq] using h))

/-- A full-answer map satisfying independent validators preserves total correctness. -/
theorem correct (F : Set V) (validA : V → A → Prop) (validB : V → B → Prop)
    (hf : ∀ v ∈ F, ∀ a, validA v a → validB v (f a))
    {next : Procedure J K A} (hn : Correct eval F validA next) :
    Correct eval F validB (transport f next) := by
  constructor
  · intro v hv
    obtain ⟨a,qs,hr⟩ := hn.1 v hv
    exact ⟨f a,qs,run_forward eval f hr⟩
  · intro v hv b qs hr
    obtain ⟨a,ha,rfl⟩ := run_backward eval f hr
    exact hf v hv a (hn.2 v hv a qs ha)

/-- Any complete output map preserves exact worst primitive cost on every input fiber. -/
theorem worst_eq (F : Set V) (next : Procedure J K A) :
    worst eval F (transport f next) = worst eval F next := by
  apply le_antisymm
  · refine iSup_le fun v => iSup_le fun hv => iSup_le fun b => iSup_le fun qs => iSup_le fun hr => ?_
    obtain ⟨a,ha,_⟩ := run_backward eval f hr
    exact run_le_worst eval F next hv ha
  · refine iSup_le fun v => iSup_le fun hv => iSup_le fun a => iSup_le fun qs => iSup_le fun hr => ?_
    exact run_le_worst eval F (transport f next) hv (run_forward eval f hr)

/-- A total correct full-answer map bounds the optimum over all procedures in its destination language. -/
theorem optimum_le (F : Set V) (validA : V → A → Prop) (validB : V → B → Prop)
    (hf : ∀ v ∈ F, ∀ a, validA v a → validB v (f a)) :
    optimum eval F validB ≤ optimum eval F validA := by
  refine le_iInf fun next => ?_
  exact (optimum_le_worst eval F validB (transport f next.1)
    (correct eval f F validA validB hf next.2)).trans_eq (worst_eq eval f F next.1)

end AAT.AG.RepairObservationDuality.PrimitiveOutputMap
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.PrimitiveOutputMap
