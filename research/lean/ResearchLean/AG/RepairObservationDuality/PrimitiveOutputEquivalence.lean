import ResearchLean.AG.RepairObservationDuality.PrimitiveQueries
/-!
# G-131 C/D: reversible full output coordinates preserve query optima

## Implementation notes

Only full answer values change by the supplied equivalence. Every question,
reply and repeated question is unchanged. This transfers minima between the
flattened full vector and the prescribed whole correction coordinates; it
does not replace a correction by its image or residual.
-/
namespace AAT.AG.RepairObservationDuality.PrimitiveOutputEquivalence
open PrimitiveQueries
variable {V J K A B : Type*} (eval : V → J → K) (e : A ≃ B)

/-- C/D's answer transport leaves every primitive request and visible history unchanged. -/
def transport (next : Procedure J K A) : Procedure J K B :=
  fun hist => Sum.map e id (next hist)

/-- Answer transport's step is precisely the full output equivalence, or the same original question. -/
theorem transport_apply (next : Procedure J K A) (hist : History J K) :
    transport e next hist = Sum.map e id (next hist) := rfl

/-- Every original run transports its full answer with exactly the same actual question list. -/
theorem run_forward {next : Procedure J K A} {v hist a qs}
    (hr : Run eval next v hist a qs) : Run eval (transport e next) v hist (e a) qs := by
  induction hr with
  | halt h => exact Run.halt (by rw [transport_apply,h]; rfl)
  | ask h _ ih => exact Run.ask (by rw [transport_apply,h]; rfl) ih

/-- Every transported run restores its original full answer and identical primitive list. -/
theorem run_backward {next : Procedure J K A} {v hist b qs}
    (hr : Run eval (transport e next) v hist b qs) : Run eval next v hist (e.symm b) qs := by
  induction hr with
  | @halt hist b h =>
    apply Run.halt
    rw [transport_apply] at h
    cases he : next hist with
    | inl a =>
      rw [he] at h
      have hi := Sum.inl.inj h
      rw [← hi,e.symm_apply_apply]
    | inr j => rw [he] at h; cases h
  | @ask hist b j qs h _ ih =>
    apply Run.ask _ ih
    rw [transport_apply] at h
    cases he : next hist with
    | inl a => rw [he] at h; cases h
    | inr i =>
      rw [he] at h
      exact congrArg Sum.inr (Sum.inr.inj h)

/-- Full answer transport reflects and preserves every run with its exact repeated query count. -/
theorem run_iff (next : Procedure J K A) (v : V) (hist : History J K) (a : A) (qs : List J) :
    Run eval (transport e next) v hist (e a) qs ↔ Run eval next v hist a qs := by
  constructor
  · intro hr
    simpa only [e.symm_apply_apply] using run_backward eval e hr
  · exact run_forward eval e

/-- Whole answer transport preserves total correctness against the independently transported validator. -/
theorem correct_iff (F : Set V) (valid : V → A → Prop) (next : Procedure J K A) :
    Correct eval F (fun v b => valid v (e.symm b)) (transport e next) ↔ Correct eval F valid next := by
  constructor
  · rintro ⟨ht,hv⟩
    refine ⟨?_,?_⟩
    · intro v hm
      obtain ⟨b,qs,hr⟩ := ht v hm
      refine ⟨e.symm b,qs,(run_iff eval e next v [] (e.symm b) qs).mp ?_⟩
      simpa only [e.apply_symm_apply] using hr
    · intro v hm a qs hr
      simpa only [e.symm_apply_apply] using hv v hm (e a) qs ((run_iff eval e next v [] a qs).mpr hr)
  · rintro ⟨ht,hv⟩
    refine ⟨?_,?_⟩
    · intro v hm
      obtain ⟨a,qs,hr⟩ := ht v hm
      exact ⟨e a,qs,(run_iff eval e next v [] a qs).mpr hr⟩
    · intro v hm b qs hr
      apply hv v hm (e.symm b) qs
      apply (run_iff eval e next v [] (e.symm b) qs).mp
      simpa only [e.apply_symm_apply] using hr

/-- Whole output equivalence preserves every actual procedure's worst primitive query count. -/
theorem worst_eq (F : Set V) (next : Procedure J K A) :
    worst eval F (transport e next) = worst eval F next := by
  apply le_antisymm
  · refine iSup_le fun v => iSup_le fun hv => iSup_le fun b => iSup_le fun qs => iSup_le fun hr => ?_
    apply run_le_worst eval F next hv
    apply (run_iff eval e next v [] (e.symm b) qs).mp
    simpa only [e.apply_symm_apply] using hr
  · refine iSup_le fun v => iSup_le fun hv => iSup_le fun a => iSup_le fun qs => iSup_le fun hr => ?_
    exact run_le_worst eval F (transport e next) hv ((run_iff eval e next v [] a qs).mpr hr)

/-- Forward and inverse full answer transports recover the original history-only procedure. -/
theorem transport_symm (next : Procedure J K A) :
    transport e.symm (transport e next) = next := by
  funext hist
  rw [transport_apply,transport_apply]
  cases next hist <;> simp only [Sum.map_inl,Sum.map_inr,e.symm_apply_apply,id_eq]

/-- Every correct full-output procedure is retained in the optimum after a reversible coordinate change. -/
theorem optimum_eq (F : Set V) (valid : V → A → Prop) :
    optimum eval F (fun v b => valid v (e.symm b)) = optimum eval F valid := by
  apply le_antisymm
  · refine le_iInf fun next => ?_
    exact (optimum_le_worst eval F _ (transport e next.1)
      ((correct_iff eval e F valid next.1).mpr next.2)).trans_eq (worst_eq eval e F next.1)
  · refine le_iInf fun next => ?_
    have hback : transport e (transport e.symm next.1) = next.1 := by
      simpa only [Equiv.symm_symm] using transport_symm e.symm next.1
    have hc := (correct_iff eval e F valid (transport e.symm next.1)).mp
      (by rw [hback]; exact next.2)
    exact (optimum_le_worst eval F valid (transport e.symm next.1) hc).trans_eq
      (worst_eq eval e.symm F next.1)

end AAT.AG.RepairObservationDuality.PrimitiveOutputEquivalence
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.PrimitiveOutputEquivalence
