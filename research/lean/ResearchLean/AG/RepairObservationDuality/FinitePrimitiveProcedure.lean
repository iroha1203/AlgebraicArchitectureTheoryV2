import ResearchLean.AG.RepairObservationDuality.PrimitiveQueries

/-!
# G-131 D: finite fixed controllers with a generated full-value finisher

## Implementation notes

The controller asks a known list and passes only the visible history to its
finisher. In the planning application the finisher is a terminating finite
search/linear solver, rather than a supplied valid answer. Every repeated
question is retained and counted here.
-/
namespace AAT.AG.RepairObservationDuality.FinitePrimitiveProcedure
open PrimitiveQueries
variable {V J k A : Type*}
variable (eval : V → J → k) (points : List J) (finish : History J k → A)

/-- D's fixed controller reads only its known question list and visible history. -/
def procedure : Procedure J k A := fun hist => match points.drop hist.length with
  | [] => Sum.inl (finish hist)
  | j :: _ => Sum.inr j

/-- The controller's next step depends exactly on the remaining fixed questions. -/
theorem procedure_apply (hist : History J k) :
    procedure points finish hist = match points.drop hist.length with
      | [] => Sum.inl (finish hist)
      | j :: _ => Sum.inr j := rfl

/-- The complete finite execution is generated from each actual prefix and suffix. -/
theorem run_aux (v : V) (pre remaining : List J) (hp : points = pre ++ remaining) :
    Run eval (procedure points finish) v (transcript eval pre v)
      (finish (transcript eval points v)) remaining := by
  induction remaining generalizing pre with
  | nil =>
    apply Run.halt
    rw [procedure_apply]
    simp only [hp, List.append_nil, transcript, List.length_map, List.drop_length]
  | cons j js ih =>
    have ht : points = (pre ++ [j]) ++ js := by simpa only [List.append_assoc,List.singleton_append] using hp
    apply Run.ask (by rw [procedure_apply]; simp [transcript, hp])
    simpa only [transcript, List.map_append, List.map_singleton] using ih (pre ++ [j]) ht

/-- D's generated controller always terminates after exactly its original question list. -/
theorem run (v : V) :
    Run eval (procedure points finish) v [] (finish (transcript eval points v)) points := by
  simpa only [transcript, List.map_nil] using run_aux eval points finish v [] points rfl

/-- Every run of the finite controller has its computed full value and its complete question list. -/
theorem run_iff (v : V) (a : A) (qs : List J) :
    Run eval (procedure points finish) v [] a qs ↔
      a = finish (transcript eval points v) ∧ qs = points := by
  constructor
  · intro h
    exact h.deterministic (run eval points finish v)
  · rintro ⟨ha,hq⟩
    rw [ha,hq]
    exact run eval points finish v

/-- A generated finisher valid on every actual transcript makes the whole finite controller correct. -/
theorem correct (F : Set V) (valid : V → A → Prop)
    (hf : ∀ v ∈ F, valid v (finish (transcript eval points v))) :
    Correct eval F valid (procedure points finish) := by
  constructor
  · intro v _
    exact ⟨_,points,run eval points finish v⟩
  · intro v hv a qs hr
    rw [(run_iff eval points finish v a qs).mp hr |>.1]
    exact hf v hv

/-- Every actual run counts exactly the fixed list length, including repeats. -/
theorem worst_le (F : Set V) :
    worst eval F (procedure points finish) ≤ (points.length : ℕ∞) := by
  refine iSup_le fun v => iSup_le fun hv => iSup_le fun a => iSup_le fun qs => iSup_le fun hr => ?_
  rw [(run_iff eval points finish v a qs).mp hr |>.2]

/-- On every nonempty known fiber the worst count is exactly the fixed list length. -/
theorem worst_eq (F : Set V) {w : V} (hw : w ∈ F) :
    worst eval F (procedure points finish) = (points.length : ℕ∞) := by
  apply le_antisymm (worst_le eval points finish F)
  exact run_le_worst eval F (procedure points finish) hw (run eval points finish w)

end AAT.AG.RepairObservationDuality.FinitePrimitiveProcedure
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FinitePrimitiveProcedure
