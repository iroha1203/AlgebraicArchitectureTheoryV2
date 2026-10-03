import ResearchLean.AG.RepairObservationDuality.PrimitiveQueries

/-!
# G-131 B: subtracting known primitive constants

Changing the successful origin changes each reply by a known constant. The
procedure converts its visible history before choosing a next step. The
unknown input, full output, and entire repeated query list remain the same.

## Implementation notes

Converting the visible history allows the original next-step function
to operate unchanged. Supplying translated answers in advance would require
the unknown evaluations instead of just their known constant differences.

-/

namespace AAT.AG.RepairObservationDuality.PrimitiveReplyTranslation
open PrimitiveQueries
variable {F J K A : Type*} [AddCommGroup K]

/-- B's known per-index constants translate each visible reply without changing its original index. -/
def history (c : J → K) (hist : History J K) : History J K :=
  hist.map fun p => (p.1, p.2 + c p.1)

/-- A procedure sees its original replies after the known translation of its visible history. -/
def procedure (c : J → K) (next : Procedure J K A) : Procedure J K A :=
  fun hist => next (history c hist)

variable (raw shifted : F → J → K) (c : J → K)
variable (heval : ∀ X j, raw X j = shifted X j + c j)
include heval

/-- B's origin shift preserves each run, its full output and all repetitions in both directions. -/
theorem run_iff (next : Procedure J K A) (X : F) (hist : History J K) (a : A) (qs : List J) :
    Run shifted (procedure c next) X hist a qs ↔
      Run raw next X (history c hist) a qs := by
  constructor
  · intro run
    induction run with
    | halt h => exact Run.halt h
    | @ask hist a j qs h tail ih =>
        apply Run.ask (show next (history c hist) = Sum.inr j from h)
        simpa only [history, List.map_append, List.map_cons, List.map_nil, heval] using ih
  · intro run
    generalize hh : history c hist = rhist at run
    induction run generalizing hist with
    | halt h =>
        apply Run.halt
        simpa only [procedure, hh] using h
    | @ask rhist a j qs h tail ih =>
        apply Run.ask (by simpa only [procedure, hh] using h)
        apply ih
        simp only [history] at hh
        simp only [history, List.map_append, List.map_cons, List.map_nil, ← heval, hh]

/-- B's origin translation preserves total correctness for the independently specified full output. -/
theorem correct_iff (fiber : Set F) (valid : F → A → Prop) (next : Procedure J K A) :
    Correct shifted fiber valid (procedure c next) ↔ Correct raw fiber valid next := by
  constructor
  · rintro ⟨ht,hv⟩
    constructor
    · intro X hm
      obtain ⟨a,qs,hr⟩ := ht X hm
      exact ⟨a,qs,(run_iff raw shifted c heval next X [] a qs).mp hr⟩
    · intro X hm a qs hr
      exact hv X hm a qs ((run_iff raw shifted c heval next X [] a qs).mpr hr)
  · rintro ⟨ht,hv⟩
    constructor
    · intro X hm
      obtain ⟨a,qs,hr⟩ := ht X hm
      exact ⟨a,qs,(run_iff raw shifted c heval next X [] a qs).mpr hr⟩
    · intro X hm a qs hr
      exact hv X hm a qs ((run_iff raw shifted c heval next X [] a qs).mp hr)

/-- B's per-procedure worst cost is unchanged by subtracting known response constants. -/
theorem worst_eq (fiber : Set F) (next : Procedure J K A) :
    worst shifted fiber (procedure c next) = worst raw fiber next := by
  apply le_antisymm
  · refine iSup_le fun X => iSup_le fun hm => iSup_le fun a =>
      iSup_le fun qs => iSup_le fun hr => ?_
    exact run_le_worst raw fiber next hm ((run_iff raw shifted c heval next X [] a qs).mp hr)
  · refine iSup_le fun X => iSup_le fun hm => iSup_le fun a =>
      iSup_le fun qs => iSup_le fun hr => ?_
    exact run_le_worst shifted fiber (procedure c next) hm
      ((run_iff raw shifted c heval next X [] a qs).mpr hr)

/-- Translating every correct raw procedure bounds the shifted optimum without assuming a solver. -/
theorem optimum_le (fiber : Set F) (valid : F → A → Prop) :
    optimum shifted fiber valid ≤ optimum raw fiber valid := by
  refine le_iInf fun next => ?_
  exact (optimum_le_worst shifted fiber valid (procedure c next.1)
    ((correct_iff raw shifted c heval fiber valid next.1).mpr next.2)).trans_eq
      (worst_eq raw shifted c heval fiber next.1)

/-- B's full origin shift preserves the optimum over all correct procedures, including infinity. -/
theorem optimum_eq (fiber : Set F) (valid : F → A → Prop) :
    optimum shifted fiber valid = optimum raw fiber valid := by
  apply le_antisymm (optimum_le raw shifted c heval fiber valid)
  apply optimum_le shifted raw (fun j => -c j) _ fiber valid
  intro X j
  rw [heval]
  simp

end AAT.AG.RepairObservationDuality.PrimitiveReplyTranslation
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.PrimitiveReplyTranslation
