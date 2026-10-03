import ResearchLean.AG.RepairObservationDuality.PrimitiveQueries

/-!
# Actual primitive evaluations and parameter executions

## Implementation notes

G-131 A/C / n1017 §3.5, §6: an actual permitted primitive evaluation agrees
with the parameter evaluation after ν. Every parameter has an actual
realization. These are input representation conditions; no correct procedure
or optimal count is assumed. The same history-only procedure retains the
complete output, ordered replies, repeated questions and actual query cost.
-/
namespace AAT.AG.RepairObservationDuality.PrimitiveInputQueries
open PrimitiveQueries
set_option autoImplicit false
variable {F V J K A : Type*} (ν : F → V) (realize : V → F)
variable (hrealize : ∀ v, ν (realize v) = v)
variable (actual : F → J → K) (parameter : V → J → K)
variable (heval : ∀ X j, actual X j = parameter (ν X) j)
include heval

/-- G-131 A/C / n1017 §3.5, §6: the same deterministic procedure on an actual
input and its parameter has the same full output and exact query list. -/
theorem run_iff (next : Procedure J K A) (X : F) (hist : History J K)
    (a : A) (qs : List J) :
    Run actual next X hist a qs ↔ Run parameter next (ν X) hist a qs := by
  constructor
  · intro run
    induction run with
    | halt h => exact Run.halt h
    | @ask hist a j qs h tail ih =>
      apply Run.ask h
      simpa only [heval] using ih
  · intro run
    induction run with
    | halt h => exact Run.halt h
    | @ask hist a j qs h tail ih =>
      apply Run.ask h
      simpa only [heval] using ih

/-- G-131 A/C / n1017 §3.5, §6: fixed executions preserve every original
primitive name and response in order, including repeated names. -/
theorem transcript_eq (points : List J) (X : F) :
    transcript actual points X = transcript parameter points (ν X) := by
  apply List.map_congr_left
  intro j _
  exact congrArg (fun t => (j,t)) (heval X j)

include hrealize

/-- G-131 C / n1017 §6 constructor API: total correctness of the same
history-only procedure is equivalent on the actual fiber and its parameters. -/
theorem correct_iff (fiber : Set V) (valid : V → A → Prop)
    (next : Procedure J K A) :
    Correct actual (ν ⁻¹' fiber) (fun X a => valid (ν X) a) next ↔
      Correct parameter fiber valid next := by
  constructor
  · rintro ⟨ht,hv⟩
    constructor
    · intro v hm
      obtain ⟨a,qs,hr⟩ := ht (realize v) (by simpa [hrealize] using hm)
      exact ⟨a,qs,by simpa only [hrealize] using
        (run_iff ν actual parameter heval next (realize v) [] a qs).mp hr⟩
    · intro v hm a qs hr
      have ha := hv (realize v) (by simpa [hrealize] using hm) a qs
        ((run_iff ν actual parameter heval next (realize v) [] a qs).mpr
          (by simpa only [hrealize] using hr))
      simpa only [hrealize] using ha
  · rintro ⟨ht,hv⟩
    constructor
    · intro X hm
      obtain ⟨a,qs,hr⟩ := ht (ν X) hm
      exact ⟨a,qs,(run_iff ν actual parameter heval next X [] a qs).mpr hr⟩
    · intro X hm a qs hr
      exact hv (ν X) hm a qs ((run_iff ν actual parameter heval next X [] a qs).mp hr)

/-- G-131 C / n1017 §6: the actual worst query count equals the parameter
worst count for every procedure, counting the entire repeated query list. -/
theorem worst_eq (fiber : Set V) (next : Procedure J K A) :
    worst actual (ν ⁻¹' fiber) next = worst parameter fiber next := by
  apply le_antisymm
  · refine iSup_le fun X => iSup_le fun hm => iSup_le fun a =>
      iSup_le fun qs => iSup_le fun hr => ?_
    exact run_le_worst parameter fiber next hm
      ((run_iff ν actual parameter heval next X [] a qs).mp hr)
  · refine iSup_le fun v => iSup_le fun hm => iSup_le fun a =>
      iSup_le fun qs => iSup_le fun hr => ?_
    exact run_le_worst actual (ν ⁻¹' fiber) next
      (show realize v ∈ ν ⁻¹' fiber by simpa [hrealize] using hm)
      ((run_iff ν actual parameter heval next (realize v) [] a qs).mpr
        (by simpa only [hrealize] using hr))

/-- G-131 C / n1017 §6: minimization over all terminating correct deterministic
procedures has the same value, including infinity and the all-impossible zero. -/
theorem optimum_eq (fiber : Set V) (valid : V → A → Prop) :
    optimum actual (ν ⁻¹' fiber) (fun X a => valid (ν X) a) =
      optimum parameter fiber valid := by
  apply le_antisymm
  · refine le_iInf fun next => ?_
    exact (optimum_le_worst actual (ν ⁻¹' fiber) (fun X a => valid (ν X) a) next.1
      ((correct_iff ν realize hrealize actual parameter heval fiber valid next.1).mpr next.2)).trans_eq
      (worst_eq ν realize hrealize actual parameter heval fiber next.1)
  · refine le_iInf fun next => ?_
    exact (optimum_le_worst parameter fiber valid next.1
      ((correct_iff ν realize hrealize actual parameter heval fiber valid next.1).mp next.2)).trans_eq
      (worst_eq ν realize hrealize actual parameter heval fiber next.1).symm

end AAT.AG.RepairObservationDuality.PrimitiveInputQueries
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.PrimitiveInputQueries
