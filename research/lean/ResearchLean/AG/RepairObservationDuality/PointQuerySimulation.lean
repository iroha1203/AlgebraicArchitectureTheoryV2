import ResearchLean.AG.RepairObservationDuality.AdditiveObservationAction
import ResearchLean.AG.MinimalCompatibilityObservations.QueryOptimum

/-!
# G-131 B: primitive and point query simulations

Both next-step functions see only their own history. The conversion from
arbitrary points reconstructs the known offsets by replaying the next-step
function on the visible primitive history. Every executed question remains
in the list, including repetitions of the same primitive or point.

## Implementation notes

Primitive history does not store a point offset. Replaying the point
next-step function recovers it from visible replies; supplying the offsets
as additional input would change the permitted procedure model.

-/

namespace AAT.AG.RepairObservationDuality.PointQuerySimulation
open PrimitiveQueries MinimalCompatibilityObservations AdditiveObservationAction

variable {k V J : Type*} [Field k] [AddCommGroup V] [Module k V]
variable (lam : J → V →ₗ[k] k)

/-- B's primitive response is the original linear evaluation at the unknown input. -/
def evaluation (n : V) (j : J) : k := lam j n

/-- The visible point response is decoded using its own known query offset. -/
def decode (hist : QueryHistory (J × k)) : History J k :=
  hist.map fun p => (p.1.1, p.2.2 - p.1.2)

/-- A primitive procedure becomes a point procedure asking the same index at offset zero. -/
def toPoint (next : Procedure J k Bool) : QueryProcedure (J × k) := fun hist =>
  match next (decode hist) with
  | Sum.inl a => Sum.inl a
  | Sum.inr j => Sum.inr (j, 0)

/-- Every primitive run is a point run with identical output and one zero point per query. -/
theorem primitive_to_point {next : Procedure J k Bool} {n : V} {hist a qs}
    (run : Run (evaluation lam) next n hist a qs) (phist : QueryHistory (J × k))
    (he : decode phist = hist) :
    letI := action lam;
    QueryRun (toPoint next) (Multiplicative.ofAdd n) phist a
      (qs.map fun j => (j, 0)) := by
  letI := action lam
  induction run generalizing phist with
  | halt h =>
      apply QueryRun.halt
      simp only [toPoint, he, h]
  | @ask hist a j qs h tail ih =>
      apply QueryRun.ask (x := (j, 0))
      · simp only [toPoint, he, h]
      · apply ih
        simp only [decode] at he
        simp [decode, List.map_append, he, evaluation, action_apply]

/-- Conversely, each run of the converted point procedure decodes to the same primitive run. -/
theorem point_to_primitive {next : Procedure J k Bool} {n : Multiplicative V}
    {hist a qs} (run : @QueryRun (Multiplicative V) (J × k) _ (action lam) (toPoint next) n hist a qs) :
    Run (evaluation lam) next n.toAdd (decode hist) a (qs.map Prod.fst) ∧
      qs = (qs.map Prod.fst).map (fun j => (j, 0)) := by
  letI := action lam
  induction run with
  | @halt hist a h =>
      have hp : next (decode hist) = Sum.inl a := by
        cases hn : next (decode hist) with
        | inl b => simpa only [toPoint, hn, Sum.inl.injEq] using h
        | inr j => simp only [toPoint, hn, Sum.inr_ne_inl] at h
      exact ⟨Run.halt hp, rfl⟩
  | @ask hist a p qs h tail ih =>
      obtain ⟨j, hp, he⟩ : ∃ j, next (decode hist) = Sum.inr j ∧ p = (j, 0) := by
        cases hn : next (decode hist) with
        | inl b => simp only [toPoint, hn, Sum.inl_ne_inr] at h
        | inr j => exact ⟨j, rfl, (Sum.inr.inj (by simpa only [toPoint, hn] using h)).symm⟩
      subst p
      refine ⟨Run.ask hp ?_, ?_⟩
      · have hd : decode (hist ++ [((j, 0), n • (j, 0))]) =
            decode hist ++ [(j, evaluation lam n.toAdd j)] := by
          change List.map (fun p => (p.1.1, p.2.2 - p.1.2))
            (hist ++ [((j, 0), (j, 0 + lam j n.toAdd))]) = _
          simp only [decode, List.map_append, List.map_cons, List.map_nil,
            zero_add, sub_zero, evaluation]
        exact hd ▸ ih.1
      · exact congrArg (List.cons (j, 0)) ih.2

/-- Replaying a point next-step function recovers its offset for each primitive reply. -/
def inflateStep (next : QueryProcedure (J × k)) (hist : QueryHistory (J × k))
    (reply : J × k) : QueryHistory (J × k) :=
  match next hist with
  | Sum.inl _ => hist
  | Sum.inr p => hist ++ [(p, (p.1, p.2 + reply.2))]

/-- B's reconstructed point history depends only on the procedure and visible primitive history. -/
def inflate (next : QueryProcedure (J × k)) (hist : History J k) : QueryHistory (J × k) :=
  hist.foldl (inflateStep next) []

/-- An arbitrary point procedure becomes a primitive procedure asking its next point's index. -/
def fromPoint (next : QueryProcedure (J × k)) : Procedure J k Bool := fun hist =>
  match next (inflate next hist) with
  | Sum.inl a => Sum.inl a
  | Sum.inr p => Sum.inr p.1

/-- The reconstructed history appends the exact point response to the asked index. -/
theorem inflate_append {next : QueryProcedure (J × k)} {hist : History J k}
    {p : J × k} (hp : next (inflate next hist) = Sum.inr p) (n : V) :
    letI := action lam;
    inflate next (hist ++ [(p.1, evaluation lam n p.1)]) =
      inflate next hist ++ [(p, (Multiplicative.ofAdd n) • p)] := by
  letI := action lam
  simp only [inflate, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change inflateStep next (inflate next hist) (p.1, evaluation lam n p.1) = _
  simp only [inflateStep, hp, evaluation]
  rfl

/-- Every arbitrary point run is simulated by primitive queries with the same repeated index list. -/
theorem arbitrary_point_to_primitive {next : QueryProcedure (J × k)}
    {n : Multiplicative V} {phist a qs} (run : @QueryRun (Multiplicative V) (J × k) _ (action lam) next n phist a qs)
    (hist : History J k) (he : inflate next hist = phist) :
    Run (evaluation lam) (fromPoint next) n.toAdd hist a (qs.map Prod.fst) := by
  letI := action lam
  induction run generalizing hist with
  | halt h =>
      apply Run.halt
      simp only [fromPoint, he, h]
  | @ask phist a p qs h tail ih =>
      apply Run.ask (j := p.1)
      · simp only [fromPoint, he, h]
      · apply ih
        exact (inflate_append lam (he ▸ h) n.toAdd).trans (by rw [he]; rfl)

/-- Every physical run of the reconstructed primitive procedure lifts to the same point execution. -/
theorem primitive_to_arbitrary_point {next : QueryProcedure (J × k)} {n : V}
    {hist a qs} (run : Run (evaluation lam) (fromPoint next) n hist a qs) :
    letI := action lam;
    ∃ pqs, QueryRun next (Multiplicative.ofAdd n) (inflate next hist) a pqs ∧
      pqs.map Prod.fst = qs := by
  letI := action lam
  induction run with
  | @halt hist a h =>
      refine ⟨[], QueryRun.halt ?_, rfl⟩
      cases hp : next (inflate next hist) with
      | inl b => simpa only [fromPoint, hp, Sum.inl.injEq] using h
      | inr p => simp only [fromPoint, hp, Sum.inr_ne_inl] at h
  | @ask hist a j qs h tail ih =>
      obtain ⟨p, hp, hj⟩ : ∃ p, next (inflate next hist) = Sum.inr p ∧ p.1 = j := by
        cases hp : next (inflate next hist) with
        | inl b => simp only [fromPoint, hp, Sum.inl_ne_inr] at h
        | inr p => exact ⟨p, rfl, Sum.inr.inj (by simpa only [fromPoint, hp] using h)⟩
      obtain ⟨pqs, prun, hqs⟩ := ih
      refine ⟨p :: pqs, QueryRun.ask hp ?_, by simp [hj, hqs]⟩
      rw [← inflate_append lam hp n, hj]
      exact prun

/-- The zero-offset simulation preserves termination and correct repair-kernel decisions both ways. -/
theorem toPoint_correct_iff (R : Submodule k V) (next : Procedure J k Bool) :
    letI := action lam;
    Correct (evaluation lam) Set.univ (fun n a => a = true ↔ n ∈ R) next ↔
      CorrectQueryProcedure (compatible R) (toPoint next) := by
  letI := action lam
  constructor
  · intro hc
    constructor
    · intro n
      obtain ⟨a, qs, run⟩ := hc.1 n.toAdd (Set.mem_univ _)
      exact ⟨a, qs.map (fun j => (j, 0)), primitive_to_point lam run [] rfl⟩
    · intro n a qs run
      exact hc.2 n.toAdd (Set.mem_univ _) a (qs.map Prod.fst)
        (point_to_primitive lam run).1
  · intro hc
    constructor
    · intro n _
      obtain ⟨a, qs, run⟩ := hc.1 (Multiplicative.ofAdd n)
      exact ⟨a, qs.map Prod.fst, (point_to_primitive lam run).1⟩
    · intro n _ a qs run
      exact hc.2 (Multiplicative.ofAdd n) a (qs.map fun j => (j, 0))
        (primitive_to_point lam run [] rfl)

/-- Reconstructing arbitrary offsets preserves total correct kernel decisions in both directions. -/
theorem fromPoint_correct_iff (R : Submodule k V) (next : QueryProcedure (J × k)) :
    letI := action lam;
    CorrectQueryProcedure (compatible R) next ↔
      Correct (evaluation lam) Set.univ (fun n a => a = true ↔ n ∈ R) (fromPoint next) := by
  letI := action lam
  constructor
  · intro hc
    constructor
    · intro n _
      obtain ⟨a, qs, run⟩ := hc.1 (Multiplicative.ofAdd n)
      exact ⟨a, qs.map Prod.fst, arbitrary_point_to_primitive lam run [] rfl⟩
    · intro n _ a qs run
      obtain ⟨pqs, prun, _⟩ := primitive_to_arbitrary_point lam run
      exact hc.2 (Multiplicative.ofAdd n) a pqs prun
  · intro hc
    constructor
    · intro n
      obtain ⟨a, qs, run⟩ := hc.1 n.toAdd (Set.mem_univ _)
      obtain ⟨pqs, prun, _⟩ := primitive_to_arbitrary_point lam run
      exact ⟨a, pqs, prun⟩
    · intro n a qs run
      exact hc.2 n.toAdd (Set.mem_univ _) a (qs.map Prod.fst)
        (arbitrary_point_to_primitive lam run [] rfl)

/-- The zero-offset conversion preserves worst cost, counting all repetitions. -/
theorem toPoint_worst_eq (next : Procedure J k Bool) :
    letI := action lam;
    worstQueries (G := Multiplicative V) (toPoint next) =
      worst (evaluation lam) Set.univ next := by
  letI := action lam
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun a => iSup_le fun qs => iSup_le fun run => ?_
    have hr := (point_to_primitive lam run).1
    simpa only [List.length_map] using
      run_le_worst (evaluation lam) Set.univ next (Set.mem_univ _) hr
  · refine iSup_le fun n => iSup_le fun _ => iSup_le fun a =>
      iSup_le fun qs => iSup_le fun run => ?_
    simpa only [List.length_map] using run_count_le_worst (toPoint next)
      (Multiplicative.ofAdd n) a (qs.map fun j => (j, 0))
      (primitive_to_point lam run [] rfl)

/-- Replaying arbitrary point choices preserves worst cost even for multiple offsets at one index. -/
theorem fromPoint_worst_eq (next : QueryProcedure (J × k)) :
    letI := action lam;
    worst (evaluation lam) Set.univ (fromPoint next) =
      worstQueries (G := Multiplicative V) next := by
  letI := action lam
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun _ => iSup_le fun a =>
      iSup_le fun qs => iSup_le fun run => ?_
    obtain ⟨pqs, prun, he⟩ := primitive_to_arbitrary_point lam run
    have hlen : pqs.length = qs.length := by rw [← he, List.length_map]
    simpa only [hlen] using run_count_le_worst next (Multiplicative.ofAdd n) a pqs prun
  · refine iSup_le fun n => iSup_le fun a => iSup_le fun qs => iSup_le fun run => ?_
    simpa only [List.length_map] using run_le_worst (evaluation lam) Set.univ
      (fromPoint next) (Set.mem_univ _) (arbitrary_point_to_primitive lam run [] rfl)

/-- B's optimum ranges over all primitive procedures and all G-128 point procedures with equal cost. -/
theorem optimum_eq (R : Submodule k V) :
    letI := action lam;
    optimum (evaluation lam) Set.univ (fun n a => a = true ↔ n ∈ R) =
      optimalQueries (X := J × k) (compatible R) := by
  letI := action lam
  apply le_antisymm
  · change _ ≤ ⨅ p : {p : QueryProcedure (J × k) // CorrectQueryProcedure (compatible R) p}, _
    apply le_iInf
    intro p
    have hc := (fromPoint_correct_iff lam R p.1).mp p.2
    exact (optimum_le_worst (evaluation lam) Set.univ (fun n a => a = true ↔ n ∈ R)
      (fromPoint p.1) hc).trans_eq (fromPoint_worst_eq lam p.1)
  · change _ ≤ ⨅ p : {p : Procedure J k Bool //
        Correct (evaluation lam) Set.univ (fun n a => a = true ↔ n ∈ R) p}, _
    apply le_iInf
    intro p
    let candidate : {p : QueryProcedure (J × k) // CorrectQueryProcedure (compatible R) p} :=
      ⟨toPoint p.1, (toPoint_correct_iff lam R p.1).mp p.2⟩
    have hle := iInf_le (fun p : {p : QueryProcedure (J × k) //
      CorrectQueryProcedure (compatible R) p} => worstQueries (G := Multiplicative V) p.1) candidate
    exact hle.trans_eq (toPoint_worst_eq lam p.1)

/-- B's identical optima equal the minimum sufficient original-index set, including infinite cost. -/
theorem optimum_eq_minimum [DecidableEq J] (R : Submodule k V) :
    optimum (evaluation lam) Set.univ (fun n a => a = true ↔ n ∈ R) =
      minimum lam (0 : V →ₗ[k] k) R := by
  classical
  letI := action lam
  rw [optimum_eq lam R, optimalQueries_eq_minObservations, minimum_eq lam R]

end AAT.AG.RepairObservationDuality.PointQuerySimulation
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.PointQuerySimulation
