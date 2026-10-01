import ResearchLean.AG.RelativeRepairComposition.FiniteDualWitness
import Mathlib.Data.ZMod.Basic

/-! # Nonzero finite failed-row and full-column tests, including empty candidates -/
namespace AAT.AG.RelativeRepairComposition.C13FiniteDualRegression
open FiniteElimination
/-- The field with two elements used for finite row and column tests. -/
abbrev k := ZMod 2

/-- The complete finite field input list contains both elements. -/
def fieldValues : Enumeration k := ⟨[0,1],by decide⟩
/-- The face coordinate list contains the original single coordinate. -/
def faceValues : Enumeration Unit := ⟨[()],by intro x; cases x; simp⟩
/-- There are no always coordinates in this concrete nonzero obstruction. -/
def D : (Empty → k) →ₗ[k] (Unit → k) := 0
/-- The false candidate is full identity; the true candidate has the entire zero column. -/
def C (e : Bool) : (Unit → k) →ₗ[k] (Unit → k) :=
  if e = false then LinearMap.id else 0
/-- The original face rhs is nonzero. -/
def rhs : Unit → k := fun _ => 1
/-- Only the zero-column candidate is allowed in this failed input. -/
def forbidden : Set Bool := {e | e = true}
/-- Decide the named zero-column selection predicate by the original Boolean index. -/
instance forbiddenDecidable : DecidablePred (· ∈ forbidden) := fun e => inferInstanceAs (Decidable (e = true))

/-- The explicit nonzero row directly passes every full allowed-column and rhs test. -/
theorem valid_nonzero : FiniteDual.Valid D C rhs forbidden (fun _ => 1) := by decide
/-- The zero row cannot exclude the same nonzero rhs. -/
theorem invalid_zero : ¬ FiniteDual.Valid D C rhs forbidden (fun _ => 0) := by decide
/-- Allowing the full identity column rejects every putative failed row. -/
theorem no_failure_all : ∀ w : Unit → k, ¬ FiniteDual.Valid D C rhs Set.univ w := by decide
/-- The complete finite search returns the nonzero excluding row on the failed range. -/
theorem find_failed : FiniteDual.find D C rhs forbidden fieldValues faceValues = some (fun _ => 1) := by decide
/-- The same fixed row list returns none when the successful identity candidate is allowed. -/
theorem find_success : FiniteDual.find D C rhs Set.univ fieldValues faceValues = none := by decide
/-- A zero rhs admits no excluding dual row for the same candidate range. -/
theorem find_zero_rhs : FiniteDual.find D C 0 forbidden fieldValues faceValues = none := by decide

/-- An empty named candidate family uses its whole original empty input. -/
def noCandidates (e : Empty) : (Unit → k) →ₗ[k] (Unit → k) := Empty.elim e
/-- The unchanged nonzero rhs is excluded even with every member of the empty candidate family allowed. -/
theorem find_empty_candidates :
    FiniteDual.find D noCandidates rhs Set.univ fieldValues faceValues = some (fun _ => 1) := by decide
/-- The checked returned dual evaluates the same nonzero quotient rhs. -/
theorem dual_nonzero :
    FiniteDual.quotientDual D C rhs forbidden (fun _ => 1) valid_nonzero
      (LinearInterface.q D rhs) ≠ 0 :=
  (FiniteDual.quotientDual_spec D C rhs forbidden (fun _ => 1) valid_nonzero).1
/-- The same returned dual kills the whole allowed original zero column. -/
theorem dual_allowed_zero :
    (FiniteDual.quotientDual D C rhs forbidden (fun _ => 1) valid_nonzero).comp
      (CokernelNamed.column D C true) = 0 :=
  (FiniteDual.quotientDual_spec D C rhs forbidden (fun _ => 1) valid_nonzero).2 true rfl

/-- At the zero obstruction every selected sum is feasible, and empty is uniquely minimal. -/
theorem zero_minimal_iff (S : Set Bool) :
    Minimal (fun V => (0 : (Unit → k) ⧸ LinearMap.range D) ∈
      NamedDual.ranges (CokernelNamed.column D C) V) S ↔ S = ∅ :=
  NamedDual.minimal_zero_iff (CokernelNamed.column D C) S

/-- The empty-family computed row descends to a nonzero original quotient dual. -/
def emptyDual : Module.Dual k ((Unit → k) ⧸ LinearMap.range D) :=
  FiniteDual.quotientDual D noCandidates rhs Set.univ (fun _ => 1) (by decide)

/-- All names in the empty-family dual support are absent, while the same obstruction is nonzero. -/
theorem empty_dual_support :
    emptyDual (LinearInterface.q D rhs) ≠ 0 ∧
      NamedDual.support (CokernelNamed.column D noCandidates) emptyDual = ∅ := by
  constructor
  · exact (FiniteDual.quotientDual_spec D noCandidates rhs Set.univ (fun _ => 1) (by decide)).1
  · ext e; exact Empty.elim e

/-- The original empty support excludes every transversal for the unchanged nonzero rhs. -/
theorem empty_no_transversal (S : Set Empty) :
    ¬ NamedDual.Hits (CokernelNamed.column D noCandidates) (LinearInterface.q D rhs) S :=
  NamedDual.no_transversal_of_empty_support (CokernelNamed.column D noCandidates)
    (LinearInterface.q D rhs) emptyDual empty_dual_support.1 empty_dual_support.2 S

end AAT.AG.RelativeRepairComposition.C13FiniteDualRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C13FiniteDualRegression
