import ResearchLean.AG.RelativeRepairComposition.W1ActualRepairs
import ResearchLean.AG.RepairObservationDuality.PrimitiveInputQueries

/-!
# G-131 E: the original W1 physical inputs and primitive evaluations

## Implementation notes

The input consists of two arbitrary elements of the whole native affine
projection kernel. The whole-kernel theorem, rather than a restriction of
operations to selected translations, identifies each with its value at zero.
Those actual operations are precisely W1's original fixed rx and ry. Every
parameter is realized before any repair or correctness requirement.
-/
namespace AAT.AG.RepairObservationDuality.W1PhysicalInputs
open RelativeRepairComposition NativeAffine W1AffineInput
set_option autoImplicit false

/-- All pairs of original full-kernel physical rx/ry operations. -/
abbrev Inputs := Bool → (projection (k := ZMod 3) (A := ZMod 3)).ker

/-- The two full physical input coordinates, with false denoting rx. -/
abbrev Values := Bool → ZMod 3

/-- Parameters are the actual physical operations evaluated at zero. -/
def values (X : Inputs) : Values := fun j => (X j).1 0

/-- Every pair of parameters is realized by full native physical operations. -/
def realize (v : Values) : Inputs := fun j => translationKernel (Multiplicative.ofAdd (v j))

/-- Realization retains both input parameters exactly. -/
theorem values_realize (v : Values) : values (realize v) = v := by
  funext j
  exact add_zero (v j)

/-- No full native physical input lies outside this realization. -/
theorem realize_values (X : Inputs) : realize (values X) = X := by
  funext j
  apply Subtype.ext
  exact ((projection_eq_one_iff (X j).1).mp (X j).2).symm

/-- The original six-edge W1 tower uses precisely the observed physical values. -/
noncomputable def tower (X : Inputs) := originalTower true (values X false) (values X true)

/-- The actual rx anchor of the original W1 is the original full physical input operation. -/
theorem reference_rx (X : Inputs) : reference true (values X false) (values X true)
    (i := ()) (j := ()) edgeRx = (X false).1 := by
  rw [(projection_eq_one_iff (X false).1).mp (X false).2]
  simp [geometry, reference, values, edgeA, edgeRx]

/-- The actual ry anchor of the original W1 is the original full physical input operation. -/
theorem reference_ry (X : Inputs) : reference true (values X false) (values X true)
    (i := ()) (j := ()) edgeRy = (X true).1 := by
  rw [(projection_eq_one_iff (X true).1).mp (X true).2]
  simp [geometry, reference, values, edgeA, edgeRx, edgeRy]

/-- The primitive evaluations are projections of the same two-coordinate space. -/
def primitive (j : Bool) : Values →ₗ[ZMod 3] ZMod 3 := LinearMap.proj j

/-- An exact primitive query evaluates one actual original operation at zero. -/
def evaluate (X : Inputs) (j : Bool) : ZMod 3 := (X j).1 0

/-- All actual evaluations, rather than only realized ones, agree with their primitive linear forms. -/
theorem evaluate_values (X : Inputs) (j : Bool) : evaluate X j = primitive j (values X) := rfl

/-- Querying the original W1 fixed rx/ry operations returns the same two primitive values. -/
theorem original_evaluation (X : Inputs) :
    reference true (values X false) (values X true) (i := ()) (j := ()) edgeRx 0 = evaluate X false ∧
    reference true (values X false) (values X true) (i := ()) (j := ()) edgeRy 0 = evaluate X true := by
  rw [reference_rx, reference_ry]
  exact ⟨rfl, rfl⟩

/-- Every history-only controller has exactly the same primitive response trace on the physical inputs. -/
theorem run_iff {A : Type*} (next : PrimitiveQueries.Procedure Bool (ZMod 3) A)
    (X : Inputs) (hist : PrimitiveQueries.History Bool (ZMod 3)) (a : A) (qs : List Bool) :
    PrimitiveQueries.Run evaluate next X hist a qs ↔
      PrimitiveQueries.Run (fun v j => primitive j v) next (values X) hist a qs :=
  PrimitiveInputQueries.run_iff values evaluate (fun v j => primitive j v) evaluate_values next X hist a qs

end AAT.AG.RepairObservationDuality.W1PhysicalInputs
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1PhysicalInputs
