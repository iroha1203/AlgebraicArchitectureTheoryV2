import ResearchLean.AG.RelativeRepairComposition.FiniteCoordinateEnumerations
import Mathlib.Data.List.Pi

/-!
# Complete executable dependent coefficient-family enumeration

The list is generated from the original index list and each complete value list.
It includes the unique empty family and needs no choice of a missing coordinate.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration
universe ui uy
variable {I : Type ui} [DecidableEq I] {Y : I → Type uy}

/-- Enumerate every whole coefficient family using the given complete original lists. -/
def pi (enumI : FiniteElimination.Enumeration I)
    (enumY : ∀ i, FiniteElimination.Enumeration (Y i)) :
    FiniteElimination.Enumeration (∀ i, Y i) where
  values := (List.pi enumI.values (fun i => (enumY i).values)).map
    (fun f i => f i (enumI.complete i))
  complete y := by
    apply List.mem_map.mpr
    refine ⟨fun i _ => y i,?_,rfl⟩
    exact (List.mem_pi (fun i => (enumY i).values) (fun i _ => y i)).mpr
      (fun i _ => (enumY i).complete (y i))

end AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
