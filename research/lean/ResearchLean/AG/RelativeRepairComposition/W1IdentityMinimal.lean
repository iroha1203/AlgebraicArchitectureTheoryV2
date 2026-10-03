import ResearchLean.AG.RelativeRepairComposition.W1IdentityClassification
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeEquations

/-!
# The same identity-holonomy input has a unique minimal empty range

The complete original affine repair set is nonempty for every permission set.
The construction changes only the private a correction, retaining both authored
occurrences and all physical anchors and candidate masks.
-/
namespace AAT.AG.RelativeRepairComposition.W1IdentityMinimal
open TransportCoherence AbelianLiftingObstruction
open W1AffineInput W1Regions W1ActualRepairs W1PermissionClassification
open W1IdentityClassification

/-- Every original permission set admits the same full actual identity-linear repair. -/
theorem actual_exists (x y : ZMod 3) (S : Set (EdgeName (K := geometry))) :
    Nonempty (RealRepairs false x y S) := by
  apply (identityActualEquiv x y S).nonempty_congr.mpr
  exact ⟨⟨(2 * (y - x), 0), ⟨fun _ => rfl, fun _ => by rw [twice_twice, sub_self]⟩⟩⟩

/-- Empty permissions are uniquely minimal among all original permission sets, for every x,y. -/
theorem minimal_iff_empty (x y : ZMod 3) (S : Set (EdgeName (K := geometry))) :
    Minimal (fun V => Nonempty (RealRepairs false x y V)) S ↔ S = ∅ := by
  constructor
  · intro hm
    exact Set.eq_empty_iff_forall_notMem.mpr (fun e he => hm.2 (actual_exists x y ∅) (Set.empty_subset S) he)
  · rintro rfl
    exact ⟨actual_exists x y ∅, fun _ _ _ => Set.empty_subset _⟩

/-- The same full repair predicate on the actual original candidate subtype also has unique empty minimum. -/
theorem named_minimal_iff_empty (x y : ZMod 3) (S : Set candidates) :
    Minimal (fun V => Nonempty (RealRepairs false x y (OriginalRanges.allowed candidates V))) S ↔ S = ∅ := by
  constructor
  · intro hm
    exact Set.eq_empty_iff_forall_notMem.mpr
      (fun e he => hm.2 (actual_exists x y _) (Set.empty_subset S) he)
  · rintro rfl
    exact ⟨actual_exists x y _, fun _ _ _ => Set.empty_subset _⟩

end AAT.AG.RelativeRepairComposition.W1IdentityMinimal
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1IdentityMinimal
