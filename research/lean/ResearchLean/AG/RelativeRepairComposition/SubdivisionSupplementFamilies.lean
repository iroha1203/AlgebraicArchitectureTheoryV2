import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalCorrections
import ResearchLean.AG.RelativeRepairComposition.SubdivisionPrivatePartition

/-!
# Every local fresh freedom and the full private owner's actual kernel

## Implementation notes

The local supplemental groups are defined by original incidence, independently
of this comparison. Nonowners have zero values because the chosen edge is
private; the owner's value ranges over the entire actual fresh kernel. Both
inverse maps retain all values before any action or orbit quotient is taken.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uI uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen) (U : I → ClosedRegion K)
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
local notation "Aw" => Additive (Kernel p q factor.middle)

/-- All independently defined local supplemental values, including every nonowner. -/
abbrev Family := ∀ j, localSupplement T chosen factor (U j)

include hi in
/-- Every nonowner supplemental value is forced to zero by original private incidence. -/
theorem nonowner_zero (r : Family T chosen factor U) (j : I) (hj : j ≠ owner) :
    (r j).1 = 0 :=
  localSupplement_zero T chosen factor (U j)
    (chosen_outside_other K chosen U P candidates owner j hi hj) (r j)

variable [DecidableEq I]

/-- Restore any full actual fresh value at its owner and the forced zeros elsewhere. -/
noncomputable def restore (r : Aw) : Family T chosen factor U := by
  classical
  intro j
  exact ⟨if j = owner then r else 0, by
    apply (mem_localSupplement T chosen factor (U j) _).mpr
    intro hn
    by_cases hj : j = owner
    · subst j
      exact False.elim (hn hi.1)
    · simp only [if_neg hj]⟩

/-- Restoration exposes every original local value without selecting a smaller owner kernel. -/
theorem restore_value (r : Aw) (j : I) :
    (restore T chosen factor U P candidates owner hi r j).1 =
      if j = owner then r else 0 := by
  classical
  rfl

/-- The owner's restored value is the arbitrary original actual fresh value. -/
theorem restore_owner (r : Aw) :
    (restore T chosen factor U P candidates owner hi r owner).1 = r := by
  rw [restore_value,if_pos rfl]

/-- Restoring the owner value preserves the entire independently supplied supplemental family. -/
theorem restore_read (r : Family T chosen factor U) :
    restore T chosen factor U P candidates owner hi (r owner).1 = r := by
  classical
  funext j
  apply Subtype.ext
  rw [restore_value]
  by_cases hj : j = owner
  · subst j
    exact if_pos rfl
  · rw [if_neg hj,nonowner_zero T chosen factor U P candidates owner hi r j hj]

/-- All local freedoms and the entire actual owner kernel have both additive inverse maps. -/
noncomputable def equivalence : Family T chosen factor U ≃+ Aw where
  toFun r := (r owner).1
  invFun := restore T chosen factor U P candidates owner hi
  left_inv := restore_read T chosen factor U P candidates owner hi
  right_inv := restore_owner T chosen factor U P candidates owner hi
  map_add' _ _ := rfl

/-- The complete family comparison reads precisely the owner's actual value. -/
theorem equivalence_value (r : Family T chosen factor U) :
    equivalence T chosen factor U P candidates owner hi r = (r owner).1 := rfl

/-- The inverse comparison restores all local values, rather than only their effects. -/
theorem equivalence_inverse_value (r : Aw) (j : I) :
    ((equivalence T chosen factor U P candidates owner hi).symm r j).1 =
      if j = owner then r else 0 := restore_value T chosen factor U P candidates owner hi r j

end AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.SupplementFamilies
