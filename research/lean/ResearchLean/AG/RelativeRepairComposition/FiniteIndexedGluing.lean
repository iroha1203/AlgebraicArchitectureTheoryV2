import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.IndexedClosedCovers
import ResearchLean.AG.RelativeRepairComposition.FiniteElimination

/-!
# Finite assembly of complete original relative families

## Implementation notes

The covering region is found in the given complete finite list. The cover law
proves that this search succeeds; it supplies no selected region or repair.
Compatibility restores every original value independently of the list order.
The computed map agrees with the accepted general family gluing map.
-/
namespace AAT.AG.RelativeRepairComposition
namespace FiniteFamilyGlue
universe uI uJ uA
variable {I : Type uI} {J : Type uJ}
variable (s : J → Set I) [∀ j, DecidablePred (· ∈ s j)]
variable (enumJ : FiniteElimination.Enumeration J) (hc : ∀ i, ∃ j, i ∈ s j)

/-- Search the complete finite region list for a region containing this original cell. -/
def selector (i : I) : {j : J // i ∈ s j} := by
  let found := enumJ.values.find? (fun j => decide (i ∈ s j))
  have hf : found.isSome = true := by
    rw [List.find?_isSome]
    obtain ⟨j,hj⟩ := hc i
    exact ⟨j,enumJ.complete j,by simpa using hj⟩
  refine ⟨found.get hf,?_⟩
  have hs := List.find?_some (Option.some_get hf).symm
  simpa [found] using hs

/-- The finite search returns a region containing the same original cell. -/
theorem selector_mem (i : I) : i ∈ s (selector s enumJ hc i).1 :=
  (selector s enumJ hc i).2

variable (A : I → Type uA) [∀ i, AddCommGroup (A i)] (p : Set I)

/-- Restore all global original values by the computed covering-region search. -/
def glue : Family.indexedCompatible A s p →+ Family.relative A Set.univ p where
  toFun b := ⟨fun i => (b.1 (selector s enumJ hc i.1).1).1
    ⟨i.1,selector_mem s enumJ hc i.1⟩,
    fun i hi => (b.1 (selector s enumJ hc i.1).1).2 ⟨i.1,selector_mem s enumJ hc i.1⟩ hi⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The restored full value equals the value in each region containing that cell. -/
theorem glue_value (b : Family.indexedCompatible A s p) (j : J) (i : I) (hi : i ∈ s j) :
    (glue s enumJ hc A p b).1 ⟨i,Set.mem_univ i⟩ = (b.1 j).1 ⟨i,hi⟩ :=
  (Family.mem_indexedCompatible A s p b.1).mp b.2
    (selector s enumJ hc i).1 j i (selector_mem s enumJ hc i) hi

/-- Finite restoration after restriction returns all original global values. -/
theorem glue_restriction (b : Family.relative A Set.univ p) :
    glue s enumJ hc A p (Family.indexedRestriction A s p b) = b := rfl

/-- Restriction after finite restoration returns every compatible local value. -/
theorem restriction_glue (b : Family.indexedCompatible A s p) :
    Family.indexedRestriction A s p (glue s enumJ hc A p b) = b := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  funext i
  exact glue_value s enumJ hc A p b j i.1 i.2

/-- The finite algorithm is exactly the full original family equivalence. -/
def equivalence : Family.relative A Set.univ p ≃+ Family.indexedCompatible A s p where
  toFun := Family.indexedRestriction A s p
  invFun := glue s enumJ hc A p
  left_inv := glue_restriction s enumJ hc A p
  right_inv := restriction_glue s enumJ hc A p
  map_add' := (Family.indexedRestriction A s p).map_add

/-- Finite restoration agrees with general gluing on the full original family. -/
theorem glue_eq_general (b : Family.indexedCompatible A s p) :
    glue s enumJ hc A p b = Family.indexedGlue A s p hc b := by
  apply Subtype.ext
  funext i
  obtain ⟨j,hj⟩ := hc i.1
  exact (glue_value s enumJ hc A p b j i.1 hj).trans
    (Family.indexed_glue_on A s p hc b j i.1 hj).symm

/-- Changing the finite region list preserves every full restored value. -/
theorem glue_enum_independent (enumJ' : FiniteElimination.Enumeration J)
    (b : Family.indexedCompatible A s p) :
    glue s enumJ hc A p b = glue s enumJ' hc A p b := by
  rw [glue_eq_general,glue_eq_general]

end FiniteFamilyGlue
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
