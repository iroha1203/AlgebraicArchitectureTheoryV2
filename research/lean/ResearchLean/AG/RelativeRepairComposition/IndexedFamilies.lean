import ResearchLean.AG.RelativeRepairComposition.RelativeFamilies

/-!
# Original relative families on an indexed cover

## Implementation notes

G-130 B retains every original cell value in every local family. Compatibility
means equality at each shared original cell. A covering index chosen for that cell
constructs the global value, and compatibility proves independence of the choice.
This general, noncomputable construction applies to finite covers; it supplies no
finite elimination algorithm or computable section for G-130 C.
-/

namespace AAT.AG.RelativeRepairComposition
namespace Family
universe uI uJ uL uA
variable {I : Type uI} {J : Type uJ} {L : Type uL}
variable (A : I → Type uA) [∀ i, AddCommGroup (A i)]
variable (s : J → Set I) (p : Set I)

/-- All local relative families agreeing at each common original cell. -/
def indexedCompatible : AddSubgroup (∀ j, relative A (s j) p) where
  carrier := {b | ∀ j k i (hj : i ∈ s j) (hk : i ∈ s k), (b j).1 ⟨i,hj⟩ = (b k).1 ⟨i,hk⟩}
  zero_mem' := by
    change ∀ j k i (hj : i ∈ s j) (hk : i ∈ s k), (0 : A i) = 0
    intros; rfl
  add_mem' := by
    intro b c hb hc
    change ∀ j k i (hj : i ∈ s j) (hk : i ∈ s k),
      (b j).1 ⟨i,hj⟩ + (c j).1 ⟨i,hj⟩ = (b k).1 ⟨i,hk⟩ + (c k).1 ⟨i,hk⟩
    intro j k i hj hk
    rw [hb j k i hj hk, hc j k i hj hk]
  neg_mem' := by
    intro b hb
    change ∀ j k i (hj : i ∈ s j) (hk : i ∈ s k),
      -(b j).1 ⟨i,hj⟩ = -(b k).1 ⟨i,hk⟩
    intro j k i hj hk
    rw [hb j k i hj hk]

/-- Compatibility is equality of the full original value on every overlap. -/
theorem mem_indexedCompatible (b : ∀ j, relative A (s j) p) :
    b ∈ indexedCompatible A s p ↔
      ∀ j k i (hj : i ∈ s j) (hk : i ∈ s k), (b j).1 ⟨i,hj⟩ = (b k).1 ⟨i,hk⟩ := Iff.rfl

/-- The complete original family restricts to all regions with their full values. -/
def indexedRestriction : relative A Set.univ p →+ indexedCompatible A s p where
  toFun b := ⟨fun j => relativeRestrict A p (Set.subset_univ (s j)) b, by
    change ∀ j k i (hj : i ∈ s j) (hk : i ∈ s k),
      b.1 ⟨i,Set.mem_univ i⟩ = b.1 ⟨i,Set.mem_univ i⟩
    intros; rfl⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Every local value of the restriction is the same original global value. -/
theorem indexed_restriction_val (b : relative A Set.univ p) (j : J) (i : s j) :
    ((indexedRestriction A s p b).1 j).1 i = b.1 ⟨i.1,Set.mem_univ i.1⟩ := rfl

/-- Choose an included region from the original-cell cover condition. -/
noncomputable def coveringIndex (hc : ∀ i, ∃ j, i ∈ s j) (i : I) : J :=
  Classical.choose (hc i)

/-- The covering index contains the very same original cell. -/
theorem covering_index_mem (hc : ∀ i, ∃ j, i ∈ s j) (i : I) :
    i ∈ s (coveringIndex s hc i) := Classical.choose_spec (hc i)

/-- Generate a global relative family from all compatible local values. -/
noncomputable def indexedGlue (hc : ∀ i, ∃ j, i ∈ s j) :
    indexedCompatible A s p →+ relative A Set.univ p where
  toFun b := ⟨fun i => (b.1 (coveringIndex s hc i.1)).1 ⟨i.1,covering_index_mem s hc i.1⟩,
    fun i hi => (b.1 (coveringIndex s hc i.1)).2 _ hi⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Global restoration agrees with every local value, independently of the chosen index. -/
theorem indexed_glue_on (hc : ∀ i, ∃ j, i ∈ s j)
    (b : indexedCompatible A s p) (j : J) (i : I) (hi : i ∈ s j) :
    (indexedGlue A s p hc b).1 ⟨i,Set.mem_univ i⟩ = (b.1 j).1 ⟨i,hi⟩ :=
  b.2 (coveringIndex s hc i) j i (covering_index_mem s hc i) hi

/-- Restoring a full original family after all restrictions returns the whole family. -/
theorem indexed_glue_restriction (hc : ∀ i, ∃ j, i ∈ s j)
    (b : relative A Set.univ p) :
    indexedGlue A s p hc (indexedRestriction A s p b) = b := rfl

/-- Restricting the restored global family returns all compatible local values. -/
theorem indexed_restriction_glue (hc : ∀ i, ∃ j, i ∈ s j)
    (b : indexedCompatible A s p) :
    indexedRestriction A s p (indexedGlue A s p hc b) = b := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  funext i
  exact indexed_glue_on A s p hc b j i.1 i.2

/-- A cover detects equality of every full global relative family. -/
theorem indexed_restriction_injective (hc : ∀ i, ∃ j, i ∈ s j) :
    Function.Injective (indexedRestriction A s p) := by
  intro b c h
  have hh := congrArg (indexedGlue A s p hc) h
  simpa only [indexed_glue_restriction] using hh

/-- All original relative families are additively equivalent to all compatible local families. -/
noncomputable def indexedEquiv (hc : ∀ i, ∃ j, i ∈ s j) :
    relative A Set.univ p ≃+ indexedCompatible A s p where
  toFun := indexedRestriction A s p
  invFun := indexedGlue A s p hc
  left_inv := indexed_glue_restriction A s p hc
  right_inv := indexed_restriction_glue A s p hc
  map_add' := (indexedRestriction A s p).map_add

variable {s} (t : L → Set I) (α : L → J) (hα : ∀ l, t l ⊆ s (α l))

/-- Refine all local values by the specified inclusion of original cell sets. -/
def indexedRefinement : indexedCompatible A s p →+ indexedCompatible A t p where
  toFun b := ⟨fun l => relativeRestrict A p (hα l) (b.1 (α l)), by
    intro j k i hj hk
    exact b.2 (α j) (α k) i (hα j hj) (hα k hk)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Refinement keeps the complete original value in each included region. -/
theorem indexed_refinement_val (b : indexedCompatible A s p) (l : L) (i : t l) :
    ((indexedRefinement A p t α hα b).1 l).1 i = (b.1 (α l)).1 ⟨i.1,hα l i.2⟩ := rfl

/-- All global restrictions commute with original-cell refinement. -/
theorem indexed_refinement_restriction (b : relative A Set.univ p) :
    indexedRefinement A p t α hα (indexedRestriction A s p b) =
      indexedRestriction A t p b := rfl

/-- Both covers restore the same global family after refinement. -/
theorem indexed_glue_refinement (hs : ∀ i, ∃ j, i ∈ s j) (ht : ∀ i, ∃ l, i ∈ t l)
    (b : indexedCompatible A s p) :
    indexedGlue A t p ht (indexedRefinement A p t α hα b) = indexedGlue A s p hs b := by
  apply indexed_restriction_injective A t p ht
  rw [indexed_restriction_glue, ← indexed_refinement_restriction A p t α hα,
    indexed_restriction_glue]

end Family
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
