import ResearchLean.AG.RelativeRepairComposition.RelativeComplex
/-!
# Relative dependent families and degreewise exactness over a cover.

## Implementation notes

Every family keeps its original index and full coefficient group. Fixed-cell
vanishing is preserved by restriction. Extension by zero is degreewise only;
no chain-map property is assumed for extension.
-/

namespace AAT.AG.RelativeRepairComposition
namespace Family
universe uI uA
variable {I : Type uI} (A : I → Type uA) [∀ i, AddCommGroup (A i)]

/-- Restrict original dependent values along an inclusion of cell sets. -/
def inclusionRestrict {s t : Set I} (hst : t ⊆ s) :
    (∀ i : s, A i.1) →+ (∀ i : t, A i.1) where
  toFun b i := b ⟨i.1,hst i.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Nested restrictions keep the same original value. -/
theorem inclusion_restrict_restrict {s t : Set I} (hst : t ⊆ s) (b : ∀ i, A i) :
    inclusionRestrict A hst (restrict A s b) = restrict A t b := rfl

/-- Restricting an included family is its original zero extension restricted back. -/
theorem inclusion_restrict_extend {s t : Set I} (hst : t ⊆ s) (b : ∀ i : s, A i.1) :
    inclusionRestrict A hst b = restrict A t (extend A s b) := by
  funext i
  exact (extend_on A s b i.1 (hst i.2)).symm

/-- Families on original cells in s which vanish on the same fixed cells p. -/
def relative (s p : Set I) : AddSubgroup (∀ i : s, A i.1) where
  carrier := {b | ∀ i : s, i.1 ∈ p → b i = 0}
  zero_mem' := by intro i hi; rfl
  add_mem' := by intro b c hb hc i hi; change b i + c i = 0; rw [hb i hi,hc i hi,add_zero]
  neg_mem' := by intro b hb i hi; change -(b i) = 0; rw [hb i hi,neg_zero]

/-- Membership states vanishing at each fixed original cell. -/
theorem mem_relative (s p : Set I) (b : ∀ i : s, A i.1) :
    b ∈ relative A s p ↔ ∀ i : s, i.1 ∈ p → b i = 0 := Iff.rfl

/-- A relative family is inhabited by the zero value at every original cell. -/
theorem zero_mem_relative (s p : Set I) : (0 : ∀ i : s, A i.1) ∈ relative A s p :=
  (relative A s p).zero_mem

/-- A nonzero value at an included fixed cell gives an explicit family failing the relative condition. -/
theorem not_relative_single (s p : Set I) (i : I) (hi : i ∈ s) (hp : i ∈ p)
    (a : A i) (ha : a ≠ 0) :
    ∃ b : ∀ j : s, A j.1, b ∉ relative A s p := by
  classical
  refine ⟨Pi.single ⟨i,hi⟩ a,?_⟩
  intro hb
  exact ha (by simpa only [Pi.single_eq_same] using hb ⟨i,hi⟩ hp)

/-- The complete original family is the kernel of restriction to the same fixed cells. -/
def univRelativeEquiv (p : Set I) : relative A Set.univ p ≃+ (restrict A p).ker where
  toFun b := ⟨fun i => b.1 ⟨i,Set.mem_univ i⟩,by
    funext i
    exact b.2 ⟨i.1,Set.mem_univ i.1⟩ i.2⟩
  invFun b := ⟨fun i => b.1 i.1,fun i hi => congrFun b.2 ⟨i.1,hi⟩⟩
  left_inv b := by apply Subtype.ext; funext i; rfl
  right_inv b := by apply Subtype.ext; funext i; rfl
  map_add' _ _ := rfl

/-- Reindexing the complete family retains each original value. -/
theorem univ_relative_equiv_val (p : Set I) (b : relative A Set.univ p) (i : I) :
    (univRelativeEquiv A p b).1 i = b.1 ⟨i,Set.mem_univ i⟩ := rfl

/-- The inverse reindexing is exactly restriction to all original cells. -/
theorem univ_relative_equiv_symm_val (p : Set I) (b : (restrict A p).ker) :
    ((univRelativeEquiv A p).symm b).1 = restrict A Set.univ b.1 := rfl

/-- Restriction to all original cells retains all values injectively. -/
theorem restrict_univ_injective : Function.Injective (restrict A Set.univ) := by
  intro b c h
  funext i
  exact congrFun h ⟨i,Set.mem_univ i⟩

/-- Relative restriction along inclusion of original cells. -/
def relativeRestrict {s t : Set I} (p : Set I) (hst : t ⊆ s) :
    relative A s p →+ relative A t p where
  toFun b := ⟨fun i => b.1 ⟨i.1,hst i.2⟩,fun _ hi => b.2 _ hi⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The restricted family has exactly the original value. -/
theorem relative_restrict_val {s t : Set I} (p : Set I) (hst : t ⊆ s)
    (b : relative A s p) (i : t) :
    (relativeRestrict A p hst b).1 i = b.1 ⟨i.1,hst i.2⟩ := rfl

/-- The underlying relative restriction is the same raw inclusion restriction. -/
theorem relative_restrict_eq_inclusion {s t : Set I} (p : Set I) (hst : t ⊆ s)
    (b : relative A s p) :
    (relativeRestrict A p hst b).1 = inclusionRestrict A hst b.1 := rfl

/-- Degreewise extension by zero respects the fixed cells. -/
noncomputable def relativeExtend (s t p : Set I) :
    relative A t p →+ relative A s p := by
  classical
  exact {
    toFun := fun b => ⟨fun i => if hi : i.1 ∈ t then b.1 ⟨i.1,hi⟩ else 0, by
      intro i hi; dsimp only; split
      · exact b.2 _ hi
      · rfl⟩
    map_zero' := by apply Subtype.ext; funext i; dsimp only; by_cases hi : i.1 ∈ t <;> simp [hi]
    map_add' := by intro b c; apply Subtype.ext; funext i; dsimp only; by_cases hi : i.1 ∈ t <;> simp [hi] }

/-- Extension agrees with every included original value. -/
theorem relative_extend_on (s t p : Set I)
    (b : relative A t p) (i : s) (hi : i.1 ∈ t) :
    (relativeExtend A s t p b).1 i = b.1 ⟨i.1,hi⟩ := by
  classical
  simp [relativeExtend,hi]

/-- The cover restriction keeps both local original families. -/
def coverDiagonal (s t p : Set I) :
    relative A Set.univ p →+ relative A s p × relative A t p :=
  (relativeRestrict A p (Set.subset_univ s)).prod
    (relativeRestrict A p (Set.subset_univ t))

/-- The overlap difference is the first local value minus the second, as in the fixed cover sequence. -/
def coverDifference (s t p : Set I) :
    relative A s p × relative A t p →+ relative A (s ∩ t) p :=
  ((relativeRestrict A p Set.inter_subset_left).comp (AddMonoidHom.fst _ _)) -
    ((relativeRestrict A p Set.inter_subset_right).comp (AddMonoidHom.snd _ _))

/-- Evaluate the diagonal on both original restrictions. -/
theorem cover_diagonal_val (s t p : Set I) (b : relative A Set.univ p) :
    coverDiagonal A s t p b =
      (relativeRestrict A p (Set.subset_univ s) b,
       relativeRestrict A p (Set.subset_univ t) b) := rfl

/-- Evaluate the overlap difference on its original cell. -/
theorem cover_difference_val (s t p : Set I)
    (b : relative A s p × relative A t p) (i : ↥(s ∩ t)) :
    (coverDifference A s t p b).1 i = b.1.1 ⟨i.1,i.2.1⟩ - b.2.1 ⟨i.1,i.2.2⟩ := rfl

/-- Local restrictions of a global family have zero difference. -/
theorem cover_difference_diagonal (s t p : Set I) (b : relative A Set.univ p) :
    coverDifference A s t p (coverDiagonal A s t p b) = 0 := by
  apply Subtype.ext; funext i
  exact sub_self _

/-- A cover determines every original value and makes its diagonal injective. -/
theorem cover_diagonal_injective (s t p : Set I) (hc : s ∪ t = Set.univ) :
    Function.Injective (coverDiagonal A s t p) := by
  intro b c h
  apply Subtype.ext; funext i
  have hi : i.1 ∈ s ∪ t := by rw [hc]; trivial
  rcases hi with hs | ht
  · exact congrArg (fun q => q.1.1 ⟨i.1,hs⟩) h
  · exact congrArg (fun q => q.2.1 ⟨i.1,ht⟩) h

/-- Any overlap family is a difference of local relative families. -/
theorem cover_difference_surjective (s t p : Set I) :
    Function.Surjective (coverDifference A s t p) := by
  intro b
  refine ⟨(relativeExtend A s (s ∩ t) p b,0),?_⟩
  apply Subtype.ext; funext i
  rw [cover_difference_val,relative_extend_on A s (s ∩ t) p _ _ i.2]
  exact sub_zero _

/-- Equal overlap restrictions glue to one relative original family on a cover. -/
theorem cover_glue (s t p : Set I) (hc : s ∪ t = Set.univ)
    (b : relative A s p × relative A t p)
    (hb : coverDifference A s t p b = 0) :
    ∃ c, coverDiagonal A s t p c = b := by
  classical
  have covered (i : I) : i ∈ s ∨ i ∈ t := by
    have : i ∈ s ∪ t := by rw [hc]; trivial
    exact this
  let c : relative A Set.univ p := ⟨fun i => if hs : i.1 ∈ s then b.1.1 ⟨i.1,hs⟩
      else b.2.1 ⟨i.1,(covered i.1).resolve_left hs⟩, by
    intro i hi; dsimp only; split
    · exact b.1.2 _ hi
    · exact b.2.2 _ hi⟩
  refine ⟨c,?_⟩
  apply Prod.ext
  · apply Subtype.ext; funext i
    change (if hs : i.1 ∈ s then b.1.1 ⟨i.1,hs⟩ else _) = b.1.1 i
    simp [i.2]
  · apply Subtype.ext; funext i
    change (if hs : i.1 ∈ s then b.1.1 ⟨i.1,hs⟩ else _) = b.2.1 i
    split
    · rename_i hs
      have hz := congrArg (fun q => q.1 ⟨i.1,hs,i.2⟩) hb
      change b.1.1 ⟨i.1,hs⟩ - b.2.1 i = 0 at hz
      exact sub_eq_zero.mp hz
    · rfl

/-- The kernel of the overlap difference is exactly the global restriction image. -/
theorem cover_exact (s t p : Set I) (hc : s ∪ t = Set.univ) :
    Function.Exact (coverDiagonal A s t p) (coverDifference A s t p) := by
  intro b
  constructor
  · exact cover_glue A s t p hc b
  · rintro ⟨c,rfl⟩
    exact cover_difference_diagonal A s t p c
end Family
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
