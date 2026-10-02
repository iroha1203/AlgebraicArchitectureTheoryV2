import ResearchLean.AG.RelativeRepairComposition.RelativeFamilies

/-!
# Degreewise global coordinates for all relative local values

## Implementation notes

This identifies a relative family with its zero extension, degree by degree.
It asserts no compatibility of extension with differentials. Local subdivision
uses the full subgroup and proves each differential comparison separately.
-/
namespace AAT.AG.RelativeRepairComposition.Family
universe ui ua
variable {I : Type ui} (A : I → Type ua) [∀ i, AddCommGroup (A i)]

/-- Full global values supported on s and zero on the original fixed cells p. -/
def localized (s p : Set I) : AddSubgroup (∀ i, A i) where
  carrier := {b | ∀ i, i ∉ s ∨ i ∈ p → b i = 0}
  zero_mem' := by intro i hi; rfl
  add_mem' := by intro b c hb hc i hi; change b i + c i = 0; rw [hb i hi,hc i hi,add_zero]
  neg_mem' := by intro b hb i hi; change -(b i) = 0; rw [hb i hi,neg_zero]

/-- Localized membership keeps both original support and fixed conditions. -/
theorem mem_localized (s p : Set I) (b : ∀ i, A i) :
    b ∈ localized A s p ↔ ∀ i, i ∉ s ∨ i ∈ p → b i = 0 := Iff.rfl

/-- Read the zero value at any excluded or fixed original cell. -/
theorem localized_zero {s p : Set I} (b : localized A s p) (i : I)
    (hi : i ∉ s ∨ i ∈ p) : b.1 i = 0 := (mem_localized A s p b.1).mp b.2 i hi

/-- Degreewise extension is zero at every excluded original name. -/
theorem extend_off (s : Set I) (b : ∀ i : s, A i.1) (i : I) (hi : i ∉ s) :
    extend A s b i = 0 := by
  classical
  simp [extend,hi]

/-- Zero extension identifies every relative local family with the full localized subgroup. -/
noncomputable def localizedEquiv (s p : Set I) : relative A s p ≃+ localized A s p where
  toFun b := ⟨extend A s b.1,by
    intro i hi
    rcases hi with hs | hp
    · exact extend_off A s b.1 i hs
    · by_cases hs : i ∈ s
      · rw [extend_on A s b.1 i hs]; exact b.2 _ hp
      · exact extend_off A s b.1 i hs⟩
  invFun b := ⟨restrict A s b.1,fun i hi => b.2 i.1 (Or.inr hi)⟩
  left_inv b := Subtype.ext (restrict_extend A s b.1)
  right_inv b := by
    apply Subtype.ext
    funext i
    change extend A s (restrict A s b.1) i = b.1 i
    by_cases hs : i ∈ s
    · exact extend_on A s _ i hs
    · rw [extend_off A s _ i hs]; exact (b.2 i (Or.inl hs)).symm
  map_add' b c := Subtype.ext (map_add (extend A s) b.1 c.1)

/-- Every included original value is unchanged by the degreewise identification. -/
theorem localizedEquiv_on (s p : Set I) (b : relative A s p) (i : s) :
    (localizedEquiv A s p b).1 i.1 = b.1 i := extend_on A s b.1 i.1 i.2

/-- The inverse reads all original included values, with no coefficient quotient. -/
theorem localizedEquiv_inverse (s p : Set I) (b : localized A s p) (i : s) :
    ((localizedEquiv A s p).symm b).1 i = b.1 i.1 := rfl

end AAT.AG.RelativeRepairComposition.Family
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Family
