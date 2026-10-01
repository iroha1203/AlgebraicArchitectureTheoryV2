import ResearchLean.AG.RelativeRepairComposition.NamedDualRanges
import Mathlib.LinearAlgebra.Pi

/-!
# Selected full column sums with the same original names

The selected domain is the product of all full coefficient spaces at allowed
names. Its range is the independently defined sum of those column ranges.
-/
namespace AAT.AG.RelativeRepairComposition.NamedDual
attribute [local instance] Classical.propDecidable
universe uk ue uy uo
variable {k : Type uk} [Field k] {E : Type ue} [Fintype E]
variable {Y : E → Type uy} [∀ e, AddCommGroup (Y e)] [∀ e, Module k (Y e)]
variable {O : Type uo} [AddCommGroup O] [Module k O]
variable (B : ∀ e, Y e →ₗ[k] O)

/-- Sum the full columns at exactly the selected original names. -/
noncomputable def sumSelected (S : Set E) : (∀ e : S, Y e.1) →ₗ[k] O := by
  classical
  exact LinearMap.lsum k (fun e : S => Y e.1) k (fun e => B e.1)

/-- The selected map uses the literal sum of the original full columns. -/
theorem sumSelected_apply (S : Set E) (y : ∀ e : S, Y e.1) :
    sumSelected B S y = ∑ e : S, B e.1 (y e) := by
  classical
  simp only [sumSelected,LinearMap.lsum_apply,LinearMap.sum_apply,
    LinearMap.comp_apply,LinearMap.proj_apply]

/-- A single selected input restores the same named full column. -/
theorem sumSelected_single (S : Set E) (e : S) (y : Y e.1) :
    sumSelected B S (by classical exact Pi.single e y) = B e.1 y := by
  classical
  exact LinearMap.lsum_piSingle k (fun e : S => Y e.1) k (fun e => B e.1) e y

/-- The finite full-column sum has exactly the independently defined selected range. -/
theorem range_sumSelected (S : Set E) :
    LinearMap.range (sumSelected B S) = ranges B S := by
  classical
  apply le_antisymm
  · rintro _ ⟨y,rfl⟩
    rw [sumSelected_apply]
    exact Submodule.sum_mem _ (fun e _ => range_le B S e.1 e.2 ⟨y e,rfl⟩)
  · apply iSup_le
    intro e
    apply iSup_le
    intro he z hz
    rcases hz with ⟨y,rfl⟩
    exact ⟨Pi.single ⟨e,he⟩ y,sumSelected_single B S ⟨e,he⟩ y⟩

/-- All selected full inputs, rather than a single preimage, express feasibility. -/
theorem mem_ranges_iff_sum (S : Set E) (o : O) :
    o ∈ ranges B S ↔ ∃ y : ∀ e : S, Y e.1, sumSelected B S y = o := by
  rw [← range_sumSelected B S]
  rfl

/-- Extend selected values by literal zero at every unselected original name. -/
noncomputable def extendSelected (S : Set E) : (∀ e : S, Y e.1) →ₗ[k] (∀ e, Y e) where
  toFun y e := if he : e ∈ S then y ⟨e,he⟩ else 0
  map_add' y z := by funext e; by_cases he : e ∈ S <;> simp [he]
  map_smul' t y := by funext e; by_cases he : e ∈ S <;> simp [he]

omit [Fintype E] in
/-- Selected extension reads the same original coefficient value. -/
theorem extend_value (S : Set E) (y : ∀ e : S, Y e.1) (e : S) :
    extendSelected (k := k) S y e.1 = y e := dif_pos e.2

omit [Fintype E] in
/-- Every unselected original coefficient value is exactly zero. -/
theorem extend_zero (S : Set E) (y : ∀ e : S, Y e.1) (e : E) (he : e ∉ S) :
    extendSelected (k := k) S y e = 0 := dif_neg he

omit [Fintype E] in
/-- A selected single value extends to the same full original single value. -/
theorem extend_single (S : Set E) (e : S) (y : Y e.1) :
    extendSelected (k := k) S (Pi.single e y) = Pi.single e.1 y := by
  classical
  funext j
  by_cases hj : j = e.1
  · subst j
    simp [extendSelected,e.2]
  · by_cases hs : j ∈ S
    · have hne : (⟨j,hs⟩ : S) ≠ e := fun h => hj (congrArg Subtype.val h)
      simp [extendSelected,hs,hj,hne]
    · simp [extendSelected,hs,hj]

omit [Fintype E] in
/-- Extending all supported original values and reading them back retains the whole family. -/
theorem extend_read (S : Set E) (y : ∀ e, Y e) (hy : ∀ e ∉ S, y e = 0) :
    extendSelected (k := k) S (fun e => y e.1) = y := by
  funext e
  by_cases he : e ∈ S
  · exact dif_pos he
  · exact (dif_neg he).trans (hy e he).symm

/-- The selected sum is the same full column map after zero extension. -/
theorem sum_extend (S : Set E) :
    (LinearMap.lsum k Y k B).comp (extendSelected (k := k) S) = sumSelected B S := by
  classical
  apply LinearMap.pi_ext
  intro e y
  simp only [LinearMap.comp_apply,extend_single,LinearMap.lsum_piSingle,sumSelected_single]

/-- Linear output maps act on every same named column sum. -/
theorem map_sumSelected {V : Type*} [AddCommGroup V] [Module k V]
    (f : O →ₗ[k] V) (S : Set E) (y : ∀ e : S, Y e.1) :
    f (sumSelected B S y) = sumSelected (fun e => f.comp (B e)) S y := by
  classical
  simp only [sumSelected_apply,map_sum,LinearMap.comp_apply]

end AAT.AG.RelativeRepairComposition.NamedDual
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
