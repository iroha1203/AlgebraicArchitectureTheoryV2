import ResearchLean.AG.RelativeRepairComposition.W1CandidateColumns
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeClassification

/-!
# W1 all-range dual criterion and original minimal repair ranges

## Implementation notes

All selected sets use the actual original candidate subtype with both named
full columns. The actual-repair/range equivalence is the accepted general
original theorem on this same native tower and actual defect. Since each full
column is surjective, every nonzero-obstruction dual support is both names.
Zero obstruction and nonzero obstruction therefore give different minimal sets.
-/
namespace AAT.AG.RelativeRepairComposition.W1DualMinimalRanges
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1ActualRepairs W1FiniteCoefficients
open W1RelativeCoefficients W1OriginalObstruction W1CandidateColumns
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable (x y : ZMod 3)
local notation "T" => originalTower true x y
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)
local notation "B" => OriginalRanges.column (k := ZMod 3) (M) fixedRegion candidates
  candidates_outside (original_linear true x y)

/-- Every member of the unchanged original candidate subtype is b or c, with no renaming by its column image. -/
theorem candidate_cases (e : candidates) : e = candidateB ∨ e = candidateC := by
  rcases e with ⟨e, he⟩
  rcases he with he | he <;> subst e
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every original named full candidate column covers the whole original obstruction quotient. -/
theorem column_surjective (e : candidates) : Function.Surjective ((B) e) := by
  rcases candidate_cases e with he | he <;> subst e
  · exact b_column_surjective x y
  · exact c_column_surjective x y

/-- Any nonempty set of original candidate names generates the entire original obstruction quotient. -/
theorem nonempty_range_top (S : Set candidates) (hs : S.Nonempty) : NamedDual.ranges (B) S = ⊤ := by
  obtain ⟨e, he⟩ := hs
  apply top_unique
  intro o ho
  obtain ⟨a, rfl⟩ := column_surjective x y e o
  exact NamedDual.range_le (B) S e he ⟨a, rfl⟩

/-- The empty selected range remains exactly zero in the full original quotient. -/
theorem empty_range_zero : NamedDual.ranges (B) ∅ = ⊥ := by
  simp [NamedDual.ranges]

/-- The same actual original obstruction belongs to a selected range precisely at d=0 or a nonempty selection. -/
theorem range_contains_iff (S : Set candidates) :
    obstruction x y ∈ NamedDual.ranges (B) S ↔ y - x = 0 ∨ S.Nonempty := by
  constructor
  · intro hm
    by_cases hs : S.Nonempty
    · exact Or.inr hs
    · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
      rw [he, empty_range_zero, Submodule.mem_bot] at hm
      exact Or.inl ((obstruction_eq_zero_iff x y).mp hm)
  · rintro (hd | hs)
    · rw [(obstruction_eq_zero_iff x y).mpr hd]
      exact Submodule.zero_mem _
    · rw [nonempty_range_top x y S hs]
      exact Submodule.mem_top

/-- The independent native original repairs use the same physical anchors and forbidden original candidate names as the general range theorem. -/
theorem native_range_iff (S : Set candidates) :
    Nonempty (SupportedRepair (T) (fixedEdges (OriginalRanges.allowed candidates S))) ↔
      obstruction x y ∈ NamedDual.ranges (B) S :=
  OriginalRangeClassification.repair_nonempty_iff_range (k := ZMod 3) (T) fixedRegion candidates
    candidates_outside (original_linear true x y) (fixed_faces true x y) S

/-- Every independent full original affine repair obeys the same exact all-selected-range criterion. -/
theorem actual_range_iff (S : Set candidates) :
    Nonempty (RealRepairs true x y (OriginalRanges.allowed candidates S)) ↔
      obstruction x y ∈ NamedDual.ranges (B) S :=
  (NativeAffine.repairEquivalence geometry (reference true x y) (reference true x y)
    comparison (linear_faces true x y) (fixedEdges (OriginalRanges.allowed candidates S))).nonempty_congr.symm.trans
      (native_range_iff x y S)

/-- The original all-S dual-transversal theorem applies to the same full actual affine repair sets and actual obstruction. -/
theorem actual_dual_iff (S : Set candidates) :
    Nonempty (RealRepairs true x y (OriginalRanges.allowed candidates S)) ↔
      NamedDual.Hits (B) (obstruction x y) S :=
  (actual_range_iff x y S).trans (NamedDual.mem_ranges_iff_hits (B) (obstruction x y) S)

/-- The same full actual original repair predicate and dual-transversal predicate have exactly the same inclusion-minimal ranges. -/
theorem minimal_actual_iff_dual (S : Set candidates) :
    Minimal (fun V => Nonempty (RealRepairs true x y (OriginalRanges.allowed candidates V))) S ↔
      Minimal (NamedDual.Hits (B) (obstruction x y)) S := by
  simp only [Minimal, actual_dual_iff]

/-- A concrete original quotient dual reads the derived whole obstruction coordinate. -/
noncomputable def dualCoordinate : Module.Dual (ZMod 3)
    (OriginalRanges.ObstructionSpace (k := ZMod 3) (M) fixedRegion candidates (original_linear true x y)) :=
  (obstructionCoordinate x y).toLinearMap

/-- The actual finite dual evaluation is y-x, on the same original q(-delta). -/
theorem dualCoordinate_obstruction : dualCoordinate x y (obstruction x y) = y - x :=
  obstruction_coordinate x y

/-- Every dual nonzero on the actual obstruction has the full two-name support; original candidate names are not merged. -/
theorem nonzero_dual_support
    (phi : Module.Dual (ZMod 3)
      (OriginalRanges.ObstructionSpace (k := ZMod 3) (M) fixedRegion candidates (original_linear true x y)))
    (hp : phi (obstruction x y) ≠ 0) : NamedDual.support (B) phi = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e hzero
  obtain ⟨a, ha⟩ := column_surjective x y e (obstruction x y)
  have hv := LinearMap.congr_fun hzero a
  change phi ((B) e a) = 0 at hv
  exact hp (ha ▸ hv)

/-- Nonzero d gives a concrete empty-range failure dual whose full named support contains both original candidates. -/
theorem empty_failure_dual (hd : y - x ≠ 0) :
    dualCoordinate x y (obstruction x y) ≠ 0 ∧ NamedDual.support (B) (dualCoordinate x y) = Set.univ := by
  have hp : dualCoordinate x y (obstruction x y) ≠ 0 := by rw [dualCoordinate_obstruction]; exact hd
  exact ⟨hp, nonzero_dual_support x y _ hp⟩

/-- Original actual feasibility and original full quotient membership have exactly the same inclusion-minimal sets. -/
theorem minimal_actual_iff_range (S : Set candidates) :
    Minimal (fun V => Nonempty (RealRepairs true x y (OriginalRanges.allowed candidates V))) S ↔
      Minimal (fun V => obstruction x y ∈ NamedDual.ranges (B) V) S := by
  simp only [Minimal, actual_range_iff]

/-- At zero actual obstruction, the empty set is the unique minimal range for independent original full affine repairs. -/
theorem minimal_zero_iff (hd : y - x = 0) (S : Set candidates) :
    Minimal (fun V => Nonempty (RealRepairs true x y (OriginalRanges.allowed candidates V))) S ↔ S = ∅ := by
  rw [minimal_actual_iff_range, (obstruction_eq_zero_iff x y).mpr hd]
  exact NamedDual.minimal_zero_iff (B) S

/-- Minimal nonempty sets consist of a single actual member; this supports the original two-candidate classification. -/
theorem minimal_nonempty_iff_singleton (S : Set candidates) :
    Minimal Set.Nonempty S ↔ ∃ e : candidates, S = {e} := by
  constructor
  · intro hm
    obtain ⟨e, he⟩ := hm.1
    exact ⟨e, Set.Subset.antisymm (hm.2 ⟨e, rfl⟩ (Set.singleton_subset_iff.mpr he))
      (Set.singleton_subset_iff.mpr he)⟩
  · rintro ⟨e, rfl⟩
    refine ⟨⟨e, rfl⟩, ?_⟩
    intro V hv hs
    obtain ⟨v, hvm⟩ := hv
    have he : v = e := hs hvm
    exact Set.singleton_subset_iff.mpr (he ▸ hvm)

/-- At nonzero d, exactly the two distinct original singleton candidate sets are minimal actual repair ranges. -/
theorem minimal_nonzero_iff (hd : y - x ≠ 0) (S : Set candidates) :
    Minimal (fun V => Nonempty (RealRepairs true x y (OriginalRanges.allowed candidates V))) S ↔
      S = {candidateB} ∨ S = {candidateC} := by
  rw [minimal_actual_iff_range]
  simp only [Minimal, range_contains_iff, hd, false_or]
  change Minimal Set.Nonempty S ↔ _
  rw [minimal_nonempty_iff_singleton]
  constructor
  · rintro ⟨e, he⟩
    rcases candidate_cases e with hb | hc
    · exact Or.inl (he.trans (congrArg (fun e : candidates => ({e} : Set candidates)) hb))
    · exact Or.inr (he.trans (congrArg (fun e : candidates => ({e} : Set candidates)) hc))
  · rintro (hb | hc)
    · exact ⟨candidateB, hb⟩
    · exact ⟨candidateC, hc⟩

end AAT.AG.RelativeRepairComposition.W1DualMinimalRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1DualMinimalRanges
