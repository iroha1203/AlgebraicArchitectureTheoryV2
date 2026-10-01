import ResearchLean.AG.RelativeRepairComposition.C16AffinePinRegression
import ResearchLean.AG.RelativeRepairComposition.AffineContextFamilies

/-! # Nonzero full affine pin input used by the general actual contextual theorem -/
namespace AAT.AG.RelativeRepairComposition.C16AffineContextRegression
open TransportCoherence AbelianLiftingObstruction NativeAffine
open C14AffineRegression (V x y)
open C16AffinePinRegression

/-- The true original loop is allowed; the false loop remains a forbidden candidate without anchoring vertices. -/
def allowed : Set (EdgeName (K := geometry)) := {e | e.2.2 = true}

/-- The whole original candidate range has exactly the old false-loop restriction. -/
theorem fixed_condition : fixedEdgesForRange (ClosedRegion.empty (K := geometry)).edges Set.univ allowed =
    fixed := by
  ext ⟨i,j,e⟩
  cases e <;> simp [fixedEdgesForRange,ClosedRegion.empty,allowed,fixed]

/-- A genuine shared actual repair supplies all pin operations to the primitive whole context input. -/
def baseRepair : Repair geometry references comparisons
    (fixedEdgesForRange (ClosedRegion.empty (K := geometry)).edges Set.univ allowed) where
  operation := sharedRepair.operation
  linear := sharedRepair.linear
  face := sharedRepair.face
  fixed_value e he := sharedRepair.fixed_value e (by rw [fixed_condition] at he; exact he)

/-- The fixed original face law is generated from the empty physical fixed face set. -/
theorem fixed_law : ∀ f ∈ (ClosedRegion.empty (K := geometry)).faces,
    translation (k := ZMod 3) (comparisons f) * GroupExtension.pathValue geometry references (geometry.twoLeft f) =
      GroupExtension.pathValue geometry references (geometry.twoRight f) := fun _ h => h.elim

/-- The concrete nonzero tester is an actual lawful full input accepted by the general environment type. -/
noncomputable def input := ParallelPins.contextInput geometry originals references comparisons
  ClosedRegion.empty Set.univ aligned original_three fixed_law allowed baseRepair

/-- Compatible whole permissions keep every new pin uniformly forbidden. -/
noncomputable def permissions : input.Range allowed :=
  ParallelPins.contextRange geometry originals references comparisons
    ClosedRegion.empty Set.univ aligned original_three fixed_law allowed baseRepair

/-- The full concrete environment has a genuine actual repaired object. -/
noncomputable def actualRepair : input.Repairs permissions :=
  ParallelPins.contextRepair geometry originals references comparisons
    ClosedRegion.empty Set.univ aligned original_three fixed_law allowed baseRepair

/-- Every actual whole environment object has the nonzero original shared value x. -/
theorem actual_true (s : input.Repairs permissions) : input.boundary permissions s ⟨(),(),true⟩ = x := by
  have h := ParallelPins.context_shared_repair geometry originals references comparisons
    ClosedRegion.empty Set.univ aligned original_three fixed_law allowed baseRepair s
  change input.sharedRepair permissions s = baseRepair at h
  change realCorrection geometry references comparisons _ (input.sharedRepair permissions s) _ = x
  rw [h]
  exact true_correction

/-- The same actual whole input cannot realize the zero shared family. -/
theorem actual_zero_failure : ¬ ∃ s : input.Repairs permissions, input.boundary permissions s = 0 := by
  rintro ⟨s,h⟩
  have ht := actual_true s
  rw [h] at ht
  have hv := congrArg (fun v : V => v 0) ht
  norm_num [x] at hv

/-- Exact actual permitted labels are the full original zero-coboundary vectors. -/
theorem actual_label_conditions (b : geometry.Vertex → V) :
    b ∈ gaugeLabels input.geometry input.references input.fixed.vertices
      (fixedEdgesForRange input.fixed.edges input.candidates permissions.allowed) ↔
        b ∈ gaugeLabels geometry references ∅ Set.univ := by
  have hf := ParallelPins.context_fixed_set geometry originals references comparisons
    ClosedRegion.empty Set.univ aligned original_three fixed_law allowed baseRepair
  change fixedEdgesForRange input.fixed.edges input.candidates permissions.allowed =
    ParallelPins.forbidden geometry (fixedEdgesForRange ClosedRegion.empty.edges Set.univ allowed) at hf
  rw [hf]
  exact ParallelPins.pin_label_conditions geometry references _ ∅ _ b

/-- A nonzero full original vector survives as an actual compatible whole environment label. -/
noncomputable def actualLabel : gaugeLabels input.geometry input.references input.fixed.vertices
    (fixedEdgesForRange input.fixed.edges input.candidates permissions.allowed) :=
  ⟨fun _ => x,(actual_label_conditions _).mpr whole_label_x⟩

/-- The actual context label retains its nonzero first coordinate. -/
theorem actual_label_nonzero : actualLabel ≠ 0 := by
  intro h
  have hv := congrArg (fun b => b.1 () 0) h
  norm_num [actualLabel,x] at hv

/-- The retained full vector labels an actual whole stabilizer arrow on both old and pin operations. -/
noncomputable def actualArrow : Arrow input.geometry input.references input.comparisons input.fixed.vertices
    (fixedEdgesForRange input.fixed.edges input.candidates permissions.allowed) actualRepair actualRepair := by
  refine ⟨actualLabel, ?_⟩
  intro i j e
  cases e with
  | inl e =>
    exact (ParallelPins.whole_label_stabilizes geometry references
      (fixedEdgesForRange ClosedRegion.empty.edges Set.univ allowed) ∅ comparisons
      ⟨fun _ => x,whole_label_x⟩ baseRepair e).symm
  | inr e =>
    exact (ParallelPins.whole_label_stabilizes geometry references
      (fixedEdgesForRange ClosedRegion.empty.edges Set.univ allowed) ∅ comparisons
      ⟨fun _ => x,whole_label_x⟩ baseRepair e).symm

/-- The genuine whole stabilizer arrow has a nonzero label rather than a quotient effect. -/
theorem actual_arrow_nonzero : actualArrow.1 ≠ 0 := actual_label_nonzero

/-- The nonzero context lies in the quantifier over all actual whole external environments. -/
noncomputable def environment : AffineContextInput.Environments (W := geometry) (LW := originals)
    (RW := references) (cW := comparisons) (PW := ClosedRegion.empty) (CW := Set.univ) allowed :=
  ⟨input,permissions⟩

/-- The general original-operation contextual equivalence applies to this full nonzero three-cell input. -/
theorem actual_contextual :
    (∀ env : AffineContextInput.Environments (W := geometry) (LW := originals)
      (RW := references) (cW := comparisons) (PW := ClosedRegion.empty) (CW := Set.univ) allowed,
      Nonempty (AffineContextInput.StrictRepairs input env.1 permissions env.2) ↔
        Nonempty (AffineContextInput.StrictRepairs input env.1 permissions env.2)) ↔
          Set.range (input.boundary permissions) = Set.range (input.boundary permissions) :=
  input.contextual_strict_actual permissions input permissions

end AAT.AG.RelativeRepairComposition.C16AffineContextRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C16AffineContextRegression
