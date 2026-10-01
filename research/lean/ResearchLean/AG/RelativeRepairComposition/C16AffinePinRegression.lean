import ResearchLean.AG.RelativeRepairComposition.AffinePinLabels
import ResearchLean.AG.RelativeRepairComposition.AffinePinCandidates
import ResearchLean.AG.RelativeRepairComposition.C15AffineFamilyRegression

/-!
# Actual nonzero pins, retained labels and a nonempty original three-cell

The shared input keeps the full F3² shear. Its authored three-cell compares the
empty route with the original forward-then-backward face route. Both original
face occurrences and all bookends survive the pin construction. This is a
regression of E's tester, not a substitute for the prescribed W1–W5 inputs.
-/
namespace AAT.AG.RelativeRepairComposition.C16AffinePinRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine
open C14AffineRegression C15AffineFamilyRegression

/-- The original forward face appears between the two concrete loop words. -/
def forwardFace : WhiskeredFace K.toFiniteTransportTwoPresentation () () :=
  ⟨(), .nil (), .nil (), .forward⟩

/-- The original backward face returns between exactly the same two loop words. -/
def backwardFace : WhiskeredFace K.toFiniteTransportTwoPresentation () () :=
  ⟨(), .nil (), .nil (), .backward⟩

/-- Nonempty original three-cell with two complete typed routes through the original face. -/
def geometry : FiniteTransportPresentation where
  toFiniteTransportTwoPresentation := K.toFiniteTransportTwoPresentation
  ThreeCell := Unit
  threeCellFintype := inferInstance
  threeSource _ := ()
  threeTarget _ := ()
  threeStart _ := forwardFace.before
  threeFinish _ := forwardFace.before
  threeLeft _ := .nil forwardFace.before
  threeRight _ := .cons forwardFace.asStep (.cons backwardFace.asStep (.nil forwardFace.before))

/-- Actual nonzero-parameter references retain the original shear and two vector coordinates. -/
def references : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Operations (ZMod 3) V := refs x

/-- Actual independent arbitrary original operations are retained on the shared geometry. -/
def originals : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Operations (ZMod 3) V := input x

/-- The original authored comparison remains the nonzero second-coordinate translation. -/
def comparisons : geometry.TwoCell → V := baseComparison

/-- The same physically fixed false loop is the original fixed range. -/
def fixed : Set (EdgeName (K := geometry)) := {e | e.2.2 = false}

/-- The genuine shared repair satisfies its original full operations and face before pins are generated. -/
def sharedRepair : Repair geometry references comparisons fixed where
  operation := (allowedRepair x).operation
  linear := (allowedRepair x).linear
  face := (allowedRepair x).face
  fixed_value := (allowedRepair x).fixed_value

/-- The complete original three-cell evaluates the inverse comparison followed by its comparison. -/
theorem original_three : ∀ f : geometry.ThreeCell,
    pastingOperation geometry references comparisons (geometry.threeLeft f) =
      pastingOperation geometry references comparisons (geometry.threeRight f) := by
  intro _
  change (1 : Operations (ZMod 3) V) =
    (1 * (1 * (translation (k := ZMod 3) y)⁻¹ * 1⁻¹)) *
      (1 * translation (k := ZMod 3) y * 1⁻¹)
  simp only [one_mul, inv_one, mul_one, inv_mul_cancel]

/-- Every original real linear face condition follows from the retained native affine family. -/
theorem aligned : ∀ f : geometry.TwoCell,
    (GroupExtension.pathValue geometry references (geometry.twoLeft f)).linear =
      (GroupExtension.pathValue geometry references (geometry.twoRight f)).linear :=
  family_aligned K C14AffineRegression.reference referenceTranslations C14AffineRegression.aligned x

/-- The old false shared correction is exactly zero at the physically fixed edge. -/
theorem false_correction : realCorrection geometry references comparisons fixed sharedRepair ⟨(),(),false⟩ = 0 := by
  change (refs x (i := ()) (j := ()) false * (refs x (i := ()) (j := ()) false)⁻¹) 0 = 0
  rw [mul_inv_cancel]
  rfl

/-- The old true shared operation has the nonzero first-coordinate correction. -/
theorem true_repaired_value : sharedRepair.operation (i := ()) (j := ()) true =
    translation (k := ZMod 3) x * references (i := ()) (j := ()) true := by
  change translation (k := ZMod 3) y * (translation (k := ZMod 3) x * shear.toAffineEquiv) =
    translation (k := ZMod 3) x * refs x (i := ()) (j := ()) true
  rw [reference_true]
  change translation (k := ZMod 3) y * (translation (k := ZMod 3) x * shear.toAffineEquiv) =
    translation (k := ZMod 3) x * (translation (k := ZMod 3) y * shear.toAffineEquiv)
  rw [← mul_assoc, translation_mul, add_comm y x, ← mul_assoc, translation_mul]

/-- The same full actual correction evaluates to x on the original true edge. -/
theorem true_correction : realCorrection geometry references comparisons fixed sharedRepair ⟨(),(),true⟩ = x := by
  unfold realCorrection
  rw [true_repaired_value, mul_assoc, mul_inv_cancel, mul_one]
  simp

/-- The actual forbidden-pin environment has a genuine repair at the nonzero shared value. -/
def testRepair := ParallelPins.singletonRepair geometry references comparisons fixed sharedRepair

/-- Copied complete original three-cell law holds in the actual pin environment. -/
theorem test_three : ∀ f : (ParallelPinGeometry.presentation geometry).ThreeCell,
    pastingOperation (ParallelPinGeometry.presentation geometry)
      (ParallelPins.reference geometry references (realCorrection geometry references comparisons fixed sharedRepair))
      (ParallelPins.comparison geometry comparisons)
      ((ParallelPinGeometry.presentation geometry).threeLeft f) =
    pastingOperation (ParallelPinGeometry.presentation geometry)
      (ParallelPins.reference geometry references (realCorrection geometry references comparisons fixed sharedRepair))
      (ParallelPins.comparison geometry comparisons)
      ((ParallelPinGeometry.presentation geometry).threeRight f) :=
  ParallelPins.reference_three_law geometry references _ comparisons original_three

/-- Every actual environment repair has the same nonzero true shared correction. -/
theorem every_test_true
    (s : Repair (ParallelPinGeometry.presentation geometry)
      (ParallelPins.reference geometry references (realCorrection geometry references comparisons fixed sharedRepair))
      (ParallelPins.comparison geometry comparisons) (ParallelPins.forbidden geometry fixed)) :
    realCorrection geometry references comparisons fixed
      (ParallelPins.restrictRepair geometry references comparisons fixed _ s) ⟨(),(),true⟩ = x := by
  have h := congrFun (ParallelPins.singleton_correction geometry references comparisons fixed _ s)
    (⟨(),(),true⟩ : EdgeName (K := geometry))
  exact h.trans true_correction

/-- The zero boundary value cannot be realized by the same nonzero actual test environment. -/
theorem zero_boundary_failure : ¬ ∃ s : Repair (ParallelPinGeometry.presentation geometry)
      (ParallelPins.reference geometry references (realCorrection geometry references comparisons fixed sharedRepair))
      (ParallelPins.comparison geometry comparisons) (ParallelPins.forbidden geometry fixed),
    realCorrection geometry references comparisons fixed
      (ParallelPins.restrictRepair geometry references comparisons fixed _ s) = 0 := by
  rintro ⟨s,hs⟩
  have h := every_test_true s
  rw [hs] at h
  have hv := congrArg (fun a : V => a 0) h
  norm_num [x] at hv

/-- The original nonzero first-coordinate label preserves every full shared reference edge. -/
theorem whole_label_x : (fun _ : geometry.Vertex => x) ∈
    gaugeLabels geometry references ∅ Set.univ := by
  refine ⟨by intro v hv; exact hv.elim, ?_⟩
  rintro ⟨i,j,b⟩ _
  have hlin : (references (i := i) (j := j) b).linear = shear := by
    cases b
    · change projection (translation (k := ZMod 3) x * shear.toAffineEquiv) = shear
      rw [map_mul, projection_translation, one_mul]
      rfl
    · change projection (translation (k := ZMod 3) (0 : V) *
        (translation (k := ZMod 3) y * shear.toAffineEquiv)) = shear
      rw [map_mul, map_mul, projection_translation, projection_translation, one_mul, one_mul]
      rfl
  change x = (references b).linear x
  rw [hlin]
  ext a
  fin_cases a <;> norm_num [shear,x]

/-- The original full nonzero label survives the actual singleton environment unchanged. -/
def nonzeroTestLabel : gaugeLabels (ParallelPinGeometry.presentation geometry)
    (ParallelPins.reference geometry references (realCorrection geometry references comparisons fixed sharedRepair))
    ∅ (ParallelPins.forbidden geometry fixed) :=
  ⟨fun _ => x, (ParallelPins.pin_label_conditions geometry references fixed ∅ _ _).mpr whole_label_x⟩

/-- This full permitted environment label is nonzero as a label, including its ineffective directions. -/
theorem test_label_not_zero : nonzeroTestLabel ≠ 0 := by
  intro h
  have hv := congrArg (fun b => b.1 () 0) h
  norm_num [nonzeroTestLabel,x] at hv

/-- A forbidden shear label remains forbidden after adding pins and identity-comparison faces. -/
theorem test_label_y_forbidden : (fun _ : geometry.Vertex => y) ∉
    gaugeLabels (ParallelPinGeometry.presentation geometry)
      (ParallelPins.reference geometry references (realCorrection geometry references comparisons fixed sharedRepair))
      ∅ (ParallelPins.forbidden geometry fixed) := by
  intro hb
  have h := (ParallelPins.pin_label_conditions geometry references fixed ∅ _ _).mp hb
  apply gauge_y_forbidden_every_value x
  exact ⟨h.1, fun e _ => h.2 e trivial⟩

/-- The same original label gives a real stabilizer arrow at the shared repair. -/
def nonzeroSharedArrow : Arrow geometry references comparisons ∅ fixed sharedRepair sharedRepair :=
  ParallelPins.wholeLabelArrow geometry references fixed ∅ comparisons ⟨fun _ => x,whole_label_x⟩ sharedRepair

/-- The real stabilizer arrow retains the nonzero original first-coordinate vector. -/
theorem shared_arrow_not_zero : nonzeroSharedArrow.1 ≠ 0 := by
  intro h
  have hv := congrArg (fun b => b.1 () 0) h
  norm_num [nonzeroSharedArrow,ParallelPins.wholeLabelArrow,x] at hv

end AAT.AG.RelativeRepairComposition.C16AffinePinRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C16AffinePinRegression
