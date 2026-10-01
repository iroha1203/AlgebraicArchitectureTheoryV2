import ResearchLean.AG.RelativeRepairComposition.AffineFamilyLabels
import ResearchLean.AG.RelativeRepairComposition.AffineFamilyFiniteInput
import ResearchLean.AG.RelativeRepairComposition.AffineFamilyRelativeDefect
import ResearchLean.AG.RelativeRepairComposition.C14AffineRegression

/-!
# Nonzero primitive parameters change actual affine feasibility

## Implementation notes

The full F3² shear and distinct arbitrary original operations are retained. The
parameter translates every original edge and only the false reference loop. Its
actual defect is the parameter vector itself. Fixing both references succeeds
at zero and fails at a nonzero vector; allowing the true candidate gives an
actual repair for every vector using the same original linear transport.
-/
namespace AAT.AG.RelativeRepairComposition.C15AffineFamilyRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine
open C14AffineRegression

/-- Every original input operation receives the full original parameter vector. -/
def originalTranslations : V →ₗ[ZMod 3] (EdgeName (K := K) → V) := LinearMap.pi fun _ => LinearMap.id

/-- Only the original false reference receives the full original parameter vector. -/
def referenceTranslations : V →ₗ[ZMod 3] (EdgeName (K := K) → V) where
  toFun v e := if e.2.2 = false then v else 0
  map_add' v w := by funext e; cases he : e.2.2 <;> simp [he]
  map_smul' t v := by funext e; cases he : e.2.2 <;> simp [he]

/-- The fixed primitive comparison is the original second standard translation. -/
def baseComparison : K.TwoCell → V := fun _ => y

/-- Every parameter retains the actual arbitrary original affine operations. -/
def input (v : V) : ∀ {i j : K.Vertex}, K.Edge i j → Operations (ZMod 3) V :=
  familyOriginal K original originalTranslations v

/-- Every parameter realizes actual reference operations before any repair is selected. -/
def refs (v : V) : ∀ {i j : K.Vertex}, K.Edge i j → Operations (ZMod 3) V :=
  familyReference K reference referenceTranslations v

/-- The realized false reference is its original shear preceded by the full parameter translation. -/
theorem reference_false (v : V) : refs v (i := ()) (j := ()) false = translation (k := ZMod 3) v * shear.toAffineEquiv := rfl

/-- The realized true reference stays the same actual second-coordinate translation and original shear. -/
theorem reference_true (v : V) : refs v (i := ()) (j := ()) true = reference (i := ()) (j := ()) true := by
  change translation (k := ZMod 3) (0 : V) * reference (i := ()) (j := ()) true = _
  rw [translation_zero, one_mul]

/-- The original actual input value changes by the same full parameter translation without changing its linear part. -/
theorem original_false_parameter (v : V) : input v (i := ()) (j := ()) false 0 = v + (![2,1] : V) := by
  change v + original (i := ()) (j := ()) false 0 = _
  rw [original_false_value]

/-- The primitive base face is exactly coherent before any parameter is substituted. -/
theorem base_coherent :
    translation (k := ZMod 3) (baseComparison ()) * GroupExtension.pathValue K reference (K.twoLeft ()) =
      GroupExtension.pathValue K reference (K.twoRight ()) := by
  change translation (k := ZMod 3) y * (1 * shear.toAffineEquiv) =
    1 * (translation (k := ZMod 3) y * shear.toAffineEquiv)
  rw [one_mul, one_mul]

/-- The independent actual base defect is zero by the primitive full face equality. -/
theorem base_defect_zero : realDefectVector K reference baseComparison () = 0 :=
  (face_coherent_iff_defect_zero K reference baseComparison () (aligned ())).mp base_coherent

/-- The original complete face words generate the parameter vector itself as the linear defect term. -/
theorem generated_parameter_value (v : V) :
    familyDefectLinear K reference referenceTranslations (0 : V →ₗ[ZMod 3] (K.TwoCell → V)) v () = v := by
  change 0 + (vectorPath K reference (referenceTranslations v) (K.twoLeft ()) -
    vectorPath K reference (referenceTranslations v) (K.twoRight ())) = v
  change 0 + (v + 0 - (0 + 0)) = v
  simp only [add_zero, zero_add, sub_zero]

/-- Actual affine composition, through the general primitive-family API, produces the full parameter as defect. -/
theorem actual_parameter_defect (v : V) : realDefectVector K (refs v) baseComparison () = v := by
  have h := family_defect_affine K reference baseComparison referenceTranslations
    (0 : V →ₗ[ZMod 3] (K.TwoCell → V)) aligned v ()
  simpa only [familyComparisons, LinearMap.zero_apply, add_zero, base_defect_zero,
    generated_parameter_value, zero_add] using h

/-- Every parameter uses the same entire original degree-one matrix. -/
theorem matrix_reused (v : V) : edgeMatrix 2 K (refs v) = edgeMatrix 2 K reference :=
  family_edge_matrix 2 K reference referenceTranslations v

/-- Fixing every original actual reference is possible exactly at the zero parameter. -/
theorem all_fixed_iff (v : V) : Nonempty (Repair K (refs v) baseComparison Set.univ) ↔ v = 0 := by
  constructor
  · rintro ⟨s⟩
    have h := s.face ()
    have hl := s.fixed_value (⟨(),(),false⟩ : EdgeName (K := K)) (Set.mem_univ _)
    have hr := s.fixed_value (⟨(),(),true⟩ : EdgeName (K := K)) (Set.mem_univ _)
    change translation (k := ZMod 3) (baseComparison ()) * (1 * s.operation (i := ()) (j := ()) false) =
      1 * s.operation (i := ()) (j := ()) true at h
    rw [hl,hr] at h
    have hd := (face_coherent_iff_defect_zero K (refs v) baseComparison ()
      (family_aligned K reference referenceTranslations aligned v ())).mp h
    rw [actual_parameter_defect] at hd
    exact hd
  · intro hv
    subst v
    refine ⟨⟨refs 0,fun _ => rfl,?_,fun _ _ => rfl⟩⟩
    intro f
    cases f
    have h := (face_coherent_iff_defect_zero K (refs 0) baseComparison ()
      (family_aligned K reference referenceTranslations aligned 0 ())).mpr
        ((actual_parameter_defect 0).trans rfl)
    exact h

/-- A nonzero actual parameter fails when both original references are physically fixed. -/
theorem nonzero_all_fixed_failure : ¬ Nonempty (Repair K (refs x) baseComparison Set.univ) := by
  intro h
  have hv := (all_fixed_iff x).mp h
  have h0 := congrArg (fun a : V => a 0) hv
  norm_num [x] at h0

/-- A genuine actual repair retains the false reference and repairs the original true candidate at every parameter. -/
def allowedRepair (v : V) : Repair K (refs v) baseComparison C13RangeInput.fixed.edges where
  operation e := if (e : Bool) = false then refs v e
    else translation (k := ZMod 3) y * refs v (i := ()) (j := ()) false
  linear e := by
    cases e
    · rfl
    · rw [reference_true]
      change projection (translation (k := ZMod 3) y * (translation (k := ZMod 3) v * shear.toAffineEquiv)) =
        projection (translation (k := ZMod 3) y * shear.toAffineEquiv)
      rw [map_mul, map_mul, map_mul, projection_translation, projection_translation]
      simp only [one_mul]
  face _ := by
    change translation (k := ZMod 3) y * (1 * refs v (i := ()) (j := ()) false) =
      1 * (translation (k := ZMod 3) y * refs v (i := ()) (j := ()) false)
    rw [one_mul, one_mul]
  fixed_value e he := by
    change e.2.2 = false at he
    simp only [he, ↓reduceIte]

/-- The same nonzero actual parameter succeeds when the original true candidate is allowed. -/
theorem nonzero_allowed_success : Nonempty (Repair K (refs x) baseComparison C13RangeInput.fixed.edges) :=
  ⟨allowedRepair x⟩

/-- The positive independent real repair is a whole native supported repair of the generated parameter tower. -/
theorem positive_native (v : V) : Nonempty (SupportedRepair
    (familyTower K original reference baseComparison originalTranslations referenceTranslations
      (0 : V →ₗ[ZMod 3] (K.TwoCell → V)) aligned v) C13RangeInput.fixed.edges) := by
  simp only [familyTower, familyComparisons, LinearMap.zero_apply, add_zero]
  refine ⟨(repairEquivalence K (input v) (refs v) baseComparison
    (family_aligned K reference referenceTranslations aligned v) C13RangeInput.fixed.edges).symm (allowedRepair v)⟩

/-- Every parameter retains the same entire independent real-label subgroup on the original fixed loop. -/
theorem full_gauge_labels_reused (v : V) :
    gaugeLabels K (refs v) ∅ C13RangeInput.fixed.edges = gaugeLabels K reference ∅ C13RangeInput.fixed.edges :=
  translated_gauge_labels K reference (referenceTranslations v) ∅ C13RangeInput.fixed.edges

/-- The nonzero first original coordinate stays an allowed full label for every primitive value. -/
theorem gauge_x_allowed_every_value (v : V) :
    (fun _ : K.Vertex => x) ∈ gaugeLabels K (refs v) ∅ C13RangeInput.fixed.edges := by
  rw [full_gauge_labels_reused]
  exact C14AffineRegression.gauge_label_x_allowed

/-- The nonzero second original coordinate remains forbidden by the actual shear for every primitive value. -/
theorem gauge_y_forbidden_every_value (v : V) :
    (fun _ : K.Vertex => y) ∉ gaugeLabels K (refs v) ∅ C13RangeInput.fixed.edges := by
  rw [full_gauge_labels_reused]
  exact C14AffineRegression.gauge_label_y_forbidden

end AAT.AG.RelativeRepairComposition.C15AffineFamilyRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C15AffineFamilyRegression
