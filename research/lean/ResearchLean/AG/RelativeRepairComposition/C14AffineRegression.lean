import ResearchLean.AG.RelativeRepairComposition.NativeAffineRestriction
import ResearchLean.AG.RelativeRepairComposition.NativeAffineFiniteInput
import ResearchLean.AG.RelativeRepairComposition.NativeAffineRanges
import ResearchLean.AG.RelativeRepairComposition.C13RangeInput
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Original F3² affine inputs with nonidentity linear transport and actual positive and negative repairs -/
namespace AAT.AG.RelativeRepairComposition.C14AffineRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine

/-- The full real translation vector space has both standard F3 coordinates. -/
abbrev V := Fin 2 → ZMod 3
/-- The original two loops and full authored face retain their accepted names. -/
abbrev K := C13RangeInput.geometry
/-- Original full edge-name equality is the concrete equality on Unit endpoints and Bool loop names. -/
instance edgeNameEquality : DecidableEq (EdgeName (K := K)) :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, Σ _ : Unit, Bool))
/-- The first original standard translation vector. -/
def x : V := ![1, 0]
/-- The second original standard translation vector. -/
def y : V := ![0, 1]

/-- A nonidentity real linear shear with its full explicit inverse. -/
def shear : V ≃ₗ[ZMod 3] V where
  toFun v := ![v 0 + v 1, v 1]
  invFun v := ![v 0 - v 1, v 1]
  left_inv v := by ext j; fin_cases j <;> simp
  right_inv v := by ext j; fin_cases j <;> simp
  map_add' v w := by ext j; fin_cases j <;> simp [add_comm, add_left_comm, add_assoc]
  map_smul' a v := by ext j; fin_cases j <;> simp [mul_add]

/-- The actual reference operations share the shear but have different terminal translations. -/
def reference : ∀ {i j : K.Vertex}, K.Edge i j → Operations (ZMod 3) V :=
  fun e => if (e : Bool) = true then translation (k := ZMod 3) y * shear.toAffineEquiv
    else shear.toAffineEquiv

/-- The original operations are independent nonidentity affine maps, retained before reselecting the reference. -/
def original : ∀ {i j : K.Vertex}, K.Edge i j → Operations (ZMod 3) V :=
  fun e => if (e : Bool) = true then
    translation (k := ZMod 3) (![1,1] : V) * shear.toAffineEquiv * shear.toAffineEquiv
  else translation (k := ZMod 3) (![2,1] : V) * shear.toAffineEquiv⁻¹

/-- The authored real comparator translates in the first coordinate. -/
def comparisons : K.TwoCell → V := fun _ => x

/-- The two original reference words have equal full linear components. -/
theorem aligned (f : K.TwoCell) :
    (GroupExtension.pathValue K reference (K.twoLeft f)).linear =
      (GroupExtension.pathValue K reference (K.twoRight f)).linear := by
  change (1 * shear.toAffineEquiv).linear =
    (1 * (translation (k := ZMod 3) y * shear.toAffineEquiv)).linear
  rw [one_mul, one_mul]
  change projection shear.toAffineEquiv = projection (translation (k := ZMod 3) y * shear.toAffineEquiv)
  rw [map_mul, projection_translation, one_mul]

/-- The whole original affine tower is generated from the distinct original and reference operations. -/
noncomputable abbrev actualTower := tower K original reference comparisons aligned

/-- No original triple is removed; this original geometry has no triples. -/
theorem authored_three (s : K.ThreeCell) :
    pastingOperation K reference comparisons (K.threeLeft s) =
      pastingOperation K reference comparisons (K.threeRight s) := Empty.elim s

/-- The original false operation is nonidentity and different from the actual reference. -/
theorem original_false_value : original (i := ()) (j := ()) false 0 = (![2,1] : V) := by
  change (![2,1] : V) + shear.symm 0 = ![2,1]
  rw [map_zero, add_zero]

/-- Reselection preserves the original nonidentity affine operation as the input edge. -/
theorem tower_original_false : actualTower.original.edgeLift (i := ()) (j := ()) false =
    original (i := ()) (j := ()) false := rfl

/-- The original false operation differs from its actual shearing reference. -/
theorem original_reference_distinct : original (i := ()) (j := ()) false ≠ reference (i := ()) (j := ()) false := by
  intro h
  have he := congrArg (fun g : Operations (ZMod 3) V => g 0 0) h
  change original (i := ()) (j := ()) false 0 0 = reference (i := ()) (j := ()) false 0 0 at he
  rw [original_false_value] at he
  change (2 : ZMod 3) = 0 at he
  exact (by decide : (2 : ZMod 3) ≠ 0) he

/-- The real full reference transport sends the second standard vector to the sum of both vectors. -/
theorem native_transport_nonidentity :
    coefficient K original reference comparisons aligned ()
      (actualTower.toTower.localCoefficients.edge (i := ()) (j := ()) false
        ((coefficient K original reference comparisons aligned ()).symm y)) = x + y := by
  rw [edge_coefficient, AddEquiv.apply_symm_apply]
  change shear y = x + y
  ext j
  fin_cases j <;> norm_num [reference, shear, x, y]

/-- The nonzero first-coordinate label preserves the original fixed shear loop. -/
theorem gauge_label_x_allowed :
    (fun _ : K.Vertex => x) ∈ gaugeLabels K reference ∅ C13RangeInput.fixed.edges := by
  constructor
  · intro v hv; exact False.elim hv
  · intro e he
    change e.2.2 = false at he
    rw [he]
    change x = shear x
    ext j
    fin_cases j <;> norm_num [shear, x]

/-- The second-coordinate label fails to preserve the same original fixed shear loop. -/
theorem gauge_label_y_forbidden :
    (fun _ : K.Vertex => y) ∉ gaugeLabels K reference ∅ C13RangeInput.fixed.edges := by
  intro h
  have he := h.2 (⟨(),(),false⟩ : EdgeName (K := K)) rfl
  change y = shear y at he
  have hj := congrArg (fun v : V => v 0) he
  norm_num [shear, y] at hj

/-- Every original full native kernel coordinate reconstructs the actual second translation. -/
theorem full_kernel_vector :
    FiberAut.hom (kernelInclusion (GroupExtension.projection (projection (k := ZMod 3) (A := V)))
      (GroupExtension.terminal (V ≃ₗ[ZMod 3] V)) (actualTower.original.object ())
      (Additive.toMul ((coefficient K original reference comparisons aligned ()).symm y))) =
        translation (k := ZMod 3) y := coefficient_inverse_value K original reference comparisons aligned () y

/-- Every original real translation centralizes the entire full affine projection kernel. -/
theorem comparator_full_centralizer :
    ∀ a : (projection (k := ZMod 3) (A := V)).ker,
      translation (k := ZMod 3) x * a.1 = a.1 * translation (k := ZMod 3) x := by
  apply (centralizes_kernel_iff (translation (k := ZMod 3) x)).mpr
  simp

/-- The real shear fails to centralize the entire original affine projection kernel. -/
theorem shear_not_full_centralizer :
    ¬ ∀ a : (projection (k := ZMod 3) (A := V)).ker,
      shear.toAffineEquiv * a.1 = a.1 * shear.toAffineEquiv := by
  intro h
  have hs := (centralizes_kernel_iff shear.toAffineEquiv).mp h
  have he := congrArg (fun g : Operations (ZMod 3) V => g y 0) hs
  norm_num [shear, y, translation] at he

/-- The positive repaired original true loop uses the authored first-coordinate translation. -/
def repaired : ∀ {i j : K.Vertex}, K.Edge i j → Operations (ZMod 3) V :=
  fun e => if (e : Bool) = true then translation (k := ZMod 3) x * shear.toAffineEquiv
    else shear.toAffineEquiv

/-- A genuine original affine repair keeps the physically fixed false loop and repairs the candidate true loop. -/
def positive : Repair K reference comparisons C13RangeInput.fixed.edges where
  operation := repaired
  linear e := by
    cases e
    · rfl
    · change projection (translation (k := ZMod 3) x * shear.toAffineEquiv) =
        projection (translation (k := ZMod 3) y * shear.toAffineEquiv)
      rw [map_mul, map_mul, projection_translation, projection_translation]
  face _ := by
    change translation (k := ZMod 3) x * (1 * shear.toAffineEquiv) =
      1 * (translation (k := ZMod 3) x * shear.toAffineEquiv)
    rw [one_mul, one_mul]
  fixed_value e he := by
    change e.2.2 = false at he
    rw [he]
    rfl

/-- The independent positive real repair restores the same original native repair choices. -/
theorem positive_native : Nonempty (SupportedRepair actualTower C13RangeInput.fixed.edges) :=
  ⟨(repairEquivalence K original reference comparisons aligned C13RangeInput.fixed.edges).symm positive⟩

/-- Fixing both original operations is impossible because their authored real comparator equality fails. -/
theorem all_fixed_impossible : ¬ Nonempty (Repair K reference comparisons Set.univ) := by
  rintro ⟨s⟩
  have hf := s.face ()
  have hl := s.fixed_value (⟨(),(),false⟩ : EdgeName (K := K)) (Set.mem_univ _)
  have hr := s.fixed_value (⟨(),(),true⟩ : EdgeName (K := K)) (Set.mem_univ _)
  change translation (k := ZMod 3) x * (1 * s.operation (i := ()) (j := ()) false) =
    1 * s.operation (i := ()) (j := ()) true at hf
  rw [hl, hr, one_mul, one_mul] at hf
  have he := congrArg (fun g : Operations (ZMod 3) V => g 0 0) hf
  change (1 : ZMod 3) = 0 at he
  norm_num at he

/-- The same negative real case is impossible for the whole original native supported repair type. -/
theorem all_fixed_native_impossible : ¬ Nonempty (SupportedRepair actualTower Set.univ) := by
  intro h
  exact all_fixed_impossible ((repairEquivalence K original reference comparisons aligned Set.univ).nonempty_congr.mp h)

/-- The original finite degree-one matrix retains the positive first-coordinate false-loop column. -/
theorem actual_matrix_positive :
    edgeMatrix 2 K reference ((), (0 : Fin 2)) ((⟨(),(),false⟩ : EdgeName (K := K)), (0 : Fin 2)) = 1 := by
  change ((1 : ZMod 3) - 0) = 1
  rw [sub_zero]

/-- The original finite degree-one matrix retains the negative true-loop column on the same authored word. -/
theorem actual_matrix_negative :
    edgeMatrix 2 K reference ((), (0 : Fin 2)) ((⟨(),(),true⟩ : EdgeName (K := K)), (0 : Fin 2)) = -1 := by
  change ((0 : ZMod 3) - 1) = -1
  rw [zero_sub]

/-- The actual finite defect has a nonzero first coordinate from the authored real translation. -/
theorem actual_defect_first : defectCoordinates 2 K reference comparisons ((), (0 : Fin 2)) = 1 := by
  change (translation (k := ZMod 3) x * shear.toAffineEquiv *
    (translation (k := ZMod 3) y * shear.toAffineEquiv)⁻¹) 0 0 = 1
  rw [mul_inv_rev, ← mul_assoc, mul_assoc (translation (k := ZMod 3) x), mul_inv_cancel, mul_one]
  change (1 : ZMod 3) + (-0 + 0) = 1
  simp

/-- The actual finite defect records the reference disagreement in its second full kernel coordinate. -/
theorem actual_defect_second : defectCoordinates 2 K reference comparisons ((), (1 : Fin 2)) = -1 := by
  change (translation (k := ZMod 3) x * shear.toAffineEquiv *
    (translation (k := ZMod 3) y * shear.toAffineEquiv)⁻¹) 0 1 = -1
  rw [mul_inv_rev, ← mul_assoc, mul_assoc (translation (k := ZMod 3) x), mul_inv_cancel, mul_one]
  change (0 : ZMod 3) + (-1 + 0) = -1
  simp

end AAT.AG.RelativeRepairComposition.C14AffineRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C14AffineRegression
