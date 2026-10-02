import ResearchLean.AG.RelativeRepairComposition.SubdivisionMinimalRanges
import ResearchLean.AG.RelativeRepairComposition.SubdivisionRangeCohomology
import ResearchLean.AG.RelativeRepairComposition.C18SubdivisionRegression
import ResearchLean.AG.RelativeRepairComposition.C17ForbiddenRange
import ResearchLean.AG.RelativeRepairComposition.NativeAffineDifferentials

/-!
# The same specified W4 has a nonzero full always quotient and a full candidate column

The full native always source has zero original differential. Its original
obstruction quotient is the entire face kernel, with the actual negative defect
at coordinate one. The actual subdivision transports these whole values.

## Implementation notes

The full quotient coordinate is derived from the independently defined always
differential and its proved zero image. A supplied obstruction point or a
coordinate chosen only on the candidate image would not test the actual
signed defect and surjectivity onto the whole quotient. The same complete face
kernel coordinate supplies both the quotient comparison and its full dual.
-/
namespace AAT.AG.RelativeRepairComposition.C19SubdivisionRangeRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine C17SubdivisionInput
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
attribute [local instance] Classical.propDecidable
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules
/-- Universal old-edge membership supplies the decision used by the full W4 differential APIs. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := geometry)).edges) :=
  fun _ => isTrue trivial

/-- The entire original candidate set keeps the complete b name. -/
def candidates : Set (EdgeName (K := geometry)) := {candidate}
/-- No original candidate lies in the original fixed edge part. -/
theorem candidates_outside : ∀ e ∈ candidates, e ∉ fixedRegion.edges := by
  intro e he h
  exact h.elim
/-- The original fixed face law is discharged because the specified fixed part has no face. -/
theorem fixed_faces : ∀ f ∈ fixedRegion.faces,
    originalTower.toTower.upper.pathLift (geometry.twoLeft f) ≫ FiberAut.hom (originalTower.comparator f) =
      originalTower.toTower.upper.pathLift (geometry.twoRight f) := by
  intro f hf
  exact hf.elim
/-- The original complete kernel transport is linear for the original native affine modules. -/
theorem original_linear {i j : geometry.Vertex} (e : geometry.Edge i j) (t : ZMod 3)
    (x : originalTower.toTower.localCoefficients.A i) :
    originalTower.toTower.localCoefficients.edge e (t • x) =
      t • originalTower.toTower.localCoefficients.edge e x :=
  NativeAffine.edge_linear geometry reference reference comparison linear_faces e t x

/-- The full original face differential reads exactly the entire actual b correction. -/
theorem d1_coordinate (h : C1 originalTower.toTower.localCoefficients) :
    middleCoefficient (d1 originalTower.toTower.localCoefficients h ()) = middleCoefficient (h candidate) := by
  refine (NativeAffine.d1_value geometry reference reference comparison linear_faces h ()).trans ?_
  simp only [geometry,vectorPath,GroupExtension.pathValue,reference,
    if_neg Bool.false_ne_true,one_mul]
  change -(-(middleCoefficient (h candidate))) +
    (-(middleCoefficient (h chosen)) + (middleCoefficient (h chosen) + 0)) - 0 =
      middleCoefficient (h candidate)
  abel

/-- The complete relative face family is equivalent to the entire original F3 kernel coordinate. -/
noncomputable def faceCoordinate :
    RelativeCover.C2 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion ≃ₗ[ZMod 3] ZMod 3 where
  toFun c := linearCoefficient geometry reference reference comparison linear_faces () (c.1 ⟨(),Set.mem_univ _⟩)
  invFun t := ⟨fun _ => (linearCoefficient geometry reference reference comparison linear_faces ()).symm t,
    by intro f hf; exact hf.elim⟩
  left_inv c := by
    apply Subtype.ext
    funext f
    cases f.1
    exact (linearCoefficient geometry reference reference comparison linear_faces ()).symm_apply_apply _
  right_inv t := (linearCoefficient geometry reference reference comparison linear_faces ()).apply_symm_apply t
  map_add' a b := (linearCoefficient geometry reference reference comparison linear_faces ()).map_add _ _
  map_smul' t a := (linearCoefficient geometry reference reference comparison linear_faces ()).map_smul _ _

/-- The same face linear coordinate is the earlier full native kernel coordinate. -/
theorem faceCoordinate_value (c : RelativeCover.C2 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion) :
    faceCoordinate c = middleCoefficient (c.1 ⟨(),Set.mem_univ _⟩) := rfl

/-- Every independently specified original always correction has zero original full face differential. -/
theorem always_D_zero
    (h : OriginalColumns.alwaysSpace (k := ZMod 3) originalTower.toTower.localCoefficients fixedRegion candidates) :
    OriginalColumns.D originalTower.toTower.localCoefficients fixedRegion candidates original_linear h = 0 := by
  apply faceCoordinate.injective
  rw [faceCoordinate_value,map_zero,OriginalColumns.D_value,d1_coordinate]
  have hb := h.2 ⟨candidate,Set.mem_singleton candidate⟩
  rw [hb,map_zero]

/-- The entire original always image is zero, with no restriction on the actual a correction. -/
theorem always_range_zero :
    LinearMap.range (OriginalColumns.D originalTower.toTower.localCoefficients fixedRegion candidates original_linear) = ⊥ := by
  apply le_antisymm
  · rintro _ ⟨h,rfl⟩
    rw [always_D_zero]
    exact Submodule.zero_mem _
  · exact bot_le

/-- The actual original always quotient retains every full original face coordinate. -/
noncomputable def obstructionCoordinate :
    OriginalRanges.ObstructionSpace (k := ZMod 3) originalTower.toTower.localCoefficients
      fixedRegion candidates original_linear ≃ₗ[ZMod 3] ZMod 3 :=
  ((LinearMap.range (OriginalColumns.D originalTower.toTower.localCoefficients fixedRegion candidates original_linear)).quotEquivOfEqBot
    always_range_zero).trans faceCoordinate

/-- The quotient coordinate evaluates every actual full original face representative. -/
theorem obstructionCoordinate_q (c : RelativeCover.C2 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion) :
    obstructionCoordinate (LinearInterface.q
      (OriginalColumns.D originalTower.toTower.localCoefficients fixedRegion candidates original_linear) c) =
      faceCoordinate c := rfl

/-- The same actual signed obstruction, rather than an assumed nonzero quotient point. -/
noncomputable def obstruction :=
  LinearInterface.q (OriginalColumns.D originalTower.toTower.localCoefficients fixedRegion candidates original_linear)
    (-ActualEquation.defectFamily originalTower fixedRegion fixed_faces)

/-- The actual signed obstruction has coordinate one in the full original always quotient. -/
theorem obstruction_coordinate : obstructionCoordinate obstruction = 1 := by
  rw [obstruction,obstructionCoordinate_q,map_neg,faceCoordinate_value]
  change -middleCoefficient (originalTower.toTower.defect ()) = 1
  rw [C18SubdivisionRegression.old_defect_coordinate,neg_neg]

/-- The same actual original obstruction is nonzero in the full original quotient. -/
theorem obstruction_ne_zero : obstruction ≠ 0 := by
  intro h
  have hv := congrArg obstructionCoordinate h
  rw [obstruction_coordinate,map_zero] at hv
  exact one_ne_zero hv

/-- The original complete candidate b is retained as an element of the entire candidate set. -/
def candidateName : candidates := ⟨candidate,Set.mem_singleton candidate⟩

/-- The complete relative original differential reads the full original native b correction. -/
theorem relative_differential_coordinate
    (h : RelativeCover.C1 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion) :
    faceCoordinate (FiniteCoefficients.differential1 originalTower.toTower.localCoefficients
      original_linear ClosedRegion.all fixedRegion h) = middleCoefficient (h.1 ⟨candidate,Set.mem_univ _⟩) := by
  rw [FiniteCoefficients.differential1_eq,faceCoordinate_value]
  have hr := congrFun (RelativeCover.original2_restrict originalTower.toTower.localCoefficients fixedRegion
    (RelativeCover.d1 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion h)) ⟨(),Set.mem_univ _⟩
  have hd := congrArg (fun c : RelativeComplex.relativeC2 originalTower.toTower.localCoefficients fixedRegion => c.1 ())
    (RelativeCover.original_d1 originalTower.toTower.localCoefficients fixedRegion h)
  exact (congrArg middleCoefficient (hr.symm.trans hd)).trans
    (d1_coordinate (fun e => h.1 ⟨e,Set.mem_univ e⟩))

/-- Every full original candidate kernel value maps to that same value in the actual quotient coordinate. -/
theorem column_coordinate (x : originalTower.toTower.localCoefficients.A candidate.2.1) :
    obstructionCoordinate (OriginalRanges.column (k := ZMod 3) originalTower.toTower.localCoefficients
      fixedRegion candidates candidates_outside original_linear candidateName x) = middleCoefficient x := by
  rw [OriginalRanges.column_apply]
  rw [obstructionCoordinate_q]
  rw [OriginalColumns.column_apply]
  rw [relative_differential_coordinate]
  have hv := OriginalColumns.candidate_value (k := ZMod 3) originalTower.toTower.localCoefficients
    fixedRegion candidates candidates_outside
      ((LinearMap.single (ZMod 3) (fun e : candidates => originalTower.toTower.localCoefficients.A e.1.2.1)
        candidateName) x) candidateName
  have hx : ((LinearMap.single (ZMod 3)
      (fun e : candidates => originalTower.toTower.localCoefficients.A e.1.2.1) candidateName) x) candidateName = x := by
    simp only [LinearMap.single_apply,Pi.single_eq_same]
  exact congrArg middleCoefficient (hv.trans hx)

/-- The actual entire original candidate column is surjective onto the entire independent always quotient. -/
theorem column_surjective : Function.Surjective
    (OriginalRanges.column (k := ZMod 3) originalTower.toTower.localCoefficients
      fixedRegion candidates candidates_outside original_linear candidateName) := by
  intro o
  refine ⟨middleCoefficient.symm (obstructionCoordinate o),?_⟩
  apply obstructionCoordinate.injective
  rw [column_coordinate,AddEquiv.apply_symm_apply]

/-- The actual split quotient is compared with the same nonzero original full quotient. -/
noncomputable def splitObstructionCoordinate :=
  (Subdivision.RangeQuotient.equivalence originalTower fixedRegion candidates chosen factors
    (by exact not_false) C18SubdivisionRegression.chosen_not_candidate original_linear).trans obstructionCoordinate

/-- The same actual split signed defect defines the independent new obstruction point. -/
noncomputable def splitObstruction :=
  LinearInterface.q
    (OriginalColumns.D (k := ZMod 3) splitTower.toTower.localCoefficients
      (Subdivision.oldRegion geometry chosen fixedRegion (by exact not_false))
      (Subdivision.oldEdgeSet geometry chosen candidates)
      (Subdivision.LinearCoefficients.edge_linear originalTower chosen factors original_linear))
    (-ActualEquation.defectFamily splitTower
      (Subdivision.oldRegion geometry chosen fixedRegion (by exact not_false))
      (Subdivision.fixed_face_laws originalTower chosen factors fixedRegion (by exact not_false) fixed_faces))

/-- The independently generated actual split obstruction has the same nonzero full coordinate one. -/
theorem split_obstruction_coordinate : splitObstructionCoordinate splitObstruction = 1 := by
  rw [splitObstructionCoordinate,LinearEquiv.trans_apply]
  change obstructionCoordinate ((Subdivision.RangeQuotient.equivalence originalTower fixedRegion candidates chosen factors
    (by exact not_false) C18SubdivisionRegression.chosen_not_candidate original_linear)
    (LinearInterface.q _ (-ActualEquation.defectFamily splitTower _ _))) = 1
  rw [Subdivision.RangeQuotient.obstruction_eq]
  exact obstruction_coordinate

/-- The actual split obstruction is nonzero in its entire independently defined always quotient. -/
theorem split_obstruction_ne_zero : splitObstruction ≠ 0 := by
  intro h
  have hv := congrArg splitObstructionCoordinate h
  rw [split_obstruction_coordinate,map_zero] at hv
  exact one_ne_zero hv

/-- A dual on the entire original actual quotient reads its full F3 coordinate. -/
noncomputable def obstructionDual : Module.Dual (ZMod 3)
    (OriginalRanges.ObstructionSpace (k := ZMod 3) originalTower.toTower.localCoefficients
      fixedRegion candidates original_linear) := obstructionCoordinate.toLinearMap

/-- The full actual quotient dual is nonzero on the actual original obstruction. -/
theorem obstructionDual_value : obstructionDual obstruction = 1 := obstruction_coordinate

/-- The full-column support of this nonzero obstruction dual is the whole singleton named candidate set. -/
theorem obstructionDual_support : NamedDual.support
    (OriginalRanges.column (k := ZMod 3) originalTower.toTower.localCoefficients
      fixedRegion candidates candidates_outside original_linear) obstructionDual = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  have he : e = candidateName := Subtype.ext e.2
  subst e
  intro hz
  have hv := LinearMap.congr_fun hz (middleCoefficient.symm 1)
  change obstructionCoordinate (OriginalRanges.column (k := ZMod 3) originalTower.toTower.localCoefficients
    fixedRegion candidates candidates_outside original_linear candidateName (middleCoefficient.symm 1)) = 0 at hv
  rw [column_coordinate,AddEquiv.apply_symm_apply] at hv
  exact one_ne_zero hv

/-- Every selected full original quotient range contains the obstruction exactly when b is selected. -/
theorem obstruction_mem_range_iff (S : Set candidates) :
    obstruction ∈ NamedDual.ranges
      (OriginalRanges.column (k := ZMod 3) originalTower.toTower.localCoefficients
        fixedRegion candidates candidates_outside original_linear) S ↔ candidateName ∈ S := by
  constructor
  · intro h
    have hh := (NamedDual.mem_ranges_iff_hits _ obstruction S).mp h obstructionDual
      (by rw [obstructionDual_value]; exact one_ne_zero)
    obtain ⟨e,he,_⟩ := hh
    have hn : e = candidateName := Subtype.ext e.2
    exact hn ▸ he
  · intro he
    obtain ⟨x,hx⟩ := column_surjective obstruction
    exact NamedDual.range_le _ S candidateName he (hx ▸ (LinearMap.mem_range_self _ x))

/-- The complete original candidate is the unique inclusion-minimal full obstruction range. -/
theorem minimal_obstruction_iff (S : Set candidates) :
    Minimal (fun V => obstruction ∈ NamedDual.ranges
      (OriginalRanges.column (k := ZMod 3) originalTower.toTower.localCoefficients
        fixedRegion candidates candidates_outside original_linear) V) S ↔ S = Set.univ := by
  constructor
  · intro h
    have hb := (obstruction_mem_range_iff S).mp h.1
    apply Set.eq_univ_of_forall
    intro e
    have he : e = candidateName := Subtype.ext e.2
    exact he.symm ▸ hb
  · rintro rfl
    refine ⟨(obstruction_mem_range_iff Set.univ).mpr (Set.mem_univ _),?_⟩
    intro V hv hvs e he
    have hb := (obstruction_mem_range_iff V).mp hv
    have hn : e = candidateName := Subtype.ext e.2
    exact hn.symm ▸ hb

/-- Every independent original actual repair range is minimal exactly at the full named singleton b. -/
theorem minimal_actual_repair_iff (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair originalTower (fixedEdgesForRange fixedRegion.edges candidates (OriginalRanges.allowed candidates V)))) S ↔ S = Set.univ :=
  (OriginalRangeClassification.minimal_repair_iff_range (k := ZMod 3) originalTower
    fixedRegion candidates candidates_outside original_linear fixed_faces S).trans
      (minimal_obstruction_iff S)

/-- The independent actual split repair ranges have precisely the same minimal named range. -/
theorem split_minimal_actual_repair_iff (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair splitTower (fixedEdgesForRange (Subdivision.oldRegion geometry chosen fixedRegion (by exact not_false)).edges (Subdivision.oldEdgeSet geometry chosen candidates) (OriginalRanges.allowed (Subdivision.oldEdgeSet geometry chosen candidates) V)))) ((Subdivision.CandidateColumns.nameEquiv candidates chosen C18SubdivisionRegression.chosen_not_candidate) '' S) ↔ S = Set.univ :=
  (Subdivision.MinimalRanges.minimal_actual_repair_iff originalTower fixedRegion candidates chosen factors
    (by exact not_false) C18SubdivisionRegression.chosen_not_candidate original_linear
    candidates_outside fixed_faces S).trans (minimal_actual_repair_iff S)

/-- The same retained actual split candidate reads every original full kernel value in the same quotient. -/
theorem split_column_coordinate (x : originalTower.toTower.localCoefficients.A candidate.2.1) :
    splitObstructionCoordinate
      ((OriginalRanges.column (k := ZMod 3) splitTower.toTower.localCoefficients (Subdivision.oldRegion geometry chosen fixedRegion (by exact not_false)) (Subdivision.oldEdgeSet geometry chosen candidates) (Subdivision.CandidateColumns.retained_outside fixedRegion candidates chosen (by exact not_false) candidates_outside) (Subdivision.LinearCoefficients.edge_linear originalTower chosen factors original_linear)) ((Subdivision.CandidateColumns.nameEquiv candidates chosen C18SubdivisionRegression.chosen_not_candidate) candidateName)
        (Subdivision.CandidateColumns.kernelEquiv (k := ZMod 3) originalTower candidates chosen factors
          C18SubdivisionRegression.chosen_not_candidate candidateName x)) = middleCoefficient x := by
  rw [splitObstructionCoordinate,LinearEquiv.trans_apply]
  exact (congrArg obstructionCoordinate (Subdivision.CandidateColumns.quotient_column originalTower
    fixedRegion candidates chosen factors (by exact not_false) C18SubdivisionRegression.chosen_not_candidate
      original_linear candidates_outside candidateName x)).trans (column_coordinate x)

/-- The retained full candidate column is surjective onto the entire independent split obstruction quotient. -/
theorem split_column_surjective : Function.Surjective ((OriginalRanges.column (k := ZMod 3) splitTower.toTower.localCoefficients (Subdivision.oldRegion geometry chosen fixedRegion (by exact not_false)) (Subdivision.oldEdgeSet geometry chosen candidates) (Subdivision.CandidateColumns.retained_outside fixedRegion candidates chosen (by exact not_false) candidates_outside) (Subdivision.LinearCoefficients.edge_linear originalTower chosen factors original_linear)) ((Subdivision.CandidateColumns.nameEquiv candidates chosen C18SubdivisionRegression.chosen_not_candidate) candidateName)) := by
  intro o
  refine ⟨Subdivision.CandidateColumns.kernelEquiv (k := ZMod 3) originalTower candidates chosen factors
    C18SubdivisionRegression.chosen_not_candidate candidateName
      (middleCoefficient.symm (splitObstructionCoordinate o)),?_⟩
  apply splitObstructionCoordinate.injective
  rw [split_column_coordinate,AddEquiv.apply_symm_apply]

end AAT.AG.RelativeRepairComposition.C19SubdivisionRangeRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C19SubdivisionRangeRegression
