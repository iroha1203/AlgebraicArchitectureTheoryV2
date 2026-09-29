import ResearchLean.AG.AbelianLiftingObstruction.H1Classification
import ResearchLean.AG.AbelianLiftingObstruction.CrossStageKernel
import ResearchLean.AG.CrossStageCoherence.RelativeObstruction

/-! # The original Chapter 4 arrows as an abelian lifting problem

The same edge section and authored comparisons supply the general input.
Only the three hypotheses explicitly allowed by G-129 A are retained here;
the syzygy hypothesis is supplied separately to the obstruction theorem.
-/

namespace AAT.AG.AbelianLiftingObstruction.CrossStage

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence TransportCoherence.Arbitrary

universe u v

variable {K : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}

/-- Both strong properties come from the original two-stage edge. -/
noncomputable abbrev originalLift (data : TwoLayerLiftData.{u, v} K U) :
    LiftData K.toFiniteTransportTwoPresentation
      (geometryProjection U ⋙ packageProjection U) where
  object := data.geometry
  edgeBase e := (data.edgeLift e).base.base
  edgeLift := data.edgeLift
  edgeStrong e := by
    letI := data.edgeGeometryStrong e
    letI := data.edgeCoreStrong e
    exact geometryHom_isCompositeStronglyCocartesian (data.edgeLift e)

/-- The composite lift keeps the original full geometry path arrow. -/
theorem originalLift_path (data : TwoLayerLiftData.{u, v} K U)
    {i j : K.Vertex} (w : K.Path i j) :
    (originalLift data).pathLift w = data.pathLift w := by
  induction w with
  | nil _ => rfl
  | cons e w ih => exact congrArg (fun x => data.edgeLift e ≫ x) ih

/-- Its bottom path is the bottom projection of the original geometry path. -/
theorem originalLift_base (data : TwoLayerLiftData.{u, v} K U)
    {i j : K.Vertex} (w : K.Path i j) :
    (originalLift data).pathBase w = (data.pathLift w).base.base := by
  rw [← originalLift_path data w]
  exact ((originalLift data).map_pathLift w).symm

/-- Every original upper edge coordinate retains the full geometry arrow. -/
theorem selected_path (data : TwoLayerLiftData.{u, v} K U)
    (c : UpperEdgeReselection data) {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper K (geometryProjection U) (packageProjection U)
      (originalLift data) (fun e => compositeFiberEquiv _ (c _ _ e))).pathLift w =
        upperReselectedPathLift data c w := by
  induction w with
  | nil _ => rfl
  | cons e w ih => exact congrArg (fun x => upperReselectedEdgeLift data c e ≫ x) ih

/-- The A2 equation is the existing alignment on the same core paths. -/
theorem selected_path_core (data : TwoLayerTransportData.{u, v} K U)
    (s : EdgeSectionFamily data) {i j : K.Vertex} (w : K.Path i j) :
    (upperReselectedPathLift data.lift s.lift w).base =
      TransportCoherence.reselectedPathLift data.coreData.lift s.core w := by
  rw [upperReselectedPathLift_base, s.pushforward_lift_eq_core]
  rfl

/-- The selected original geometry edge is strong for the composite tower. -/
theorem selectedStrong (data : TwoLayerLiftData.{u, v} K U)
    (c : UpperEdgeReselection data) {i j : K.Vertex} (e : K.Edge i j) :
    (geometryProjection U ⋙ packageProjection U).IsStronglyCocartesian
      (data.edgeLift e).base.base (upperReselectedEdgeLift data c e) := by
  exact reselectedEdgeLift_isStronglyCocartesian (originalLift data)
    (fun _ _ e => compositeFiberEquiv _ (c _ _ e)) e

/-- The image of this same selected edge is strong for the lower tower. -/
theorem selectedCoreStrong (data : TwoLayerLiftData.{u, v} K U)
    (c : UpperEdgeReselection data) {i j : K.Vertex} (e : K.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      (data.edgeLift e).base.base (upperReselectedEdgeLift data c e).base := by
  exact selectedLowerStrong K (geometryProjection U) (packageProjection U)
    (originalLift data) data.edgeCoreStrong
    (fun e => compositeFiberEquiv _ (c _ _ e)) e

/-- G-129 D: construct the general input from the very same Chapter 4 section. -/
noncomputable abbrev presentation (data : TwoLayerTransportData.{u, v} K U)
    (s : EdgeSectionFamily data) (alignment : CoreAlignmentAt data s)
    (comm : ∀ v, ∀ a b : Kernel (geometryProjection U) (packageProjection U)
      (data.lift.geometry v), a * b = b * a)
    (bijective : ∀ {i j : K.Vertex} (e : K.Edge i j),
      Function.Bijective (kernelTransportHom (geometryProjection U) (packageProjection U)
        (upperReselectedEdgeLift data.lift s.lift e)
        (selectedStrong data.lift s.lift e)
        (selectedCoreStrong data.lift s.lift e)))
    (central : ∀ f, ∀ a : Kernel (geometryProjection U) (packageProjection U)
      (data.lift.geometry (K.twoTarget f)),
      compositeFiberEquiv _ (data.comparator f) * kernelInclusion _ _ _ a =
        kernelInclusion _ _ _ a * compositeFiberEquiv _ (data.comparator f)) :
    OriginalTowerPresentation K (geometryProjection U) (packageProjection U) where
  original := originalLift data.lift
  originalLowerStrong := data.lift.edgeCoreStrong
  core e := packageFiberAutMulEquiv _ (s.core _ _ e)
  lift e := compositeFiberEquiv _ (s.lift _ _ e)
  lift_core e := by
    rw [compositeFiberEquiv_pushforward]
    exact congrArg (packageFiberAutMulEquiv _) (s.projects _ _ e)
  faceBase f := by rw [originalLift_base, originalLift_base]; exact data.twoCellBase f
  comparator f := compositeFiberEquiv _ (data.comparator f)
  coreAlignment f := by
    rw [selected_path, selected_path]
    change (upperReselectedPathLift data.lift s.lift (K.twoLeft f)).base.comp
      (CompositeFiberAut.hom (data.comparator f)).base =
      (upperReselectedPathLift data.lift s.lift (K.twoRight f)).base
    rw [selected_path_core, selected_path_core]
    exact alignment f
  kernelComm := comm
  edgeBijective := bijective
  comparatorCentralizes := central

variable (data : TwoLayerTransportData.{u, v} K U)
variable (s : EdgeSectionFamily data) (alignment : CoreAlignmentAt data s)
variable (comm : ∀ v, ∀ a b : Kernel (geometryProjection U) (packageProjection U)
  (data.lift.geometry v), a * b = b * a)
variable (bijective : ∀ {i j : K.Vertex} (e : K.Edge i j),
  Function.Bijective (kernelTransportHom (geometryProjection U) (packageProjection U)
    (upperReselectedEdgeLift data.lift s.lift e)
    (selectedStrong data.lift s.lift e) (selectedCoreStrong data.lift s.lift e)))
variable (central : ∀ f, ∀ a : Kernel (geometryProjection U) (packageProjection U)
  (data.lift.geometry (K.twoTarget f)),
  compositeFiberEquiv _ (data.comparator f) * kernelInclusion _ _ _ a =
    kernelInclusion _ _ _ a * compositeFiberEquiv _ (data.comparator f))


local notation "T" => presentation data s alignment comm bijective central

/-- The generated comparator is the same full Chapter 4 automorphism. -/
theorem canonicalFace_eq (f : K.TwoCell) :
    (T).toTower.canonicalFace f =
      compositeFiberEquiv _ (sectionCellComparator data s f) := by
  apply FiberAut.ext_of_strong_fac _
    ((T).toTower.upper.pathLift_isStronglyCocartesian (K.twoLeft f))
  change _ ≫ FiberAut.hom (canonicalFiberComparator _ _ _ _ _ _) = _
  rw [Arbitrary.canonicalFiberComparator_fac]
  symm
  change (selectedUpper K _ _ (originalLift data.lift)
    (fun e => compositeFiberEquiv _ (s.lift _ _ e))).pathLift (K.twoLeft f) ≫
    FiberAut.hom (compositeFiberEquiv _ (sectionCellComparator data s f)) =
    (selectedUpper K _ _ (originalLift data.lift)
      (fun e => compositeFiberEquiv _ (s.lift _ _ e))).pathLift (K.twoRight f)
  rw [selected_path, selected_path]
  exact upperCanonicalTwoCellComparator_fac data s.lift f

/-- B1 is exactly sectionInnerObstruction, including its original arrow. -/
theorem faceDefect_eq (f : K.TwoCell) :
    (T).toTower.faceDefect f = innerKernelEquiv _
      (sectionInnerObstruction data s alignment f) := by
  apply kernelInclusion_injective _ _ _
  rw [(T).toTower.faceDefect_inclusion, canonicalFace_eq]
  rfl

/-- Every additive correction is the same strict inner edge coordinate. -/
noncomputable def strictGauge (h : C1 (T).toTower.localCoefficients) :
    StrictEdgeReselection data.lift :=
  fun i j e => (innerKernelEquiv _).symm (Additive.toMul (h ⟨i, j, e⟩))

/-- Conversely every strict coordinate supplies the actual-kernel cochain. -/
noncomputable def correction (g : StrictEdgeReselection data.lift) :
    C1 (T).toTower.localCoefficients :=
  fun e => Additive.ofMul (innerKernelEquiv _ (g e.1 e.2.1 e.2.2))

/-- Converting a strict coordinate to a cochain and back preserves every edge. -/
@[simp] theorem strictGauge_correction (g : StrictEdgeReselection data.lift) :
    strictGauge data s alignment comm bijective central
      (correction data s alignment comm bijective central g) = g := by
  funext i j e
  exact (innerKernelEquiv _).symm_apply_apply _

/-- Converting an actual-kernel cochain to strict coordinates and back is identity. -/
@[simp] theorem correction_strictGauge (h : C1 (T).toTower.localCoefficients) :
    correction data s alignment comm bijective central
      (strictGauge data s alignment comm bijective central h) = h := by
  funext ⟨i, j, e⟩
  exact congrArg Additive.ofMul ((innerKernelEquiv _).apply_symm_apply _)

/-- Corrections preserve the original relative upper coordinate edge by edge. -/
theorem correctionChoice_eq (h : C1 (T).toTower.localCoefficients)
    {i j : K.Vertex} (e : K.Edge i j) :
    (T).correctionChoice h e = compositeFiberEquiv _
      (relativeUpperReselection s (strictGauge data s alignment comm bijective central h) i j e) := by
  change kernelInclusion (geometryProjection U) (packageProjection U)
      (data.lift.geometry j) (Additive.toMul (h ⟨i, j, e⟩)) *
      compositeFiberEquiv _ (s.lift i j e) = _
  rfl

/-- The same correction equation tests the same full authored path equalities. -/
theorem correction_coherent_iff (h : C1 (T).toTower.localCoefficients) :
    d1 (T).toTower.localCoefficients h = -(T).toTower.defect ↔
      SectionRelativeCoherentAt data s
        (strictGauge data s alignment comm bijective central h) := by
  rw [← (T).toTower.correctedDefect_eq_zero_iff_d1,
    (T).toTower.correctedDefect_eq_zero_iff_coherent]
  change (∀ f, reselectedPathLift (T).toTower.upper ((T).toTower.correctionReselection h)
      (K.twoLeft f) ≫ FiberAut.hom ((T).comparator f) =
      reselectedPathLift (T).toTower.upper ((T).toTower.correctionReselection h)
        (K.twoRight f)) ↔ _
  have path_eq : ∀ {i j : K.Vertex} (w : K.Path i j),
      reselectedPathLift (T).toTower.upper ((T).toTower.correctionReselection h) w =
        upperReselectedPathLift data.lift
          (relativeUpperReselection s (strictGauge data s alignment comm bijective central h)) w := by
    intro i j w
    rw [← (T).correctionChoice_path]
    induction w with
    | nil _ => rfl
    | cons e w ih =>
      change GeometryTotalHom.comp _ _ = GeometryTotalHom.comp _ _
      rw [ih]
      congr 1
  simp only [path_eq]
  rfl

/-- Recomputing B1 after any correction gives the original relative inner cochain. -/
theorem correctedFaceDefect_eq (h : C1 (T).toTower.localCoefficients) (f : K.TwoCell) :
    (T).toTower.correctedFaceDefect h f = innerKernelEquiv _
      (relativeInnerDefectCochain data s alignment
        (strictGauge data s alignment comm bijective central h) f) := by
  let g := strictGauge data s alignment comm bijective central h
  let other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (geometryProjection U ⋙ packageProjection U) (data.lift.geometry j) :=
    (T).correctionChoice h
  have hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward (geometryProjection U) (packageProjection U)
        (data.lift.geometry j) (other e) =
          (T).core e :=
    (T).correctionChoice_core h
  have hc : canonicalFaceComparator ((T).alternativeTransportData other) 1 f =
      compositeFiberEquiv _
        (sectionCellComparator data (relativeEdgeSection s g) f) := by
    apply FiberAut.ext_of_strong_fac _
      (((T).alternativeTransportData other).lift.pathLift_isStronglyCocartesian (K.twoLeft f))
    have hf := Arbitrary.canonicalFaceComparator_fac
      ((T).alternativeTransportData other) 1 f
    simp only [Arbitrary.reselectedPathLift_one] at hf
    rw [hf]
    have hp : ∀ {i j : K.Vertex} (w : K.Path i j),
        ((T).alternativeTransportData other).lift.pathLift w =
          upperReselectedPathLift data.lift (relativeUpperReselection s g) w := by
      intro i j w
      induction w with
      | nil _ => rfl
      | cons e w ih =>
        change GeometryTotalHom.comp _ _ = GeometryTotalHom.comp _ _
        rw [ih]
        congr 1
    rw [hp, hp]
    exact (upperCanonicalTwoCellComparator_fac data (relativeUpperReselection s g) f).symm
  apply kernelInclusion_injective _ _ _
  have hr := (T).alternativeRawDefect_eq other hother f
  have hcor : (T).alternativeCorrection
      other hother = h :=
    (T).solutionCorrection_correctionChoice h
  rw [hcor] at hr
  rw [← hr]
  unfold Arbitrary.rawFaceDefect
  rw [hc]
  rfl

/-- B2 is a value equality with relativeInnerDefectCochain, for every strict gauge. -/
theorem relativeDefect_add (g : StrictEdgeReselection data.lift) :
    (fun f => Additive.ofMul (innerKernelEquiv _
      (relativeInnerDefectCochain data s alignment g f))) =
      (T).toTower.defect + d1 (T).toTower.localCoefficients
        (correction data s alignment comm bijective central g) := by
  rw [← (T).toTower.correctedDefect_eq]
  funext f
  change _ = Additive.ofMul ((T).toTower.correctedFaceDefect _ f)
  rw [correctedFaceDefect_eq, strictGauge_correction]
  rfl

/-- Transporting authored comparisons retains their full original automorphisms. -/
theorem whisker_eq {i j : K.Vertex}
    (a : CompositeFiberAut (data.lift.geometry i)) (w : K.Path i j) :
    whiskerFiberAut (T).toTower.upper 1 (compositeFiberEquiv _ a) w =
      compositeFiberEquiv _ (upperWhiskerCompositeFiberAut data.lift s.lift a w) := by
  apply FiberAut.ext_of_strong_fac _
    ((T).toTower.upper.pathLift_isStronglyCocartesian w)
  have hfac := whiskerFiberAut_fac (T).toTower.upper 1 (compositeFiberEquiv _ a) w
  simp only [Arbitrary.reselectedPathLift_one, Arbitrary.fiberAutThenPath] at hfac
  rw [hfac]
  change CompositeFiberAut.hom a ≫
    (selectedUpper K _ _ (originalLift data.lift)
      (fun e => compositeFiberEquiv _ (s.lift _ _ e))).pathLift w =
    (selectedUpper K _ _ (originalLift data.lift)
      (fun e => compositeFiberEquiv _ (s.lift _ _ e))).pathLift w ≫ _
  rw [selected_path]
  exact (upperWhiskerCompositeFiberAut_fac data.lift s.lift a w).symm

/-- Equality of the original two authored pastings becomes the same A4 condition. -/
theorem authoredPasting_eq {i j : K.Vertex} {w z : K.Path i j}
    (P : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    authoredPastingComparator (T).toTower.toTransportData 1 P =
      compositeFiberEquiv _ (upperAuthoredPastingComparator data s.lift P) := by
  induction P with
  | nil _ => exact (map_one (compositeFiberEquiv _)).symm
  | cons step tail ih =>
    change authoredPastingComparator (T).toTower.toTransportData 1 tail *
      orientedFaceAuthoredComparator (T).toTower.toTransportData 1 step.face = _
    rw [ih]
    change _ = compositeFiberEquiv _ (_ * _)
    rw [map_mul]
    congr 1
    unfold Arbitrary.orientedFaceAuthoredComparator Arbitrary.orientedFaceComparator
      upperOrientedFaceComparator
    cases step.face.orientation with
    | forward => exact whisker_eq data s alignment comm bijective central _ _
    | backward =>
      simpa only [map_inv] using
        whisker_eq data s alignment comm bijective central
          ((data.comparator step.face.cell)⁻¹) step.face.outgoing

/-- The same Chapter 4 syzygy, without a vanishing premise, supplies A4. -/
theorem syzygy (hs : UpperSyzygyCompatible data s.lift) :
    ∀ cell : K.ThreeCell, AuthoredSyzygy (T).toTower.toTransportData 1
      (K.threeLeft cell) (K.threeRight cell) := by
  intro cell
  unfold AuthoredSyzygy
  rw [authoredPasting_eq, authoredPasting_eq, hs cell]

/-- B3 returns to the independently defined Chapter 4 coherentizable predicate. -/
theorem solution_nonempty_iff :
    Nonempty (Solution (T)) ↔ SectionRelativeCoherentizable data s := by
  rw [(T).solution_nonempty_iff_correction]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨strictGauge data s alignment comm bijective central h,
      (correction_coherent_iff data s alignment comm bijective central h).mp hh⟩
  · rintro ⟨g, hg⟩
    refine ⟨correction data s alignment comm bijective central g, ?_⟩
    apply (correction_coherent_iff data s alignment comm bijective central _).mpr
    simpa only [strictGauge_correction] using hg

/-- All original geometry edge coordinates over the fixed core satisfying the authored faces. -/
def ChapterSolution := {c : UpperEdgeReselection data.lift //
    pushforwardEdgeReselection data.lift c = s.core ∧ CrossStageCoherentAt data c}

/-- Return every general solution to exactly its original geometry automorphisms. -/
noncomputable def solutionEquiv : Solution (T) ≃ ChapterSolution data s where
  toFun S := ⟨fun i j e => (compositeFiberEquiv _).symm (S.choice e), by
    constructor
    · funext i j e
      apply (packageFiberAutMulEquiv _).injective
      change packageFiberAutMulEquiv _
        (compositeFiberPushforward _ ((compositeFiberEquiv _).symm (S.choice e))) = _
      rw [← compositeFiberEquiv_pushforward]
      exact S.choice_core e
    · intro f
      have hp : ∀ {i j : K.Vertex} (w : K.Path i j),
          (selectedUpper K _ _ (T).original S.choice).pathLift w =
            upperReselectedPathLift data.lift
              (fun i j e => (compositeFiberEquiv _).symm (S.choice e)) w := by
        intro i j w
        induction w with
        | nil _ => rfl
        | cons e w ih =>
          change _ ≫ (selectedUpper K _ _ _ S.choice).pathLift w =
            _ ≫ upperReselectedPathLift data.lift _ w
          rw [ih]
          rfl
      simpa only [hp] using S.face f⟩
  invFun c := {
    choice e := compositeFiberEquiv _ (c.1 _ _ e)
    choice_core e := by
      rw [compositeFiberEquiv_pushforward]
      exact congrArg (packageFiberAutMulEquiv _)
        (congrFun (congrFun (congrFun c.2.1 _) _) e)
    face f := by
      change (selectedUpper K _ _ (originalLift data.lift)
        (fun e => compositeFiberEquiv _ (c.1 _ _ e))).pathLift (K.twoLeft f) ≫
        FiberAut.hom (compositeFiberEquiv _ (data.comparator f)) =
        (selectedUpper K _ _ (originalLift data.lift)
          (fun e => compositeFiberEquiv _ (c.1 _ _ e))).pathLift (K.twoRight f)
      rw [selected_path, selected_path]
      exact c.2.2 f }
  left_inv S := by
    apply Solution.ext
    intro i j e
    exact (compositeFiberEquiv _).apply_symm_apply _
  right_inv c := by
    apply Subtype.ext
    funext i j e
    exact (compositeFiberEquiv _).symm_apply_apply _

/-- This correspondence preserves the full original edge arrows. -/
theorem solutionEquiv_edge (S : Solution (T)) {i j : K.Vertex} (e : K.Edge i j) :
    upperReselectedEdgeLift data.lift
      (solutionEquiv data s alignment comm bijective central S).1 e =
        (selectedUpper K _ _ (T).original S.choice).edgeLift e := by
  change (data.lift.edgeLift e).comp (CompositeFiberAut.hom
      ((compositeFiberEquiv _).symm (S.choice e))) = _
  rfl

/-- C's action is the same StrictEdgeReselection on original geometry edges. -/
theorem solutionAction_edge (z : Z1 (T).toTower.localCoefficients) (S : Solution (T))
    {i j : K.Vertex} (e : K.Edge i j) :
    (solutionEquiv data s alignment comm bijective central ((T).solutionAction z S)).1 i j e =
      innerFiberInclusion _
        (strictGauge data s alignment comm bijective central z.1 i j e) *
      (solutionEquiv data s alignment comm bijective central S).1 i j e := by
  apply (compositeFiberEquiv _).injective
  rw [map_mul]
  change ((T).solutionAction z S).choice e =
      kernelInclusion (geometryProjection U) (packageProjection U)
        (data.lift.geometry j) (Additive.toMul (z.1 ⟨i, j, e⟩)) * S.choice e
  exact (T).solutionAction_edge z S e

/-- C1 returns to the two original full geometry automorphisms at the edge's endpoints. -/
theorem vertexGauge_edge (b : C0 (T).toTower.localCoefficients) (S : Solution (T))
    {i j : K.Vertex} (e : K.Edge i j) :
    upperReselectedEdgeLift data.lift
      (solutionEquiv data s alignment comm bijective central ((T).vertexGauge b S)).1 e =
      ((CompositeFiberAut.hom (innerFiberInclusion _
        ((innerKernelEquiv _).symm (Additive.toMul (-(b i)))))).comp
        (upperReselectedEdgeLift data.lift
          (solutionEquiv data s alignment comm bijective central S).1 e)).comp
      (CompositeFiberAut.hom (innerFiberInclusion _
        ((innerKernelEquiv _).symm (Additive.toMul (b j))))) := by
  rw [solutionEquiv_edge, solutionEquiv_edge]
  exact (T).vertexGauge_edge_arrow b S e

/-- The obstruction of the same AAT section vanishes exactly when it is coherentizable. -/
theorem obstructionClass_zero_iff (hs : UpperSyzygyCompatible data s.lift) :
    (T).toTower.obstructionClass (syzygy data s alignment comm bijective central hs) = 0 ↔
      SectionRelativeCoherentizable data s :=
  ((T).obstructionClass_eq_zero_iff_solution _).trans
    (solution_nonempty_iff data s alignment comm bijective central)

end AAT.AG.AbelianLiftingObstruction.CrossStage

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.CrossStage
