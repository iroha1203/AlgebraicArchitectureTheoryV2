import ResearchLean.AG.RelativeRepairComposition.RestrictedPresentation

/-!
# Restriction of the original tower, actual defects, repairs and morphisms

G-130 A / n1017 §2.1–2.2: construct the same original categorical tower on a
closed presentation, preserving its full kernels, transports, core, reference
lifts and comparators. Actual defect, correction, reconstruction and every
original vertex reidentification restrict through the same native functors.

## Implementation notes

All inherited hypotheses come from the same original arrows. Strong uniqueness
compares canonical face and whole fiber transport, then authored route values
restrict step by step. Actual repair and supported equation restrictions are
constructed separately and their coordinate and restoration functors agree on
objects and all morphism labels. Fixed names are pulled back along the original
edge bijection, so candidate range relaxation uses exactly those same names.
-/

namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
namespace ClosedRegion
variable (U : ClosedRegion K)
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]

/-- G-130 A: full original tower with the same core, lifts and comparators. -/
noncomputable def restrictTower {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) : OriginalTowerPresentation (presentation U) p q where
  original := restrictLiftData U T.original
  originalLowerStrong e := T.originalLowerStrong e.1
  core e := T.core e.1
  lift e := T.lift e.1
  lift_core e := T.lift_core e.1
  faceBase f := by
    change (restrictLiftData U T.original).pathBase ((twoPresentation U).twoLeft f) =
      (restrictLiftData U T.original).pathBase ((twoPresentation U).twoRight f)
    rw [restrict_path_base, restrict_path_base, forget_two_left, forget_two_right]
    exact T.faceBase f.1
  comparator f := T.comparator f.1
  coreAlignment f := by
    change p.map ((restrictLiftData U (selectedUpper K p q T.original T.lift)).pathLift
      ((twoPresentation U).twoLeft f)) ≫ p.map (FiberAut.hom (T.comparator f.1)) =
      p.map ((restrictLiftData U (selectedUpper K p q T.original T.lift)).pathLift
        ((twoPresentation U).twoRight f))
    rw [restrict_path_lift, restrict_path_lift, forget_two_left, forget_two_right]
    exact T.coreAlignment f.1
  kernelComm v := T.kernelComm v.1
  edgeBijective e := T.edgeBijective e.1
  comparatorCentralizes f := T.comparatorCentralizes f.1

/-- Restricting a tower generates precisely the restriction of its full actual kernels. -/
theorem restrict_tower_coefficients {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) :
    (restrictTower U T).toTower.localCoefficients =
      restrictCoefficients U T.toTower.localCoefficients := rfl

/-- G-130 A: the actual repair restricts with all its original edge choices. -/
noncomputable def restrictSolution {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (R : Solution T) : Solution (restrictTower U T) where
  choice e := R.choice e.1
  choice_core e := R.choice_core e.1
  face f := by
    change (restrictLiftData U (selectedUpper K p q T.original R.choice)).pathLift
      ((twoPresentation U).twoLeft f) ≫ FiberAut.hom (T.comparator f.1) =
      (restrictLiftData U (selectedUpper K p q T.original R.choice)).pathLift
        ((twoPresentation U).twoRight f)
    rw [restrict_path_lift, restrict_path_lift, forget_two_left, forget_two_right]
    exact R.face f.1

/-- Actual choice values survive restriction unchanged. -/
theorem restrict_solution_choice {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (R : Solution T)
    {i j : Vertex U} (e : Edge U i j) : (restrictSolution U T R).choice e = R.choice e.1 := rfl

/-- The actual-kernel correction is the same named edge value after restriction. -/
theorem restrict_solution_correction {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (R : Solution T) :
    (restrictTower U T).solutionCorrection (restrictSolution U T R) =
      nativeR1 U T.toTower.localCoefficients (T.solutionCorrection R) := rfl

/-- Correction reconstruction retains each original actual edge choice under restriction. -/
theorem restrict_correction_choice {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (h : AbelianLiftingObstruction.C1 T.toTower.localCoefficients)
    {i j : Vertex U} (e : Edge U i j) :
    (restrictTower U T).correctionChoice (nativeR1 U T.toTower.localCoefficients h) e =
      T.correctionChoice h e.1 := rfl

/-- The restricted selected upper paths are evaluations of the same original paths. -/
theorem restrict_selected_path_lift {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) {i j : Vertex U} (w : Path U i j) :
    (restrictTower U T).toTower.upper.pathLift w = T.toTower.upper.pathLift (forgetPath U w) :=
  restrict_path_lift U (selectedUpper K p q T.original T.lift) w

/-- The restricted canonical face comparison is the original strong comparison. -/
theorem restrict_canonical_face {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (f : (presentation U).TwoCell) :
    (restrictTower U T).toTower.canonicalFace f = T.toTower.canonicalFace f.1 := by
  apply FiberAut.ext_of_strong_fac
    (T.toTower.upper.pathLift (K.twoLeft f.1))
    (T.toTower.upper.pathLift_isStronglyCocartesian (K.twoLeft f.1))
  have hnew := canonicalFiberComparator_fac (p ⋙ q)
    ((restrictTower U T).toTower.upper.pathBase ((presentation U).twoLeft f))
    ((restrictTower U T).toTower.upper.pathLift ((presentation U).twoLeft f))
    ((restrictTower U T).toTower.upper.pathLift ((presentation U).twoRight f))
    ((restrictTower U T).toTower.upper.pathLift_isStronglyCocartesian ((presentation U).twoLeft f))
    (by rw [(restrictTower U T).toTower.faceBase f]
        exact (restrictTower U T).toTower.upper.pathLift_isStronglyCocartesian ((presentation U).twoRight f))
  change (restrictTower U T).toTower.upper.pathLift ((twoPresentation U).twoLeft f) ≫
    FiberAut.hom ((restrictTower U T).toTower.canonicalFace f) =
      (restrictTower U T).toTower.upper.pathLift ((twoPresentation U).twoRight f) at hnew
  rw [restrict_selected_path_lift, restrict_selected_path_lift, forget_two_left, forget_two_right] at hnew
  exact hnew.trans (canonicalFiberComparator_fac (p ⋙ q) _ _ _
    (T.toTower.upper.pathLift_isStronglyCocartesian (K.twoLeft f.1))
    (by rw [T.toTower.faceBase f.1]
        exact T.toTower.upper.pathLift_isStronglyCocartesian (K.twoRight f.1))).symm

/-- The full actual kernel defect is unchanged on each selected face. -/
theorem restrict_face_defect {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (f : (presentation U).TwoCell) :
    (restrictTower U T).toTower.faceDefect f = T.toTower.faceDefect f.1 := by
  apply kernelInclusion_injective p q _
  calc
    kernelInclusion p q _ ((restrictTower U T).toTower.faceDefect f) =
        (restrictTower U T).toTower.comparator f * ((restrictTower U T).toTower.canonicalFace f)⁻¹ :=
      (restrictTower U T).toTower.faceDefect_inclusion f
    _ = T.toTower.comparator f.1 * (T.toTower.canonicalFace f.1)⁻¹ := by
      rw [restrict_canonical_face]
      rfl
    _ = kernelInclusion p q _ (T.toTower.faceDefect f.1) :=
      (T.toTower.faceDefect_inclusion f.1).symm

/-- The actual defect cochain commutes with the same native restriction. -/
theorem restrict_defect {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) :
    (restrictTower U T).toTower.defect = nativeR2 U T.toTower.localCoefficients T.toTower.defect := by
  funext f
  exact congrArg Additive.ofMul (restrict_face_defect U T f)

/-- Actual vertex reidentification commutes with restriction on every original choice. -/
theorem restrict_vertex_gauge {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (b : AbelianLiftingObstruction.C0 T.toTower.localCoefficients)
    (R : Solution T) :
    restrictSolution U T (T.vertexGauge b R) =
      (restrictTower U T).vertexGauge (nativeR0 U T.toTower.localCoefficients b) (restrictSolution U T R) := by
  have hc : (restrictTower U T).solutionCorrection (restrictSolution U T (T.vertexGauge b R)) =
      (restrictTower U T).solutionCorrection
        ((restrictTower U T).vertexGauge (nativeR0 U T.toTower.localCoefficients b) (restrictSolution U T R)) := by
    rw [restrict_solution_correction, T.vertexGauge_correction, map_add,
      native_r_d0, (restrictTower U T).vertexGauge_correction, restrict_solution_correction]
    rfl
  apply Solution.ext
  intro i j e
  exact ((restrictTower U T).correctionChoice_solutionCorrection _ e).symm.trans
    ((congrArg (fun h => (restrictTower U T).correctionChoice h e) hc).trans
      ((restrictTower U T).correctionChoice_solutionCorrection _ e))

/-- Whole fiber automorphism transport is the same actual strong path after restriction. -/
theorem restrict_whisker {r : E ⥤ B}
    (L : LiftData K.toFiniteTransportTwoPresentation r) {i j : Vertex U}
    (a : FiberAut r (L.object i.1)) (w : Path U i j) :
    Arbitrary.whiskerFiberAut (restrictLiftData U L) 1 a w = Arbitrary.whiskerFiberAut L 1 a (forgetPath U w) := by
  apply FiberAut.ext_of_strong_fac (L.pathLift (forgetPath U w))
    (L.pathLift_isStronglyCocartesian (forgetPath U w))
  have hn := Arbitrary.whiskerFiberAut_fac (restrictLiftData U L) 1 a w
  have ho := Arbitrary.whiskerFiberAut_fac L 1 a (forgetPath U w)
  simp only [Arbitrary.fiberAutThenPath, Arbitrary.reselectedPathLift_one, restrict_path_lift] at hn ho
  exact hn.trans ho.symm

/-- Each authored face retains its actual comparator transported along its original suffix. -/
theorem restrict_authored_face {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) {i j : K.Vertex}
    (face : WhiskeredFace K.toFiniteTransportTwoPresentation i j)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices) (hf : face.cell ∈ U.faces)
    (hpre : pathEdges face.incoming ⊆ U.edges) (hpost : pathEdges face.outgoing ⊆ U.edges) :
    Arbitrary.orientedFaceComparator (restrictTower U T).toTower.toTransportData 1
      (Arbitrary.authoredComparatorFamily (restrictTower U T).toTower.toTransportData)
      (restrictWhiskeredFace U face hi hj hf hpre hpost) =
    Arbitrary.orientedFaceComparator T.toTower.toTransportData 1
      (Arbitrary.authoredComparatorFamily T.toTower.toTransportData) face := by
  cases face with
  | mk cell pre post orientation =>
    cases orientation <;>
      change Arbitrary.whiskerFiberAut (restrictLiftData U T.toTower.upper) 1 _
        (restrictPath U post _ hj hpost) = Arbitrary.whiskerFiberAut T.toTower.upper 1 _ post
    all_goals rw [restrict_whisker, forget_restrict]
    all_goals rfl

/-- Every actual authored route comparator survives restriction in temporal order. -/
theorem restrict_authored_pasting {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) {i j : K.Vertex} {w z : K.Path i j}
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation w z)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hb : pathEdges w ⊆ U.edges) (hz : pathEdges z ⊆ U.edges)
    (hf : pastingFaces pasting ⊆ U.faces) (hc : pastingContextEdges pasting ⊆ U.edges) :
    Arbitrary.authoredPastingComparator (restrictTower U T).toTower.toTransportData 1
      (restrictPasting U pasting hi hj hb hz hf hc) =
    Arbitrary.authoredPastingComparator T.toTower.toTransportData 1 pasting := by
  induction pasting with
  | nil w => simp only [Arbitrary.authoredPastingComparator, restrictPasting, Arbitrary.pastingComparator]
  | cons step tail ih =>
    simp only [Arbitrary.authoredPastingComparator] at ih ⊢
    simp only [restrictPasting, Arbitrary.pastingComparator, restrictStep, restrict_authored_face, ih]

/-- Original three-cell authored coherence restricts from the same two actual routes. -/
theorem restrict_authored_syzygy {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q)
    (hsyzygy : ∀ s : K.ThreeCell, Arbitrary.AuthoredSyzygy T.toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s)) :
    ∀ t : (presentation U).ThreeCell, Arbitrary.AuthoredSyzygy (restrictTower U T).toTower.toTransportData 1
      ((presentation U).threeLeft t) ((presentation U).threeRight t) := by
  intro t
  change Arbitrary.authoredPastingComparator (restrictTower U T).toTower.toTransportData 1
      (restrictPasting U (K.threeLeft t.1) _ _ _ _ _ _) =
    Arbitrary.authoredPastingComparator (restrictTower U T).toTower.toTransportData 1
      (restrictPasting U (K.threeRight t.1) _ _ _ _ _ _)
  rw [restrict_authored_pasting, restrict_authored_pasting]
  exact hsyzygy t.1

/-- Fixed original vertex names selected by the closed region. -/
def restrictedVertices (vertices : Set K.Vertex) : Set (presentation U).Vertex :=
  {v | v.1 ∈ vertices}

/-- Fixed original edge names selected by the closed region. -/
def restrictedEdges (fixed : Set (EdgeName (K := K))) : Set (EdgeName (K := presentation U)) :=
  {e | (edgeNameEquiv U e).1 ∈ fixed}

/-- Range fixing commutes with selection of the same part and candidate names. -/
theorem restricted_fixed_range (part candidates allowed : Set (EdgeName (K := K))) :
    restrictedEdges U (fixedEdgesForRange part candidates allowed) =
      fixedEdgesForRange (restrictedEdges U part) (restrictedEdges U candidates) (restrictedEdges U allowed) := rfl

/-- Restriction preserves each independently fixed actual edge of a supported repair. -/
noncomputable def restrictRepair {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (fixed : Set (EdgeName (K := K)))
    (R : SupportedRepair T fixed) : SupportedRepair (restrictTower U T) (restrictedEdges U fixed) :=
  ⟨restrictSolution U T R.1, fun e he => R.2 (edgeNameEquiv U e).1 he⟩

/-- Every original permitted gauge label restricts by its same values and coboundary. -/
noncomputable def restrictGaugeLabel {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    supportedC0 T vertices fixed →+
      supportedC0 (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed) where
  toFun b := ⟨nativeR0 U T.toTower.localCoefficients b.1, by
    apply (mem_supportedC0 (restrictTower U T) _ _ _).mpr
    constructor
    · intro v hv
      exact supportedC0_vertex_zero T vertices fixed b v.1 hv
    · apply (mem_supportedC1 (restrictTower U T) _ _).mpr
      intro e he
      exact (mem_supportedC1 T fixed _).mp (supportedC0_d0_mem T vertices fixed b)
        (edgeNameEquiv U e).1 he⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Native gauge restriction retains the value of every selected original vertex. -/
theorem restrict_gauge_label_val {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) :
    (restrictGaugeLabel U T vertices fixed b).1 = nativeR0 U T.toTower.localCoefficients b.1 := rfl

/-- Supported repair restriction commutes with the same actual vertex reidentification. -/
theorem restrict_repair_gauge {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : SupportedRepair T fixed) :
    restrictRepair U T fixed (repairGauge T vertices fixed b R) =
      repairGauge (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed)
        (restrictGaugeLabel U T vertices fixed b) (restrictRepair U T fixed R) :=
  Subtype.ext (restrict_vertex_gauge U T b.1 R.1)

/-- G-130 A: native restriction maps every actual repair and its full original gauge label. -/
noncomputable def repairRestrictionFunctor {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    RepairGroupoid T vertices fixed ⥤
      RepairGroupoid (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed) where
  obj R := (restrictRepair U T fixed R.back :
    RepairGroupoid (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed))
  map {R _} b := ⟨Multiplicative.ofAdd (restrictGaugeLabel U T vertices fixed b.1.toAdd),
    (restrict_repair_gauge U T vertices fixed b.1.toAdd R.back).symm.trans
      (congrArg (restrictRepair U T fixed) b.2)⟩
  map_id _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))
  map_comp _ _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))

/-- Every restricted native morphism retains each selected original vertex value. -/
theorem repair_restriction_map_label {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    {R Q : RepairGroupoid T vertices fixed} (b : R ⟶ Q) :
    ((repairRestrictionFunctor U T vertices fixed).map b).1.toAdd.1 =
      nativeR0 U T.toTower.localCoefficients b.1.toAdd.1 := rfl

/-- Each restricted repair keeps the same original edge choice. -/
theorem repair_restriction_obj_choice {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (R : RepairGroupoid T vertices fixed) {i j : Vertex U} (e : Edge U i j) :
    ((repairRestrictionFunctor U T vertices fixed).obj R).back.1.choice e = R.back.1.choice e.1 := rfl

/-- Actual repair coordinates commute with the same selected edge restriction. -/
theorem restrict_repair_coord {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (fixed : Set (EdgeName (K := K))) (R : SupportedRepair T fixed) :
    (repairCoord (restrictTower U T) (restrictedEdges U fixed) (restrictRepair U T fixed R)).1.1 =
      nativeR1 U T.toTower.localCoefficients (repairCoord T fixed R).1.1 := rfl

/-- Restrict an independent supported equation using the same differential and actual defect. -/
noncomputable def restrictCorrection {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (fixed : Set (EdgeName (K := K)))
    (h : SupportedCorrection T fixed) :
    SupportedCorrection (restrictTower U T) (restrictedEdges U fixed) :=
  ⟨⟨nativeR1 U T.toTower.localCoefficients h.1.1, by
    apply (mem_supportedC1 (restrictTower U T) _ _).mpr
    intro e he
    exact (mem_supportedC1 T fixed h.1.1).mp h.1.2 (edgeNameEquiv U e).1 he⟩, by
      have hc := (native_r_d1 U T.toTower.localCoefficients h.1.1).symm.trans
        (congrArg (nativeR2 U T.toTower.localCoefficients) h.2)
      rw [map_neg, ← restrict_defect] at hc
      exact hc⟩

/-- Actual supported coordinates commute as whole supported equations. -/
theorem restrict_coord {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (fixed : Set (EdgeName (K := K))) (R : SupportedRepair T fixed) :
    repairCoord (restrictTower U T) (restrictedEdges U fixed) (restrictRepair U T fixed R) =
      restrictCorrection U T fixed (repairCoord T fixed R) := by
  apply Subtype.ext
  apply Subtype.ext
  exact restrict_repair_coord U T fixed R

/-- Restoration of every supported equation commutes with the same actual repair restriction. -/
theorem restrict_rec {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (fixed : Set (EdgeName (K := K))) (h : SupportedCorrection T fixed) :
    restrictRepair U T fixed (repairRec T fixed h) =
      repairRec (restrictTower U T) (restrictedEdges U fixed) (restrictCorrection U T fixed h) := by
  apply (repairEquiv (restrictTower U T) (restrictedEdges U fixed)).injective
  change repairCoord (restrictTower U T) (restrictedEdges U fixed) _ =
    repairCoord (restrictTower U T) (restrictedEdges U fixed) _
  rw [restrict_coord, repairCoord_rec, repairCoord_rec]

/-- Correction restriction retains every original edge coordinate. -/
theorem restrict_correction_val {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (fixed : Set (EdgeName (K := K))) (h : SupportedCorrection T fixed) :
    (restrictCorrection U T fixed h).1.1 = nativeR1 U T.toTower.localCoefficients h.1.1 := rfl

/-- Restriction commutes with the direct coboundary action on supported equations. -/
theorem restrict_correction_gauge {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (h : SupportedCorrection T fixed) :
    restrictCorrection U T fixed (correctionGauge T vertices fixed b h) =
      correctionGauge (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed)
        (restrictGaugeLabel U T vertices fixed b) (restrictCorrection U T fixed h) := by
  apply Subtype.ext
  apply Subtype.ext
  change nativeR1 U T.toTower.localCoefficients (h.1.1 + d0 T.toTower.localCoefficients b.1) =
    nativeR1 U T.toTower.localCoefficients h.1.1 +
      d0 (restrictCoefficients U T.toTower.localCoefficients) (nativeR0 U T.toTower.localCoefficients b.1)
  rw [map_add, native_r_d0]

/-- The native correction restriction retains each restricted original gauge label. -/
noncomputable def correctionRestrictionFunctor {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    CorrectionGroupoid T vertices fixed ⥤
      CorrectionGroupoid (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed) where
  obj h := (restrictCorrection U T fixed h.back :
    CorrectionGroupoid (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed))
  map {h _} b := ⟨Multiplicative.ofAdd (restrictGaugeLabel U T vertices fixed b.1.toAdd),
    (restrict_correction_gauge U T vertices fixed b.1.toAdd h.back).symm.trans
      (congrArg (restrictCorrection U T fixed) b.2)⟩
  map_id _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))
  map_comp _ _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))

/-- Coordinate restriction is an equality of native functors, on both objects and morphisms. -/
theorem coord_restriction_functors {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    repairRestrictionFunctor U T vertices fixed ⋙
      coordFunctor (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed) =
    coordFunctor T vertices fixed ⋙ correctionRestrictionFunctor U T vertices fixed := rfl

/-- Restoration restriction is an equality of native functors, on both objects and morphisms. -/
theorem rec_restriction_functors {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    correctionRestrictionFunctor U T vertices fixed ⋙
      recFunctor (restrictTower U T) (restrictedVertices U vertices) (restrictedEdges U fixed) =
    recFunctor T vertices fixed ⋙ repairRestrictionFunctor U T vertices fixed := rfl

/-- The full actual corrected defect, even for an arbitrary correction, restricts naturally. -/
theorem restrict_corrected_defect {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (h : AbelianLiftingObstruction.C1 T.toTower.localCoefficients) :
    (restrictTower U T).toTower.correctedDefect (nativeR1 U T.toTower.localCoefficients h) =
      nativeR2 U T.toTower.localCoefficients (T.toTower.correctedDefect h) := by
  rw [TowerPresentation.correctedDefect_eq, TowerPresentation.correctedDefect_eq,
    map_add, restrict_defect, native_r_d1]
  rfl

/-- Selecting original fixed edge names preserves inclusions. -/
theorem restricted_edges_mono {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger) :
    restrictedEdges U fixed ⊆ restrictedEdges U larger := fun _ he => h he

/-- Generic relaxation of fixed actual edges retains every original repair and gauge value. -/
noncomputable def repairRelaxationFunctor {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger) :
    RepairGroupoid T vertices larger ⥤ RepairGroupoid T vertices fixed where
  obj R := (repairInclusion T h R.back : RepairGroupoid T vertices fixed)
  map {R _} b := ⟨Multiplicative.ofAdd (gaugeInclusion T vertices h b.1.toAdd),
    (gauge_inclusion T vertices h b.1.toAdd R.back).symm.trans
      (congrArg (repairInclusion T h) b.2)⟩
  map_id _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))
  map_comp _ _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))

/-- Closed-region restriction and range relaxation commute as complete native functors. -/
theorem repair_restriction_relaxation {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger) :
    repairRestrictionFunctor U T vertices larger ⋙
      repairRelaxationFunctor (restrictTower U T) (restrictedVertices U vertices) (restricted_edges_mono U h) =
    repairRelaxationFunctor T vertices h ⋙ repairRestrictionFunctor U T vertices fixed := rfl

/-- Every relaxed native morphism retains its whole original vertex label. -/
theorem repair_relaxation_map_label {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger)
    {R Q : RepairGroupoid T vertices larger} (b : R ⟶ Q) :
    ((repairRelaxationFunctor T vertices h).map b).1.toAdd.1 = b.1.toAdd.1 := rfl

end ClosedRegion
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
