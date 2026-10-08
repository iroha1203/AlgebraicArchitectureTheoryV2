import ResearchLean.AG.AtlasCoefficientFiber.SupportDegenerate
import ResearchLean.AG.AtlasCoefficientFiber.Kappa

/-!
# G-135 D：原垂直・水平blockとB・D・Vの台包含

## Implementation notes

同じ細辺のnone分類を台包含前後で保ち、元の両射影を基底ごとに照合する。
混在面の原三辺微分を通してBとDの包含式を証明する。
混在閉路の包含を供給写像にする案は、原Bの核との接続を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 原水平辺も元のsome分類と同じ細辺名を保つ。 -/
def supportHorizontalEdgeInclude (e : HorizontalEdge M A) : HorizontalEdge M B :=
  ⟨supportCellInclude Nf.edgeSupport (fun _ ht => hab ht) e.1, e.2⟩
/-- 水平辺包含の元細辺は同じ支持セル包含。 -/
@[simp] theorem supportHorizontalEdgeInclude_val (e : HorizontalEdge M A) :
    (supportHorizontalEdgeInclude M hab e).1 =
      supportCellInclude Nf.edgeSupport (fun _ ht => hab ht) e.1 := rfl

/-- 水平辺自由chainの同じ名前付き基底包含。 -/
def supportHorizontalEdgeChainInclude : (HorizontalEdge M A →₀ ℚ) →ₗ[ℚ] (HorizontalEdge M B →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (supportHorizontalEdgeInclude M hab)
/-- 水平辺chain包含の全基底値。 -/
@[simp] theorem supportHorizontalEdgeChainInclude_single (e : HorizontalEdge M A) (r : ℚ) :
    supportHorizontalEdgeChainInclude M hab (Finsupp.single e r) =
      Finsupp.single (supportHorizontalEdgeInclude M hab e) r := Finsupp.mapDomain_single

/-- 原垂直射影と原支持chain包含は同じnone分類を保って可換。 -/
theorem supportVerticalEdgeProjection (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    verticalEdgeProjection M B (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x) =
      supportVerticalEdgeChainInclude M hab (verticalEdgeProjection M A x) := by
  have hh : (verticalEdgeProjection M B).comp (selectedInclude Nf.edgeSupport (fun _ ht => hab ht)) =
      (supportVerticalEdgeChainInclude M hab).comp (verticalEdgeProjection M A) := by
    apply Finsupp.lhom_ext
    intro e r
    change verticalEdgeProjection M B
      (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (Finsupp.single e r)) =
      supportVerticalEdgeChainInclude M hab (verticalEdgeProjection M A (Finsupp.single e r))
    rw [supportChainInclude_single]
    by_cases he : M.edgeMap e.1 = none
    · let v : VerticalEdge M A := ⟨e, he⟩
      change verticalEdgeProjection M B (Finsupp.single (supportVerticalEdgeInclude M hab v).1 r) =
        supportVerticalEdgeChainInclude M hab (verticalEdgeProjection M A (Finsupp.single v.1 r))
      rw [verticalEdgeProjection_single, verticalEdgeProjection_single, supportVerticalEdgeChainInclude_single]
    · let e' : HorizontalEdge M A := ⟨e, he⟩
      change verticalEdgeProjection M B (Finsupp.single (supportHorizontalEdgeInclude M hab e').1 r) =
        supportVerticalEdgeChainInclude M hab (verticalEdgeProjection M A (Finsupp.single e'.1 r))
      rw [verticalEdgeProjection_horizontal_single, verticalEdgeProjection_horizontal_single, map_zero]
  exact LinearMap.congr_fun hh x

/-- 原水平射影も同じsome分類と台包含に対して可換。 -/
theorem supportHorizontalEdgeProjection (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    horizontalEdgeProjection M B (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) x) =
      supportHorizontalEdgeChainInclude M hab (horizontalEdgeProjection M A x) := by
  have hh : (horizontalEdgeProjection M B).comp (selectedInclude Nf.edgeSupport (fun _ ht => hab ht)) =
      (supportHorizontalEdgeChainInclude M hab).comp (horizontalEdgeProjection M A) := by
    apply Finsupp.lhom_ext
    intro e r
    change horizontalEdgeProjection M B
      (selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (Finsupp.single e r)) =
      supportHorizontalEdgeChainInclude M hab (horizontalEdgeProjection M A (Finsupp.single e r))
    rw [supportChainInclude_single]
    by_cases he : M.edgeMap e.1 = none
    · let v : VerticalEdge M A := ⟨e, he⟩
      change horizontalEdgeProjection M B (Finsupp.single (supportVerticalEdgeInclude M hab v).1 r) =
        supportHorizontalEdgeChainInclude M hab (horizontalEdgeProjection M A (Finsupp.single v.1 r))
      rw [horizontalEdgeProjection_vertical_single, horizontalEdgeProjection_vertical_single, map_zero]
    · let e' : HorizontalEdge M A := ⟨e, he⟩
      change horizontalEdgeProjection M B (Finsupp.single (supportHorizontalEdgeInclude M hab e').1 r) =
        supportHorizontalEdgeChainInclude M hab (horizontalEdgeProjection M A (Finsupp.single e'.1 r))
      rw [horizontalEdgeProjection_single, horizontalEdgeProjection_single, supportHorizontalEdgeChainInclude_single]
  exact LinearMap.congr_fun hh x

/-- 原垂直辺の端点微分は同じ支持chart包含と可換。 -/
theorem supportVerticalEdgeBoundary (x : VerticalEdge M A →₀ ℚ) :
    verticalEdgeBoundary M B (supportVerticalEdgeChainInclude M hab x) =
      selectedInclude Nf.chartSupport (fun _ ht => hab ht) (verticalEdgeBoundary M A x) := by
  rw [verticalEdgeBoundary_apply, verticalEdgeBoundary_apply, supportVerticalEdgeChainInclude_inclusion]
  exact (LinearMap.congr_fun (supportChainInclude_boundary1 Nf (fun _ ht => hab ht))
    (verticalEdgeInclusion M A x)).symm

/-- 原混在行列Dは同じ原微分の垂直射影として台包含と可換。 -/
theorem supportMixedVerticalBoundary (x : MixedFace M A →₀ ℚ) :
    mixedVerticalBoundary M B (supportMixedFaceChainInclude M hab x) =
      supportVerticalEdgeChainInclude M hab (mixedVerticalBoundary M A x) := by
  rw [mixedVerticalBoundary_apply, mixedVerticalBoundary_apply, supportMixedFaceChainInclude_inclusion]
  have hh := LinearMap.congr_fun (supportChainInclude_boundary2 Nf (fun _ ht => hab ht))
    (mixedFaceInclusion M A x)
  change selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (chainD2 Nf _ (mixedFaceInclusion M A x)) =
    chainD2 Nf _ (selectedInclude Nf.faceSupport (fun _ ht => hab ht) (mixedFaceInclusion M A x)) at hh
  exact (congrArg (verticalEdgeProjection M B) hh).symm.trans
    (supportVerticalEdgeProjection M hab (chainD2 Nf _ (mixedFaceInclusion M A x)))

/-- 原混在incidence行列Bは同じ原微分の水平射影として台包含と可換。 -/
theorem supportMixedHorizontalBoundary (x : MixedFace M A →₀ ℚ) :
    mixedHorizontalBoundary M B (supportMixedFaceChainInclude M hab x) =
      supportHorizontalEdgeChainInclude M hab (mixedHorizontalBoundary M A x) := by
  rw [mixedHorizontalBoundary_apply, mixedHorizontalBoundary_apply, supportMixedFaceChainInclude_inclusion]
  have hh := LinearMap.congr_fun (supportChainInclude_boundary2 Nf (fun _ ht => hab ht))
    (mixedFaceInclusion M A x)
  change selectedInclude Nf.edgeSupport (fun _ ht => hab ht) (chainD2 Nf _ (mixedFaceInclusion M A x)) =
    chainD2 Nf _ (selectedInclude Nf.faceSupport (fun _ ht => hab ht) (mixedFaceInclusion M A x)) at hh
  exact (congrArg (horizontalEdgeProjection M B) hh).symm.trans
    (supportHorizontalEdgeProjection M hab (chainD2 Nf _ (mixedFaceInclusion M A x)))

/-- 原ker Bの混在閉路を同じ混在面chain包含で含める。 -/
def supportMixedCyclesInclude : mixedCycles M A →ₗ[ℚ] mixedCycles M B :=
  ((supportMixedFaceChainInclude M hab).comp (mixedCycles M A).subtype).codRestrict _ (fun x => by
    change mixedHorizontalBoundary M B (supportMixedFaceChainInclude M hab x.1) = 0
    rw [supportMixedHorizontalBoundary, show mixedHorizontalBoundary M A x.1 = 0 from x.2, map_zero])

/-- 原ker B包含の値は同じ混在面chain包含。 -/
@[simp] theorem supportMixedCyclesInclude_val (x : mixedCycles M A) :
    (supportMixedCyclesInclude M hab x).1 = supportMixedFaceChainInclude M hab x.1 := rfl

/-- 原垂直閉路を同じ垂直辺chain包含で含める。 -/
def supportVerticalCyclesInclude : verticalCycles M A →ₗ[ℚ] verticalCycles M B :=
  ((supportVerticalEdgeChainInclude M hab).comp (verticalCycles M A).subtype).codRestrict _ (fun x => by
    change verticalEdgeBoundary M B (supportVerticalEdgeChainInclude M hab x.1) = 0
    rw [supportVerticalEdgeBoundary, show verticalEdgeBoundary M A x.1 = 0 from x.2, map_zero])

/-- 原垂直閉路包含の値は同じ垂直辺chain包含。 -/
@[simp] theorem supportVerticalCyclesInclude_val (x : verticalCycles M A) :
    (supportVerticalCyclesInclude M hab x).1 = supportVerticalEdgeChainInclude M hab x.1 := rfl

/-- 原ker B上のDyは同じ垂直閉路包含と全代表で可換。 -/
theorem supportMixedCycleToVertical (x : mixedCycles M A) :
    mixedCycleToVertical M B (supportMixedCyclesInclude M hab x) =
      supportVerticalCyclesInclude M hab (mixedCycleToVertical M A x) := by
  apply Subtype.ext
  rw [mixedCycleToVertical_val, supportMixedCyclesInclude_val,
    supportVerticalCyclesInclude_val, mixedCycleToVertical_val, supportMixedVerticalBoundary]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportHorizontalEdgeInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportHorizontalEdgeInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportHorizontalEdgeChainInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportHorizontalEdgeChainInclude_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalEdgeProjection
#print axioms AAT.AG.AtlasCoefficientFiber.supportHorizontalEdgeProjection
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalEdgeBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedVerticalBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedHorizontalBoundary
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedCyclesInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedCyclesInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalCyclesInclude
#print axioms AAT.AG.AtlasCoefficientFiber.supportVerticalCyclesInclude_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportMixedCycleToVertical
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
