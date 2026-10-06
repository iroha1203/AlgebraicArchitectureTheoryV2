import ResearchLean.AG.FaceRelationSubdivision.LawFiniteDifferential
import Formal.Util.AssertStandardAxioms

/-!
# 原始三成分有限和と同じ実Law・fiber Hom

## Implementation notes

chain式は汎用bridgeの方向仮定である。基本操作では原始r/s表の証明を渡す。
Law Homは独立座標有限和から作り、fiber Homの共役として定義しない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
variable {Nc Nf : ResolutionInvariance.TargetSupportedNerve q}
variable (M0 : SupportedBasisMap Nf.chartSupport Nc.chartSupport)
variable (M1 : SupportedBasisMap Nf.edgeSupport Nc.edgeSupport)
variable (M2 : SupportedBasisMap Nf.faceSupport Nc.faceSupport)
variable (h0 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw =
    M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
variable (h1 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw =
    M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw)

/-- 原始三成分の有限和を任意Aの同じ実subset Homへ送る。 -/
def subsetFiniteHom (A : Set q.Target) :
    ThreeCochainComplex.Hom (Nc.targetSubsetComplex A) (Nf.targetSubsetComplex A) :=
  dualSubsetHom A A (M0.selected A) (M1.selected A) (M2.selected A)
    (by
      have h := M1.selected_square_of_raw_square M0
        (TargetSupportedNerve.rawD1 Nf) (TargetSupportedNerve.rawD1 Nc) h0 A
      simpa only [TargetSupportedNerve.selected_rawD1] using h)
    (by
      have h := M2.selected_square_of_raw_square M1
        (TargetSupportedNerve.rawD2 Nf) (TargetSupportedNerve.rawD2 Nc) h1 A
      simpa only [TargetSupportedNerve.selected_rawD2] using h)

/-- 同じ有限和subset Homの次数0射。 -/
@[simp] theorem subsetFiniteHom_f0 (A) :
    (subsetFiniteHom M0 M1 M2 h0 h1 A).f0 = dualCellMap (M0.selected A) := rfl
/-- 同じ有限和subset Homの次数1射。 -/
@[simp] theorem subsetFiniteHom_f1 (A) :
    (subsetFiniteHom M0 M1 M2 h0 h1 A).f1 = dualCellMap (M1.selected A) := rfl
/-- 同じ有限和subset Homの次数2射。 -/
@[simp] theorem subsetFiniteHom_f2 (A) :
    (subsetFiniteHom M0 M1 M2 h0 h1 A).f2 = dualCellMap (M2.selected A) := rfl

variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 独立座標生成による同じ三成分の実Law Hom。 -/
def lawFiniteHom [Fintype Source] :
    ThreeCochainComplex.Hom (Nc.lawGeneratedComplex laws ha) (Nf.lawGeneratedComplex laws ha) where
  f0 := M0.lawDual laws ha
  f1 := M1.lawDual laws ha
  f2 := M2.lawDual laws ha
  comm0 z := by
    have h := M1.lawDual_square laws ha M0
      (TargetSupportedNerve.rawD1 Nf) (TargetSupportedNerve.rawD1 Nc) h0
    rw [lawDual_rawD1, lawDual_rawD1] at h
    simpa only [LinearMap.comp_apply, TargetSupportedNerve.lawGeneratedComplex_d0] using
      LinearMap.congr_fun h z
  comm1 z := by
    have h := M2.lawDual_square laws ha M1
      (TargetSupportedNerve.rawD2 Nf) (TargetSupportedNerve.rawD2 Nc) h1
    rw [lawDual_rawD2, lawDual_rawD2] at h
    simpa only [LinearMap.comp_apply, TargetSupportedNerve.lawGeneratedComplex_d1] using
      LinearMap.congr_fun h z

/-- 実Law Homの次数0は原始座標有限和そのもの。 -/
@[simp] theorem lawFiniteHom_f0 [Fintype Source] :
    (lawFiniteHom M0 M1 M2 h0 h1 laws ha).f0 = M0.lawDual laws ha := rfl
/-- 実Law Homの次数1は原始座標有限和そのもの。 -/
@[simp] theorem lawFiniteHom_f1 [Fintype Source] :
    (lawFiniteHom M0 M1 M2 h0 h1 laws ha).f1 = M1.lawDual laws ha := rfl
/-- 実Law Homの次数2は原始座標有限和そのもの。 -/
@[simp] theorem lawFiniteHom_f2 [Fintype Source] :
    (lawFiniteHom M0 M1 M2 h0 h1 laws ha).f2 = M2.lawDual laws ha := rfl

/-- 全Lawから同じlabel fiberの実cochain projection。 -/
def lawFiberHom [Fintype Source] (N : ResolutionInvariance.TargetSupportedNerve q)
    (l : LawValueLabel laws) :
    ThreeCochainComplex.Hom (N.lawGeneratedComplex laws ha)
      (N.targetSubsetComplex (labelValueFiber laws q ha l)) where
  f0 := lawFiberRead laws ha N.chartSupport l
  f1 := lawFiberRead laws ha N.edgeSupport l
  f2 := lawFiberRead laws ha N.faceSupport l
  comm0 z := by
    rw [N.lawGeneratedComplex_d0, N.targetSubsetComplex_d0]
    exact lawFiberRead_d0 N laws ha l z
  comm1 z := by
    rw [N.lawGeneratedComplex_d1, N.targetSubsetComplex_d1]
    exact lawFiberRead_d1 N laws ha l z

/-- 同じfiber projectionの次数0評価。 -/
@[simp] theorem lawFiberHom_f0 [Fintype Source] (N) (l) :
    (lawFiberHom laws ha N l).f0 = lawFiberRead laws ha N.chartSupport l := rfl
/-- 同じfiber projectionの次数1評価。 -/
@[simp] theorem lawFiberHom_f1 [Fintype Source] (N) (l) :
    (lawFiberHom laws ha N l).f1 = lawFiberRead laws ha N.edgeSupport l := rfl
/-- 同じfiber projectionの次数2評価。 -/
@[simp] theorem lawFiberHom_f2 [Fintype Source] (N) (l) :
    (lawFiberHom laws ha N l).f2 = lawFiberRead laws ha N.faceSupport l := rfl

/-- 全三成分で、独立Law有限和と同じ原始fiber比較は可換。 -/
theorem lawFiniteFiber_square [Fintype Source] (l : LawValueLabel laws) :
    cochainComp (lawFiniteHom M0 M1 M2 h0 h1 laws ha) (lawFiberHom laws ha Nf l) =
      cochainComp (lawFiberHom laws ha Nc l)
        (subsetFiniteHom M0 M1 M2 h0 h1 (labelValueFiber laws q ha l)) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    exact M0.lawDual_fiber laws ha l z
  · apply LinearMap.ext
    intro z
    exact M1.lawDual_fiber laws ha l z
  · apply LinearMap.ext
    intro z
    exact M2.lawDual_fiber laws ha l z

/-- 同じ実Homの正方形は既存H1商の同じ写像で可換。 -/
theorem lawFiniteFiber_h1_square [Fintype Source] (l : LawValueLabel laws) :
    (lawFiberHom laws ha Nf l).h1Map.comp (lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map =
      (subsetFiniteHom M0 M1 M2 h0 h1 (labelValueFiber laws q ha l)).h1Map.comp
        (lawFiberHom laws ha Nc l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map
    (lawFiniteFiber_square M0 M1 M2 h0 h1 laws ha l)
  simpa only [cochainComp_h1Map] using h

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
