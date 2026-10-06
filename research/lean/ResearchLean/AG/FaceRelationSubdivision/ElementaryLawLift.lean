import ResearchLean.AG.FaceRelationSubdivision.LawLiftVariation
import ResearchLean.AG.FaceRelationSubdivision.TriangleLift
import ResearchLean.AG.FaceRelationSubdivision.SubdivisionLift
import ResearchLean.AG.FaceRelationSubdivision.ElementaryLawMaps

/-!
# 指定持ち上げの同じ独立Law射と読み戻し

## Implementation notes

指定された旧辺の二つの道を結ぶ原始tとliftedS1/2を直接Law座標化する。
一般variationへの等号をraw有限和で放電し、標準homotopyと旧H1へ接続する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}

namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

omit [Fintype Source] in
/-- 指定された新sectionの端点chain式は原始t補正から生成。 -/
theorem liftedS_comm01 : (TargetSupportedNerve.rawD1 (supported N e)).raw.comp (liftedS1 N e).raw =
    (s0 N e).raw.comp (TargetSupportedNerve.rawD1 N).raw := by
  rw [liftedS1_raw]
  simpa only [SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp] using
    lawLift_raw_comm01 (s0 N e) (s1 N e) (s_comm01 N e) (liftT N e)
omit [Fintype Source] in
/-- 指定された新sectionの面chain式も同じ原始有限和。 -/
theorem liftedS_comm12 : (TargetSupportedNerve.rawD2 (supported N e)).raw.comp (liftedS2 N e).raw =
    (liftedS1 N e).raw.comp (TargetSupportedNerve.rawD2 N).raw := by
  rw [liftedS1_raw, liftedS2_raw]
  simpa only [SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp] using
    lawLift_raw_comm12 (s1 N e) (s2 N e) (s_comm12 N e) (liftT N e)

/-- 指定原始道の新sectionを独立Law有限和として生成。 -/
def liftedLawS := lawFiniteHom (s0 N e) (liftedS1 N e) (liftedS2 N e)
  (liftedS_comm01 N e) (liftedS_comm12 N e) laws ha
/-- 新sectionの同じ次数0有限和。 -/
@[simp] theorem liftedLawS_f0 : (liftedLawS N e laws ha).f0 = (s0 N e).lawDual laws ha := rfl
/-- 新sectionの同じ次数1有限和。 -/
@[simp] theorem liftedLawS_f1 : (liftedLawS N e laws ha).f1 = (liftedS1 N e).lawDual laws ha := rfl
/-- 新sectionの同じ次数2有限和。 -/
@[simp] theorem liftedLawS_f2 : (liftedLawS N e laws ha).f2 = (liftedS2 N e).lawDual laws ha := rfl

/-- 同じ旧sectionの独立有限和式を全三成分で照合する。 -/
theorem sLawFiniteHom_eq : lawFiniteHom (s0 N e) (s1 N e) (s2 N e)
    (s_comm01 N e) (s_comm12 N e) laws ha = lawS N e laws ha := by
  apply cochain_ext
  · rw [lawFiniteHom_f0, lawS_f0]
  · rw [lawFiniteHom_f1, lawS_f1]
  · rw [lawFiniteHom_f2, lawS_f2]

/-- 指定原始新sectionは同じtから生成した一般variationに一致。 -/
theorem liftedLawS_eq_variation : liftedLawS N e laws ha =
    lawLiftHom (s0 N e) (s1 N e) (s2 N e) (s_comm01 N e) (s_comm12 N e) (liftT N e) laws ha := by
  apply cochain_ext
  · rw [liftedLawS_f0, lawLiftHom_f0]
  · rw [liftedLawS_f1, lawLiftHom_f1]
    apply SupportedBasisMap.lawDual_eq_of_raw_eq
    rw [liftedS1_raw, SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp]
  · rw [liftedLawS_f2, lawLiftHom_f2]
    apply SupportedBasisMap.lawDual_eq_of_raw_eq
    rw [liftedS2_raw, SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp]

omit [Fintype Source] in
/-- 同じ指定原始有限和の支持選択は既存lifted収縮の同じsection Hom。 -/
theorem liftedSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom (s0 N e) (liftedS1 N e) (liftedS2 N e)
      (liftedS_comm01 N e) (liftedS_comm12 N e) A = (liftedContraction N e A).sHom := by
  apply cochain_ext
  · rw [subsetFiniteHom_f0, SubsetChainContraction.sHom_f0, liftedContraction_eq,
      SubsetChainContraction.varyLift_s0, chainContraction_s0]
  · rw [subsetFiniteHom_f1, SubsetChainContraction.sHom_f1, liftedContraction_s1]
  · rw [subsetFiniteHom_f2, SubsetChainContraction.sHom_f2, liftedContraction_s2]

/-- 同じ指定原始有限和によるLaw Homの構成式。 -/
@[simp] theorem liftedLawS_eq_finite : liftedLawS N e laws ha =
    lawFiniteHom (s0 N e) (liftedS1 N e) (liftedS2 N e)
      (liftedS_comm01 N e) (liftedS_comm12 N e) laws ha := rfl

/-- 同じ指定Law sectionは全三成分で同じ実fiber読み戻しへ着地。 -/
theorem liftedLawS_fiber (l : LawValueLabel laws) :
    cochainComp (liftedLawS N e laws ha) (lawFiberHom laws ha N l) =
      cochainComp (lawFiberHom laws ha (supported N e) l)
        (liftedContraction N e (labelValueFiber laws q ha l)).sHom := by
  rw [liftedLawS_eq_finite]
  have h := lawFiniteFiber_square (s0 N e) (liftedS1 N e) (liftedS2 N e)
    (liftedS_comm01 N e) (liftedS_comm12 N e) laws ha l
  rw [liftedSubsetFiniteHom_eq] at h
  exact h

/-- 同じ指定Law sectionの旧H1商も同じ実fiberの読み戻しと可換。 -/
theorem liftedLawS_h1_fiber (l : LawValueLabel laws) :
    (lawFiberHom laws ha N l).h1Map.comp (liftedLawS N e laws ha).h1Map =
      (liftedContraction N e (labelValueFiber laws q ha l)).sHom.h1Map.comp
        (lawFiberHom laws ha (supported N e) l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map (liftedLawS_fiber N e laws ha l)
  simpa only [cochainComp_h1Map] using h

/-- 指定された同じ二つの実Law sectionを結ぶ標準ホモトピー。 -/
def liftedLawHomotopy : Homotopy (zeroExtensionMap (liftedLawS N e laws ha))
    (zeroExtensionMap (lawS N e laws ha)) := by
  rw [liftedLawS_eq_variation, ← sLawFiniteHom_eq]
  exact lawLiftHomotopy _ _ _ (s_comm01 N e) (s_comm12 N e) (liftT N e) laws ha
/-- 指定持ち上げは全整数次数で同じ実Law読み戻しを与える。 -/
theorem liftedLawS_homologyMap (n : ℤ) :
    HomologicalComplex.homologyMap (zeroExtensionMap (liftedLawS N e laws ha)) n =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawS N e laws ha)) n :=
  (liftedLawHomotopy N e laws ha).homologyMap_eq n
/-- 指定持ち上げは同じ既存H1商の読み戻しを与える。 -/
theorem liftedLawS_h1Map : (liftedLawS N e laws ha).h1Map = (lawS N e laws ha).h1Map := by
  rw [liftedLawS_eq_variation, lawLiftHom_h1Map, sLawFiniteHom_eq]

end TriangleAddition

namespace EdgeSubdivision
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent) (o : Occurrence N e)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

omit [Fintype Source] in
/-- 指定された新sectionの端点chain式は原始t補正から生成。 -/
theorem liftedS_comm01 : (TargetSupportedNerve.rawD1 (supported N e)).raw.comp (liftedS1 N e o).raw =
    (s0 N e).raw.comp (TargetSupportedNerve.rawD1 N).raw := by
  rw [liftedS1_raw]
  simpa only [SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp] using
    lawLift_raw_comm01 (s0 N e) (s1 N e) (s_comm01 N e) (liftT N e o)
omit [Fintype Source] in
/-- 指定された新sectionの面chain式も同じ原始有限和。 -/
theorem liftedS_comm12 : (TargetSupportedNerve.rawD2 (supported N e)).raw.comp (liftedS2 N e o).raw =
    (liftedS1 N e o).raw.comp (TargetSupportedNerve.rawD2 N).raw := by
  rw [liftedS1_raw, liftedS2_raw]
  simpa only [SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp] using
    lawLift_raw_comm12 (s1 N e) (s2 N e) (s_comm12 N e) (liftT N e o)

/-- 指定原始道の新sectionを独立Law有限和として生成。 -/
def liftedLawS := lawFiniteHom (s0 N e) (liftedS1 N e o) (liftedS2 N e o)
  (liftedS_comm01 N e o) (liftedS_comm12 N e o) laws ha
/-- 新sectionの同じ次数0有限和。 -/
@[simp] theorem liftedLawS_f0 : (liftedLawS N e o laws ha).f0 = (s0 N e).lawDual laws ha := rfl
/-- 新sectionの同じ次数1有限和。 -/
@[simp] theorem liftedLawS_f1 : (liftedLawS N e o laws ha).f1 = (liftedS1 N e o).lawDual laws ha := rfl
/-- 新sectionの同じ次数2有限和。 -/
@[simp] theorem liftedLawS_f2 : (liftedLawS N e o laws ha).f2 = (liftedS2 N e o).lawDual laws ha := rfl

/-- 同じ旧sectionの独立有限和式を全三成分で照合する。 -/
theorem sLawFiniteHom_eq : lawFiniteHom (s0 N e) (s1 N e) (s2 N e)
    (s_comm01 N e) (s_comm12 N e) laws ha = lawS N e laws ha := by
  apply cochain_ext
  · rw [lawFiniteHom_f0, lawS_f0]
  · rw [lawFiniteHom_f1, lawS_f1]
  · rw [lawFiniteHom_f2, lawS_f2]

/-- 指定原始新sectionは同じtから生成した一般variationに一致。 -/
theorem liftedLawS_eq_variation : liftedLawS N e o laws ha =
    lawLiftHom (s0 N e) (s1 N e) (s2 N e) (s_comm01 N e) (s_comm12 N e) (liftT N e o) laws ha := by
  apply cochain_ext
  · rw [liftedLawS_f0, lawLiftHom_f0]
  · rw [liftedLawS_f1, lawLiftHom_f1]
    apply SupportedBasisMap.lawDual_eq_of_raw_eq
    rw [liftedS1_raw, SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp]
  · rw [liftedLawS_f2, lawLiftHom_f2]
    apply SupportedBasisMap.lawDual_eq_of_raw_eq
    rw [liftedS2_raw, SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp]

omit [Fintype Source] in
/-- 同じ指定原始有限和の支持選択は既存lifted収縮の同じsection Hom。 -/
theorem liftedSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom (s0 N e) (liftedS1 N e o) (liftedS2 N e o)
      (liftedS_comm01 N e o) (liftedS_comm12 N e o) A = (liftedContraction N e o A).sHom := by
  apply cochain_ext
  · rw [subsetFiniteHom_f0, SubsetChainContraction.sHom_f0, liftedContraction_eq,
      SubsetChainContraction.varyLift_s0, chainContraction_s0]
  · rw [subsetFiniteHom_f1, SubsetChainContraction.sHom_f1, liftedContraction_s1]
  · rw [subsetFiniteHom_f2, SubsetChainContraction.sHom_f2, liftedContraction_s2]

/-- 同じ指定原始有限和によるLaw Homの構成式。 -/
@[simp] theorem liftedLawS_eq_finite : liftedLawS N e o laws ha =
    lawFiniteHom (s0 N e) (liftedS1 N e o) (liftedS2 N e o)
      (liftedS_comm01 N e o) (liftedS_comm12 N e o) laws ha := rfl

/-- 同じ指定Law sectionは全三成分で同じ実fiber読み戻しへ着地。 -/
theorem liftedLawS_fiber (l : LawValueLabel laws) :
    cochainComp (liftedLawS N e o laws ha) (lawFiberHom laws ha N l) =
      cochainComp (lawFiberHom laws ha (supported N e) l)
        (liftedContraction N e o (labelValueFiber laws q ha l)).sHom := by
  rw [liftedLawS_eq_finite]
  have h := lawFiniteFiber_square (s0 N e) (liftedS1 N e o) (liftedS2 N e o)
    (liftedS_comm01 N e o) (liftedS_comm12 N e o) laws ha l
  rw [liftedSubsetFiniteHom_eq] at h
  exact h

/-- 同じ指定Law sectionの旧H1商も同じ実fiberの読み戻しと可換。 -/
theorem liftedLawS_h1_fiber (l : LawValueLabel laws) :
    (lawFiberHom laws ha N l).h1Map.comp (liftedLawS N e o laws ha).h1Map =
      (liftedContraction N e o (labelValueFiber laws q ha l)).sHom.h1Map.comp
        (lawFiberHom laws ha (supported N e) l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map (liftedLawS_fiber N e o laws ha l)
  simpa only [cochainComp_h1Map] using h

/-- 指定された同じ二つの実Law sectionを結ぶ標準ホモトピー。 -/
def liftedLawHomotopy : Homotopy (zeroExtensionMap (liftedLawS N e o laws ha))
    (zeroExtensionMap (lawS N e laws ha)) := by
  rw [liftedLawS_eq_variation, ← sLawFiniteHom_eq]
  exact lawLiftHomotopy _ _ _ (s_comm01 N e) (s_comm12 N e) (liftT N e o) laws ha
/-- 指定持ち上げは全整数次数で同じ実Law読み戻しを与える。 -/
theorem liftedLawS_homologyMap (n : ℤ) :
    HomologicalComplex.homologyMap (zeroExtensionMap (liftedLawS N e o laws ha)) n =
      HomologicalComplex.homologyMap (zeroExtensionMap (lawS N e laws ha)) n :=
  (liftedLawHomotopy N e o laws ha).homologyMap_eq n
/-- 指定持ち上げは同じ既存H1商の読み戻しを与える。 -/
theorem liftedLawS_h1Map : (liftedLawS N e o laws ha).h1Map = (lawS N e laws ha).h1Map := by
  rw [liftedLawS_eq_variation, lawLiftHom_h1Map, sLawFiniteHom_eq]

end EdgeSubdivision

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
