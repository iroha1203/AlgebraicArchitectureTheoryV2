import ResearchLean.AG.FaceRelationSubdivision.ElementaryLawLift
import ResearchLean.AG.FaceRelationSubdivision.ElementaryLawHomotopy

/-!
# 原始h0補正による同じLaw cocycle代表

## Implementation notes

同じ原始hのLaw補正式をcocycleに適用し、実代表の差を同じd0境界として表示する。
旧H1類は既存boundaryToCyclesの実商で等号を証明する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}

namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じ原始h0補正はcocycleを同じr*s読み戻し代表に移す。 -/
theorem law_cocycle_normalize (z : ((supported N e).lawGeneratedComplex laws ha).C1)
    (hz : ((supported N e).lawGeneratedComplex laws ha).d1 z = 0) :
    z - ((supported N e).lawGeneratedComplex laws ha).d0 (lawH0 N e laws ha z) =
      (lawR N e laws ha).f1 ((lawS N e laws ha).f1 z) := by
  have hd1 : (supported N e).lawGeneratedD1 laws ha z = 0 := by
    simpa only [TargetSupportedNerve.lawGeneratedComplex_d1] using hz
  have h := law_correction1 N e laws ha z
  rw [hd1, map_zero, zero_add] at h
  rw [TargetSupportedNerve.lawGeneratedComplex_d0, lawR_f1, lawS_f1]
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

/-- 同じr*s cocycle代表は既存H1商で元の類に一致。 -/
theorem law_cocycle_readback_class
    (z : LinearMap.ker ((supported N e).lawGeneratedComplex laws ha).d1) :
    (lawR N e laws ha).h1Map ((lawS N e laws ha).h1Map
      ((LinearMap.range ((supported N e).lawGeneratedComplex laws ha).boundaryToCycles).mkQ z)) =
      (LinearMap.range ((supported N e).lawGeneratedComplex laws ha).boundaryToCycles).mkQ z := by
  rw [ThreeCochainComplex.Hom.h1Map_mk, ThreeCochainComplex.Hom.h1Map_mk]
  apply (Submodule.Quotient.eq _).2
  refine ⟨-lawH0 N e laws ha z.1, ?_⟩
  apply Subtype.ext
  simp only [ThreeCochainComplex.boundaryToCycles_apply, Submodule.coe_sub,
    ThreeCochainComplex.Hom.cyclesMap_apply]
  have h := law_cocycle_normalize N e laws ha z.1 z.2
  rw [map_neg]
  exact eq_sub_iff_add_eq.mpr (by simpa only [sub_eq_add_neg, add_comm] using h)

/-- 指定された別の道で読み戻しても同じ既存H1類を得る。 -/
theorem liftedLawS_readback_class
    (x : ((supported N e).lawGeneratedComplex laws ha).H1) :
    (lawR N e laws ha).h1Map ((liftedLawS N e laws ha).h1Map x) = x := by
  rw [liftedLawS_h1Map]
  refine Submodule.Quotient.induction_on _ x ?_
  intro z
  exact law_cocycle_readback_class N e laws ha z

end TriangleAddition

namespace EdgeSubdivision
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent) (o : Occurrence N e)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じ原始h0補正はcocycleを同じr*s読み戻し代表に移す。 -/
theorem law_cocycle_normalize (z : ((supported N e).lawGeneratedComplex laws ha).C1)
    (hz : ((supported N e).lawGeneratedComplex laws ha).d1 z = 0) :
    z - ((supported N e).lawGeneratedComplex laws ha).d0 (lawH0 N e laws ha z) =
      (lawR N e laws ha).f1 ((lawS N e laws ha).f1 z) := by
  have hd1 : (supported N e).lawGeneratedD1 laws ha z = 0 := by
    simpa only [TargetSupportedNerve.lawGeneratedComplex_d1] using hz
  have h := law_correction1 N e laws ha z
  rw [hd1, map_zero, zero_add] at h
  rw [TargetSupportedNerve.lawGeneratedComplex_d0, lawR_f1, lawS_f1]
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

/-- 同じr*s cocycle代表は既存H1商で元の類に一致。 -/
theorem law_cocycle_readback_class
    (z : LinearMap.ker ((supported N e).lawGeneratedComplex laws ha).d1) :
    (lawR N e laws ha).h1Map ((lawS N e laws ha).h1Map
      ((LinearMap.range ((supported N e).lawGeneratedComplex laws ha).boundaryToCycles).mkQ z)) =
      (LinearMap.range ((supported N e).lawGeneratedComplex laws ha).boundaryToCycles).mkQ z := by
  rw [ThreeCochainComplex.Hom.h1Map_mk, ThreeCochainComplex.Hom.h1Map_mk]
  apply (Submodule.Quotient.eq _).2
  refine ⟨-lawH0 N e laws ha z.1, ?_⟩
  apply Subtype.ext
  simp only [ThreeCochainComplex.boundaryToCycles_apply, Submodule.coe_sub,
    ThreeCochainComplex.Hom.cyclesMap_apply]
  have h := law_cocycle_normalize N e laws ha z.1 z.2
  rw [map_neg]
  exact eq_sub_iff_add_eq.mpr (by simpa only [sub_eq_add_neg, add_comm] using h)

/-- 指定された別の道で読み戻しても同じ既存H1類を得る。 -/
theorem liftedLawS_readback_class
    (x : ((supported N e).lawGeneratedComplex laws ha).H1) :
    (lawR N e laws ha).h1Map ((liftedLawS N e o laws ha).h1Map x) = x := by
  rw [liftedLawS_h1Map]
  refine Submodule.Quotient.induction_on _ x ?_
  intro z
  exact law_cocycle_readback_class N e laws ha z

end EdgeSubdivision

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
