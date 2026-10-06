import ResearchLean.AG.FaceRelationSubdivision.MixedLawFiniteCoordinates

/-!
# 混在reading有限和の実Law合成と加法

## Implementation notes

独立生成済みの有限和をSource座標へ読み、原始射の同じ等号を検査する。
全単射は検査の単射性に使い、Law射の定義を共役へ変更しない。
一般正方形の仮定は方向仮定であり、操作列では原始chain式から放電する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J L : Type u} {qi qj ql : Reading Source}
variable {si : I → Set qi.Target} {sj : J → Set qj.Target} {sl : L → Set ql.Target}
namespace SupportedBasisMap
variable (M : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj))
variable (laws : FiniteLawFamily Source) (hi : laws.Adequate qi) (hj : laws.Adequate qj)

/-- 原始射の等号は独立生成した同じ混在Law射の等号を与える。 -/
theorem mixedLawDual_eq_of_raw_eq
    (N : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj)) (h : M.raw = N.raw) :
    M.mixedLawDual laws hi hj = N.mixedLawDual laws hi hj := by
  apply LinearMap.ext
  intro z
  apply (sourceCoordinateRead laws hi si).injective
  rw [mixedLawDual_source, mixedLawDual_source, M.lawDual_eq_of_raw_eq (q := sourceReading Source) laws (sourceAdequate laws) N h]

/-- 原始直接合成の混在Law有限和は同じ二つの実射の合成。 -/
theorem mixedLawDual_comp (N : SupportedBasisMap (sourceSupport qj sj) (sourceSupport ql sl))
    (hl : laws.Adequate ql) :
    (M.comp N).mixedLawDual laws hi hl =
      (M.mixedLawDual laws hi hj).comp (N.mixedLawDual laws hj hl) := by
  apply LinearMap.ext
  intro z
  apply (sourceCoordinateRead laws hi si).injective
  rw [LinearMap.comp_apply, mixedLawDual_source, mixedLawDual_source, mixedLawDual_source,
    lawDual_comp, LinearMap.comp_apply]

/-- 原始和の混在Law座標化は同じ実射の和。 -/
theorem mixedLawDual_add (N : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj)) :
    (M.add N).mixedLawDual laws hi hj = M.mixedLawDual laws hi hj + N.mixedLawDual laws hi hj := by
  apply LinearMap.ext
  intro z
  apply (sourceCoordinateRead laws hi si).injective
  rw [LinearMap.add_apply, map_add, mixedLawDual_source, mixedLawDual_source,
    mixedLawDual_source, lawDual_add, LinearMap.add_apply]

/-- 原始符号反転は混在Law実射でも同じ符号反転。 -/
theorem mixedLawDual_neg :
    M.neg.mixedLawDual laws hi hj = -M.mixedLawDual laws hi hj := by
  apply LinearMap.ext
  intro z
  apply (sourceCoordinateRead laws hi si).injective
  rw [LinearMap.neg_apply, map_neg, mixedLawDual_source, mixedLawDual_source,
    lawDual_neg, LinearMap.neg_apply]

/-- 同じreadingの原始恒等は実Law恒等。 -/
theorem mixedLawDual_identity :
    (identity (sourceSupport qi si)).mixedLawDual laws hi hi = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply (sourceCoordinateRead laws hi si).injective
  rw [mixedLawDual_source, lawDual_identity, LinearMap.id_apply, LinearMap.id_apply]

/-- 同じ原始二微分正方形を独立混在Law正方形へ渡す。 -/
theorem mixedLawDual_square {I0 J0 : Type u}
    {si0 : I0 → Set qi.Target} {sj0 : J0 → Set qj.Target}
    (M0 : SupportedBasisMap (sourceSupport qi si0) (sourceSupport qj sj0))
    (di : SupportedBasisMap (sourceSupport qi si) (sourceSupport qi si0))
    (dj : SupportedBasisMap (sourceSupport qj sj) (sourceSupport qj sj0))
    (h : dj.raw.comp M.raw = M0.raw.comp di.raw) :
    (M.mixedLawDual laws hi hj).comp (dj.mixedLawDual laws hj hj) =
      (di.mixedLawDual laws hi hi).comp (M0.mixedLawDual laws hi hj) := by
  rw [← mixedLawDual_comp, ← mixedLawDual_comp]
  apply mixedLawDual_eq_of_raw_eq
  simpa only [raw_comp] using h

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
