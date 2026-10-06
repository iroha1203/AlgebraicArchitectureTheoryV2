import ResearchLean.AG.FaceRelationSubdivision.LawFiniteDifferential
import Formal.Util.AssertStandardAxioms

/-!
# 原始恒等式の独立Law有限和への移送

## Implementation notes

原始raw等号は一般補題の方向仮定であり、基本操作では基底計算から放電する。
Law射は受理済み独立有限和を使用し、保存結論から射を選ぶ方法を採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {q : Reading Source}
variable {si : I → Set q.Target} {sj : J → Set q.Target}
namespace SupportedBasisMap
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 原始往復恒等から、独立Law双対の同じ往復恒等を得る。 -/
theorem lawDual_comp_eq_identity (M : SupportedBasisMap si sj) (N : SupportedBasisMap sj si)
    (h : N.raw.comp M.raw = LinearMap.id) :
    (M.lawDual laws ha).comp (N.lawDual laws ha) = LinearMap.id := by
  have hr : (M.comp N).raw = (identity si).raw := by
    rw [raw_comp, raw_identity]
    exact h
  have hl := (M.comp N).lawDual_eq_of_raw_eq laws ha (identity si) hr
  simpa only [lawDual_comp, lawDual_identity] using hl

/-- 原始二項の補正式を同じLaw射の恒等式へ移す。 -/
theorem lawDual_add_eq_identity (M P : SupportedBasisMap si si)
    (h : M.raw + P.raw = LinearMap.id) :
    M.lawDual laws ha + P.lawDual laws ha = LinearMap.id := by
  have hr : (M.add P).raw = (identity si).raw := by
    rw [raw_add, raw_identity]
    exact h
  have hl := (M.add P).lawDual_eq_of_raw_eq laws ha (identity si) hr
  simpa only [lawDual_add, lawDual_identity] using hl

/-- 原始三項の補正式を同じLaw射の恒等式へ移す。 -/
theorem lawDual_add_add_eq_identity (M P Q : SupportedBasisMap si si)
    (h : M.raw + P.raw + Q.raw = LinearMap.id) :
    M.lawDual laws ha + P.lawDual laws ha + Q.lawDual laws ha = LinearMap.id := by
  have hl := lawDual_add_eq_identity laws ha (M.add P) Q (by simpa only [raw_add] using h)
  simpa only [lawDual_add] using hl

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
