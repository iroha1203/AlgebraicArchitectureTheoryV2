import ResearchLean.AG.FaceRelationSubdivision.LawFiniteFiber
import Formal.Util.AssertStandardAxioms

/-!
# 原始有限和のLaw座標化の合成・加法

## Implementation notes

射は独立なLaw基底像から生成済みであり、等号の検査だけを全ラベルfiberで行う。
原始射の等号は選択零延長の単射から降ろし、双対合成の公開APIを使う。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J L : Type u} {q : Reading Source}
variable {si : I → Set q.Target} {sj : J → Set q.Target} {sl : L → Set q.Target}
namespace SupportedBasisMap
variable (M : SupportedBasisMap si sj) (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 原始射が等しければ独立生成Law射も等しい。 -/
theorem lawDual_eq_of_raw_eq (N : SupportedBasisMap si sj) (h : M.raw = N.raw) :
    M.lawDual laws ha = N.lawDual laws ha := by
  apply LinearMap.ext
  intro z
  apply lawFiberRead_joint_injective laws ha si
  intro l
  rw [lawDual_fiber, lawDual_fiber, M.selected_eq_of_raw_eq N h]

/-- 原始有限和の直接合成をLaw座標化すると同じ実cochain合成になる。 -/
theorem lawDual_comp (N : SupportedBasisMap sj sl) :
    (M.comp N).lawDual laws ha = (M.lawDual laws ha).comp (N.lawDual laws ha) := by
  apply LinearMap.ext
  intro z
  apply lawFiberRead_joint_injective laws ha si
  intro l
  rw [LinearMap.comp_apply, lawDual_fiber, lawDual_fiber, lawDual_fiber,
    selected_comp, dualCellMap_comp, LinearMap.comp_apply]

/-- 原始恒等のLaw座標化は同じ実恒等。 -/
theorem lawDual_identity (si : I → Set q.Target) :
    (identity si).lawDual laws ha = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply lawFiberRead_joint_injective laws ha si
  intro l
  rw [lawDual_fiber, selected_identity, dualCellMap_identity, LinearMap.id_apply,
    LinearMap.id_apply]

/-- 原始像の和はLaw座標の実射の和を生成する。 -/
theorem lawDual_add (N : SupportedBasisMap si sj) :
    (M.add N).lawDual laws ha = M.lawDual laws ha + N.lawDual laws ha := by
  apply LinearMap.ext
  intro z
  apply lawFiberRead_joint_injective laws ha si
  intro l
  rw [lawDual_fiber, selected_add, dualCellMap_add, LinearMap.add_apply,
    LinearMap.add_apply, map_add, lawDual_fiber, lawDual_fiber]

/-- 原始像の符号反転も同じLaw射の符号反転になる。 -/
theorem lawDual_neg : M.neg.lawDual laws ha = -M.lawDual laws ha := by
  apply LinearMap.ext
  intro z
  apply lawFiberRead_joint_injective laws ha si
  intro l
  rw [lawDual_fiber, selected_neg, dualCellMap_neg, LinearMap.neg_apply,
    LinearMap.neg_apply, map_neg, lawDual_fiber]

/-- 原始chain正方形の全成分を同じLaw cochain正方形へ移す。 -/
theorem lawDual_square {I0 J0 : Type u} {si0 : I0 → Set q.Target} {sj0 : J0 → Set q.Target}
    (M0 : SupportedBasisMap si0 sj0) (di : SupportedBasisMap si si0)
    (dj : SupportedBasisMap sj sj0)
    (h : dj.raw.comp M.raw = M0.raw.comp di.raw) :
    (M.lawDual laws ha).comp (dj.lawDual laws ha) =
      (di.lawDual laws ha).comp (M0.lawDual laws ha) := by
  rw [← lawDual_comp, ← lawDual_comp]
  apply lawDual_eq_of_raw_eq
  simpa only [raw_comp] using h

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
