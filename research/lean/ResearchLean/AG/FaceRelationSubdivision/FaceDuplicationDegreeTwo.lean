import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationComparison
import ResearchLean.AG.AtlasDefectComposition.EndpointNaturality
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-!
# 面複製の実次数2像

選択された面Fとfresh面の差を実cochainで評価し、比較の次数2像をその核に同定する。

## Implementation notes

旧面へのrestrictionを核元の原像として明示する。
次元一致から核を推測する方法は用いず、全旧面とfresh面で評価する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent) (A : Set q.Target)

/-- 全支持での旧面の選択包含。 -/
def oldFace (f : N.FaceInTargetSubset A) : (supported N F).FaceInTargetSubset A :=
  ⟨.inl f.val, f.property⟩
/-- 全支持での原始foldによる選択面輸送。 -/
def foldFace (f : (supported N F).FaceInTargetSubset A) : N.FaceInTargetSubset A :=
  ⟨fold N F f.val, f.property⟩
/-- 選択面包含の元。 -/
@[simp] theorem oldFace_val (f : N.FaceInTargetSubset A) : (oldFace N F A f).val = .inl f.val := rfl
/-- 選択foldの元。 -/
@[simp] theorem foldFace_val (f : (supported N F).FaceInTargetSubset A) :
    (foldFace N F A f).val = fold N F f.val := rfl
/-- 旧面の包含とfoldの合成は全選択面で恒等。 -/
@[simp] theorem foldFace_oldFace (f : N.FaceInTargetSubset A) :
    foldFace N F A (oldFace N F A f) = f := rfl
/-- 同じ実生成比較の次数2は原始foldを読む。 -/
@[simp] theorem subsetHom_f2 (z : (N.targetSubsetComplex A).C2)
    (f : (supported N F).FaceInTargetSubset A) :
    (subsetHom N F A).f2 z f = z (foldFace N F A f) := by
  exact ((comparison N F).targetSubsetPullback2_apply A A (subset_compatible A) z f).trans (by
    rw [(comparison N F).targetSubsetFaceMapOption_eq_some A A (subset_compatible A) f (fold N F f.val)
      (comparison_face N F f.val)]
    rfl)
/-- 同じ実次数2像は旧面で元のcochainを回復する。 -/
@[simp] theorem subsetHom_f2_old (z : (N.targetSubsetComplex A).C2) (f : N.FaceInTargetSubset A) :
    (subsetHom N F A).f2 z (oldFace N F A f) = z f := by
  rw [subsetHom_f2, foldFace_oldFace]

/-- 実section双対の次数2は同じ旧面包含を読む。 -/
@[simp] theorem reverseSubsetHom_f2 (z : ((supported N F).targetSubsetComplex A).C2)
    (f : N.FaceInTargetSubset A) :
    (reverseSubsetHom N F A).f2 z f = z (oldFace N F A f) := by
  exact ((reverseComparison N F).targetSubsetPullback2_apply A A (subset_compatible A) z f).trans (by
    rw [(reverseComparison N F).targetSubsetFaceMapOption_eq_some A A (subset_compatible A) f (.inl f.val)
      (reverseComparison_face N F f.val)]
    rfl)
variable (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A)
/-- 原始Fの支持がAに交わる場合の旧選択面。 -/
def selectedFace : N.FaceInTargetSubset A := ⟨F, hF⟩
/-- 同じ支持証拠から選択されるfresh面。 -/
def freshFace : (supported N F).FaceInTargetSubset A := ⟨.inr PUnit.unit, hF⟩
/-- 旧Fの選択元。 -/
@[simp] theorem selectedFace_val : (selectedFace N F A hF).val = F := rfl
/-- fresh面の選択元。 -/
@[simp] theorem freshFace_val : (freshFace N F A hF).val = .inr PUnit.unit := rfl
/-- fresh面のfoldは同じF。 -/
@[simp] theorem foldFace_fresh :
    foldFace N F A (freshFace N F A hF) = selectedFace N F A hF := rfl
/-- 実cochainのfresh面と元面の差。 -/
def difference : ((supported N F).targetSubsetComplex A).C2 →ₗ[ℚ] ℚ where
  toFun z := z (freshFace N F A hF) - z (oldFace N F A (selectedFace N F A hF))
  map_add' z w := by
    change (z _ + w _) - (z _ + w _) = (z _ - z _) + (w _ - w _)
    ring
  map_smul' a z := by
    change a * z _ - a * z _ = a * (z _ - z _)
    ring
/-- 差の原始座標評価。 -/
@[simp] theorem difference_apply (z : ((supported N F).targetSubsetComplex A).C2) :
    difference N F A hF z =
      z (freshFace N F A hF) - z (oldFace N F A (selectedFace N F A hF)) := rfl
/-- fresh面だけに値を置く実cochain。 -/
def freshOnly (a : ℚ) : ((supported N F).targetSubsetComplex A).C2 :=
  fun f => match f.val with | .inl _ => 0 | .inr _ => a
/-- fresh単独cochainは全旧面で零。 -/
@[simp] theorem freshOnly_old (a : ℚ) (f : N.FaceInTargetSubset A) :
    freshOnly N F A a (oldFace N F A f) = 0 := rfl
/-- fresh単独cochainのfresh評価。 -/
@[simp] theorem freshOnly_fresh (a : ℚ) :
    freshOnly N F A a (freshFace N F A hF) = a := rfl
/-- 差はfresh単独cochainを全ての有理数へ送る。 -/
@[simp] theorem difference_freshOnly (a : ℚ) : difference N F A hF (freshOnly N F A a) = a := by
  simp only [difference_apply, freshOnly_fresh, freshOnly_old, sub_zero]
/-- 差は実cochain全空間からℚへの全射。 -/
theorem difference_surjective : Function.Surjective (difference N F A hF) :=
  fun a => ⟨freshOnly N F A a, difference_freshOnly N F A hF a⟩
/-- 同じ実次数2比較の像は差で零になる。 -/
theorem difference_f2 (z : (N.targetSubsetComplex A).C2) :
    difference N F A hF ((subsetHom N F A).f2 z) = 0 := by
  simp only [difference_apply, subsetHom_f2, foldFace_fresh, foldFace_oldFace, sub_self]
/-- 差の核は同じ実次数2比較の像そのもの。 -/
theorem difference_kernel : LinearMap.ker (difference N F A hF) =
    LinearMap.range (subsetHom N F A).f2 := by
  ext z
  constructor
  · intro hz
    have heq : z (freshFace N F A hF) = z (oldFace N F A (selectedFace N F A hF)) :=
      sub_eq_zero.mp hz
    refine ⟨fun f => z (oldFace N F A f), ?_⟩
    funext f
    rw [subsetHom_f2]
    rcases f with ⟨f, hf⟩
    rcases f with f | x
    · rfl
    · cases x
      exact heq.symm
  · rintro ⟨z, rfl⟩
    exact difference_f2 N F A hF z
/-- 同じ実微分の像は、比較の次数2像に入る。 -/
theorem differential_range_le :
    LinearMap.range ((supported N F).targetSubsetComplex A).d1 ≤
      LinearMap.range (subsetHom N F A).f2 := by
  rintro z ⟨x, rfl⟩
  refine ⟨(N.targetSubsetComplex A).d1 x, ?_⟩
  rw [(subsetHom N F A).comm1, subsetHom_f1]
/-- 原始差は同じ実微分で零となる。 -/
theorem difference_d1 (z : ((supported N F).targetSubsetComplex A).C1) :
    difference N F A hF (((supported N F).targetSubsetComplex A).d1 z) = 0 := by
  have hz := differential_range_le N F A ⟨z, rfl⟩
  rw [← difference_kernel N F A hF] at hz
  exact hz

end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
