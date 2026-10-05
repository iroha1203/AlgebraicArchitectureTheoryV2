import ResearchLean.AG.AtlasDefectComposition.DefectSequence
import Formal.Util.AssertStandardAxioms
/-! # 六項列の全射の自然性

Implementation notes: 同じ二つの可換正方形から核・余核の射を生成する。
この線形補助の正方形は実台制限への適用で放電する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SixTermNaturality
variable {K U V W U' V' W' : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup U'] [Module K U'] [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
/-- 実可換正方形から生成する核射。 -/
def kernelMap (f : U →ₗ[K] V) (f' : U' →ₗ[K] V') (a : U →ₗ[K] U') (b : V →ₗ[K] V')
    (h : ∀ x, b (f x) = f' (a x)) : LinearMap.ker f →ₗ[K] LinearMap.ker f' :=
  (a.comp (LinearMap.ker f).subtype).codRestrict _ (by intro x; change f' (a x.val)=0;rw [← h,x.2,map_zero])
/-- 核射の元は元の source 射を評価する。 -/
@[simp] theorem kernelMap_val (f : U →ₗ[K] V) (f' : U' →ₗ[K] V') (a : U →ₗ[K] U') (b : V →ₗ[K] V')
    (h : ∀ x, b (f x) = f' (a x)) (x : LinearMap.ker f) : (kernelMap f f' a b h x).val = a x.val := rfl
/-- 実可換正方形から生成する余核射。 -/
def cokernelMap (f : U →ₗ[K] V) (f' : U' →ₗ[K] V') (a : U →ₗ[K] U') (b : V →ₗ[K] V')
    (h : ∀ x, b (f x) = f' (a x)) : V ⧸ LinearMap.range f →ₗ[K] V' ⧸ LinearMap.range f' :=
  (LinearMap.range f).mapQ (LinearMap.range f') b (by rintro _ ⟨x,rfl⟩;exact ⟨a x,(h x).symm⟩)
/-- 余核射の代表元は元の target 射を評価する。 -/
@[simp] theorem cokernelMap_mk (f : U →ₗ[K] V) (f' : U' →ₗ[K] V') (a : U →ₗ[K] U') (b : V →ₗ[K] V')
    (h : ∀ x, b (f x) = f' (a x)) (x : V) : cokernelMap f f' a b h ((LinearMap.range f).mkQ x) =
      (LinearMap.range f').mkQ (b x) := rfl
variable (f : U →ₗ[K] V) (g : V →ₗ[K] W) (f' : U' →ₗ[K] V') (g' : V' →ₗ[K] W')
variable (a : U →ₗ[K] U') (b : V →ₗ[K] V') (c : W →ₗ[K] W')
variable (hf : ∀ x, b (f x) = f' (a x)) (hg : ∀ x, c (g x) = g' (b x))
include hf hg
/-- 同じ二正方形からの合成正方形。 -/
theorem comp_square (x : U) : c ((g.comp f) x) = (g'.comp f') (a x) := by
  simp only [LinearMap.comp_apply];rw [hg,hf]
/-- 六項列の最初の核包含は自然である。 -/
theorem first_natural (x : LinearMap.ker f) :
    kernelMap _ _ a c (comp_square f g f' g' a b c hf hg) (DefectSequence.first f g x) =
      DefectSequence.first f' g' (kernelMap f f' a b hf x) := by apply Subtype.ext;rfl
/-- 六項列の合成核から後段核への射は自然である。 -/
theorem second_natural (x : LinearMap.ker (g.comp f)) :
    kernelMap g g' b c hg (DefectSequence.second f g x) =
      DefectSequence.second f' g' (kernelMap _ _ a c (comp_square f g f' g' a b c hf hg) x) := by
  apply Subtype.ext
  exact hf x.val
/-- 相殺写像は実後段核と前段余核の射について自然である。 -/
theorem cancellation_natural (x : LinearMap.ker g) :
    cokernelMap f f' a b hf (DefectSequence.cancellation f g x) =
      DefectSequence.cancellation f' g' (kernelMap g g' b c hg x) := rfl
/-- 前段余核から合成余核への射は自然である。 -/
theorem fourth_natural (x : V ⧸ LinearMap.range f) :
    cokernelMap _ _ a c (comp_square f g f' g' a b c hf hg) (DefectSequence.fourth f g x) =
      DefectSequence.fourth f' g' (cokernelMap f f' a b hf x) := by
  obtain ⟨v,rfl⟩ := (LinearMap.range f).mkQ_surjective x
  simp only [DefectSequence.fourth_mk,cokernelMap_mk]
  rw [hg]
/-- 合成余核から後段余核への射も自然である。 -/
theorem fifth_natural (x : W ⧸ LinearMap.range (g.comp f)) :
    cokernelMap g g' b c hg (DefectSequence.fifth f g x) =
      DefectSequence.fifth f' g' (cokernelMap _ _ a c (comp_square f g f' g' a b c hf hg) x) := by
  obtain ⟨w,rfl⟩ := (LinearMap.range (g.comp f)).mkQ_surjective x
  rfl
end AAT.AG.AtlasDefectComposition.SixTermNaturality
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SixTermNaturality
