import ResearchLean.AG.AtlasDefectComposition.DefectSequence
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import Formal.Util.AssertStandardAxioms
/-! # 六項完全列の元と全五射を保つ同型

Implementation notes: 二射の実可換式から六項列の各実商・実核と全五射を同定する。相殺像は同じ実余核同型の制限で構成し、rank等号だけを同定の代用にしない。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.DefectConjugation
variable {U V W U' V' W' : Type*}
variable [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W] [AddCommGroup U'] [Module ℚ U']
variable [AddCommGroup V'] [Module ℚ V'] [AddCommGroup W'] [Module ℚ W']
variable (f : U →ₗ[ℚ] V) (g : V →ₗ[ℚ] W)
variable (f' : U' →ₗ[ℚ] V') (g' : V' →ₗ[ℚ] W')
variable (eU : U ≃ₗ[ℚ] U') (eV : V ≃ₗ[ℚ] V') (eW : W ≃ₗ[ℚ] W')
variable (hf : ∀ x, eV (f x) = f' (eU x)) (hg : ∀ x, eW (g x) = g' (eV x))
include hf hg in
/-- 二つの可換式から得る、独立に与えられた合成射の可換式。 -/
theorem comp_square (x : U) : eW ((g.comp f) x) = (g'.comp f') (eU x) := by
  rw [LinearMap.comp_apply,hg,hf];rfl
/-- 六項列第一項の実核同定。 -/
def kernelFirst := LinearConjugation.kernelEquiv f f' eU eV hf
/-- 六項列第二項の実合成核同定。 -/
def kernelComposite := LinearConjugation.kernelEquiv (g.comp f) (g'.comp f') eU eW
  (comp_square f g f' g' eU eV eW hf hg)
/-- 六項列第三項の実後段核同定。 -/
def kernelLast := LinearConjugation.kernelEquiv g g' eV eW hg
/-- 六項列第四項の実前段余核同定。 -/
def cokernelFirst := LinearConjugation.cokernelEquiv f f' eU eV hf
/-- 六項列第五項の実合成余核同定。 -/
def cokernelComposite := LinearConjugation.cokernelEquiv (g.comp f) (g'.comp f') eU eW
  (comp_square f g f' g' eU eV eW hf hg)
/-- 六項列第六項の実後段余核同定。 -/
def cokernelLast := LinearConjugation.cokernelEquiv g g' eV eW hg
/-- 六項列の最初の核包含は実同型と可換である。 -/
theorem first_natural (x : LinearMap.ker f) :
    kernelComposite f g f' g' eU eV eW hf hg (DefectSequence.first f g x) =
      DefectSequence.first f' g' (kernelFirst f f' eU eV hf x) := by
  apply Subtype.ext
  rfl
/-- 六項列の合成核射は実同型と可換である。 -/
theorem second_natural (x : LinearMap.ker (g.comp f)) :
    kernelLast g g' eV eW hg (DefectSequence.second f g x) =
      DefectSequence.second f' g' (kernelComposite f g f' g' eU eV eW hf hg x) := by
  apply Subtype.ext
  exact hf x.val
/-- 中間の実類を前段余核へ送る相殺射は実同型と可換である。 -/
theorem cancellation_natural (x : LinearMap.ker g) :
    cokernelFirst f f' eU eV hf (DefectSequence.cancellation f g x) =
      DefectSequence.cancellation f' g' (kernelLast g g' eV eW hg x) := by
  rw [DefectSequence.cancellation_apply,DefectSequence.cancellation_apply]
  rfl
/-- 後段実写像による余核射は実同型と可換である。 -/
theorem fourth_natural (x : V ⧸ LinearMap.range f) :
    cokernelComposite f g f' g' eU eV eW hf hg (DefectSequence.fourth f g x) =
      DefectSequence.fourth f' g' (cokernelFirst f f' eU eV hf x) := by
  obtain ⟨x,rfl⟩ := (LinearMap.range f).mkQ_surjective x
  change (LinearMap.range (g'.comp f')).mkQ (eW (g x)) =
    (LinearMap.range (g'.comp f')).mkQ (g' (eV x))
  rw [hg]
/-- 最後の実商射は実同型と可換である。 -/
theorem fifth_natural (x : W ⧸ LinearMap.range (g.comp f)) :
    cokernelLast g g' eV eW hg (DefectSequence.fifth f g x) =
      DefectSequence.fifth f' g' (cokernelComposite f g f' g' eU eV eW hf hg x) := by
  obtain ⟨x,rfl⟩ := (LinearMap.range (g.comp f)).mkQ_surjective x
  rfl
include eW hg in
/-- 相殺射の実像も同型に沿って一致する。 -/
theorem cancellation_range :
    (LinearMap.range (DefectSequence.cancellation f g)).map
      (cokernelFirst f f' eU eV hf).toLinearMap =
        LinearMap.range (DefectSequence.cancellation f' g') :=
  LinearConjugation.range_map _ _ (kernelLast g g' eV eW hg)
    (cokernelFirst f f' eU eV hf)
    (cancellation_natural f g f' g' eU eV eW hf hg)
/-- 相殺像の元は前段余核の実同型で運ばれる。 -/
def cancellationRangeEquiv : LinearMap.range (DefectSequence.cancellation f g) ≃ₗ[ℚ]
    LinearMap.range (DefectSequence.cancellation f' g') :=
  (cokernelFirst f f' eU eV hf).ofSubmodules _ _
    (cancellation_range f g f' g' eU eV eW hf hg)
end AAT.AG.AtlasDefectComposition.DefectConjugation
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.DefectConjugation
