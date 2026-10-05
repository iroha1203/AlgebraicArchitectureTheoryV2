import ResearchLean.AG.AtlasDefectComposition.FiniteDefectFamily
import Formal.Util.AssertStandardAxioms
/-! # 実六項列から成分六項列への全射同定

Implementation notes: 実対象の同型正方形と成分族の六項列を合成する。各射の元の同定を保存してから実相殺像を分解する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.FiniteDefectConjugation
universe v w
variable {J : Type v} [Fintype J]
variable {U V W : Type w} [AddCommGroup U] [Module ℚ U]
variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable {A B C : J → Type w}
variable [∀ j, AddCommGroup (A j)] [∀ j, Module ℚ (A j)]
variable [∀ j, AddCommGroup (B j)] [∀ j, Module ℚ (B j)]
variable [∀ j, AddCommGroup (C j)] [∀ j, Module ℚ (C j)]
variable (f : U →ₗ[ℚ] V) (g : V →ₗ[ℚ] W)
variable (a : ∀ j, A j →ₗ[ℚ] B j) (b : ∀ j, B j →ₗ[ℚ] C j)
variable (eU : U ≃ₗ[ℚ] ((j : J) → A j)) (eV : V ≃ₗ[ℚ] ((j : J) → B j))
variable (eW : W ≃ₗ[ℚ] ((j : J) → C j))
variable (hf : ∀ x, eV (f x) = FiniteLinearFamily.map a (eU x))
variable (hg : ∀ x, eW (g x) = FiniteLinearFamily.map b (eV x))
open DefectConjugation
/-- 実前段核の成分同型。 -/
def firstEquiv := (kernelFirst f (FiniteLinearFamily.map a) eU eV hf).trans
  (FiniteLinearFamily.kernelEquiv a)
/-- 実合成核の成分同型。 -/
def secondEquiv := (kernelComposite f g (FiniteLinearFamily.map a)
  (FiniteLinearFamily.map b) eU eV eW hf hg).trans (FiniteDefectFamily.kernelComposite a b)
/-- 実後段核の成分同型。 -/
def thirdEquiv := (kernelLast g (FiniteLinearFamily.map b) eV eW hg).trans
  (FiniteLinearFamily.kernelEquiv b)
/-- 実前段余核の成分同型。 -/
def fourthEquiv := (cokernelFirst f (FiniteLinearFamily.map a) eU eV hf).trans
  (FiniteLinearFamily.cokernelEquiv a)
/-- 実合成余核の成分同型。 -/
def fifthEquiv := (cokernelComposite f g (FiniteLinearFamily.map a)
  (FiniteLinearFamily.map b) eU eV eW hf hg).trans (FiniteDefectFamily.cokernelComposite a b)
/-- 実後段余核の成分同型。 -/
def sixthEquiv := (cokernelLast g (FiniteLinearFamily.map b) eV eW hg).trans
  (FiniteLinearFamily.cokernelEquiv b)
omit [Fintype J] in
/-- 第一射は同じ成分の核包含である。 -/
theorem first_component (x : LinearMap.ker f) (j : J) :
    secondEquiv f g a b eU eV eW hf hg (DefectSequence.first f g x) j =
      DefectSequence.first (a j) (b j) (firstEquiv f a eU eV hf x j) := by
  dsimp only [firstEquiv,secondEquiv,LinearEquiv.trans_apply]
  rw [DefectConjugation.first_natural f g (FiniteLinearFamily.map a)
    (FiniteLinearFamily.map b) eU eV eW hf hg]
  exact FiniteDefectFamily.first_component a b _ j
omit [Fintype J] in
/-- 第二射は同じ成分の前段実射である。 -/
theorem second_component (x : LinearMap.ker (g.comp f)) (j : J) :
    thirdEquiv g b eV eW hg (DefectSequence.second f g x) j =
      DefectSequence.second (a j) (b j) (secondEquiv f g a b eU eV eW hf hg x j) := by
  dsimp only [thirdEquiv,secondEquiv,LinearEquiv.trans_apply]
  rw [DefectConjugation.second_natural f g (FiniteLinearFamily.map a)
    (FiniteLinearFamily.map b) eU eV eW hf hg]
  exact FiniteDefectFamily.second_component a b _ j
/-- 相殺射は同じ成分の実相殺射である。 -/
theorem cancellation_component (x : LinearMap.ker g) (j : J) :
    fourthEquiv f a eU eV hf (DefectSequence.cancellation f g x) j =
      DefectSequence.cancellation (a j) (b j) (thirdEquiv g b eV eW hg x j) := by
  dsimp only [fourthEquiv,thirdEquiv,LinearEquiv.trans_apply]
  rw [DefectConjugation.cancellation_natural f g (FiniteLinearFamily.map a)
    (FiniteLinearFamily.map b) eU eV eW hf hg]
  exact FiniteDefectFamily.cancellation_component a b _ j
/-- 第四射は同じ成分の後段実射による商射である。 -/
theorem fourth_component (x : V ⧸ LinearMap.range f) (j : J) :
    fifthEquiv f g a b eU eV eW hf hg (DefectSequence.fourth f g x) j =
      DefectSequence.fourth (a j) (b j) (fourthEquiv f a eU eV hf x j) := by
  dsimp only [fifthEquiv,fourthEquiv,LinearEquiv.trans_apply]
  rw [DefectConjugation.fourth_natural f g (FiniteLinearFamily.map a)
    (FiniteLinearFamily.map b) eU eV eW hf hg]
  exact FiniteDefectFamily.fourth_component a b _ j
/-- 第五射は同じ成分の実商射である。 -/
theorem fifth_component (x : W ⧸ LinearMap.range (g.comp f)) (j : J) :
    sixthEquiv g b eV eW hg (DefectSequence.fifth f g x) j =
      DefectSequence.fifth (a j) (b j) (fifthEquiv f g a b eU eV eW hf hg x j) := by
  dsimp only [sixthEquiv,fifthEquiv,LinearEquiv.trans_apply]
  rw [DefectConjugation.fifth_natural f g (FiniteLinearFamily.map a)
    (FiniteLinearFamily.map b) eU eV eW hf hg]
  exact FiniteDefectFamily.fifth_component a b _ j
/-- 実相殺像は各同じ添字の実相殺像へ分解される。 -/
def cancellationRangeEquiv : LinearMap.range (DefectSequence.cancellation f g) ≃ₗ[ℚ]
    ((j : J) → LinearMap.range (DefectSequence.cancellation (a j) (b j))) :=
  (DefectConjugation.cancellationRangeEquiv f g (FiniteLinearFamily.map a)
    (FiniteLinearFamily.map b) eU eV eW hf hg).trans
      (FiniteDefectFamily.cancellationRangeEquiv a b)
end AAT.AG.AtlasDefectComposition.FiniteDefectConjugation
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.FiniteDefectConjugation
