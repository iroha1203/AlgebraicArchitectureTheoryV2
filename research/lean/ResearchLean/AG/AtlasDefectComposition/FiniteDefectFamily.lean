import ResearchLean.AG.AtlasDefectComposition.FiniteLinearFamily
import ResearchLean.AG.AtlasDefectComposition.DefectConjugation
import Formal.Util.AssertStandardAxioms
/-! # 六項完全列と相殺の有限族分解

Implementation notes: 有限族の各実核・実余核を使い、各添字で五つの実射を評価する。相殺の像も同じ添字の実像へ同定する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.FiniteDefectFamily
universe v w
variable {J : Type v} [Fintype J] {U V W : J → Type w}
variable [∀ j, AddCommGroup (U j)] [∀ j, Module ℚ (U j)]
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℚ (V j)]
variable [∀ j, AddCommGroup (W j)] [∀ j, Module ℚ (W j)]
variable (f : ∀ j, U j →ₗ[ℚ] V j) (g : ∀ j, V j →ₗ[ℚ] W j)
open FiniteLinearFamily DefectSequence
/-- 実合成核も各実合成核の族である。 -/
def kernelComposite : LinearMap.ker ((map g).comp (map f)) ≃ₗ[ℚ]
    ((j : J) → LinearMap.ker ((g j).comp (f j))) := kernelEquiv (fun j => (g j).comp (f j))
/-- 実合成余核も各実合成余核の族である。 -/
def cokernelComposite : (((j : J) → W j) ⧸ LinearMap.range ((map g).comp (map f))) ≃ₗ[ℚ]
    ((j : J) → W j ⧸ LinearMap.range ((g j).comp (f j))) :=
  cokernelEquiv (fun j => (g j).comp (f j))
omit [Fintype J] in
/-- 核包含は各同じ添字の核包含である。 -/
theorem first_component (x : LinearMap.ker (map f)) (j : J) :
    kernelComposite f g (first (map f) (map g) x) j =
      first (f j) (g j) (kernelEquiv f x j) := by
  apply Subtype.ext;rfl
omit [Fintype J] in
/-- 合成核射は各同じ添字の前段実写像である。 -/
theorem second_component (x : LinearMap.ker ((map g).comp (map f))) (j : J) :
    kernelEquiv g (second (map f) (map g) x) j =
      second (f j) (g j) (kernelComposite f g x j) := by
  apply Subtype.ext;rfl
/-- 相殺射は各同じ添字の後段実核から前段実余核へ作用する。 -/
theorem cancellation_component (x : LinearMap.ker (map g)) (j : J) :
    cokernelEquiv f (cancellation (map f) (map g) x) j =
      cancellation (f j) (g j) (kernelEquiv g x j) := by
  rw [cancellation_apply,cokernelEquiv_mk,cancellation_apply,kernelEquiv_val]
/-- 第四射は各同じ添字の後段実写像による商射である。 -/
theorem fourth_component (x : ((j : J) → V j) ⧸ LinearMap.range (map f)) (j : J) :
    cokernelComposite f g (fourth (map f) (map g) x) j =
      fourth (f j) (g j) (cokernelEquiv f x j) := by
  obtain ⟨x,rfl⟩ := (LinearMap.range (map f)).mkQ_surjective x
  change cokernelEquiv (fun j => (g j).comp (f j))
    ((LinearMap.range (map (fun j => (g j).comp (f j)))).mkQ (map g x)) j = _
  rw [cokernelEquiv_mk,cokernelEquiv_mk,fourth_mk,map_apply]
/-- 最後の商射は各同じ添字の実商射である。 -/
theorem fifth_component (x : ((j : J) → W j) ⧸ LinearMap.range ((map g).comp (map f)))
    (j : J) : cokernelEquiv g (fifth (map f) (map g) x) j =
      fifth (f j) (g j) (cokernelComposite f g x j) := by
  obtain ⟨x,rfl⟩ := (LinearMap.range ((map g).comp (map f))).mkQ_surjective x
  change cokernelEquiv g ((LinearMap.range (map g)).mkQ x) j =
    fifth (f j) (g j) (cokernelEquiv (fun j => (g j).comp (f j))
      ((LinearMap.range (map (fun j => (g j).comp (f j)))).mkQ x) j)
  rw [cokernelEquiv_mk,cokernelEquiv_mk,fifth_mk]
/-- 族相殺射と成分相殺射の族の実可換式。 -/
theorem cancellation_square (x : LinearMap.ker (map g)) :
    cokernelEquiv f (cancellation (map f) (map g) x) =
      map (fun j => cancellation (f j) (g j)) (kernelEquiv g x) := by
  funext j
  exact cancellation_component f g x j
/-- 相殺の実像も全ラベルの実相殺像の族へ同定される。 -/
def cancellationRangeEquiv : LinearMap.range (cancellation (map f) (map g)) ≃ₗ[ℚ]
    ((j : J) → LinearMap.range (cancellation (f j) (g j))) :=
  ((cokernelEquiv f).ofSubmodules _ _
    (AAT.AG.AtlasDefectComposition.LinearConjugation.range_map _ _
      (kernelEquiv g) (cokernelEquiv f) (cancellation_square f g))).trans
        (rangeEquiv (fun j => cancellation (f j) (g j)))
end AAT.AG.AtlasDefectComposition.FiniteDefectFamily
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.FiniteDefectFamily
