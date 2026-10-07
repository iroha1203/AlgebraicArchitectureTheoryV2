import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationDegreeTwo
import ResearchLean.AG.FaceRelationSubdivision.IncidenceBasis
import Formal.Util.AssertStandardAxioms

/-! # 面複製の原始支持chain分解

## Implementation notes

原始foldと旧面包含を選択chainへ生成する。fresh面−旧Fを追加基底にし、
その係数とfoldを明示逆にする。期待次元や相同型を入力にはしない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent) (A : Set q.Target)
/-- 原始foldの支持chain生成。 -/
def chainR2 : K2 (supported N F) A →ₗ[ℚ] K2 N A := (comparison N F).basis2.selected A
/-- 原始旧面包含の支持chain生成。 -/
def chainS2 : K2 N A →ₗ[ℚ] K2 (supported N F) A := (reverseComparison N F).basis2.selected A
/-- foldの実選択基底式。 -/
@[simp] theorem chainR2_single (f : (supported N F).FaceInTargetSubset A) (a : ℚ) :
    chainR2 N F A (Finsupp.single f a) = a • Finsupp.single (foldFace N F A f) 1 := by
  rw [chainR2, SupportedBasisMap.selected_single, IncidenceSupportedComparison.basis2_image,
    comparison_face, rationalOptionCell_some]
  congr 1
  exact subtypeDomain_single_selected N.faceSupport A (foldFace N F A f) 1
/-- 旧面包含の実選択基底式。 -/
@[simp] theorem chainS2_single (f : N.FaceInTargetSubset A) (a : ℚ) :
    chainS2 N F A (Finsupp.single f a) = a • Finsupp.single (oldFace N F A f) 1 := by
  rw [chainS2, SupportedBasisMap.selected_single, IncidenceSupportedComparison.basis2_image,
    reverseComparison_face, rationalOptionCell_some]
  congr 1
  exact subtypeDomain_single_selected (supported N F).faceSupport A (oldFace N F A f) 1
/-- 原始foldと包含は支持chain上でも左逆。 -/
theorem chainR2_chainS2 : (chainR2 N F A).comp (chainS2 N F A) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro f a
  simp only [LinearMap.comp_apply, chainS2_single, chainR2_single,
    foldFace_oldFace, LinearMap.id_apply, Finsupp.smul_single, smul_eq_mul, mul_one]
/-- 原始生成収縮の全三次数双対は同じ実subset Hom。 -/
theorem chain_dual_comparison : (comparison N F).basisHom A = subsetHom N F A :=
  (comparison N F).basisHom_eq_generated A
/-- 原始sectionの全三次数双対も同じ実subset Hom。 -/
theorem chain_dual_section : (reverseComparison N F).basisHom A = reverseSubsetHom N F A :=
  (reverseComparison N F).basisHom_eq_generated A
/-- 複製で次数0原始生成は恒等。 -/
theorem chainR0_eq_id : (comparison N F).basis0.selected A = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  rw [SupportedBasisMap.selected_single, IncidenceSupportedComparison.basis0_image, comparison_chart]
  rw [subtypeDomain_single_selected N.chartSupport A v 1]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl
/-- 複製で次数1原始生成は恒等。 -/
theorem chainR1_eq_id : (comparison N F).basis1.selected A = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro e a
  rw [SupportedBasisMap.selected_single, IncidenceSupportedComparison.basis1_image,
    comparison_edge, rationalOptionCell_some, subtypeDomain_single_selected N.edgeSupport A e 1]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl
/-- 複製では低次微分そのものが保たれる。 -/
theorem chainD1_eq : chainD1 (supported N F) A = chainD1 N A := rfl
/-- 同じ原始foldのchain可換式を次数1恒等で読む。 -/
theorem chainD2_projection (x : K2 (supported N F) A) :
    chainD2 (supported N F) A x = chainD2 N A (chainR2 N F A x) := by
  have h := (comparison N F).supportedChainMap_comm2 A A
    (IncidenceSupportedComparison.selfSubsetMapsTo A) x
  rw [← IncidenceSupportedComparison.selected_basis1_eq,
    ← IncidenceSupportedComparison.selected_basis2_eq, chainR1_eq_id] at h
  exact h
variable (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A)
/-- 追加基底はfresh面−指定旧面。 -/
def extraChain : K2 (supported N F) A :=
  Finsupp.single (freshFace N F A hF) 1 - Finsupp.single (oldFace N F A (selectedFace N F A hF)) 1
/-- fresh係数を読む射。 -/
def freshCoefficient : K2 (supported N F) A →ₗ[ℚ] ℚ := Finsupp.lapply (freshFace N F A hF)
/-- 追加基底の線形延長。 -/
def extraChainMap : ℚ →ₗ[ℚ] K2 (supported N F) A := LinearMap.toSpanSingleton ℚ _ (extraChain N F A hF)
/-- 追加基底の原始fold像は零。 -/
theorem chainR2_extra : chainR2 N F A (extraChain N F A hF) = 0 := by
  simp only [extraChain, map_sub, chainR2_single, foldFace_fresh, foldFace_oldFace, one_smul, sub_self]
/-- 追加基底の微分は零。 -/
theorem chainD2_extra : chainD2 (supported N F) A (extraChain N F A hF) = 0 := by
  rw [chainD2_projection, chainR2_extra, map_zero]
/-- fresh基底と旧基底は異なる。 -/
theorem fresh_ne_old (f : N.FaceInTargetSubset A) : freshFace N F A hF ≠ oldFace N F A f := by
  intro h
  have hv := congrArg Subtype.val h
  simp only [freshFace_val, oldFace_val] at hv
  cases hv
/-- 旧面基底はfresh係数を持たない。 -/
@[simp] theorem freshCoefficient_old (f : N.FaceInTargetSubset A) (a : ℚ) :
    freshCoefficient N F A hF (Finsupp.single (oldFace N F A f) a) = 0 := by
  classical
  exact Finsupp.single_eq_of_ne (fresh_ne_old N F A hF f)
/-- fresh基底の係数。 -/
@[simp] theorem freshCoefficient_fresh (a : ℚ) :
    freshCoefficient N F A hF (Finsupp.single (freshFace N F A hF) a) = a := Finsupp.single_eq_same
/-- 追加基底のfresh係数は1。 -/
@[simp] theorem freshCoefficient_extra : freshCoefficient N F A hF (extraChain N F A hF) = 1 := by
  simp only [extraChain, map_sub, freshCoefficient_fresh, freshCoefficient_old, sub_zero]
/-- 旧chain包含のfresh係数は零。 -/
theorem freshCoefficient_chainS2 : (freshCoefficient N F A hF).comp (chainS2 N F A) = 0 := by
  apply Finsupp.lhom_ext
  intro f a
  simp only [LinearMap.comp_apply, chainS2_single, map_smul, freshCoefficient_old, smul_zero,
    LinearMap.zero_apply]
/-- fold像を旧セルへ戻し差分を補うと全chainを回復する。 -/
theorem chain_split_reconstruct : (chainS2 N F A).comp (chainR2 N F A) +
    (extraChainMap N F A hF).comp (freshCoefficient N F A hF) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro f a
  simp only [LinearMap.add_apply, LinearMap.comp_apply, chainR2_single, map_smul,
    chainS2_single, one_smul, LinearMap.id_apply]
  rcases f with ⟨f,hf⟩
  rcases f with f | x
  · have he : (⟨Sum.inl f,hf⟩ : (supported N F).FaceInTargetSubset A) = oldFace N F A ⟨f,hf⟩ := rfl
    rw [he, foldFace_oldFace, freshCoefficient_old, map_zero]
    simp only [add_zero, Finsupp.smul_single, smul_eq_mul, mul_one]
  · cases x
    have he : (⟨Sum.inr PUnit.unit,hf⟩ : (supported N F).FaceInTargetSubset A) = freshFace N F A hF := rfl
    rw [he, foldFace_fresh, freshCoefficient_fresh]
    simp only [extraChainMap, LinearMap.toSpanSingleton_apply, extraChain, smul_sub,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    abel
/-- 選択された成分の実chain次数2分解。第一成分は同じ原始fold。 -/
def chainSplit : K2 (supported N F) A ≃ₗ[ℚ] K2 N A × ℚ :=
  LinearEquiv.ofLinear ((chainR2 N F A).prod (freshCoefficient N F A hF))
    ((chainS2 N F A).coprod (extraChainMap N F A hF))
    (by
      apply LinearMap.ext
      intro x
      change (chainR2 N F A (chainS2 N F A x.1 + x.2 • extraChain N F A hF),
        freshCoefficient N F A hF (chainS2 N F A x.1 + x.2 • extraChain N F A hF)) = x
      apply Prod.ext
      · rw [map_add, map_smul, chainR2_extra, smul_zero, add_zero]
        exact LinearMap.congr_fun (chainR2_chainS2 N F A) x.1
      · change freshCoefficient N F A hF (chainS2 N F A x.1 + x.2 • extraChain N F A hF) = x.2
        rw [map_add, map_smul, freshCoefficient_extra, smul_eq_mul, mul_one]
        have hz := LinearMap.congr_fun (freshCoefficient_chainS2 N F A hF) x.1
        change freshCoefficient N F A hF (chainS2 N F A x.1) = 0 at hz
        rw [hz, zero_add])
    (by exact chain_split_reconstruct N F A hF)
/-- 分解の第一成分は同じ原始r。 -/
@[simp] theorem chainSplit_fst (x : K2 (supported N F) A) :
    (chainSplit N F A hF x).1 = chainR2 N F A x := rfl
/-- 分解の第二成分はfresh係数。 -/
@[simp] theorem chainSplit_snd (x : K2 (supported N F) A) :
    (chainSplit N F A hF x).2 = freshCoefficient N F A hF x := rfl
/-- 分解の逆は旧セルとfresh−F基底の明示線形和。 -/
@[simp] theorem chainSplit_symm (x : K2 N A × ℚ) :
    (chainSplit N F A hF).symm x = chainS2 N F A x.1 + x.2 • extraChain N F A hF := rfl
/-- 微分は分解の旧成分だけを読む。低次恒等と合わせK′=K⊕Q[2]。 -/
theorem chainSplit_differential (x : K2 (supported N F) A) :
    chainD2 (supported N F) A x = chainD2 N A (chainSplit N F A hF x).1 :=
  chainD2_projection N F A x
end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
