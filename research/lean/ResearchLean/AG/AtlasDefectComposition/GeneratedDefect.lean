import ResearchLean.AG.AtlasDefectComposition.DefectSequence
import ResearchLean.AG.AtlasDefectComposition.ComparisonLaws
import ResearchLean.AG.AtlasDefectComposition.SubsetComposition
import ResearchLean.AG.UniformInvariance.DefectSemantics
import Formal.Util.AssertStandardAxioms

/-!
# 実生成H¹の相殺と欠損

G-133 Bの一般六項列を既存H¹商の実比較へ適用する。商の代表元について、後段で
消えることを実primitiveの存在へ、前段の像に入ることを粗cocycleと中間primitiveへ同定する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe v w₀ w₁ w₂ u

section Representatives
variable {k : Type v} [Field k]
variable {C₀ : ThreeCochainComplex.{v,w₀} k}
variable {C₁ : ThreeCochainComplex.{v,w₁} k}
variable {C₂ : ThreeCochainComplex.{v,w₂} k}
variable (f : ThreeCochainComplex.Hom C₀ C₁)
variable (g : ThreeCochainComplex.Hom C₁ C₂)

/-- 後段で零になる実H¹類は、実生成次数1像のprimitiveを持つ。 -/
theorem h1Map_mk_eq_zero_iff (z : LinearMap.ker C₁.d1) :
    g.h1Map ((LinearMap.range C₁.boundaryToCycles).mkQ z) = 0 ↔
      ∃ b : C₂.C0, C₂.d0 b = g.f1 z.val := by
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  change Submodule.Quotient.mk (g.cyclesMap z) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩; exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩; exact ⟨b, Subtype.ext hb⟩

/-- 前段の像に入る実H¹類は、粗cocycleとの差のprimitiveを持つ。 -/
theorem h1_mk_mem_range_iff (z : LinearMap.ker C₁.d1) :
    (LinearMap.range C₁.boundaryToCycles).mkQ z ∈ LinearMap.range f.h1Map ↔
      ∃ a : LinearMap.ker C₀.d1, ∃ c : C₁.C0, z.val - f.f1 a.val = C₁.d0 c := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := (LinearMap.range C₀.boundaryToCycles).mkQ_surjective x
    have hm : z - f.cyclesMap a ∈ LinearMap.range C₁.boundaryToCycles :=
      (Submodule.Quotient.eq _).mp hx.symm
    obtain ⟨c, hc⟩ := hm
    exact ⟨a, c, (congrArg Subtype.val hc).symm⟩
  · rintro ⟨a, c, hc⟩
    refine ⟨(LinearMap.range C₀.boundaryToCycles).mkQ a, ?_⟩
    rw [ThreeCochainComplex.Hom.h1Map_mk]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-c, Subtype.ext ?_⟩
    change C₁.d0 (-c) = f.f1 a.val - z.val
    rw [map_neg, ← hc]; abel

/-- 実H¹での相殺射の核は、前段像に属する中間類とちょうど一致する。 -/
theorem cancellation_mk_eq_zero_iff (z : LinearMap.ker C₁.d1)
    (hz : g.h1Map ((LinearMap.range C₁.boundaryToCycles).mkQ z) = 0) :
    DefectSequence.cancellation f.h1Map g.h1Map
      ⟨(LinearMap.range C₁.boundaryToCycles).mkQ z, hz⟩ = 0 ↔
      ∃ a : LinearMap.ker C₀.d1, ∃ c : C₁.C0, z.val - f.f1 a.val = C₁.d0 c := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact h1_mk_mem_range_iff f z
end Representatives

section ZeroDefect
variable {U V W : Type*}
variable [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
variable [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
variable [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
variable (f : U →ₗ[ℚ] V) (g : V →ₗ[ℚ] W)

/-- 共通入力の零欠損は二射の合成で閉じる。 -/
theorem zeroDefect_comp (hf : blockDefect f = (0, 0)) (hg : blockDefect g = (0, 0)) :
    blockDefect (g.comp f) = (0, 0) := by
  apply (blockDefect_eq_zero_iff_bijective _).mpr
  exact ((blockDefect_eq_zero_iff_bijective _).mp hg).comp
    ((blockDefect_eq_zero_iff_bijective _).mp hf)

/-- 前段と直接比較の零欠損は後段の零欠損を与える。 -/
theorem zeroDefect_second (hf : blockDefect f = (0, 0))
    (hgf : blockDefect (g.comp f) = (0, 0)) : blockDefect g = (0, 0) := by
  apply (blockDefect_eq_zero_iff_bijective _).mpr
  exact (Function.Bijective.of_comp_iff g
    ((blockDefect_eq_zero_iff_bijective f).mp hf)).mp
    ((blockDefect_eq_zero_iff_bijective _).mp hgf)

/-- 後段と直接比較の零欠損は前段の零欠損を与える。 -/
theorem zeroDefect_first (hg : blockDefect g = (0, 0))
    (hgf : blockDefect (g.comp f) = (0, 0)) : blockDefect f = (0, 0) := by
  apply (blockDefect_eq_zero_iff_bijective _).mpr
  exact (Function.Bijective.of_comp_iff'
    ((blockDefect_eq_zero_iff_bijective g).mp hg) f).mp
    ((blockDefect_eq_zero_iff_bijective _).mp hgf)

/-- 恒等比較の零欠損。 -/
theorem zeroDefect_id : blockDefect (LinearMap.id : V →ₗ[ℚ] V) = (0, 0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr Function.bijective_id
end ZeroDefect

section ActualLaw
variable {Source : Type u} [Fintype Source]
variable {q₀ q₁ q₂ : Reading Source}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}
variable (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂)
variable (laws : FiniteLawFamily Source)
variable (h₀ : laws.Adequate q₀) (h₁ : laws.Adequate q₁) (h₂ : laws.Adequate q₂)

/-- 同じ原始Law入力の実H¹二射に対する全六項完全列。 -/
theorem generated_sixTerm_exact :
    let f := M₀₁.generatedComparisonH1Map laws h₀ h₁
    let g := M₁₂.generatedComparisonH1Map laws h₁ h₂
    Function.Injective (DefectSequence.first f g) ∧
    Function.Exact (DefectSequence.first f g) (DefectSequence.second f g) ∧
    Function.Exact (DefectSequence.second f g) (DefectSequence.cancellation f g) ∧
    Function.Exact (DefectSequence.cancellation f g) (DefectSequence.fourth f g) ∧
    Function.Exact (DefectSequence.fourth f g) (DefectSequence.fifth f g) ∧
    Function.Surjective (DefectSequence.fifth f g) :=
  DefectSequence.sixTerm_exact _ _

/-- 同じLaw入力から生成した直接H¹比較の核欠損公式。 -/
theorem generated_kernel_dimension :
    (blockDefect ((comparisonComp M₀₁ M₁₂).generatedComparisonH1Map laws h₀ h₂)).1 +
      Module.finrank ℚ (LinearMap.range (DefectSequence.cancellation
        (M₀₁.generatedComparisonH1Map laws h₀ h₁)
        (M₁₂.generatedComparisonH1Map laws h₁ h₂))) =
    (blockDefect (M₀₁.generatedComparisonH1Map laws h₀ h₁)).1 +
      (blockDefect (M₁₂.generatedComparisonH1Map laws h₁ h₂)).1 := by
  rw [generatedComparisonH1Map_comp M₀₁ M₁₂ laws h₀ h₁ h₂]
  exact DefectSequence.kernel_dimension _ _

/-- 同じLaw入力から生成した直接H¹比較の余核欠損公式。 -/
theorem generated_cokernel_dimension :
    (blockDefect ((comparisonComp M₀₁ M₁₂).generatedComparisonH1Map laws h₀ h₂)).2 +
      Module.finrank ℚ (LinearMap.range (DefectSequence.cancellation
        (M₀₁.generatedComparisonH1Map laws h₀ h₁)
        (M₁₂.generatedComparisonH1Map laws h₁ h₂))) =
    (blockDefect (M₀₁.generatedComparisonH1Map laws h₀ h₁)).2 +
      (blockDefect (M₁₂.generatedComparisonH1Map laws h₁ h₂)).2 := by
  rw [generatedComparisonH1Map_comp M₀₁ M₁₂ laws h₀ h₁ h₂]
  exact DefectSequence.cokernel_dimension _ _
/-- 同じLaw族の三比較の零欠損の2-out-of-3を全方向で示す。 -/
theorem generated_zeroDefect_twoOfThree :
    let f := M₀₁.generatedComparisonH1Map laws h₀ h₁
    let g := M₁₂.generatedComparisonH1Map laws h₁ h₂
    let h := (comparisonComp M₀₁ M₁₂).generatedComparisonH1Map laws h₀ h₂
    (blockDefect f = (0, 0) → blockDefect g = (0, 0) → blockDefect h = (0, 0)) ∧
    (blockDefect f = (0, 0) → blockDefect h = (0, 0) → blockDefect g = (0, 0)) ∧
    (blockDefect g = (0, 0) → blockDefect h = (0, 0) → blockDefect f = (0, 0)) := by
  dsimp only
  rw [generatedComparisonH1Map_comp M₀₁ M₁₂ laws h₀ h₁ h₂]
  exact ⟨zeroDefect_comp _ _, zeroDefect_second _ _, zeroDefect_first _ _⟩
end ActualLaw

/-- 複体全体の等号によるtarget移送は実H¹の二欠損を保存する。 -/
theorem transportHom_defect {C : ThreeCochainComplex.{0,w₀} ℚ}
    {D E : ThreeCochainComplex.{0,w₁} ℚ} (h : D = E)
    (f : ThreeCochainComplex.Hom C D) :
    blockDefect (transportHom h f).h1Map = blockDefect f.h1Map := by
  cases h; rfl

section ActualSubset
variable {Source : Type u}
variable {q₀ q₁ q₂ : Reading Source}
variable {h₀₁ : q₀.CoarserThan q₁} {h₁₂ : q₁.CoarserThan q₂}
variable {N₀ : TargetSupportedNerve q₀} {N₁ : TargetSupportedNerve q₁}
variable {N₂ : TargetSupportedNerve q₂}
variable (M₀₁ : TargetSupportedNerveMorphism q₀ q₁ h₀₁ N₀ N₁)
variable (M₁₂ : TargetSupportedNerveMorphism q₁ q₂ h₁₂ N₁ N₂)
variable (A : Set q₀.Target)

/-- 共通Aのcanonical逆像族の実H¹二射に対する全六項完全列。 -/
theorem aSubnerve_sixTerm_exact :
    let f := (M₀₁.aSubnerveComparisonHom A).h1Map
    let g := (M₁₂.aSubnerveComparisonHom (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A)).h1Map
    Function.Injective (DefectSequence.first f g) ∧
    Function.Exact (DefectSequence.first f g) (DefectSequence.second f g) ∧
    Function.Exact (DefectSequence.second f g) (DefectSequence.cancellation f g) ∧
    Function.Exact (DefectSequence.cancellation f g) (DefectSequence.fourth f g) ∧
    Function.Exact (DefectSequence.fourth f g) (DefectSequence.fifth f g) ∧
    Function.Surjective (DefectSequence.fifth f g) :=
  DefectSequence.sixTerm_exact _ _

set_option maxHeartbeats 800000 in
/-- canonical逆像の同定を伴う直接生成H¹の核欠損公式。 -/
theorem aSubnerve_kernel_dimension :
    let f := (M₀₁.aSubnerveComparisonHom A).h1Map
    let g := (M₁₂.aSubnerveComparisonHom (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A)).h1Map
    let h := ((comparisonComp M₀₁ M₁₂).aSubnerveComparisonHom A).h1Map
    (blockDefect h).1 + Module.finrank ℚ (LinearMap.range (DefectSequence.cancellation f g)) =
      (blockDefect f).1 + (blockDefect g).1 := by
  dsimp only
  rw [← transportHom_defect (congrArg N₂.targetSubsetComplex
    (comparisonFactor_preimage_comp h₀₁ h₁₂ A))
    ((comparisonComp M₀₁ M₁₂).aSubnerveComparisonHom A),
    aSubnerveComparisonHom_h1Map_comp M₀₁ M₁₂ A]
  exact DefectSequence.kernel_dimension _ _

set_option maxHeartbeats 800000 in
/-- canonical逆像の同定を伴う直接生成H¹の余核欠損公式。 -/
theorem aSubnerve_cokernel_dimension :
    let f := (M₀₁.aSubnerveComparisonHom A).h1Map
    let g := (M₁₂.aSubnerveComparisonHom (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A)).h1Map
    let h := ((comparisonComp M₀₁ M₁₂).aSubnerveComparisonHom A).h1Map
    (blockDefect h).2 + Module.finrank ℚ (LinearMap.range (DefectSequence.cancellation f g)) =
      (blockDefect f).2 + (blockDefect g).2 := by
  dsimp only
  rw [← transportHom_defect (congrArg N₂.targetSubsetComplex
    (comparisonFactor_preimage_comp h₀₁ h₁₂ A))
    ((comparisonComp M₀₁ M₁₂).aSubnerveComparisonHom A),
    aSubnerveComparisonHom_h1Map_comp M₀₁ M₁₂ A]
  exact DefectSequence.cokernel_dimension _ _

set_option maxHeartbeats 800000 in
/-- 共通Aの三比較の零欠損の2-out-of-3。全q₁部分集合へ量化を広げない。 -/
theorem aSubnerve_zeroDefect_twoOfThree :
    let f := (M₀₁.aSubnerveComparisonHom A).h1Map
    let g := (M₁₂.aSubnerveComparisonHom (comparisonFactor q₀ q₁ h₀₁ ⁻¹' A)).h1Map
    let h := ((comparisonComp M₀₁ M₁₂).aSubnerveComparisonHom A).h1Map
    (blockDefect f = (0, 0) → blockDefect g = (0, 0) → blockDefect h = (0, 0)) ∧
    (blockDefect f = (0, 0) → blockDefect h = (0, 0) → blockDefect g = (0, 0)) ∧
    (blockDefect g = (0, 0) → blockDefect h = (0, 0) → blockDefect f = (0, 0)) := by
  dsimp only
  rw [← transportHom_defect (congrArg N₂.targetSubsetComplex
    (comparisonFactor_preimage_comp h₀₁ h₁₂ A))
    ((comparisonComp M₀₁ M₁₂).aSubnerveComparisonHom A),
    aSubnerveComparisonHom_h1Map_comp M₀₁ M₁₂ A]
  exact ⟨zeroDefect_comp _ _, zeroDefect_second _ _, zeroDefect_first _ _⟩
end ActualSubset
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
