import ResearchLean.AG.AtlasDefectComposition.WitnessTwoGeometry
import ResearchLean.AG.AtlasDefectComposition.SignatureQuotient
import Formal.Util.AssertStandardAxioms
/-! # W2 の四つの署名と零欠損の非 decoder 性

Implementation notes: 同じ原始 nerve の全六セル署名を二 chart の選択へ同定する。
欠損の零性は全 A で実 C1 の零性から導き、署名との違いを固定する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessTwo
open CanonicalResolution ResolutionInvariance TwoPhase
/-- W2 の全セル署名を元の二 chart の選択として読む。 -/
def chartSelection (s : SupportSignature.Signature N N coarser) : Set Bool :=
  {c | SupportSignature.coarseChart N N c ∈ s.val}
/-- 同じ二 chart の選択は W2 の全セル署名を必要十分に定める。 -/
theorem chartSelection_bijective : Function.Bijective chartSelection := by
  constructor
  · intro s t heq
    obtain ⟨A,rfl⟩ := SignatureGeometry.sigma_surjective family s
    obtain ⟨B,rfl⟩ := SignatureGeometry.sigma_surjective family t
    apply (sigma_eq_iff A B).mpr
    constructor
    · have hh := Set.ext_iff.mp heq false
      exact (coarse_false_mem A).symm.trans (hh.trans (coarse_false_mem B))
    · have hh := Set.ext_iff.mp heq true
      exact (coarse_true_mem A).symm.trans (hh.trans (coarse_true_mem B))
  · intro B
    refine ⟨sigma {t | (t = 0 ∧ false ∈ B) ∨ (t = 2 ∧ true ∈ B)},?_⟩
    ext c
    change SupportSignature.coarseChart N N c ∈ alpha _ ↔ c ∈ B
    cases c
    · rw [coarse_false_mem];simp
    · rw [coarse_true_mem];simp
/-- 四署名の元を保持する明示同値。 -/
def signatureEquiv : SupportSignature.Signature N N coarser ≃ Set Bool :=
  Equiv.ofBijective chartSelection chartSelection_bijective
/-- W2 は bottom を含むちょうど四つの全セル署名を持つ。 -/
theorem signature_card : Nat.card (SupportSignature.Signature N N coarser) = 4 := by
  rw [Nat.card_congr signatureEquiv,Nat.card_eq_fintype_card]
  decide
/-- 元の部分集合商にも同じ四つの全セル署名がある。 -/
theorem quotient_card : Nat.card (Quotient (SignatureGeometry.signatureSetoid family)) = 4 := by
  rw [Nat.card_congr (SignatureGeometry.quotientEquiv family)]
  exact signature_card
/-- a の閉包は実際に元の部分集合より大きい。 -/
theorem closure_strict : ({0} : Set Source) ⊂ SignatureGeometry.closure family {0} := by
  rw [closure_a]
  constructor
  · intro t ht
    simp only [Set.mem_singleton_iff] at ht
    simp [ht]
  · intro h
    have hh := h (by simp : (1 : Source) ∈ ({0,1} : Set Source))
    simp at hh
/-- 孤立 chart 入力の実 C1 は全 A で零加群である。 -/
instance subsetC1Subsingleton (A : Set Source) : Subsingleton (N.targetSubsetComplex A).C1 := by
  change Subsingleton (N.EdgeInTargetSubset A → ℚ)
  letI : IsEmpty (N.EdgeInTargetSubset A) := ⟨fun e => e.1.elim⟩
  infer_instance
/-- 実旧 H¹ 商も全 A で零である。 -/
instance subsetH1Subsingleton (A : Set Source) : Subsingleton (N.targetSubsetComplex A).H1 := by
  unfold ThreeCochainComplex.H1
  infer_instance
/-- 実生成比較の H¹ 射は全 A で全単射である。 -/
theorem actualH1_bijective (A : Set Source) : Function.Bijective (M.aSubnerveComparisonHom A).h1Map := by
  constructor
  · intro x y _; exact Subsingleton.elim _ _
  · intro y; exact ⟨0,Subsingleton.elim _ _⟩
/-- W2 の実診断次元は全 A で同じ零欠損である。 -/
theorem actualDefect_zero (A : Set Source) : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (actualH1_bijective A)
/-- 異なる元のセル署名を持つ a と c は同じ零欠損を持つ。 -/
theorem different_signature_same_defect : sigma {0} ≠ sigma {2} ∧
    blockDefect (M.aSubnerveComparisonHom {0}).h1Map =
      blockDefect (M.aSubnerveComparisonHom {2}).h1Map :=
  ⟨sigma_a_ne_c,(actualDefect_zero {0}).trans (actualDefect_zero {2}).symm⟩
/-- 診断次元だけから W2 の全名付きセル選択を復元する decoder は存在しない。 -/
theorem no_defect_decoder : ¬ ∃ d : ℕ × ℕ → SupportSignature.Signature N N coarser,
    ∀ A, d (blockDefect (M.aSubnerveComparisonHom A).h1Map) = sigma A := by
  rintro ⟨d,hd⟩
  apply sigma_a_ne_c
  have ha := hd {0}
  have hc := hd {2}
  rw [actualDefect_zero] at ha hc
  exact ha.symm.trans hc
end AAT.AG.AtlasDefectComposition.WitnessTwo
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessTwo
