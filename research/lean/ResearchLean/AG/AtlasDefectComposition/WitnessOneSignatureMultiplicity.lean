import ResearchLean.AG.AtlasDefectComposition.WitnessOneFullLaw
import ResearchLean.AG.AtlasDefectComposition.LawSignatureRestoration
import Formal.Util.AssertStandardAxioms
/-! # W1 の実二ラベルが保持する同署名多重度

Implementation notes: 粗側の二つの値 fiber を原始評価から同定する。
全名付き粗細セル署名が一致しても、元の発生ラベルは二つ残る。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase SelectedFamilies
/-- 原始第一座標 Law の粗 fiber は各単独 Bool 値である。 -/
theorem label_fiber (a : Bool) : labelValueFiber laws q₀ adequate₀ (label a) = {a} := by
  ext t
  have hd := lawDescend_commutes laws q₀ adequate₀ () (t,false,false)
  change lawDescend laws q₀ adequate₀ () t = t at hd
  change lawDescend laws q₀ adequate₀ () t = a ↔ t = a
  rw [hd]
/-- W1 の二つの非空粗 fiber は全名付きセル署名が一致する。 -/
theorem singleton_alpha_eq (a b : Bool) : SupportSignature.alpha N₀ N₁ coarser₀₁ {a} =
    SupportSignature.alpha N₀ N₁ coarser₀₁ {b} := by
  apply (SupportSignature.alpha_eq_iff N₀ N₁ coarser₀₁ _ _).mpr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro c; simp
  · intro e; simp [edgeSupport_univ₀]
  · intro f; exact f.elim
  · intro c
    simp only [Set.mem_univ,true_and,Set.mem_singleton_iff,factor₀₁]
    constructor <;> intro _
    · exact ⟨(b,false),rfl⟩
    · exact ⟨(a,false),rfl⟩
  · intro e
    simp only [edgeSupport_univ₁,Set.mem_univ,true_and,Set.mem_singleton_iff,factor₀₁]
    constructor <;> intro _
    · exact ⟨(b,false),rfl⟩
    · exact ⟨(a,false),rfl⟩
  · intro f; exact f.elim
/-- 二つの実値 fiber が持つ同じ全セル署名。 -/
theorem singleton_sigma_eq (a b : Bool) : SupportSignature.sigma N₀ N₁ coarser₀₁ {a} =
    SupportSignature.sigma N₀ N₁ coarser₀₁ {b} :=
  (SupportSignature.sigma_eq_iff N₀ N₁ coarser₀₁ _ _).mpr (singleton_alpha_eq a b)
/-- 元の coarse chart 0 があるので、同じ署名は bottom ではない。 -/
theorem singleton_nonbottom (a : Bool) : SupportSignature.sigma N₀ N₁ coarser₀₁ {a} ≠ ⊥ := by
  intro hz
  have hm := (SupportSignature.mem_alpha_coarseChart N₀ N₁ coarser₀₁ {a} 0).mpr
    ⟨a,by simp,by simp⟩
  have he := congrArg Subtype.val hz
  change SupportSignature.alpha N₀ N₁ coarser₀₁ {a} = ∅ at he
  rw [he] at hm
  exact hm
/-- W1 の全発生ラベルから作る実 selected 族。 -/
abbrev selected := lawSelectedFamily (h:=coarser₀₁) N₀ N₁ laws adequate₀
/-- W1 の実二 fiber 共通の非零署名。 -/
def sharedSignature : NonzeroSignature (SupportSignature.family N₀ N₁ coarser₀₁) :=
  ⟨SupportSignature.sigma N₀ N₁ coarser₀₁ {false},singleton_nonbottom false⟩
/-- すべての発生ラベルが同じ非零署名を保持する。 -/
theorem label_sigma (l : LawValueLabel laws) :
    SupportSignature.sigma N₀ N₁ coarser₀₁ (selected.subset l) = sharedSignature.val := by
  obtain ⟨a,rfl⟩ := labels_exhaust l
  change SupportSignature.sigma N₀ N₁ coarser₀₁ (labelValueFiber laws q₀ adequate₀ (label a)) = _
  rw [label_fiber]
  exact singleton_sigma_eq a false
/-- 共通署名の元の添字 fiber は全二ラベルと指定同値を持つ。 -/
def sharedFiberEquiv : Fiber (SupportSignature.family N₀ N₁ coarser₀₁) selected sharedSignature ≃ LawValueLabel laws where
  toFun i := i.1.1
  invFun l := ⟨⟨l,by change SupportSignature.sigma N₀ N₁ coarser₀₁ (selected.subset l) ≠ ⊥;rw [label_sigma];exact sharedSignature.2⟩,
    Subtype.ext (label_sigma l)⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- W1 の同じ署名における多重度は 2 であり、集合への圧縮で失われる。 -/
theorem shared_multiplicity : multiplicity (SupportSignature.family N₀ N₁ coarser₀₁) selected sharedSignature = 2 := by
  rw [multiplicity_apply,Nat.card_congr sharedFiberEquiv,Nat.card_eq_fintype_card]
  exact label_card
/-- W1 の全 Law 実錐も、この多重度を保持する canonical 族から復元する。 -/
def fullLawMultiplicityConeIso := lawMultiplicityConeIso N₀ N₁ laws adequate₀ M₀₁ adequate₁
end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
