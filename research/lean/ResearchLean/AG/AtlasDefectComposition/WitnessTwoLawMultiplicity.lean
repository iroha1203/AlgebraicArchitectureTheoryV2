import ResearchLean.AG.AtlasDefectComposition.WitnessTwoTargets
import ResearchLean.AG.AtlasDefectComposition.LawSignatureComparison
import Formal.Util.AssertStandardAxioms
/-! # W2 の原始 Law ラベルと同署名二成分

Implementation notes: 恒等 Law の発生値を元の Source 点へ同定する。
同署名の a,b を別のラベルとして保持し、実 Law 比較と錐を同じ多重度から復元する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition.WitnessTwo
open CanonicalResolution ResolutionInvariance TwoPhase SelectedFamilies
/-- 原始恒等 Law の t による発生ラベル。 -/
def label (t : Source) : LawValueLabel laws := LawValueLabel.ofSource laws () t
/-- 原始恒等 Law の全発生ラベルは元の三点に尽くされる。 -/
theorem labels_exhaust (l : LawValueLabel laws) : ∃ t : Source, l = label t := by
  cases l with
  | mk law value generated =>
    cases law
    exact ⟨value, by apply LawValueLabel.ext <;> rfl⟩
/-- 実発生ラベルと元の Source 三点との指定全単射。 -/
def labelEquivSource : LawValueLabel laws ≃ Source where
  toFun l := l.value
  invFun := label
  left_inv l := by obtain ⟨t,rfl⟩ := labels_exhaust l; rfl
  right_inv _ := rfl
/-- W2 の全発生ラベル数は3であり、元の三成分を保持する。 -/
theorem label_card : Nat.card (LawValueLabel laws) = 3 := by
  rw [Nat.card_congr labelEquivSource,Nat.card_eq_fintype_card]
  rfl
/-- 原始 Law のラベル fiber は同じ target 単独点である。 -/
theorem label_fiber (t : Source) : labelValueFiber laws q adequate (label t) = {t} := by
  ext a
  have hd := lawDescend_commutes laws q adequate () a
  change lawDescend laws q adequate () a = a at hd
  change lawDescend laws q adequate () a = t ↔ a = t
  rw [hd]
/-- 実 a,b ラベルは値が異なるため別添字である。 -/
theorem labels_a_ne_b : label 0 ≠ label 1 := by
  intro h
  have hv := congrArg (fun l : LawValueLabel laws => l.value) h
  exact (by decide : (0 : Source) ≠ 1) hv
/-- 各原始単独点の署名には実 chart が含まれ bottom ではない。 -/
theorem singleton_nonbottom (t : Source) : sigma {t} ≠ ⊥ := by
  intro hz
  have he := congrArg Subtype.val hz
  change alpha {t} = ∅ at he
  have hh : ∃ c : Bool, t ∈ support c := by
    fin_cases t
    · exact ⟨false,by simp [support]⟩
    · exact ⟨false,by simp [support]⟩
    · exact ⟨true,by simp [support]⟩
  obtain ⟨c,hc⟩ := hh
  have hm := (coarse_chart_select {t} c).mpr ⟨t,hc,by simp⟩
  rw [he] at hm
  exact hm
/-- W2 の元の全発生ラベル selected 族。 -/
abbrev selected := lawSelectedFamily (h:=coarser) N N laws adequate
/-- 元の a,b が共有する非零全セル署名。 -/
def sharedSignature : NonzeroSignature family := ⟨sigma {0},singleton_nonbottom 0⟩
/-- 同じ Law の shared 署名に入る値は元の a,b だけである。 -/
theorem label_sigma_iff (l : LawValueLabel laws) :
    sigma (selected.subset l) = sharedSignature.val ↔ labelEquivSource l = 0 ∨ labelEquivSource l = 1 := by
  obtain ⟨t,rfl⟩ := labels_exhaust l
  change sigma (labelValueFiber laws q adequate (label t)) = sigma {0} ↔ t = 0 ∨ t = 1
  rw [label_fiber,sigma_eq_iff]
  fin_cases t <;> simp
/-- shared 署名の元のラベル fiber は a,b の二点と全単射で対応する。 -/
def sharedFiberEquiv : Fiber family selected sharedSignature ≃ {t : Source // t = 0 ∨ t = 1} where
  toFun i := ⟨labelEquivSource i.1.1,(label_sigma_iff i.1.1).mp (congrArg Subtype.val i.2)⟩
  invFun t := ⟨⟨label t.1,by
      change sigma (labelValueFiber laws q adequate (label t.1)) ≠ ⊥
      rw [label_fiber];exact singleton_nonbottom t.1⟩,
    Subtype.ext ((label_sigma_iff (label t.1)).mpr t.2)⟩
  left_inv i := by apply Subtype.ext;apply Subtype.ext;exact labelEquivSource.left_inv i.1.1
  right_inv _ := rfl
/-- W2 の原始 a,b 成分は同署名多重度2として残る。 -/
theorem shared_multiplicity : multiplicity family selected sharedSignature = 2 := by
  rw [multiplicity_apply,Nat.card_congr sharedFiberEquiv,Nat.card_eq_fintype_card]
  decide
/-- a の元のラベルを削除せずに保持する active 添字。 -/
def activeA : Active family selected := ⟨label 0,by
  change sigma (labelValueFiber laws q adequate (label 0)) ≠ ⊥
  rw [label_fiber];exact singleton_nonbottom 0⟩
/-- b の元のラベルを削除せずに保持する active 添字。 -/
def activeB : Active family selected := ⟨label 1,by
  change sigma (labelValueFiber laws q adequate (label 1)) ≠ ⊥
  rw [label_fiber];exact singleton_nonbottom 1⟩
/-- 同署名でも a,b は元の直和の別の非零添字である。 -/
theorem active_a_ne_b : activeA ≠ activeB := fun h => labels_a_ne_b (congrArg Subtype.val h)
/-- a,b の保持された二添字は同じ全セル署名へ送られる。 -/
theorem active_a_b_signature : activeSignature family selected activeA = activeSignature family selected activeB := by
  apply Subtype.ext
  change sigma (labelValueFiber laws q adequate (label 0)) = sigma (labelValueFiber laws q adequate (label 1))
  rw [label_fiber,label_fiber]
  exact sigma_a_eq_b
/-- W2 の実全 Law coarse 複体をこの元の selected 族へ送る指定同型。 -/
def fullLawSelectedCoarseIso := lawSelectedCoarseIso (h:=coarser) N N laws adequate
/-- W2 の実全 Law 比較を元の同じ三ラベル selected 族へ送る正方形。 -/
theorem fullLawSelected_square : zeroExtensionMap (M.generatedComparisonHom laws adequate adequate) ≫
    (lawSelectedFineIso N N laws adequate adequate).hom =
    fullLawSelectedCoarseIso.hom ≫ SelectedFamilyComplex.comparison N N coarser selected M :=
  lawSelected_square N N laws adequate adequate M
/-- W2 の実全 Law 錐を a,b の多重度2を含む canonical 族から復元する。 -/
def fullLawMultiplicityConeIso := lawMultiplicityConeIso N N laws adequate M adequate
/-- 実 W2 の選択セル包含には不成立例もある。a の L chart は c に選択されない。 -/
theorem not_selectedLE_a_c : ¬ SubsetRestriction.SelectedLE N ({0} : Set Source) {2} := by
  intro h
  have hh := h.1 false ⟨0,by simp [support],by simp⟩
  simp [support] at hh
end AAT.AG.AtlasDefectComposition.WitnessTwo
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessTwo
