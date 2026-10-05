import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyMonoidal
import Formal.Util.AssertStandardAxioms
/-! # 非交和の署名多重度

Implementation notes: 署名 fiber の元を非交和のタグで分ける。
濃度加法はこの添字全単射から従い、重複署名を一成分へ圧縮しない。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SelectedFamilies
universe u v
variable {T : Type u} {Ω : Type v} (S : T → Set Ω)
/-- 非交和の各署名 fiber は元の二つの fiber の非交和である。 -/
def fiberSumEquiv (F G : Family S) (s : NonzeroSignature S) :
    Fiber S (sum S F G) s ≃ Fiber S F s ⊕ Fiber S G s where
  toFun i := match i with
    | ⟨⟨Sum.inl a,ha⟩,hs⟩ => Sum.inl ⟨⟨a,ha⟩,hs⟩
    | ⟨⟨Sum.inr b,hb⟩,hs⟩ => Sum.inr ⟨⟨b,hb⟩,hs⟩
  invFun i := match i with
    | Sum.inl a => ⟨⟨Sum.inl a.1.1,a.1.2⟩,a.2⟩
    | Sum.inr b => ⟨⟨Sum.inr b.1.1,b.1.2⟩,b.2⟩
  left_inv := by rintro ⟨⟨a | b,h⟩,hs⟩ <;> rfl
  right_inv := by rintro (a | b) <;> rfl
/-- 空族の各署名 fiber は空である。 -/
instance emptyFiberIsEmpty (s : NonzeroSignature S) : IsEmpty (Fiber S (empty S) s) :=
  ⟨fun i => i.1.1.elim⟩
/-- 空族の全非零署名多重度は零である。 -/
theorem multiplicity_empty [Finite Ω] : multiplicity S (empty S) = 0 := by
  ext s
  simp only [multiplicity_apply,Finsupp.zero_apply]
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
/-- 非交和は各非零署名の多重度の加法へ送られる。 -/
theorem multiplicity_sum [Finite Ω] (F G : Family S) :
    multiplicity S (sum S F G) = multiplicity S F + multiplicity S G := by
  ext s
  rw [Finsupp.add_apply,multiplicity_apply,multiplicity_apply,multiplicity_apply,
    Nat.card_congr (fiberSumEquiv S F G s),Nat.card_sum]
end AAT.AG.AtlasDefectComposition.SelectedFamilies
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SelectedFamilies
