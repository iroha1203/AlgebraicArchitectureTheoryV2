import ResearchLean.AG.AtlasDefectComposition.SignatureUniversal
import Formal.Util.AssertStandardAxioms
/-! # 全セル署名の join 合同商

Implementation notes: 核関係の集合商に像半束の順序を移す。
その join は代表元の union と一致し、Fix(cl) へ順序同型で接続する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SignatureGeometry
universe v w
variable {T : Type v} {Ω : Type w} (S : T → Set Ω)
/-- 同署名関係は両引数の union に関する合同である。 -/
theorem signature_join_congr {A B C D : Set T}
    (h : alpha S A = alpha S B) (k : alpha S C = alpha S D) :
    alpha S (A ∪ C) = alpha S (B ∪ D) := by rw [alpha_union,alpha_union,h,k]
/-- 署名核の通常の集合商。 -/
abbrev SignatureQuotient := Quotient (signatureSetoid S)
/-- 商の順序は保持された全名付きセル集合の包含である。 -/
instance quotientPartialOrder : PartialOrder (SignatureQuotient S) :=
  PartialOrder.lift (quotientEquiv S) (quotientEquiv S).injective
/-- 商の join は像の union を代表元に依存せず移したもの。 -/
instance quotientSemilatticeSup : SemilatticeSup (SignatureQuotient S) where
  __ := quotientPartialOrder S
  sup a b := (quotientEquiv S).symm ((quotientEquiv S) a ⊔ (quotientEquiv S) b)
  le_sup_left := by
    intro a b
    change (quotientEquiv S) a ≤ (quotientEquiv S) ((quotientEquiv S).symm _)
    rw [Equiv.apply_symm_apply]
    exact le_sup_left
  le_sup_right := by
    intro a b
    change (quotientEquiv S) b ≤ (quotientEquiv S) ((quotientEquiv S).symm _)
    rw [Equiv.apply_symm_apply]
    exact le_sup_right
  sup_le := by
    intro a b c h k
    change (quotientEquiv S) ((quotientEquiv S).symm _) ≤ (quotientEquiv S) c
    rw [Equiv.apply_symm_apply]
    exact sup_le h k
/-- 商の bottom は空セル署名に対応する。 -/
instance quotientOrderBot : OrderBot (SignatureQuotient S) where
  bot := (quotientEquiv S).symm ⊥
  bot_le := by
    intro a
    change (quotientEquiv S) ((quotientEquiv S).symm ⊥) ≤ (quotientEquiv S) a
    rw [Equiv.apply_symm_apply]
    exact bot_le
/-- 通常の商と全セル署名像の順序同型。 -/
def quotientOrderIso : SignatureQuotient S ≃o Signature S where
  toEquiv := quotientEquiv S
  map_rel_iff' := Iff.rfl
/-- 商から Fix(cl) までの指定順序同型。 -/
def quotientClosedOrderIso : SignatureQuotient S ≃o ClosedSubset S :=
  (quotientOrderIso S).trans (closedOrderIso S)
/-- 商射の代表元評価は元の実 sigma である。 -/
@[simp] theorem quotientEquiv_mk (A : Set T) :
    quotientEquiv S (Quotient.mk (signatureSetoid S) A) = sigma S A := rfl
/-- 商に移した join は subset union の商と一致する。 -/
theorem quotient_mk_union (A B : Set T) :
    Quotient.mk (signatureSetoid S) (A ∪ B) =
      Quotient.mk (signatureSetoid S) A ⊔ Quotient.mk (signatureSetoid S) B := by
  apply (quotientOrderIso S).injective
  rw [(quotientOrderIso S).map_sup]
  change sigma S (A ∪ B) = sigma S A ⊔ sigma S B
  exact Subtype.ext (alpha_union S A B)
/-- 空 subset の商は指定 bottom と一致する。 -/
theorem quotient_mk_empty : Quotient.mk (signatureSetoid S) ∅ = (⊥ : SignatureQuotient S) := by
  apply (quotientOrderIso S).injective
  rw [(quotientOrderIso S).map_bot]
  exact Subtype.ext (alpha_empty S)
/-- Fix(cl) の指定同型は join を閉包した union へ送る。 -/
theorem closedOrderIso_sup (a b : Signature S) :
    (closedOrderIso S (a ⊔ b)).val = closure S ((closedOrderIso S a).val ∪ (closedOrderIso S b).val) := by
  rw [(closedOrderIso S).map_sup]
  rfl
/-- 有限セル入力から通常の商の有限性を導く。 -/
instance quotientFinite [Finite Ω] : Finite (SignatureQuotient S) :=
  Finite.of_equiv (Signature S) (quotientEquiv S).symm
end AAT.AG.AtlasDefectComposition.SignatureGeometry
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SignatureGeometry
