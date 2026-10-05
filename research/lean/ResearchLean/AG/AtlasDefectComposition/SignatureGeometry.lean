import Mathlib.Order.Closure
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Powerset
import Formal.Util.AssertStandardAxioms
/-! # 名付きセル族からの台署名・閉包・商

Implementation notes: 各targetの実セル集合からunionと包含を作る。
署名の像に有限join構造を与え、核関係の商と閉集合へ接続する。
閉集合のjoinは閉包したunionであり、未使用targetを除く仮定は加えない。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SignatureGeometry
universe v w
variable {T : Type v} {Ω : Type w} (S : T → Set Ω)
/-- Eの各targetの名付きセル族から作る全セル選択。 -/
def alpha (A : Set T) : Set Ω := {c | ∃ t ∈ A, c ∈ S t}
/-- Eの復元側写像。全セルがXに入るtargetを保持する。 -/
def gamma (X : Set Ω) : Set T := {t | S t ⊆ X}
/-- alphaのAPI補題。セル名と実所属targetの存在を保持する。 -/
@[simp] theorem mem_alpha (A : Set T) (c : Ω) :
    c ∈ alpha S A ↔ ∃ t ∈ A, c ∈ S t := Iff.rfl
/-- gammaのAPI補題。部分セル数ではなく全所属セルの包含を読む。 -/
@[simp] theorem mem_gamma (X : Set Ω) (t : T) : t ∈ gamma S X ↔ S t ⊆ X := Iff.rfl
/-- 空subsetの署名は全セル集合のbottomである。 -/
@[simp] theorem alpha_empty : alpha S ∅ = ∅ := by ext c; simp
/-- 全セル署名はsubsetのjoinを名付きセルのunionへ送る。 -/
theorem alpha_union (A B : Set T) : alpha S (A ∪ B) = alpha S A ∪ alpha S B := by
  ext c
  simp only [mem_alpha, Set.mem_union]
  constructor
  · rintro ⟨t, h | h, hc⟩
    · exact Or.inl ⟨t,h,hc⟩
    · exact Or.inr ⟨t,h,hc⟩
  · rintro (⟨t,h,hc⟩ | ⟨t,h,hc⟩)
    · exact ⟨t,Or.inl h,hc⟩
    · exact ⟨t,Or.inr h,hc⟩
/-- subsetの包含は全セル選択の包含へ移る。 -/
theorem alpha_mono : Monotone (alpha S) := by
  intro A B h c hc
  obtain ⟨t,ht,hc⟩ := hc
  exact ⟨t,h ht,hc⟩
/-- 復元側も名付きセル集合の包含を保つ。 -/
theorem gamma_mono : Monotone (gamma S) := by
  intro X Y h t ht
  change X ⊆ Y at h
  exact ht.trans h
/-- EのGalois接続。任意のsubsetと任意の名付きセル集合を量化する。 -/
theorem galois : GaloisConnection (alpha S) (gamma S) := by
  intro A X
  constructor
  · intro h t ht c hc
    exact h ⟨t,ht,hc⟩
  · rintro h c ⟨t,ht,hc⟩
    exact h ht hc
/-- Eの閉包はセル選択からの復元であり、診断値から作らない。 -/
def closure (A : Set T) : Set T := gamma S (alpha S A)
/-- 閉包のAPI補題。元のsubsetはその閉包へ入る。 -/
theorem subset_closure (A : Set T) : A ⊆ closure S A :=
  (galois S A (alpha S A)).mp Set.Subset.rfl
/-- alpha-gamma-alphaの吸収則。全セルの選択を保持する。 -/
theorem alpha_gamma_alpha (A : Set T) : alpha S (gamma S (alpha S A)) = alpha S A := by
  apply Set.Subset.antisymm
  · exact (galois S _ _).mpr Set.Subset.rfl
  · exact alpha_mono S (subset_closure S A)
/-- 閉包は元の名付きセル署名を変更しない。 -/
@[simp] theorem alpha_closure (A : Set T) : alpha S (closure S A) = alpha S A :=
  alpha_gamma_alpha S A
/-- 閉包の単調性は二つの生成写像の単調性から出る。 -/
theorem closure_mono : Monotone (closure S) := fun _ _ h => gamma_mono S (alpha_mono S h)
/-- Eの閉包の冪等性。unsupported targetがあっても成立する。 -/
@[simp] theorem closure_idempotent (A : Set T) : closure S (closure S A) = closure S A := by
  unfold closure
  rw [alpha_gamma_alpha]
/-- 標準ClosureOperatorへの接続。三法則は今回構成した入力族から証明する。 -/
def closureOperator : ClosureOperator (Set T) where
  toFun := closure S
  monotone' := closure_mono S
  le_closure' := subset_closure S
  idempotent' := closure_idempotent S
/-- Eの署名半束は実全セル選択の像である。 -/
abbrev Signature := {X : Set Ω // X ∈ Set.range (alpha S)}
/-- 部分集合を元の実署名へ送る。 -/
def sigma (A : Set T) : Signature S := ⟨alpha S A,⟨A,rfl⟩⟩
/-- sigmaのAPI補題。保持するセル集合は実alphaそのものである。 -/
@[simp] theorem sigma_val (A : Set T) : (sigma S A).val = alpha S A := rfl
/-- 全署名は実subsetで実現され、像への全射性が成立する。 -/
theorem sigma_surjective : Function.Surjective (sigma S) := by
  rintro ⟨X,A,h⟩
  exact ⟨A,Subtype.ext h⟩
/-- 同署名は六種類の名付きセル集合の等号を保持する。 -/
theorem sigma_eq_iff (A B : Set T) : sigma S A = sigma S B ↔ alpha S A = alpha S B :=
  ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
/-- 像のjoinは実名付きセル集合のunionである。 -/
instance signatureSemilatticeSup : SemilatticeSup (Signature S) where
  sup a b := ⟨a.val ∪ b.val,by
    obtain ⟨A,hA⟩ := a.property
    obtain ⟨B,hB⟩ := b.property
    exact ⟨A ∪ B,by rw [alpha_union,hA,hB]⟩⟩
  le_sup_left := fun _ _ => Set.subset_union_left
  le_sup_right := fun _ _ => Set.subset_union_right
  sup_le := fun _ _ _ h₁ h₂ => Set.union_subset h₁ h₂
/-- 署名のbottomは空セル集合であり、必ず像に入る。 -/
instance signatureOrderBot : OrderBot (Signature S) where
  bot := ⟨∅,⟨∅,alpha_empty S⟩⟩
  bot_le := fun _ => Set.empty_subset _
/-- 署名joinの公開評価則。 -/
@[simp] theorem signature_sup_val (a b : Signature S) : (a ⊔ b).val = a.val ∪ b.val := rfl
/-- 署名bottomの公開評価則。 -/
@[simp] theorem signature_bot_val : (⊥ : Signature S).val = ∅ := rfl
/-- 有限セルから署名の像の有限性を導く。targetの有限性を追加しない一般補助。 -/
instance signatureFinite [Finite Ω] : Finite (Signature S) := by
  classical
  letI := Fintype.ofFinite Ω
  infer_instance
/-- Eの標準商写像はbottom・joinを保持する。 -/
def sigmaHom : SupBotHom (Set T) (Signature S) where
  toFun := sigma S
  map_sup' := fun A B => Subtype.ext (alpha_union S A B)
  map_bot' := Subtype.ext (alpha_empty S)
/-- 全セル復元decoderはbottom・joinを保つ実包含である。 -/
def inclusionHom : SupBotHom (Signature S) (Set Ω) where
  toFun := Subtype.val
  map_sup' := fun _ _ => rfl
  map_bot' := rfl
/-- 署名核の関係は実alphaの等号である。 -/
def signatureSetoid : Setoid (Set T) := Setoid.ker (alpha S)
/-- Eの実署名をgammaで復元したsubsetは同じ全セル署名を持つ。 -/
theorem alpha_gamma_signature (X : Signature S) : alpha S (gamma S X.val) = X.val := by
  obtain ⟨A,h⟩ := X.property
  rw [← h]
  exact alpha_gamma_alpha S A
/-- Eのcanonical閉集合代表を署名へ戻す公開同定。 -/
@[simp] theorem sigma_gamma_signature (X : Signature S) : sigma S (gamma S X.val) = X :=
  Subtype.ext (alpha_gamma_signature S X)
/-- Eの通常の商を実署名の像へ同定する。標準集合の第一同型定理を使う。 -/
def quotientEquiv : Quotient (signatureSetoid S) ≃ Signature S :=
  Setoid.quotientKerEquivRange (alpha S)
/-- EのFix(cl)は閉包の実固定点である。 -/
abbrev ClosedSubset := {A : Set T // closure S A = A}
/-- 署名から閉集合への復元。閉包法則を実像の証人から導く。 -/
def closedEquiv : Signature S ≃ ClosedSubset S where
  toFun X := ⟨gamma S X.val,by
    obtain ⟨A,h⟩ := X.property
    rw [← h]
    exact closure_idempotent S A⟩
  invFun A := sigma S A.val
  left_inv X := by
    apply Subtype.ext
    change alpha S (gamma S X.val) = X.val
    obtain ⟨A,h⟩ := X.property
    rw [← h]
    exact alpha_gamma_alpha S A
  right_inv A := Subtype.ext A.property
/-- 固定点側の順序も実subsetの包含である。 -/
def closedOrderIso : Signature S ≃o ClosedSubset S where
  toEquiv := closedEquiv S
  map_rel_iff' := by
    intro X Y
    change gamma S X.val ⊆ gamma S Y.val ↔ X.val ⊆ Y.val
    constructor
    · intro h
      obtain ⟨A,hA⟩ := X.property
      obtain ⟨B,hB⟩ := Y.property
      have h' := alpha_mono S h
      change alpha S (gamma S X.val) ⊆ alpha S (gamma S Y.val) at h'
      rw [← hA,← hB,alpha_gamma_alpha,alpha_gamma_alpha] at h'
      rw [← hA,← hB]
      exact h'
    · intro h
      exact gamma_mono S h
/-- 閉集合のjoinを閉包したunionとして構成する。 -/
instance closedSemilatticeSup : SemilatticeSup (ClosedSubset S) where
  sup A B := ⟨closure S (A.val ∪ B.val),closure_idempotent S _⟩
  le_sup_left := fun _ _ => Set.subset_union_left.trans (subset_closure S _)
  le_sup_right := fun _ _ => Set.subset_union_right.trans (subset_closure S _)
  sup_le := by
    intro A B C hA hB
    have h := closure_mono S (Set.union_subset hA hB)
    simpa only [C.property] using h
/-- Fix(cl)のbottomは閉包したempty。unsupported targetを含み得る。 -/
instance closedOrderBot : OrderBot (ClosedSubset S) where
  bot := ⟨closure S ∅,closure_idempotent S _⟩
  bot_le := by
    intro A
    have h := closure_mono S (Set.empty_subset A.val)
    simpa only [A.property] using h
/-- 閉集合joinの公開評価則。 -/
@[simp] theorem closed_sup_val (A B : ClosedSubset S) :
    (A ⊔ B).val = closure S (A.val ∪ B.val) := rfl
/-- 閉集合bottomの公開評価則。 -/
@[simp] theorem closed_bot_val : (⊥ : ClosedSubset S).val = closure S ∅ := rfl
end AAT.AG.AtlasDefectComposition.SignatureGeometry
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SignatureGeometry
