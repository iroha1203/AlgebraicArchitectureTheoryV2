import ResearchLean.AG.SafeCoarseningOrder.CycleSubsetEvaluation
import ResearchLean.AG.AtlasDefectComposition.LawSubsetDefectDecomposition

/-! # 閉路の元Lawと発生label重複度

## Implementation notes

target等号分割では元Boolを返すLawを使い二発生labelを保持する。
target全関係を含む任意分割では定数Lawを使う。同じ生成LawH¹比較の欠損を
実部分領域比較の和へ戻し、署名が一致してもlabelを同一視しない。
同署名labelのdedupは元Law直和を変えるため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.Cycle
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
/-- 元Bool sourceをそのまま読む一つの非定数Law。 -/
def separatingLaw : FiniteLawFamily Bool where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Bool
  valueDecidableEq _ := inferInstance
  eval _ s := s
/-- 元非定数評価の基本API。 -/
@[simp] theorem separating_eval (l : separatingLaw.Law) (s : Bool) : separatingLaw.eval l s=s := rfl
/-- 元sourceの両値が生成する二発生label。 -/
def separatingLabel (b : Bool) : LawValueLabel separatingLaw := LawValueLabel.ofSource separatingLaw () b
/-- 発生labelを元Bool値へ、両発生点を保持して同定する。 -/
def separatingLabelEquiv : LawValueLabel separatingLaw ≃ Bool where
  toFun l := l.value
  invFun := separatingLabel
  left_inv l := by
    rcases l with ⟨law,value,h⟩
    cases law
    apply LawValueLabel.ext <;> rfl
  right_inv _ := rfl
/-- 二つの元値の発生labelは保持される。 -/
theorem separating_labels_card : Fintype.card (LawValueLabel separatingLaw)=2 :=
  (Fintype.card_congr separatingLabelEquiv).trans Fintype.card_bool
/-- 全署名が一致する閉路でも元二labelは異なる。 -/
theorem separating_labels_ne : separatingLabel false≠separatingLabel true := by
  intro h
  exact Bool.false_ne_true (congrArg separatingLabelEquiv h)
/-- 元Bool sourceで定数Unit値を取る一つのLaw。 -/
def constantLaw : FiniteLawFamily Bool where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Unit
  valueDecidableEq _ := inferInstance
  eval _ _ := ()
/-- 定数Law評価の基本API。 -/
@[simp] theorem constant_eval (l : constantLaw.Law) (s : Bool) : constantLaw.eval l s=() := rfl
/-- 元source falseから生成する唯一の定数label。 -/
def constantLabel : LawValueLabel constantLaw := LawValueLabel.ofSource constantLaw () false
/-- 定数Lawでは全発生labelは元指定labelと一致する。 -/
instance constantLabelsUnique : Unique (LawValueLabel constantLaw) where
  default := constantLabel
  uniq l := by rcases l with ⟨law,value,h⟩; cases law; cases value; apply LawValueLabel.ext <;> rfl
/-- 定数Lawの発生label重複度は1。 -/
theorem constant_labels_card : Fintype.card (LawValueLabel constantLaw)=1 := Fintype.card_unique
variable (n : ℕ) [NeZero n] (hn : 2 ≤ n)
omit [NeZero n] in
/-- target等号分割では元非定数Lawを商readingへ明示descendする。 -/
theorem separating_adequate (Q : Setoid (ZMod n)) :
    separatingLaw.Adequate ((input n hn).quotientReading (⊥,Q)) := by
  intro l
  refine ⟨Quotient.lift id (fun s t h => h),fun s => rfl⟩
omit [NeZero n] in
/-- 元Bool/idに対する商readingは元target商mkである。 -/
@[simp] theorem quotient_read (R : Coarsening Bool (ZMod n)) (b : Bool) :
    ((input n hn).quotientReading R).read b=Quotient.mk R.1 b := rfl
omit [NeZero n] in
/-- 元非定数Lawの値blockは元Bool値の等号を保持する。 -/
theorem separating_fiber_mk (Q : Setoid (ZMod n)) (l : LawValueLabel separatingLaw) (b : Bool) :
    Quotient.mk (⊥ : Setoid Bool) b ∈ labelValueFiber separatingLaw
      ((input n hn).quotientReading (⊥,Q)) (separating_adequate n hn Q) l ↔ b=l.value := by
  rw [mem_labelValueFiber]
  have hc := lawDescend_commutes separatingLaw ((input n hn).quotientReading (⊥,Q))
    (separating_adequate n hn Q) l.law b
  rw [quotient_read,separating_eval] at hc
  rw [hc]
omit [NeZero n] in
/-- 各元発生labelの値blockは元商mkを保持するsingleton。 -/
theorem separating_fiber (Q : Setoid (ZMod n)) (l : LawValueLabel separatingLaw) :
    labelValueFiber separatingLaw ((input n hn).quotientReading (⊥,Q))
      (separating_adequate n hn Q) l={Quotient.mk (⊥ : Setoid Bool) l.value} := by
  ext t
  induction t using Quotient.inductionOn with | _ b =>
    rw [separating_fiber_mk,Set.mem_singleton_iff,Quotient.eq,Setoid.bot_def]
/-- 元二発生labelの異なる値blockは全支持で同じ名付きセル署名を持つ。 -/
theorem separating_fibers_same_signature (Q : Setoid (ZMod n)) (l m : LawValueLabel separatingLaw) :
    SupportSignature.alpha ((input n hn).quotientSupported (⊥,Q)) (input n hn).supported
      ((input n hn).quotient_coarser (⊥,Q))
      (labelValueFiber separatingLaw ((input n hn).quotientReading (⊥,Q)) (separating_adequate n hn Q) l)=
    SupportSignature.alpha ((input n hn).quotientSupported (⊥,Q)) (input n hn).supported
      ((input n hn).quotient_coarser (⊥,Q))
      (labelValueFiber separatingLaw ((input n hn).quotientReading (⊥,Q)) (separating_adequate n hn Q) m) := by
  rw [alpha_nonempty n hn (⊥,Q) _ (labelValueFiber_nonempty separatingLaw _ _ l),
    alpha_nonempty n hn (⊥,Q) _ (labelValueFiber_nonempty separatingLaw _ _ m)]
omit [NeZero n] in
/-- 定数Lawは任意target/chart分割対の商readingへdescendする。 -/
theorem constant_adequate (R : Coarsening Bool (ZMod n)) :
    constantLaw.Adequate ((input n hn).quotientReading R) := fun _ => ⟨fun _ => (),fun _ => rfl⟩
omit [NeZero n] in
/-- 定数発生labelの値blockは元商target全体である。 -/
theorem constant_fiber (R : Coarsening Bool (ZMod n)) (l : LawValueLabel constantLaw) :
    labelValueFiber constantLaw ((input n hn).quotientReading R) (constant_adequate n hn R) l=Set.univ := by
  ext t
  simp only [Set.mem_univ,iff_true]
  rw [mem_labelValueFiber]
  letI : Subsingleton (constantLaw.Value l.law) := inferInstanceAs (Subsingleton Unit)
  exact Subsingleton.elim _ _
/-- 同じ非定数Lawの粗adequacyと導出した細adequacyによる実生成H¹射。 -/
def separatingMap (Q : Setoid (ZMod n)) :=
  ((input n hn).quotientMorphism (⊥,Q)).generatedComparisonH1Map separatingLaw
    (separating_adequate n hn Q) (adequate_of_coarser separatingLaw
      ((input n hn).quotient_coarser (⊥,Q)) (separating_adequate n hn Q))
/-- 同じ定数Lawの実生成H¹射。 -/
def constantMap (R : Coarsening Bool (ZMod n)) :=
  ((input n hn).quotientMorphism R).generatedComparisonH1Map constantLaw
    (constant_adequate n hn R) (adequate_of_coarser constantLaw
      ((input n hn).quotient_coarser R) (constant_adequate n hn R))
/-- 全元二labelを保持する実Law欠損は同じ非空領域欠損の二倍。 -/
theorem separatingMap_defect (Q : Setoid (ZMod n)) :
    blockDefect (separatingMap n hn Q) =
      (2*(blockDefect (((input n hn).quotientComparison (⊥,Q)).aSubnerveComparisonHom Set.univ).h1Map).1,
       2*(blockDefect (((input n hn).quotientComparison (⊥,Q)).aSubnerveComparisonHom Set.univ).h1Map).2) := by
  rw [separatingMap,lawH1Defect_subset_sum]
  have hh (l : LawValueLabel separatingLaw) :=
    actual_nonempty_defect_eq_full n hn (⊥,Q)
      (labelValueFiber separatingLaw ((input n hn).quotientReading (⊥,Q))
        (separating_adequate n hn Q) l)
      (labelValueFiber_nonempty separatingLaw _ (separating_adequate n hn Q) l)
  simp_rw [PrimitiveInput.quotient_actualHom_old] at hh
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,separating_labels_card,nsmul_eq_mul,Nat.cast_id]
  rw [PrimitiveInput.quotient_actualHom_old]
/-- 一つの定数labelの実Law欠損は同じ全領域比較そのもの。 -/
theorem constantMap_defect (R : Coarsening Bool (ZMod n)) :
    blockDefect (constantMap n hn R)=
      blockDefect (((input n hn).quotientComparison R).aSubnerveComparisonHom Set.univ).h1Map := by
  rw [constantMap,lawH1Defect_subset_sum]
  have hh (l : LawValueLabel constantLaw) :=
    actual_nonempty_defect_eq_full n hn R
      (labelValueFiber constantLaw ((input n hn).quotientReading R)
        (constant_adequate n hn R) l)
      (labelValueFiber_nonempty constantLaw _ (constant_adequate n hn R) l)
  simp_rw [PrimitiveInput.quotient_actualHom_old] at hh
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,constant_labels_card,one_nsmul]
  rw [PrimitiveInput.quotient_actualHom_old]
end AAT.AG.SafeCoarseningOrder.Cycle

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
