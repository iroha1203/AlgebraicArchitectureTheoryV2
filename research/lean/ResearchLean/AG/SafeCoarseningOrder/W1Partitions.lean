import ResearchLean.AG.SafeCoarseningOrder.CycleQuotientHomology
import Mathlib.Tactic.FinCases

/-! # W1 の全chart分割と元商写像

## Implementation notes

restricted-growth色表は全四点分割を生成する原始一覧である。六関係の全場合を
反射/対称/推移と同値関係extで検査して完全性を証明する。
chart数は元色写像全射から商mkと可換な全単射を構成した後で数える。
四つの指定縮約だけの候補一覧は全分割を落とすため採用しない。
-/
set_option maxHeartbeats 1200000
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
/-- 四元の全15分割をrestricted-growth色表で原始生成する。 -/
def partitionMap (i : Fin 15) (v : ZMod 4) : Fin 4 :=
  ![![0,0,0,0],![0,0,0,1],![0,0,1,0],![0,0,1,1],![0,0,1,2],![0,1,0,0],![0,1,0,1],![0,1,0,2],![0,1,1,0],![0,1,1,1],![0,1,1,2],![0,1,2,0],![0,1,2,1],![0,1,2,2],![0,1,2,3]] i v
/-- 元有限色表の核としてchart分割を生成する。 -/
def partition (i : Fin 15) : Setoid (ZMod 4) := Setoid.ker (partitionMap i)
/-- 元分割関係の基本API。期待安全性を関係へ入力しない。 -/
@[simp] theorem partition_relation_iff (i : Fin 15) (v w : ZMod 4) :
    (partition i).r v w ↔ partitionMap i v=partitionMap i w := Iff.rfl
/-- 四点の同値関係全recordは六非対角関係で定まる。 -/
theorem four_rel_ext {P Q : Setoid (ZMod 4)}
    (h01 : P.r 0 1 ↔ Q.r 0 1)
    (h02 : P.r 0 2 ↔ Q.r 0 2)
    (h03 : P.r 0 3 ↔ Q.r 0 3)
    (h12 : P.r 1 2 ↔ Q.r 1 2)
    (h13 : P.r 1 3 ↔ Q.r 1 3)
    (h23 : P.r 2 3 ↔ Q.r 2 3)
    : P=Q := by
  apply Setoid.ext; intro v w
  fin_cases v <;> fin_cases w
  · exact iff_of_true (P.refl 0) (Q.refl 0)
  · exact h01
  · exact h02
  · exact h03
  · exact (P.comm' (x := 1) (y := 0)).trans (h01.trans (Q.comm' (x := 0) (y := 1)))
  · exact iff_of_true (P.refl 1) (Q.refl 1)
  · exact h12
  · exact h13
  · exact (P.comm' (x := 2) (y := 0)).trans (h02.trans (Q.comm' (x := 0) (y := 2)))
  · exact (P.comm' (x := 2) (y := 1)).trans (h12.trans (Q.comm' (x := 1) (y := 2)))
  · exact iff_of_true (P.refl 2) (Q.refl 2)
  · exact h23
  · exact (P.comm' (x := 3) (y := 0)).trans (h03.trans (Q.comm' (x := 0) (y := 3)))
  · exact (P.comm' (x := 3) (y := 1)).trans (h13.trans (Q.comm' (x := 1) (y := 3)))
  · exact (P.comm' (x := 3) (y := 2)).trans (h23.trans (Q.comm' (x := 2) (y := 3)))
  · exact iff_of_true (P.refl 3) (Q.refl 3)
/-- 原始反射/対称/推移から任意chart分割を全15表へ分類する。 -/
theorem classify_chart (Q : Setoid (ZMod 4)) : ∃ i : Fin 15, Q=partition i := by
  classical
  by_cases h01 : Q (0 : ZMod 4) 1
  ·
    by_cases h02 : Q (0 : ZMod 4) 2
    ·
      by_cases h03 : Q (0 : ZMod 4) 3
      ·
        by_cases h12 : Q (1 : ZMod 4) 2
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              refine ⟨0, ?_⟩
              apply four_rel_ext
              · exact iff_of_true h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h23 (by rw [partition_relation_iff]; decide +kernel)
            ·
              exact (h23 (Q.trans (Q.symm h02) h03)).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h13 (Q.trans (Q.symm h01) h03)).elim
            ·
              exact (h13 (Q.trans (Q.symm h01) h03)).elim
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h12 (Q.trans (Q.symm h01) h02)).elim
            ·
              exact (h12 (Q.trans (Q.symm h01) h02)).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h12 (Q.trans (Q.symm h01) h02)).elim
            ·
              exact (h12 (Q.trans (Q.symm h01) h02)).elim
      ·
        by_cases h12 : Q (1 : ZMod 4) 2
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h03 (Q.trans h01 h13)).elim
            ·
              exact (h03 (Q.trans h01 h13)).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h03 (Q.trans h02 h23)).elim
            ·
              refine ⟨1, ?_⟩
              apply four_rel_ext
              · exact iff_of_true h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h03 (Q.trans h01 h13)).elim
            ·
              exact (h03 (Q.trans h01 h13)).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h03 (Q.trans h02 h23)).elim
            ·
              exact (h12 (Q.trans (Q.symm h01) h02)).elim
    ·
      by_cases h03 : Q (0 : ZMod 4) 3
      ·
        by_cases h12 : Q (1 : ZMod 4) 2
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h02 (Q.trans h01 h12)).elim
            ·
              exact (h02 (Q.trans h01 h12)).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h02 (Q.trans h01 h12)).elim
            ·
              exact (h02 (Q.trans h01 h12)).elim
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h02 (Q.trans h03 (Q.symm h23))).elim
            ·
              refine ⟨2, ?_⟩
              apply four_rel_ext
              · exact iff_of_true h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h02 (Q.trans h03 (Q.symm h23))).elim
            ·
              exact (h13 (Q.trans (Q.symm h01) h03)).elim
      ·
        by_cases h12 : Q (1 : ZMod 4) 2
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h02 (Q.trans h01 h12)).elim
            ·
              exact (h02 (Q.trans h01 h12)).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h02 (Q.trans h01 h12)).elim
            ·
              exact (h02 (Q.trans h01 h12)).elim
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h03 (Q.trans h01 h13)).elim
            ·
              exact (h03 (Q.trans h01 h13)).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              refine ⟨3, ?_⟩
              apply four_rel_ext
              · exact iff_of_true h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h23 (by rw [partition_relation_iff]; decide +kernel)
            ·
              refine ⟨4, ?_⟩
              apply four_rel_ext
              · exact iff_of_true h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
  ·
    by_cases h02 : Q (0 : ZMod 4) 2
    ·
      by_cases h03 : Q (0 : ZMod 4) 3
      ·
        by_cases h12 : Q (1 : ZMod 4) 2
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h01 (Q.trans h02 (Q.symm h12))).elim
            ·
              exact (h01 (Q.trans h02 (Q.symm h12))).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h01 (Q.trans h02 (Q.symm h12))).elim
            ·
              exact (h01 (Q.trans h02 (Q.symm h12))).elim
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h01 (Q.trans h03 (Q.symm h13))).elim
            ·
              exact (h01 (Q.trans h03 (Q.symm h13))).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              refine ⟨5, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h23 (by rw [partition_relation_iff]; decide +kernel)
            ·
              exact (h23 (Q.trans (Q.symm h02) h03)).elim
      ·
        by_cases h12 : Q (1 : ZMod 4) 2
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h01 (Q.trans h02 (Q.symm h12))).elim
            ·
              exact (h01 (Q.trans h02 (Q.symm h12))).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h01 (Q.trans h02 (Q.symm h12))).elim
            ·
              exact (h01 (Q.trans h02 (Q.symm h12))).elim
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h03 (Q.trans h02 h23)).elim
            ·
              refine ⟨6, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h03 (Q.trans h02 h23)).elim
            ·
              refine ⟨7, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
    ·
      by_cases h03 : Q (0 : ZMod 4) 3
      ·
        by_cases h12 : Q (1 : ZMod 4) 2
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h01 (Q.trans h03 (Q.symm h13))).elim
            ·
              exact (h01 (Q.trans h03 (Q.symm h13))).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h02 (Q.trans h03 (Q.symm h23))).elim
            ·
              refine ⟨8, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h01 (Q.trans h03 (Q.symm h13))).elim
            ·
              exact (h01 (Q.trans h03 (Q.symm h13))).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h02 (Q.trans h03 (Q.symm h23))).elim
            ·
              refine ⟨11, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
      ·
        by_cases h12 : Q (1 : ZMod 4) 2
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              refine ⟨9, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h23 (by rw [partition_relation_iff]; decide +kernel)
            ·
              exact (h23 (Q.trans (Q.symm h12) h13)).elim
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h13 (Q.trans h12 h23)).elim
            ·
              refine ⟨10, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
        ·
          by_cases h13 : Q (1 : ZMod 4) 3
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              exact (h12 (Q.trans h13 (Q.symm h23))).elim
            ·
              refine ⟨12, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)
          ·
            by_cases h23 : Q (2 : ZMod 4) 3
            ·
              refine ⟨13, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_true h23 (by rw [partition_relation_iff]; decide +kernel)
            ·
              refine ⟨14, ?_⟩
              apply four_rel_ext
              · exact iff_of_false h01 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h02 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h03 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h12 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h13 (by rw [partition_relation_iff]; decide +kernel)
              · exact iff_of_false h23 (by rw [partition_relation_iff]; decide +kernel)


/-- 色表に現れる原始色数。元商全単射を下で証明する。 -/
def numClasses (i : Fin 15) : ℕ := ![1,2,2,2,3,2,2,3,2,2,3,3,3,3,4] i
/-- 各元色を、その色数のFinへ証拠付きで再表示する。 -/
def colorValue (i : Fin 15) (v : ZMod 4) : Fin (numClasses i) :=
  ⟨(partitionMap i v).val,by fin_cases i <;> fin_cases v <;> decide +kernel⟩
/-- 色の再表示は元値を保持する基本API。 -/
@[simp] theorem colorValue_val (i : Fin 15) (v : ZMod 4) :
    (colorValue i v).val=(partitionMap i v).val := rfl
/-- 原始一覧の各色は元chartの値として発生する。 -/
theorem colorValue_surjective (i : Fin 15) : Function.Surjective (colorValue i) := by
  fin_cases i <;> intro c <;> fin_cases c <;>
    first | exact ⟨0,by decide +kernel⟩ | exact ⟨1,by decide +kernel⟩ |
      exact ⟨2,by decide +kernel⟩ | exact ⟨3,by decide +kernel⟩
/-- 元分割の商chartを元発生色へ、mkと可換な全単射で同定する。 -/
def chartEquiv (i : Fin 15) : Quotient (partition i) ≃ Fin (numClasses i) where
  toFun := Quotient.lift (colorValue i) (by
    intro v w h
    apply Fin.ext
    have hh := (partition_relation_iff i v w).mp h
    simpa only [colorValue_val] using congrArg (fun x : Fin 4 => x.val) hh)
  invFun c := Quotient.mk (partition i) (Function.surjInv (colorValue_surjective i) c)
  left_inv c := Quotient.inductionOn c (fun v => by
    apply Quotient.sound
    change (partition i).r (Function.surjInv (colorValue_surjective i) (colorValue i v)) v
    rw [partition_relation_iff]
    apply Fin.ext
    have h := Function.rightInverse_surjInv (colorValue_surjective i) (colorValue i v)
    simpa only [colorValue_val] using congrArg (fun x : Fin (numClasses i) => x.val) h)
  right_inv c := Function.rightInverse_surjInv (colorValue_surjective i) c
/-- 同定後の元chart商mkは同じ発生色を返す。 -/
@[simp] theorem chartEquiv_mk (i : Fin 15) (v : ZMod 4) :
    chartEquiv i (Quotient.mk (partition i) v)=colorValue i v := rfl
/-- 元商全単射から各原始分割のchart数を導く。 -/
theorem chart_card (i : Fin 15) : Fintype.card (Quotient (partition i))=numClasses i :=
  (Fintype.card_congr (chartEquiv i)).trans (Fintype.card_fin _)
end AAT.AG.SafeCoarseningOrder.W1

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
