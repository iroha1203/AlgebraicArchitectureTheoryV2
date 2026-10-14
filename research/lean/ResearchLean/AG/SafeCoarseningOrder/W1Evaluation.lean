import ResearchLean.AG.SafeCoarseningOrder.CycleSubsetEvaluation
import ResearchLean.AG.SafeCoarseningOrder.W1Partitions
import ResearchLean.AG.AtlasGluingWidth.WidthObservation

/-! # W1 全分割の原始商セルと実診断

## Implementation notes

元全15色表の商mkと可換な全単射を有向商辺へ拡張する。
逆向き辺を別の順序対として保持し、実比較rankの共通定理へ戻した後でJを評価する。
辺向きを忘れた無向商は逆向き実セルを変えるため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
open CanonicalResolution ResolutionInvariance TwoPhase
/-- 指定Bool/id・四有向辺・全台の同じ原始入力。 -/
abbrev input : PrimitiveInput Bool Bool (ZMod 4) := Cycle.input 4 (by decide)
/-- 元指定辺の基本評価API。 -/
@[simp] theorem input_edge_iff (v w : ZMod 4) : input.edge v w ↔ w=v+1 :=
  Cycle.input_edge_iff 4 (by decide) v w
/-- 任意target分割と元chart色表の独立な全候補。 -/
def candidate (P : Setoid Bool) (i : Fin 15) : Coarsening Bool (ZMod 4) := (P,partition i)
/-- 元chart分割関係を公開する基本API。 -/
@[simp] theorem candidate_chart_iff (P : Setoid Bool) (i : Fin 15) (v w : ZMod 4) :
    (candidate P i).2.r v w ↔ partitionMap i v=partitionMap i w := partition_relation_iff i v w
/-- target分割は元Pそのものである基本API。 -/
@[simp] theorem candidate_target_iff (P : Setoid Bool) (i : Fin 15) (s t : Bool) :
    (candidate P i).1.r s t ↔ P.r s t := Iff.rfl
/-- 元発生色間に残る非対角有向辺。原始四辺から生成する。 -/
def colorEdge (i : Fin 15) (a b : Fin (numClasses i)) : Prop :=
  a≠b ∧ ∃ v : ZMod 4,colorValue i v=a ∧ colorValue i (v+1)=b
/-- 有向色辺の全生成条件を公開する。 -/
@[simp] theorem colorEdge_iff (i : Fin 15) (a b : Fin (numClasses i)) :
    colorEdge i a b ↔ a≠b ∧ ∃ v : ZMod 4,colorValue i v=a ∧ colorValue i (v+1)=b := Iff.rfl
/-- 色辺の有限原始表は計算可能な同値/存在検査を持つ。 -/
instance colorEdgeDecidable (i : Fin 15) (a b : Fin (numClasses i)) : Decidable (colorEdge i a b) := by
  exact inferInstanceAs (Decidable (a≠b ∧ ∃ v : ZMod 4,
    colorValue i v=a ∧ colorValue i (v+1)=b))
/-- 色有向辺セルは異端点順序対のsubtypeである。 -/
abbrev ColorEdge (i : Fin 15) := {e : Fin (numClasses i) × Fin (numClasses i) // colorEdge i e.1 e.2}
/-- 原始色順序対の全表から有向色辺を尽くす有限instance。 -/
instance colorEdgeFintype (i : Fin 15) : Fintype (ColorEdge i) := inferInstance
/-- 恒等色表で元辺0→1が存在する正instance。 -/
theorem color_edge_positive : colorEdge 14 (colorValue 14 0) (colorValue 14 1) := by
  rw [colorEdge_iff]
  decide +kernel
/-- 全chart合併では指定対角辺が存在しない負instance。 -/
theorem color_edge_top_negative : ¬ colorEdge 0 (colorValue 0 0) (colorValue 0 0) := by
  rw [colorEdge_iff]
  decide +kernel
/-- 元商有向辺と元色表有向辺を、両端mkを保持して全単射にする。 -/
def edgeEquiv (P : Setoid Bool) (i : Fin 15) : input.QuotientEdge (candidate P i) ≃ ColorEdge i where
  toFun e := ⟨(chartEquiv i e.1.1,chartEquiv i e.1.2),by
    obtain ⟨hn,v,w,he,hv,hw⟩ := e.2
    rw [input_edge_iff] at he
    subst w
    refine ⟨fun h => hn ((chartEquiv i).injective h),v,?_,?_⟩
    · exact (chartEquiv_mk i v).symm.trans (congrArg (chartEquiv i) hv)
    · exact (chartEquiv_mk i (v+1)).symm.trans (congrArg (chartEquiv i) hw)⟩
  invFun e := ⟨((chartEquiv i).symm e.1.1,(chartEquiv i).symm e.1.2),by
    obtain ⟨hn,v,hv,hw⟩ := e.2
    refine ⟨fun h => hn ((chartEquiv i).symm.injective h),v,v+1,
      (input_edge_iff _ _).mpr rfl,?_,?_⟩
    · change Quotient.mk (partition i) v=(chartEquiv i).symm e.1.1
      apply (chartEquiv i).injective
      rw [chartEquiv_mk,Equiv.apply_symm_apply]
      exact hv
    · change Quotient.mk (partition i) (v+1)=(chartEquiv i).symm e.1.2
      apply (chartEquiv i).injective
      rw [chartEquiv_mk,Equiv.apply_symm_apply]
      exact hw⟩
  left_inv e := Subtype.ext (Prod.ext ((chartEquiv i).symm_apply_apply e.1.1)
    ((chartEquiv i).symm_apply_apply e.1.2))
  right_inv e := Subtype.ext (Prod.ext ((chartEquiv i).apply_symm_apply e.1.1)
    ((chartEquiv i).apply_symm_apply e.1.2))

/-- 元有向色辺の有限表から得る全15分割の辺数。 -/
def numEdges (i : Fin 15) : ℕ := ![0,2,2,2,3,2,2,4,2,2,3,3,4,3,4] i
/-- 全有限原始色順序対をkernelで数え、予想rankを入力しない。 -/
theorem color_edge_card (i : Fin 15) : Fintype.card (ColorEdge i)=numEdges i := by
  fin_cases i <;> decide +kernel
/-- 原始商順序対の有限性から全商辺の有限instanceを生成する。 -/
instance quotientEdgeFintype (P : Setoid Bool) (i : Fin 15) :
    Fintype (input.QuotientEdge (candidate P i)) :=
  Cycle.quotientEdgeFintype 4 (by decide) (candidate P i)
/-- 元商辺と色辺の全単射から同じ商辺数を得る。 -/
theorem quotient_edge_card (P : Setoid Bool) (i : Fin 15) :
    Fintype.card (input.QuotientEdge (candidate P i))=numEdges i :=
  (Fintype.card_congr (edgeEquiv P i)).trans (color_edge_card i)
/-- top以外の全元分割には原始有向商辺が実在する。 -/
theorem color_edge_exists (i : Fin 15) (hi : i≠0) : Nonempty (ColorEdge i) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact ⟨⟨(colorValue 1 2,colorValue 1 (2+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 2 1,colorValue 2 (1+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 3 1,colorValue 3 (1+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 4 1,colorValue 4 (1+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 5 0,colorValue 5 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 6 0,colorValue 6 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 7 0,colorValue 7 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 8 0,colorValue 8 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 9 0,colorValue 9 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 10 0,colorValue 10 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 11 0,colorValue 11 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 12 0,colorValue 12 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 13 0,colorValue 13 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(colorValue 14 0,colorValue 14 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
/-- 同じ全分割対のtop以外で実有向商辺を構成する。 -/
def quotientEdge (P : Setoid Bool) (i : Fin 15) (hi : i≠0) :
    input.QuotientEdge (candidate P i) :=
  (edgeEquiv P i).symm (Classical.choice (color_edge_exists i hi))
/-- top以外の全候補と空含む全領域を同じ実比較のJへ評価する。 -/
theorem candidate_defect (P : Setoid Bool) (i : Fin 15) (hi : i≠0)
    (A : Set (Quotient P)) :
    blockDefect ((input.quotientComparison (candidate P i)).aSubnerveComparisonHom A).h1Map =
      @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _) (numEdges i-numClasses i,0) (0,0) := by
  have h := Cycle.all_a_defect 4 (by decide) (candidate P i) (quotientEdge P i hi) A
  change _ = @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _)
    (Fintype.card (input.QuotientEdge (candidate P i))-Fintype.card (Quotient (partition i)),0) (0,0) at h
  rw [quotient_edge_card,chart_card] at h
  exact h
/-- top以外の全候補の同じSafeを原始色セル数から確定する。 -/
theorem candidate_safe_iff (P : Setoid Bool) (i : Fin 15) (hi : i≠0) :
    input.Safe (candidate P i) ↔ numEdges i=numClasses i := by
  have h := Cycle.safe_iff_edges_eq_charts 4 (by decide) (candidate P i) (quotientEdge P i hi)
  change input.Safe (candidate P i) ↔ Fintype.card (input.QuotientEdge (candidate P i))=Fintype.card (Quotient (partition i)) at h
  rw [quotient_edge_card,chart_card] at h
  exact h

/-- 全chart併合色表では異端点有向色辺が存在しない。 -/
instance topColorEdgeIsEmpty : IsEmpty (ColorEdge 0) where
  false e := by
    letI : Subsingleton (Fin (numClasses 0)) := inferInstanceAs (Subsingleton (Fin 1))
    have h := e.2
    rw [colorEdge_iff] at h
    exact h.1 (Subsingleton.elim _ _)
/-- 元全chart商では実辺型が空なので同じ粗H¹は零となる。 -/
theorem top_H1_subsingleton (P : Setoid Bool) :
    Subsingleton (Cycle.coarseComplex 4 (by decide) (candidate P 0)).H1 := by
  letI : IsEmpty (input.QuotientEdge (candidate P 0)) :=
    ⟨fun e => isEmptyElim (edgeEquiv P 0 e)⟩
  letI : IsEmpty ((input.quotientSupported (candidate P 0)).EdgeInTargetSubset Set.univ) :=
    ⟨fun e => isEmptyElim (edgeEquiv P 0 e.1)⟩
  letI : Subsingleton (Cycle.coarseComplex 4 (by decide) (candidate P 0)).C1 :=
    inferInstanceAs (Subsingleton (((input.quotientSupported (candidate P 0)).EdgeInTargetSubset Set.univ) → ℚ))
  infer_instance
/-- 指定全chart商の同じ全領域比較は実余核1を持つ。 -/
theorem top_full_defect (P : Setoid Bool) :
    blockDefect ((input.quotientComparison (candidate P 0)).aSubnerveComparisonHom Set.univ).h1Map=(0,1) := by
  letI := top_H1_subsingleton P
  rw [← AtlasDefectComposition.transportHom_defect
    (congrArg input.supported.targetSubsetComplex Set.preimage_univ)]
  change blockDefect (Cycle.fullHom 4 (by decide) (candidate P 0)).h1Map=(0,1)
  rw [AtlasGluingWidth.Width.defect_zero_domain,Cycle.full_H1_dimension]
/-- 全chart併合の全非空商領域にも同じ実余核1が残る。 -/
theorem top_nonempty_defect (P : Setoid Bool) (A : Set (Quotient P)) (hA : A.Nonempty) :
    blockDefect ((input.quotientComparison (candidate P 0)).aSubnerveComparisonHom A).h1Map=(0,1) := by
  exact (Cycle.actual_nonempty_defect_eq_full 4 (by decide) (candidate P 0) A hA).trans (top_full_defect P)
/-- 全chart併合は同じ実full比較の非零余核により安全でない。 -/
theorem top_not_safe (P : Setoid Bool) : ¬ input.Safe (candidate P 0) := by
  intro hs
  have hd := (input.safe_iff_zeroDefect (candidate P 0)).mp hs Set.univ
  rw [top_full_defect] at hd
  exact Nat.one_ne_zero (congrArg Prod.snd hd)
/-- 原始全15分割を評価した全安全候補の正確な分類。 -/
theorem candidate_safe_classification (P : Setoid Bool) (i : Fin 15) :
    input.Safe (candidate P i) ↔ i≠0 ∧ i≠7 ∧ i≠12 := by
  by_cases hi : i=0
  · subst i
    exact iff_of_false (top_not_safe P) (by simp)
  · rw [candidate_safe_iff P i hi]
    fin_cases i <;> decide +kernel
end AAT.AG.SafeCoarseningOrder.W1



#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
