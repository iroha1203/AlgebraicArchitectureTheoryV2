import ResearchLean.AG.SafeCoarseningOrder.W2Input

/-! # W2 全共通上界と実診断

## Implementation notes

join商の四点sectionから任意上界関係を復元し、全十五分割を引き戻す。任意target分割を保持し全A実比較を評価する。一つの不安全joinだけで最大元不存在を結論する代替は安全上界を落とすため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W2
open CanonicalResolution ResolutionInvariance TwoPhase
open AtlasDefectComposition
/-- join商の原始sectionで任意共通上界関係を四点へ引き戻す。 -/
def compressed (Q : Setoid (ZMod 6)) : Setoid (ZMod 4) :=
  Setoid.comap (Function.surjInv joinMap_surjective) Q
/-- sectionによる元関係の引き戻し条件を公開する。 -/
theorem compressed_relation (Q : Setoid (ZMod 6)) (v w : ZMod 4) :
    (compressed Q).r v w ↔ Q.r (Function.surjInv joinMap_surjective v)
      (Function.surjInv joinMap_surjective w) := Iff.rfl
/-- join関係を含む任意上界を四点引き戻しから完全復元する。 -/
theorem compressed_reconstruct (Q : Setoid (ZMod 6)) (hQ : Setoid.ker joinMap ≤ Q) :
    Q=Setoid.comap joinMap (compressed Q) := by
  have hr (v : ZMod 6) : Q.r v (Function.surjInv joinMap_surjective (joinMap v)) := by
    apply hQ
    exact (Function.rightInverse_surjInv joinMap_surjective (joinMap v)).symm
  apply Setoid.ext
  intro v w
  change Q.r v w ↔ (compressed Q).r (joinMap v) (joinMap w)
  rw [compressed_relation]
  constructor
  · intro h
    exact Q.trans (Q.symm (hr v)) (Q.trans h (hr w))
  · intro h
    exact Q.trans (hr v) (Q.trans h (Q.symm (hr w)))
/-- 任意target分割と四点全分割の引き戻しで全上界候補を生成する。 -/
def upperCandidate (P : Setoid Bool) (i : Fin 15) : Coarsening Bool (ZMod 6) :=
  (P,Setoid.ker (fun v => W1.partitionMap i (joinMap v)))
/-- 元六点における全上界候補の関係評価。 -/
theorem upperCandidate_relation (P : Setoid Bool) (i : Fin 15) (v w : ZMod 6) :
    (upperCandidate P i).2.r v w ↔ W1.partitionMap i (joinMap v)=W1.partitionMap i (joinMap w) := Iff.rfl
/-- 四点分割の引き戻しは元join関係を必ず含む。 -/
theorem joined_le_upper_candidate (P : Setoid Bool) (i : Fin 15) :
    joined ≤ upperCandidate P i :=
  ⟨bot_le,fun _ _ h => congrArg (W1.partitionMap i) h⟩
/-- 任意上界のchart関係を全十五四点分割へ完全分類する。 -/
theorem classify_upper (R : Coarsening Bool (ZMod 6)) (hR : joined ≤ R) :
    ∃ i : Fin 15, R=upperCandidate R.1 i := by
  obtain ⟨i,hi⟩ := W1.classify_chart (compressed R.2)
  have hc := compressed_reconstruct R.2 hR.2
  rw [hi] at hc
  refine ⟨i,Prod.ext rfl ?_⟩
  apply hc.trans
  apply Setoid.ext; intro v w
  rw [Setoid.comap_rel,W1.partition_relation_iff]

/-- 四点分割の元発生色をjoinMap経由で六点へ戻す。 -/
def upperColor (i : Fin 15) (v : ZMod 6) : Fin (W1.numClasses i) := W1.colorValue i (joinMap v)
/-- 六点の色再表示は元分割の数値を保持する。 -/
theorem upperColor_val (i : Fin 15) (v : ZMod 6) :
    (upperColor i v).val=(W1.partitionMap i (joinMap v)).val := rfl
/-- 元六点から各上界色への全射を生成する。 -/
theorem upperColor_surjective (i : Fin 15) : Function.Surjective (upperColor i) :=
  (W1.colorValue_surjective i).comp joinMap_surjective
/-- 全上界の元商chartと発生色をmkと可換な全単射へする。 -/
def upperChartEquiv (P : Setoid Bool) (i : Fin 15) : Quotient ((upperCandidate P i).2) ≃ Fin (W1.numClasses i) where
  toFun := Quotient.lift (upperColor i) (by
    intro v w h
    apply Fin.ext
    have hh := (upperCandidate_relation P i v w).mp h
    simpa only [upperColor_val] using congrArg (fun x : Fin 4 => x.val) hh)
  invFun c := Quotient.mk ((upperCandidate P i).2) (Function.surjInv (upperColor_surjective i) c)
  left_inv c := Quotient.inductionOn c (fun v => by
    apply Quotient.sound
    change ((upperCandidate P i).2).r (Function.surjInv (upperColor_surjective i) (upperColor i v)) v
    rw [upperCandidate_relation]
    apply Fin.ext
    have h := Function.rightInverse_surjInv (upperColor_surjective i) (upperColor i v)
    simpa only [upperColor_val] using congrArg (fun x : Fin (W1.numClasses i) => x.val) h)
  right_inv c := Function.rightInverse_surjInv (upperColor_surjective i) c
/-- 元商mkは同じ六点色値を返す。 -/
@[simp] theorem upperChartEquiv_mk (P : Setoid Bool) (i : Fin 15) (v : ZMod 6) :
    upperChartEquiv P i (Quotient.mk ((upperCandidate P i).2) v)=upperColor i v := rfl
/-- 元商mk可換全単射から全上界のchart数を得る。 -/
theorem upper_chart_card (P : Setoid Bool) (i : Fin 15) : Fintype.card (Quotient ((upperCandidate P i).2))=W1.numClasses i :=
  (Fintype.card_congr (upperChartEquiv P i)).trans (Fintype.card_fin _)

/-- 元六有向辺から生成する異端点の有向色順序対。 -/
def colorEdge (i : Fin 15) (a b : Fin (W1.numClasses i)) : Prop :=
  a≠b ∧ ∃ v : ZMod 6,upperColor i v=a ∧ upperColor i (v+1)=b
/-- 有向色辺の原始生成条件を公開する。 -/
@[simp] theorem colorEdge_iff (i : Fin 15) (a b : Fin (W1.numClasses i)) :
    colorEdge i a b ↔ a≠b ∧ ∃ v : ZMod 6,upperColor i v=a ∧ upperColor i (v+1)=b := Iff.rfl
/-- 元六点の有限存在条件から色辺を決定する。 -/
instance colorEdgeDecidable (i : Fin 15) (a b : Fin (W1.numClasses i)) : Decidable (colorEdge i a b) := by
  exact inferInstanceAs (Decidable (a≠b ∧ ∃ v : ZMod 6,
    upperColor i v=a ∧ upperColor i (v+1)=b))
/-- 逆向き辺を別セルとして保持する有向色辺subtype。 -/
abbrev ColorEdge (i : Fin 15) := {e : Fin (W1.numClasses i) × Fin (W1.numClasses i) // colorEdge i e.1 e.2}
/-- 原始有向順序対の全表から色辺の有限性を生成する。 -/
instance colorEdgeFintype (i : Fin 15) : Fintype (ColorEdge i) := inferInstance
/-- join四chartの恒等色表には元a→bの有向辺が残る。 -/
theorem color_edge_positive : colorEdge 14 (upperColor 14 0) (upperColor 14 1) := by
  rw [colorEdge_iff]
  decide +kernel
/-- 全chart併合の同色対には非対角色辺がない。 -/
theorem color_edge_top_negative : ¬ colorEdge 0 (upperColor 0 0) (upperColor 0 0) := by
  rw [colorEdge_iff]
  decide +kernel
/-- 元上界商辺と有向色辺を両端mkを保持する全単射へする。 -/
def edgeEquiv (P : Setoid Bool) (i : Fin 15) : input.QuotientEdge (upperCandidate P i) ≃ ColorEdge i where
  toFun e := ⟨(upperChartEquiv P i e.1.1,upperChartEquiv P i e.1.2),by
    obtain ⟨hn,v,w,he,hv,hw⟩ := e.2
    rw [input_edge_iff] at he
    subst w
    refine ⟨fun h => hn ((upperChartEquiv P i).injective h),v,?_,?_⟩
    · exact (upperChartEquiv_mk P i v).symm.trans (congrArg (upperChartEquiv P i) hv)
    · exact (upperChartEquiv_mk P i (v+1)).symm.trans (congrArg (upperChartEquiv P i) hw)⟩
  invFun e := ⟨((upperChartEquiv P i).symm e.1.1,(upperChartEquiv P i).symm e.1.2),by
    obtain ⟨hn,v,hv,hw⟩ := e.2
    refine ⟨fun h => hn ((upperChartEquiv P i).symm.injective h),v,v+1,
      (input_edge_iff _ _).mpr rfl,?_,?_⟩
    · change Quotient.mk ((upperCandidate P i).2) v=(upperChartEquiv P i).symm e.1.1
      apply (upperChartEquiv P i).injective
      rw [upperChartEquiv_mk,Equiv.apply_symm_apply]
      exact hv
    · change Quotient.mk ((upperCandidate P i).2) (v+1)=(upperChartEquiv P i).symm e.1.2
      apply (upperChartEquiv P i).injective
      rw [upperChartEquiv_mk,Equiv.apply_symm_apply]
      exact hw⟩
  left_inv e := Subtype.ext (Prod.ext ((upperChartEquiv P i).symm_apply_apply e.1.1)
    ((upperChartEquiv P i).symm_apply_apply e.1.2))
  right_inv e := Subtype.ext (Prod.ext ((upperChartEquiv P i).apply_symm_apply e.1.1)
    ((upperChartEquiv P i).apply_symm_apply e.1.2))

/-- 元六辺から発生する全十五上界の有向辺数表。 -/
def numEdges (i : Fin 15) : ℕ := ![0,2,2,2,4,2,2,4,2,2,4,4,6,4,6] i
/-- 全原始有向色順序対をkernelで数える。 -/
theorem color_edge_card (i : Fin 15) : Fintype.card (ColorEdge i)=numEdges i := by
  fin_cases i <;> decide +kernel
/-- 上界の原始商順序対から商辺の有限性を生成する。 -/
instance quotientEdgeFintype (P : Setoid Bool) (i : Fin 15) :
    Fintype (input.QuotientEdge (upperCandidate P i)) :=
  Cycle.quotientEdgeFintype 6 (by decide) (upperCandidate P i)
/-- 元商辺全単射から各上界の有向辺数を導く。 -/
theorem quotient_edge_card (P : Setoid Bool) (i : Fin 15) :
    Fintype.card (input.QuotientEdge (upperCandidate P i))=numEdges i :=
  (Fintype.card_congr (edgeEquiv P i)).trans (color_edge_card i)
/-- 全chart併合以外の全上界で元有向辺を構成する。 -/
theorem color_edge_exists (i : Fin 15) (hi : i≠0) : Nonempty (ColorEdge i) := by
  fin_cases i
  · exact (hi rfl).elim
  · exact ⟨⟨(upperColor 1 3,upperColor 1 (3+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 2 2,upperColor 2 (2+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 3 2,upperColor 3 (2+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 4 2,upperColor 4 (2+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 5 0,upperColor 5 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 6 0,upperColor 6 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 7 0,upperColor 7 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 8 0,upperColor 8 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 9 0,upperColor 9 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 10 0,upperColor 10 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 11 0,upperColor 11 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 12 0,upperColor 12 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 13 0,upperColor 13 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
  · exact ⟨⟨(upperColor 14 0,upperColor 14 (0+1)),by rw [colorEdge_iff]; decide +kernel⟩⟩
/-- 元色辺をmk可換全単射で同じ実商辺へ戻す。 -/
def quotientEdge (P : Setoid Bool) (i : Fin 15) (hi : i≠0) :
    input.QuotientEdge (upperCandidate P i) :=
  (edgeEquiv P i).symm (Classical.choice (color_edge_exists i hi))
/-- 実pullback全射liftと商d0核から空含む全Aの上界Jを評価する。 -/
theorem upperCandidate_defect (P : Setoid Bool) (i : Fin 15) (hi : i≠0)
    (A : Set (Quotient P)) :
    blockDefect ((input.quotientComparison (upperCandidate P i)).aSubnerveComparisonHom A).h1Map =
      @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _) (numEdges i-W1.numClasses i,0) (0,0) := by
  have h := Cycle.all_a_defect 6 (by decide) (upperCandidate P i) (quotientEdge P i hi) A
  change _ = @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _)
    (Fintype.card (input.QuotientEdge (upperCandidate P i))-Fintype.card (Quotient ((upperCandidate P i).2)),0) (0,0) at h
  rw [quotient_edge_card,upper_chart_card] at h
  exact h
/-- 元実比較の安全性を原始商辺数とchart数の一致へ戻す。 -/
theorem upperCandidate_safe_iff (P : Setoid Bool) (i : Fin 15) (hi : i≠0) :
    input.Safe (upperCandidate P i) ↔ numEdges i=W1.numClasses i := by
  have h := Cycle.safe_iff_edges_eq_charts 6 (by decide) (upperCandidate P i) (quotientEdge P i hi)
  change input.Safe (upperCandidate P i) ↔ Fintype.card (input.QuotientEdge (upperCandidate P i))=Fintype.card (Quotient ((upperCandidate P i).2)) at h
  rw [quotient_edge_card,upper_chart_card] at h
  exact h


/-- 全chart併合では異端点有向辺が空になる。 -/
instance topColorEdgeIsEmpty : IsEmpty (ColorEdge 0) where
  false e := by
    letI : Subsingleton (Fin (W1.numClasses 0)) := inferInstanceAs (Subsingleton (Fin 1))
    have h := e.2
    rw [colorEdge_iff] at h
    exact h.1 (Subsingleton.elim _ _)
/-- 元空商辺から同じ粗H1が零であることを示す。 -/
theorem top_H1_subsingleton (P : Setoid Bool) :
    Subsingleton (Cycle.coarseComplex 6 (by decide) (upperCandidate P 0)).H1 := by
  letI : IsEmpty (input.QuotientEdge (upperCandidate P 0)) :=
    ⟨fun e => isEmptyElim (edgeEquiv P 0 e)⟩
  letI : IsEmpty ((input.quotientSupported (upperCandidate P 0)).EdgeInTargetSubset Set.univ) :=
    ⟨fun e => isEmptyElim (edgeEquiv P 0 e.1)⟩
  letI : Subsingleton (Cycle.coarseComplex 6 (by decide) (upperCandidate P 0)).C1 :=
    inferInstanceAs (Subsingleton (((input.quotientSupported (upperCandidate P 0)).EdgeInTargetSubset Set.univ) → ℚ))
  infer_instance
/-- 全chart併合の同じ実full比較は余核1を持つ。 -/
theorem top_full_defect (P : Setoid Bool) :
    blockDefect ((input.quotientComparison (upperCandidate P 0)).aSubnerveComparisonHom Set.univ).h1Map=(0,1) := by
  letI := top_H1_subsingleton P
  rw [← AtlasDefectComposition.transportHom_defect
    (congrArg input.supported.targetSubsetComplex Set.preimage_univ)]
  change blockDefect (Cycle.fullHom 6 (by decide) (upperCandidate P 0)).h1Map=(0,1)
  rw [AtlasGluingWidth.Width.defect_zero_domain,Cycle.full_H1_dimension]
/-- 全chart併合の非空領域比較は同署名図式で同じ余核1を持つ。 -/
theorem top_nonempty_defect (P : Setoid Bool) (A : Set (Quotient P)) (hA : A.Nonempty) :
    blockDefect ((input.quotientComparison (upperCandidate P 0)).aSubnerveComparisonHom A).h1Map=(0,1) := by
  exact (Cycle.actual_nonempty_defect_eq_full 6 (by decide) (upperCandidate P 0) A hA).trans (top_full_defect P)
/-- 全chart併合は同じ実余核により安全でない。 -/
theorem top_not_safe (P : Setoid Bool) : ¬ input.Safe (upperCandidate P 0) := by
  intro hs
  have hd := (input.safe_iff_zeroDefect (upperCandidate P 0)).mp hs Set.univ
  rw [top_full_defect] at hd
  exact Nat.one_ne_zero (congrArg Prod.snd hd)

/-- 全上界表の安全性は二block色表であることと必要十分。 -/
theorem upperCandidate_safe_classification (P : Setoid Bool) (i : Fin 15) :
    input.Safe (upperCandidate P i) ↔ W1.numClasses i=2 := by
  by_cases hi : i=0
  · subst i
    exact iff_of_false (top_not_safe P) (by decide +kernel)
  · rw [upperCandidate_safe_iff P i hi]
    fin_cases i <;> decide +kernel
/-- 元二対合併joinを四点恒等分割の引き戻しへ同定する。 -/
theorem joined_eq_upper_candidate : joined=upperCandidate ⊥ 14 := by
  refine Prod.ext (by rfl) ?_
  apply Setoid.ext; intro v w
  rw [joined_relation,upperCandidate_relation]
  fin_cases v <;> fin_cases w <;> decide +kernel
/-- 同じjoinの全A実比較を非空J=(2,0)、空J零へ評価する。 -/
theorem joined_defect (A : Set (Quotient (⊥ : Setoid Bool))) :
    blockDefect ((input.quotientComparison joined).aSubnerveComparisonHom A).h1Map =
      @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _) (2,0) (0,0) := by
  have hQ := congrArg Prod.snd joined_eq_upper_candidate
  change blockDefect ((input.quotientComparison (⊥,joined.2)).aSubnerveComparisonHom A).h1Map = _
  rw [hQ]
  exact upperCandidate_defect ⊥ 14 (by decide) A
/-- 元二対合併joinは実核2のため不安全。 -/
theorem joined_not_safe : ¬ input.Safe joined := by
  rw [joined_eq_upper_candidate,upperCandidate_safe_classification]
  decide +kernel
/-- 指定二粗化の共通上界条件を真のjoinの上界条件へ戻す。 -/
theorem common_upper_bound_iff (R : Coarsening Bool (ZMod 6)) :
    ac ≤ R ∧ df ≤ R ↔ joined ≤ R := by rw [← specified_join,sup_le_iff]
/-- 任意安全共通上界を任意target・全七二block表へ尽くす。 -/
theorem safe_common_upper_classification (R : Coarsening Bool (ZMod 6)) :
    ac ≤ R ∧ df ≤ R ∧ input.Safe R ↔
      ∃ i : Fin 15, W1.numClasses i=2 ∧ R=upperCandidate R.1 i := by
  constructor
  · rintro ⟨hac,hdf,hs⟩
    obtain ⟨i,hi⟩ := classify_upper R ((common_upper_bound_iff R).mp ⟨hac,hdf⟩)
    refine ⟨i,?_,hi⟩
    rw [hi,upperCandidate_safe_classification] at hs
    exact hs
  · rintro ⟨i,hi,hr⟩
    have hR := joined_le_upper_candidate R.1 i
    have hs := (upperCandidate_safe_classification R.1 i).mpr hi
    rw [← hr] at hR hs
    exact ⟨((common_upper_bound_iff R).mpr hR).1,((common_upper_bound_iff R).mpr hR).2,hs⟩
/-- 元a/b/cとd/e/fの二block商を具体的安全共通上界として示す。 -/
theorem safe_common_upper_exists :
    ∃ R : Coarsening Bool (ZMod 6), ac ≤ R ∧ df ≤ R ∧ input.Safe R := by
  refine ⟨upperCandidate ⊥ 3,?_,?_,?_⟩
  · exact ac_le_joined.trans (joined_le_upper_candidate ⊥ 3)
  · exact df_le_joined.trans (joined_le_upper_candidate ⊥ 3)
  · exact (upperCandidate_safe_classification ⊥ 3).mpr (by decide +kernel)
/-- target分割を任意に保ったままjoinchartを四点恒等引き戻しへ同定する。 -/
theorem joined_chart_eq_upper_candidate (P : Setoid Bool) : joined.2=(upperCandidate P 14).2 := by
  apply Setoid.ext; intro v w
  rw [joined_relation,upperCandidate_relation]
  fin_cases v <;> fin_cases w <;> decide +kernel
/-- top以外の全上界で元正periodの実全射liftから非空rank1を得る。 -/
theorem upperCandidate_rank (P : Setoid Bool) (i : Fin 15) (hi : i≠0)
    (A : Set (Quotient P)) (hA : A.Nonempty) :
    Module.finrank ℚ (LinearMap.range ((input.quotientComparison (upperCandidate P i)).aSubnerveComparisonHom A).h1Map)=1 :=
  Cycle.actual_nonempty_rank 6 (by decide) (upperCandidate P i) (quotientEdge P i hi) A hA
/-- 元joinの同じ商辺は元四点恒等色表の商辺を等号輸送して得る。 -/
def joinedQuotientEdge : input.QuotientEdge joined :=
  joined_eq_upper_candidate.symm ▸ quotientEdge ⊥ 14 (by decide)
/-- 元joinの任意非空領域で同じ実H1比較rankは1。 -/
theorem joined_rank (A : Set (Quotient (⊥ : Setoid Bool))) (hA : A.Nonempty) :
    Module.finrank ℚ (LinearMap.range ((input.quotientComparison joined).aSubnerveComparisonHom A).h1Map)=1 :=
  Cycle.actual_nonempty_rank 6 (by decide) joined joinedQuotientEdge A hA
/-- 元joinの空領域で同じ実H1比較rankは零。 -/
theorem joined_empty_rank :
    Module.finrank ℚ (LinearMap.range ((input.quotientComparison joined).aSubnerveComparisonHom ∅).h1Map)=0 :=
  Cycle.actual_empty_rank 6 (by decide) joined
/-- 元joinの実核2から同じfull比較の単射性を排除する。 -/
theorem joined_not_injective : ¬ Function.Injective
    ((input.quotientComparison joined).aSubnerveComparisonHom Set.univ).h1Map := by
  intro hi
  have hk := LinearMap.ker_eq_bot.mpr hi
  have hz := Submodule.finrank_eq_zero.mpr hk
  have hd := congrArg Prod.fst (joined_defect Set.univ)
  rw [if_pos Set.univ_nonempty,blockDefect_kernel_dimension] at hd
  have he : (2 : ℕ)=0 := hd.symm.trans hz
  omega
/-- 元joinの同じ実非単射から元粗cochainと細potential・正規化汎関数を生成する。 -/
def joinedKernelFailure : FailureCertificate.KernelFailure
    ((input.quotientComparison joined).aSubnerveComparisonHom Set.univ) :=
  Classical.choice (FailureCertificate.kernelFailure_exists _
    (by intro z; funext f; exact f.1.elim) joined_not_injective)
/-- 元joinの生成cochain類は同じ既存粗H1商で非零。 -/
theorem joined_kernel_class_nonzero :
    (LinearMap.range ((input.quotientSupported joined).targetSubsetComplex Set.univ).boundaryToCycles).mkQ
      ⟨joinedKernelFailure.x,joinedKernelFailure.x_cycle⟩ ≠ 0 :=
  FailureCertificate.KernelFailure.class_nonzero _ joinedKernelFailure
end AAT.AG.SafeCoarseningOrder.W2

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
