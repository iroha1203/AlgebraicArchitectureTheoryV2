import ResearchLean.AG.SafeCoarseningOrder.W2Input

/-! # W2 指定二併合の実比較

## Implementation notes

元商mk可換chart/有向辺全単射を先に構成し、受理された実pullback正periodの全射liftへ接続する。逆向き辺を一つにする代替は元セルを変えるため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W2
open CanonicalResolution ResolutionInvariance TwoPhase
open AtlasDefectComposition FailureCertificate
/-- Boolで元a/cまたはd/fだけの五色合併表を指定する。 -/
def foldMap (b : Bool) (v : ZMod 6) : Fin 5 := if b then dfMap v else acMap v
/-- falseは元a/c合併表を返す。 -/
theorem foldMap_false (v : ZMod 6) : foldMap false v=acMap v := rfl
/-- trueは元d/f合併表を返す。 -/
theorem foldMap_true (v : ZMod 6) : foldMap true v=dfMap v := rfl
/-- 指定chart合併と任意独立target分割の粗化。 -/
def foldCandidate (P : Setoid Bool) (b : Bool) : Coarsening Bool (ZMod 6) := (P,Setoid.ker (foldMap b))
/-- target等号のfalse候補は指定Racそのもの。 -/
theorem fold_false : foldCandidate ⊥ false=ac := rfl
/-- target等号のtrue候補は指定Rdfそのもの。 -/
theorem fold_true : foldCandidate ⊥ true=df := rfl
variable (P : Setoid Bool)
/-- 各元指定合併の関係を色等号で公開する。 -/
theorem fold_relation (b : Bool) (v w : ZMod 6) :
    (foldCandidate P b).2.r v w ↔ foldMap b v=foldMap b w := Iff.rfl
/-- 指定五色は元六点から全て発生する。 -/
theorem foldMap_surjective (b : Bool) : Function.Surjective (foldMap b) := by
  cases b <;> intro c <;> fin_cases c <;>
    first | exact ⟨0,by decide +kernel⟩ | exact ⟨1,by decide +kernel⟩ |
      exact ⟨2,by decide +kernel⟩ | exact ⟨3,by decide +kernel⟩ |
      exact ⟨4,by decide +kernel⟩ | exact ⟨5,by decide +kernel⟩
/-- 指定合併の元商mkをmathlib核商の全単射へ接続する。 -/
def foldChartEquiv (b : Bool) : Quotient (foldCandidate P b).2 ≃ Fin 5 :=
  Setoid.quotientKerEquivOfSurjective (foldMap b) (foldMap_surjective b)
/-- 元指定商mkは同じ五色表の値を返す。 -/
theorem foldChartEquiv_mk (b : Bool) (v : ZMod 6) :
    foldChartEquiv P b (Quotient.mk (foldCandidate P b).2 v)=foldMap b v := rfl
/-- 元指定商mk可換全単射からchart数5を導く。 -/
theorem fold_chart_card (b : Bool) : Fintype.card (Quotient (foldCandidate P b).2)=5 :=
  (Fintype.card_congr (foldChartEquiv P b)).trans (Fintype.card_fin _)
/-- 指定合併の元六有向辺から発生する非対角順序対。 -/
def foldEdge (b : Bool) (c d : Fin 5) : Prop :=
  c≠d ∧ ∃ v : ZMod 6, foldMap b v=c ∧ foldMap b (v+1)=d
/-- 指定有向色辺の原始生成条件を公開する。 -/
theorem foldEdge_iff (b : Bool) (c d : Fin 5) :
    foldEdge b c d ↔ c≠d ∧ ∃ v : ZMod 6, foldMap b v=c ∧ foldMap b (v+1)=d := Iff.rfl
/-- 元有限六点条件から指定色辺を決定する。 -/
instance foldEdgeDecidable (b : Bool) (c d : Fin 5) : Decidable (foldEdge b c d) := by
  exact inferInstanceAs (Decidable (c≠d ∧ ∃ v : ZMod 6, foldMap b v=c ∧ foldMap b (v+1)=d))
/-- 指定合併の逆向き別セルを保持する有向順序対subtype。 -/
abbrev FoldEdge (b : Bool) := {e : Fin 5 × Fin 5 // foldEdge b e.1 e.2}
/-- 指定元有向色辺の全有限表を生成する。 -/
instance foldEdgeFintype (b : Bool) : Fintype (FoldEdge b) := inferInstance
/-- 指定商辺と元五色有向辺を両端mk保持で全単射にする。 -/
def foldEdgeEquiv (b : Bool) : input.QuotientEdge (foldCandidate P b) ≃ FoldEdge b where
  toFun e := ⟨(foldChartEquiv P b e.1.1,foldChartEquiv P b e.1.2),by
    obtain ⟨hn,v,w,he,hv,hw⟩ := e.2
    rw [input_edge_iff] at he
    subst w
    refine ⟨fun h => hn ((foldChartEquiv P b).injective h),v,?_,?_⟩
    · exact (foldChartEquiv_mk P b v).symm.trans (congrArg (foldChartEquiv P b) hv)
    · exact (foldChartEquiv_mk P b (v+1)).symm.trans (congrArg (foldChartEquiv P b) hw)⟩
  invFun e := ⟨((foldChartEquiv P b).symm e.1.1,(foldChartEquiv P b).symm e.1.2),by
    obtain ⟨hn,v,hv,hw⟩ := e.2
    refine ⟨fun h => hn ((foldChartEquiv P b).symm.injective h),v,v+1,
      (input_edge_iff _ _).mpr rfl,?_,?_⟩
    · apply (foldChartEquiv P b).injective
      rw [foldChartEquiv_mk,Equiv.apply_symm_apply]
      exact hv
    · apply (foldChartEquiv P b).injective
      rw [foldChartEquiv_mk,Equiv.apply_symm_apply]
      exact hw⟩
  left_inv e := Subtype.ext (Prod.ext ((foldChartEquiv P b).symm_apply_apply e.1.1)
    ((foldChartEquiv P b).symm_apply_apply e.1.2))
  right_inv e := Subtype.ext (Prod.ext ((foldChartEquiv P b).apply_symm_apply e.1.1)
    ((foldChartEquiv P b).apply_symm_apply e.1.2))
/-- 元六辺の指定商順序対をkernelで数えて6を得る。 -/
theorem fold_edge_card (b : Bool) : Fintype.card (FoldEdge b)=6 := by
  cases b <;> decide +kernel
/-- 指定合併の元商順序対から実商辺の有限性を生成する。 -/
instance foldQuotientEdgeFintype (b : Bool) : Fintype (input.QuotientEdge (foldCandidate P b)) :=
  Cycle.quotientEdgeFintype 6 (by decide) (foldCandidate P b)
/-- 元商有向辺全単射から実商辺数6を導く。 -/
theorem fold_quotient_edge_card (b : Bool) : Fintype.card (input.QuotientEdge (foldCandidate P b))=6 :=
  (Fintype.card_congr (foldEdgeEquiv P b)).trans (fold_edge_card b)
/-- 元a→b色辺を同じ実商辺として構成する。 -/
def foldQuotientEdge (b : Bool) : input.QuotientEdge (foldCandidate P b) :=
  (foldEdgeEquiv P b).symm ⟨(0,1), by rw [foldEdge_iff]; cases b <;> decide +kernel⟩
/-- 各指定合併の全A実Jは非空(1,0)、空(0,0)。 -/
theorem fold_defect (b : Bool) (A : Set (Quotient P)) :
    blockDefect ((input.quotientComparison (foldCandidate P b)).aSubnerveComparisonHom A).h1Map =
      @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _) (1,0) (0,0) := by
  have h := Cycle.all_a_defect 6 (by decide) (foldCandidate P b) (foldQuotientEdge P b) A
  rw [fold_quotient_edge_card,fold_chart_card] at h
  exact h
/-- 元pullback正periodの実全射liftから各非空Aのrank1を得る。 -/
theorem fold_rank (b : Bool) (A : Set (Quotient P)) (hA : A.Nonempty) :
    Module.finrank ℚ (LinearMap.range ((input.quotientComparison (foldCandidate P b)).aSubnerveComparisonHom A).h1Map)=1 :=
  Cycle.actual_nonempty_rank 6 (by decide) (foldCandidate P b) (foldQuotientEdge P b) A hA
/-- 各指定合併は元実核1により不安全。 -/
theorem fold_not_safe (b : Bool) : ¬ input.Safe (foldCandidate P b) := by
  intro hs
  have hd := (input.safe_iff_zeroDefect (foldCandidate P b)).mp hs Set.univ
  rw [fold_defect,if_pos Set.univ_nonempty] at hd
  exact Nat.one_ne_zero (congrArg Prod.fst hd)

open AtlasDefectComposition FailureCertificate
/-- 同じ全領域比較の実核1から単射性を排除する。 -/
theorem fold_not_injective (b : Bool) : ¬ Function.Injective
    ((input.quotientComparison (foldCandidate P b)).aSubnerveComparisonHom Set.univ).h1Map := by
  intro hi
  have hk := LinearMap.ker_eq_bot.mpr hi
  have hz := Submodule.finrank_eq_zero.mpr hk
  have hd := congrArg Prod.fst (fold_defect P b Set.univ)
  rw [if_pos Set.univ_nonempty,blockDefect_kernel_dimension] at hd
  exact Nat.one_ne_zero (hd.symm.trans hz)
/-- 同じ実非単射H1から元粗cochain・細potential・正規化分離汎関数を生成する。 -/
def foldKernelFailure (b : Bool) : KernelFailure
    ((input.quotientComparison (foldCandidate P b)).aSubnerveComparisonHom Set.univ) :=
  Classical.choice (kernelFailure_exists _ (by intro z; funext f; exact f.1.elim) (fold_not_injective P b))
/-- 生成した粗cochain類は同じ既存H1商で非零。 -/
theorem fold_kernel_class_nonzero (b : Bool) :
    (LinearMap.range ((input.quotientSupported (foldCandidate P b)).targetSubsetComplex Set.univ).boundaryToCycles).mkQ
      ⟨(foldKernelFailure P b).x,(foldKernelFailure P b).x_cycle⟩ ≠ 0 :=
  KernelFailure.class_nonzero _ (foldKernelFailure P b)
/-- 指定両合併で元a→bの有向色辺が実在する。 -/
theorem fold_edge_positive (b : Bool) : foldEdge b 0 1 := by
  rw [foldEdge_iff]
  cases b <;> decide +kernel
/-- 指定両合併の対角対は有向辺セルでない。 -/
theorem fold_edge_negative (b : Bool) (c : Fin 5) : ¬ foldEdge b c c := by
  rw [foldEdge_iff]
  exact fun h => h.1 rfl
/-- 各指定合併の空領域も同じ実比較rankは零。 -/
theorem fold_empty_rank (b : Bool) :
    Module.finrank ℚ (LinearMap.range ((input.quotientComparison (foldCandidate P b)).aSubnerveComparisonHom ∅).h1Map)=0 :=
  Cycle.actual_empty_rank 6 (by decide) (foldCandidate P b)
/-- 指定二併合は同じ不安全性により極大安全元でもない。 -/
theorem fold_not_maximal (b : Bool) : ¬ Maximal input.Safe (foldCandidate P b) :=
  fun h => fold_not_safe P b h.1
end AAT.AG.SafeCoarseningOrder.W2

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
