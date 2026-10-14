import ResearchLean.AG.SafeCoarseningOrder.CycleQuotientHomology
import ResearchLean.AG.AtlasDefectComposition.SupportDefectValue

/-! # 全商領域の実JとSafe評価

## Implementation notes

元全支持と商mk全射から同じ名付きセル署名を生成し、受理全cochain比較図式で非空領域を全領域へ戻す。空領域も評価し、実比較rankから同じSafe判定を導く。
非空領域が同じグラフだという仮定を置かず、原始支持と実cochain図式から導く。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.Cycle
open CanonicalResolution ResolutionInvariance TwoPhase AtlasGluingWidth
variable (n : ℕ) [NeZero n] (hn : 2 ≤ n)
open AtlasDefectComposition
variable (R : Coarsening Bool (ZMod n))
/-- 元全台と商mk全射から六種類の実名付きセル署名を生成する。 -/
theorem support_family_all (t : Quotient R.1)
    (c : SupportSignature.Cell ((input n hn).quotientSupported R) (input n hn).supported) :
    c ∈ SupportSignature.family ((input n hn).quotientSupported R) (input n hn).supported
      ((input n hn).quotient_coarser R) t := by
  rcases c with ((c|e)|f)|((c|e)|f)
  · exact quotient_support_all n hn R c t
  · exact ⟨quotient_support_all n hn R e.1.1 t,quotient_support_all n hn R e.1.2 t⟩
  · exact f.elim
  · obtain ⟨v,rfl⟩ := Quotient.mk_surjective t
    refine ⟨v,True.intro,?_⟩
    rw [PrimitiveInput.quotient_factor]
  · obtain ⟨v,rfl⟩ := Quotient.mk_surjective t
    refine ⟨v,⟨True.intro,True.intro⟩,?_⟩
    rw [PrimitiveInput.quotient_factor]
  · exact f.elim
/-- 非空領域は元支持証拠から全名付きセルを選択する。 -/
theorem alpha_nonempty (A : Set (Quotient R.1)) (hA : A.Nonempty) :
    SupportSignature.alpha ((input n hn).quotientSupported R) (input n hn).supported
      ((input n hn).quotient_coarser R) A = Set.univ := by
  obtain ⟨t,ht⟩ := hA
  ext c
  constructor
  · intro _; exact Set.mem_univ _
  · intro _
    rw [SignatureGeometry.mem_alpha]
    exact ⟨t,ht,support_family_all n hn R t c⟩
/-- 同署名の全cochain比較図式から任意非空領域の実Jを全領域へ戻す。 -/
theorem actual_nonempty_defect_eq_full (A : Set (Quotient R.1)) (hA : A.Nonempty) :
    blockDefect (((input n hn).quotientComparison R).aSubnerveComparisonHom A).h1Map =
      blockDefect (((input n hn).quotientComparison R).aSubnerveComparisonHom Set.univ).h1Map := by
  rw [PrimitiveInput.quotient_actualHom_old,PrimitiveInput.quotient_actualHom_old]
  apply SupportDefectValue.same_alpha
  rw [alpha_nonempty n hn R A hA,alpha_nonempty n hn R Set.univ (Set.univ_nonempty)]
/-- 空領域の同じ実比較は両H¹零からJ零となる。 -/
theorem actual_empty_defect :
    blockDefect (((input n hn).quotientComparison R).aSubnerveComparisonHom ∅).h1Map=(0,0) := by
  rw [PrimitiveInput.quotient_actualHom_old]
  exact (blockDefect_eq_zero_iff_bijective _).mpr
    (PrimitiveInput.empty_comparison_bijective ((input n hn).quotientMorphism R))
/-- 空を含む任意商領域の同じ実比較を評価する。 -/
theorem all_a_defect (e : (input n hn).QuotientEdge R) (A : Set (Quotient R.1)) :
    blockDefect (((input n hn).quotientComparison R).aSubnerveComparisonHom A).h1Map =
      @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _)
        (Fintype.card ((input n hn).QuotientEdge R)-Fintype.card (Quotient R.2),0)
      (0,0) := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA,actual_nonempty_defect_eq_full n hn R A hA]
    exact actual_full_defect n hn R e
  · have he := Set.not_nonempty_iff_eq_empty.mp hA
    rw [if_neg hA,he]
    exact actual_empty_defect n hn R

/-- 実比較rank1と商Euler式から有向商辺数の下限を導く。 -/
theorem coarse_edges_ge_charts (e : (input n hn).QuotientEdge R) :
    Fintype.card (Quotient R.2) ≤ Fintype.card ((input n hn).QuotientEdge R) := by
  have hd := coarse_H1_euler n hn R
  have hr := (fullHom n hn R).h1Map.finrank_range_add_finrank_ker
  rw [fullHom_h1_rank n hn R e] at hr
  omega
/-- 実pullback rankと全領域評価に基づき、同じSafeを元セル数へ必要十分に戻す。 -/
theorem safe_iff_edges_eq_charts (e : (input n hn).QuotientEdge R) :
    (input n hn).Safe R ↔
      Fintype.card ((input n hn).QuotientEdge R)=Fintype.card (Quotient R.2) := by
  rw [PrimitiveInput.safe_iff_zeroDefect]
  constructor
  · intro hs
    have hd := hs Set.univ
    rw [actual_full_defect n hn R e] at hd
    have hc := congrArg Prod.fst hd
    have he := coarse_edges_ge_charts n hn R e
    omega
  · intro he A
    rw [all_a_defect n hn R e A,he,Nat.sub_self]
    split <;> rfl
end AAT.AG.SafeCoarseningOrder.Cycle

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
