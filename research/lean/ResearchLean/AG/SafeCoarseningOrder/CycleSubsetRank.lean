import ResearchLean.AG.SafeCoarseningOrder.CycleSubsetEvaluation

/-! # 同じ全商領域比較の実rank

## Implementation notes

実pullback periodから証明した核欠損と商Euler式でcanonical射のrankを復元する。
非空領域は全名付きセルを保つcochain比較図式で輸送し、次元だけの別写像で置換しない。
抽象同次元写像を選ぶ代替では元部分像を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.Cycle
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
variable (n : ℕ) [NeZero n] (hn : 2 ≤ n) (R : Coarsening Bool (ZMod n))
/-- 正periodで生成した同じcanonical全領域実比較のrankは1。 -/
theorem actual_full_rank (e : (input n hn).QuotientEdge R) :
    Module.finrank ℚ (LinearMap.range
      (((input n hn).quotientComparison R).aSubnerveComparisonHom Set.univ).h1Map)=1 := by
  have hk := congrArg Prod.fst (actual_full_defect n hn R e)
  rw [blockDefect_kernel_dimension] at hk
  have hr := (((input n hn).quotientComparison R).aSubnerveComparisonHom Set.univ).h1Map.finrank_range_add_finrank_ker
  have hd := coarse_H1_euler n hn R
  have hle := coarse_edges_ge_charts n hn R e
  change Module.finrank ℚ (LinearMap.range (((input n hn).quotientComparison R).aSubnerveComparisonHom Set.univ).h1Map) +
    Module.finrank ℚ (LinearMap.ker (((input n hn).quotientComparison R).aSubnerveComparisonHom Set.univ).h1Map)=
    Module.finrank ℚ (coarseComplex n hn R).H1 at hr
  dsimp only [Prod.fst] at hk
  omega
/-- 元セルを固定する全cochain図式は任意非空商領域の実rankを1へ保つ。 -/
theorem actual_nonempty_rank (e : (input n hn).QuotientEdge R)
    (A : Set (Quotient R.1)) (hA : A.Nonempty) :
    Module.finrank ℚ (LinearMap.range
      (((input n hn).quotientComparison R).aSubnerveComparisonHom A).h1Map)=1 := by
  let N := (input n hn).quotientSupported R
  let E := (input n hn).supported
  let h := (input n hn).quotient_coarser R
  let M := (input n hn).quotientMorphism R
  have heq : SupportSignature.alpha N E h A=SupportSignature.alpha N E h Set.univ := by
    rw [alpha_nonempty n hn R A hA,alpha_nonempty n hn R Set.univ Set.univ_nonempty]
  let ec := (SupportReconstruction.coarseEquiv N E h heq).h1Equiv
  let ef := (SupportReconstruction.fineEquiv N E h heq).h1Equiv
  have hs : ∀ x, ef ((M.aSubnerveComparisonHom Set.univ).h1Map x)=
      (M.aSubnerveComparisonHom A).h1Map (ec x) := by
    intro x
    have hh := congrArg (fun f => f.h1Map x) (SupportReconstruction.comparison_square N E h heq M)
    simpa only [cochainComp_h1Map,LinearMap.comp_apply] using hh
  have hd := LinearConjugation.range_dimension _ _ ec ef hs
  have hf := actual_full_rank n hn R e
  rw [PrimitiveInput.quotient_actualHom_old] at hf ⊢
  exact hd.symm.trans hf

/-- 空商領域の元粗H¹は零なので同じ実比較rankも零である。 -/
theorem actual_empty_rank : Module.finrank ℚ (LinearMap.range
    (((input n hn).quotientComparison R).aSubnerveComparisonHom ∅).h1Map)=0 := by
  letI := empty_h1_subsingleton ((input n hn).quotientReading R) ((input n hn).quotientSupported R)
  have hz : Module.finrank ℚ (((input n hn).quotientSupported R).targetSubsetComplex ∅).H1=0 :=
    Module.finrank_zero_of_subsingleton
  have hr := (((input n hn).quotientComparison R).aSubnerveComparisonHom ∅).h1Map.finrank_range_le
  omega
end AAT.AG.SafeCoarseningOrder.Cycle


#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
