import ResearchLean.AG.SafeCoarseningOrder.IsomorphismComparison
import ResearchLean.AG.SafeCoarseningOrder.FiniteClassification

/-!
# 全原始同型によるSafe・Maxの保存と反映

元比較の全cochain可換図式から同じ実H¹写像の全単射性を輸送する。
全部分領域の逆像を尽くし、包含順序同型によって極大性と最大性へ接続する。

## Implementation notes

H¹両端の生成同型で元写像を共役し、canonical細subsetの型輸送を全Homで保つ。
Safeの単調性や期待rankは使用しない。極大性は全安全元と包含だけから輸送する。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
/-- 複体全体の等号transportは同じ誘導H¹写像の全単射性を保つ。 -/
theorem transportHom_h1Map_bijective {C D E : ThreeCochainComplex ℚ} (h : D = E)
    (f : ThreeCochainComplex.Hom C D) :
    Function.Bijective (transportHom h f).h1Map ↔ Function.Bijective f.h1Map := by
  cases h
  rfl
variable {S T V S' T' V' : Type} [Fintype V] [Fintype V']
variable {M : PrimitiveInput S T V} {N : PrimitiveInput S' T' V'}
namespace PrimitiveIso
/-- 元G-134比較の実H¹共役。canonical逆像の型輸送も元Homから生成する。 -/
theorem comparison_actual_h1_square (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    (a.subsetCochainEquiv (comparisonFactor
      (N.quotientReading (a.coarseningOrderIso R)) N.reading
      (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A)).symm.toHom.h1Map.comp
        ((N.quotientComparison (a.coarseningOrderIso R)).aSubnerveComparisonHom A).h1Map =
    (transportHom (congrArg M.supported.targetSubsetComplex (a.canonical_preimage R A))
      ((M.quotientComparison R).aSubnerveComparisonHom (a.quotientTarget R ⁻¹' A))).h1Map.comp
        (a.quotientSubsetEquiv R A).symm.toHom.h1Map := by
  rw [M.quotient_actualHom_old,N.quotient_actualHom_old,
    ← reindexedComparisonHom_eq_transport]
  exact a.comparison_h1_square R A
/-- 全Aについて、輸送先の同じ実比較の全単射性と元の全単射性は必要十分。 -/
theorem comparison_bijective_iff (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    Function.Bijective ((N.quotientComparison (a.coarseningOrderIso R)).aSubnerveComparisonHom A).h1Map ↔
      Function.Bijective ((M.quotientComparison R).aSubnerveComparisonHom (a.quotientTarget R ⁻¹' A)).h1Map := by
  let ef := (a.subsetCochainEquiv (comparisonFactor
    (N.quotientReading (a.coarseningOrderIso R)) N.reading
    (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A)).symm
  let ec := (a.quotientSubsetEquiv R A).symm
  let f := (N.quotientComparison (a.coarseningOrderIso R)).aSubnerveComparisonHom A
  let g := transportHom (congrArg M.supported.targetSubsetComplex (a.canonical_preimage R A))
    ((M.quotientComparison R).aSubnerveComparisonHom (a.quotientTarget R ⁻¹' A))
  calc
    Function.Bijective f.h1Map ↔ Function.Bijective (ef.toHom.h1Map.comp f.h1Map) :=
      (ef.toHom_h1Map_bijective.of_comp_iff' f.h1Map).symm
    _ ↔ Function.Bijective (g.h1Map.comp ec.toHom.h1Map) := by
      rw [a.comparison_actual_h1_square R A]
    _ ↔ Function.Bijective g.h1Map :=
      Function.Bijective.of_comp_iff g.h1Map ec.toHom_h1Map_bijective
    _ ↔ _ := transportHom_h1Map_bijective _ _
/-- 全原始同型はSafeを保存・反映する。全Aは商target全単射の逆像で尽くす。 -/
theorem safe_iff (a : PrimitiveIso M N) (R : Coarsening T V) :
    N.Safe (a.coarseningOrderIso R) ↔ M.Safe R := by
  constructor
  · intro h A
    have hh := (a.comparison_bijective_iff R ((a.quotientTarget R).symm ⁻¹' A)).mp (h _)
    have he : a.quotientTarget R ⁻¹' ((a.quotientTarget R).symm ⁻¹' A) = A := by
      ext t
      simp only [Set.mem_preimage,Equiv.symm_apply_apply]
    rw [he] at hh
    exact hh
  · intro h A
    exact (a.comparison_bijective_iff R A).mpr (h _)
/-- 全原始同型の順序作用は極大安全元を保つ。 -/
theorem maximal_forward (a : PrimitiveIso M N) {R : Coarsening T V}
    (hR : Maximal M.Safe R) : Maximal N.Safe (a.coarseningOrderIso R) := by
  refine ⟨(a.safe_iff R).mpr hR.1,?_⟩
  intro W hW hRW
  obtain ⟨Q,rfl⟩ := a.coarseningOrderIso.surjective W
  exact a.coarseningOrderIso.monotone
    (hR.2 ((a.safe_iff Q).mp hW) (a.coarseningOrderIso.map_rel_iff.mp hRW))
/-- 極大安全元の保存・反映。逆も同じ全原始逆同型の作用。 -/
theorem maximal_iff (a : PrimitiveIso M N) (R : Coarsening T V) :
    Maximal N.Safe (a.coarseningOrderIso R) ↔ Maximal M.Safe R := by
  constructor
  · intro h
    have hh := a.symm.maximal_forward h
    simpa only [coarseningOrderIso_symm,OrderIso.symm_apply_apply] using hh
  · exact a.maximal_forward
/-- 全原始同型の順序作用は最大安全元も保つ。 -/
theorem greatest_forward (a : PrimitiveIso M N) {R : Coarsening T V}
    (hR : IsGreatest {W | M.Safe W} R) : IsGreatest {W | N.Safe W} (a.coarseningOrderIso R) := by
  refine ⟨(a.safe_iff R).mpr hR.1,?_⟩
  intro W hW
  obtain ⟨Q,rfl⟩ := a.coarseningOrderIso.surjective W
  exact a.coarseningOrderIso.monotone (hR.2 ((a.safe_iff Q).mp hW))
/-- 最大安全元の保存・反映も同じ全原始同型で成立する。 -/
theorem greatest_iff (a : PrimitiveIso M N) (R : Coarsening T V) :
    IsGreatest {W | N.Safe W} (a.coarseningOrderIso R) ↔ IsGreatest {W | M.Safe W} R := by
  constructor
  · intro h
    have hh := a.symm.greatest_forward h
    simpa only [coarseningOrderIso_symm,OrderIso.symm_apply_apply] using hh
  · exact a.greatest_forward
end PrimitiveIso
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
