import ResearchLean.AG.AtlasGluingWidth.WidthLocalH0

/-! # 指定閉路の実H⁰差制限

GOAL E / witnesses §4。同じ原始cellRowの差制限をH⁰根評価で計算する。
粗側はx-y、細側は両交差chartでx-yとなる。

## Implementation notes

二領域核の積同型とG-133のoldH0Equiv自然性を用いる。独立の行列を入力する
代替は、元の標準homology射との一致を保証しないため採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
variable (n : ℕ) [NeZero n]

/-- 二領域の実零微分核を元の二成分へ両方向に同定する。 -/
def pairKernelEquiv (C D : ThreeCochainComplex.{0,0} ℚ) :
    LinearMap.ker (pairComplex C D).d0 ≃ₗ[ℚ] (LinearMap.ker C.d0 × LinearMap.ker D.d0) where
  toFun z := (⟨z.1.1, congrArg Prod.fst z.2⟩, ⟨z.1.2, congrArg Prod.snd z.2⟩)
  invFun z := ⟨(z.1.1, z.2.1), Prod.ext z.1.2 z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 同じ実細二領域H⁰核を根評価の積で同定する。 -/
def finePairH0Equiv (hn : 2 ≤ n) :
    LinearMap.ker (pairComplex (selected n false (regionA n)).complex
      (selected n false (regionB n)).complex).d0 ≃ₗ[ℚ] (ℚ × ℚ) :=
  (pairKernelEquiv _ _).trans ((aH0Equiv n).prodCongr (bH0Equiv n hn))
/-- 同じ実粗二領域H⁰核を唯一chart評価の積で同定する。 -/
def coarsePairH0Equiv (hn : 2 ≤ n) :
    LinearMap.ker (pairComplex (CellSelection.region (coarse n) (regionA n)).complex
      (CellSelection.region (coarse n) (regionB n)).complex).d0 ≃ₗ[ℚ] (ℚ × ℚ) :=
  (pairKernelEquiv _ _).trans
    ((coarseH0Equiv n (regionA n) ⟨0,rfl⟩).prodCongr
      (coarseH0Equiv n (regionB n) (regionB_nonempty n hn)))
/-- 同じ細差制限は真交差の二chartの両方でx-yを返す。 -/
theorem fine_H0_difference (hn : 2 ≤ n) (x : ℚ × ℚ) :
    intersectionH0Equiv n hn (oldH0Map
      (CellSelection.intersectionDifference (selected n false (regionA n))
        (selected n false (regionB n))) ((finePairH0Equiv n hn).symm x)) =
      fun _ => x.1 - x.2 := by
  funext b
  rfl
omit [NeZero n] in
/-- 同じ粗差制限は唯一交差chartでx-yを返す。 -/
theorem coarse_H0_difference (hn : 2 ≤ n) (x : ℚ × ℚ) :
    coarseIntersectionH0Equiv n hn (oldH0Map
      (CellSelection.intersectionDifference (CellSelection.region (coarse n) (regionA n))
        (CellSelection.region (coarse n) (regionB n))) ((coarsePairH0Equiv n hn).symm x)) =
      x.1 - x.2 := rfl
/-- 同じ細標準二領域H⁰を実核の根評価で同定する。 -/
def finePairStandardH0Equiv (hn : 2 ≤ n) :=
  (oldH0Equiv (pairComplex (selected n false (regionA n)).complex
    (selected n false (regionB n)).complex)).symm.trans (finePairH0Equiv n hn)
/-- 同じ粗標準二領域H⁰を実核の根評価で同定する。 -/
def coarsePairStandardH0Equiv (hn : 2 ≤ n) :=
  (oldH0Equiv (pairComplex (CellSelection.region (coarse n) (regionA n)).complex
    (CellSelection.region (coarse n) (regionB n)).complex)).symm.trans (coarsePairH0Equiv n hn)
/-- 同じ細標準真交差H⁰は順序付き二chart評価へ移す。 -/
def fineIntersectionStandardH0Equiv (hn : 2 ≤ n) :=
  (oldH0Equiv (intersection n).complex).symm.trans (intersectionH0Equiv n hn)
/-- 同じ粗標準真交差H⁰は唯一chart評価へ移す。 -/
def coarseIntersectionStandardH0Equiv (hn : 2 ≤ n) :=
  (oldH0Equiv ((CellSelection.region (coarse n) (regionA n)).inter
    (CellSelection.region (coarse n) (regionB n))).complex).symm.trans
      (coarseIntersectionH0Equiv n hn)
/-- 指定の細標準cochain短完全列。 -/
def widthFineRow := StandardRow.cellRow (selected n false (regionA n)) (selected n false (regionB n))
/-- 指定の粗標準cochain短完全列。 -/
def widthCoarseRow := StandardRow.cellRow (CellSelection.region (coarse n) (regionA n))
  (CellSelection.region (coarse n) (regionB n))
/-- 元の細標準homology差制限を全元で両chartのx-yへ正規化する。 -/
theorem fine_standard_H0_difference (hn : 2 ≤ n) (x : (widthFineRow n).X₂.homology (0:ℤ)) :
    fineIntersectionStandardH0Equiv n hn (homologyMap (widthFineRow n).g 0 x) =
      fun _ => (finePairStandardH0Equiv n hn x).1 - (finePairStandardH0Equiv n hn x).2 := by
  obtain ⟨z,rfl⟩ := (oldH0Equiv _).surjective x
  dsimp only [widthFineRow, StandardRow.cellRow, StandardRow.row]
  rw [← oldH0Equiv_natural]
  simp only [fineIntersectionStandardH0Equiv, intersection, finePairStandardH0Equiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change intersectionH0Equiv n hn (oldH0Map _ z) =
    fun _ => (finePairH0Equiv n hn z).1 - (finePairH0Equiv n hn z).2
  simpa only [LinearEquiv.symm_apply_apply] using fine_H0_difference n hn (finePairH0Equiv n hn z)
omit [NeZero n] in
/-- 元の粗標準homology差制限を全元でx-yへ正規化する。 -/
theorem coarse_standard_H0_difference (hn : 2 ≤ n) (x : (widthCoarseRow n).X₂.homology (0:ℤ)) :
    coarseIntersectionStandardH0Equiv n hn (homologyMap (widthCoarseRow n).g 0 x) =
      (coarsePairStandardH0Equiv n hn x).1 - (coarsePairStandardH0Equiv n hn x).2 := by
  obtain ⟨z,rfl⟩ := (oldH0Equiv _).surjective x
  dsimp only [widthCoarseRow, StandardRow.cellRow, StandardRow.row]
  rw [← oldH0Equiv_natural]
  simp only [coarseIntersectionStandardH0Equiv, coarsePairStandardH0Equiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change coarseIntersectionH0Equiv n hn (oldH0Map _ z) =
    (coarsePairH0Equiv n hn z).1 - (coarsePairH0Equiv n hn z).2
  simpa only [LinearEquiv.symm_apply_apply] using coarse_H0_difference n hn (coarsePairH0Equiv n hn z)

/-- 根評価で生成される指定差制限の二chart座標射。 -/
def diagonalDifference : (ℚ × ℚ) →ₗ[ℚ] (Bool → ℚ) where
  toFun x _ := x.1 - x.2
  map_add' _ _ := by funext b; dsimp; ring
  map_smul' _ _ := by funext b; dsimp; ring
/-- 順序付き真交差の値差。 -/
def endpointDifference : (Bool → ℚ) →ₗ[ℚ] ℚ where
  toFun z := z true - z false
  map_add' _ _ := by dsimp; ring
  map_smul' _ _ := by dsimp; ring
/-- 指定差制限の実像は順序付き値差の核に両方向で一致する。 -/
theorem diagonal_range : LinearMap.range diagonalDifference = LinearMap.ker endpointDifference := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact sub_self _
  · intro hz
    have h : z true = z false := sub_eq_zero.mp hz
    refine ⟨(z false,0), ?_⟩
    funext b
    cases b <;> simp [diagonalDifference, h]
/-- 順序付き値差は(0,a)から任意のaを得る。 -/
theorem endpoint_difference_surjective : Function.Surjective endpointDifference := by
  intro a
  exact ⟨fun b => if b then a else 0, by simp [endpointDifference]⟩
/-- 同じ対角像の実余核は値差によってℚと両方向同型。 -/
def diagonalCokernelEquiv : ((Bool → ℚ) ⧸ LinearMap.range diagonalDifference) ≃ₗ[ℚ] ℚ :=
  (Submodule.Quotient.equiv _ _ (LinearEquiv.refl ℚ _) (by
    simpa using diagonal_range)).trans
      (endpointDifference.quotKerEquivOfSurjective endpoint_difference_surjective)
/-- 同じ細Qを元差制限の可換同定でℚへ移す。 -/
def fineQEquiv (hn : 2 ≤ n) : QuotientKernelRow.Q (widthFineRow n) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv (homologyMap (widthFineRow n).g 0).hom
    diagonalDifference (finePairStandardH0Equiv n hn) (fineIntersectionStandardH0Equiv n hn)
    (fine_standard_H0_difference n hn)).trans diagonalCokernelEquiv
/-- 細Qの全実標準交差H⁰代表元で同型値は順序付き値差。 -/
theorem fine_Q_mk (hn : 2 ≤ n) (z : (widthFineRow n).X₃.homology (0:ℤ)) :
    fineQEquiv n hn ((LinearMap.range (homologyMap (widthFineRow n).g 0).hom).mkQ z) =
      endpointDifference (fineIntersectionStandardH0Equiv n hn z) := rfl
omit [NeZero n] in
/-- 元の粗標準H⁰差制限は実際に全射。 -/
theorem coarse_standard_H0_surjective (hn : 2 ≤ n) :
    Function.Surjective (homologyMap (widthCoarseRow n).g (0:ℤ)) := by
  intro z
  refine ⟨(coarsePairStandardH0Equiv n hn).symm
    (coarseIntersectionStandardH0Equiv n hn z,0), ?_⟩
  apply (coarseIntersectionStandardH0Equiv n hn).injective
  rw [coarse_standard_H0_difference, LinearEquiv.apply_symm_apply]
  exact sub_zero _
omit [NeZero n] in
/-- 同じ粗Qは元の全射の余核なので零。 -/
theorem coarse_Q_zero (hn : 2 ≤ n) : Subsingleton (QuotientKernelRow.Q (widthCoarseRow n)) := by
  have he : LinearMap.range (homologyMap (widthCoarseRow n).g 0).hom = ⊤ :=
    LinearMap.range_eq_top.mpr (coarse_standard_H0_surjective n hn)
  change Subsingleton (_ ⧸ LinearMap.range (homologyMap (widthCoarseRow n).g 0).hom)
  rw [he]
  infer_instance

/-- 同じ指定逆像選択の輸送は原始台からの領域輸送で生成される。 -/
theorem width_selection_compatible (X : Set (Concept n)) :
    SelectionCompatible (comparison n false) (CellSelection.region (coarse n) X)
      (selected n false X) := by
  have ht := SelectionCompatible.region (comparison n false) X
  change SelectionCompatible (comparison n false) (CellSelection.region (coarse n) X)
    (CellSelection.region (fine n false) (comparisonFactor (coarseReading n) (fineReading n) (coarser n) ⁻¹' X)) at ht
  rw [factor_region] at ht
  exact ht
/-- 同じ原始Mが誘導する指定粗細二行比較。 -/
def widthRowComparison : widthCoarseRow n ⟶ widthFineRow n :=
  StandardRow.cellRowMap (comparison n false) (width_selection_compatible n (regionA n))
    (width_selection_compatible n (regionB n))
omit [NeZero n] in
/-- 指定Aは1を含まず、全概念集合の真部分集合。 -/
theorem regionA_proper (hn : 2 ≤ n) : regionA n ≠ Set.univ := by
  intro h
  have h1 : (1 : Concept n) ∈ regionA n := h ▸ Set.mem_univ _
  exact one_ne_zero n hn h1
omit [NeZero n] in
/-- 指定Bは0を含まず、全概念集合の真部分集合。 -/
theorem regionB_proper : regionB n ≠ Set.univ := by
  intro h
  have h0 : (0 : Concept n) ∈ regionB n := h ▸ Set.mem_univ _
  exact h0 rfl
/-- 指定両領域の同じG-134診断は零。 -/
theorem local_defects_zero (hn : 2 ≤ n) :
    blockDefect (actualMap n false (regionA n)) = (0,0) ∧
    blockDefect (actualMap n false (regionB n)) = (0,0) :=
  ⟨proper_defect n (regionA n) (regionA_proper n hn),
    proper_defect n (regionB n) (regionB_proper n)⟩
/-- 同じ細二領域の標準H¹は原始pathの全射微分から零。 -/
theorem fine_pair_standard_H1_zero (hn : 2 ≤ n) : Subsingleton ((widthFineRow n).X₂.homology (1:ℤ)) := by
  letI := proper_H1_zero n false (regionA n) (regionA_proper n hn)
  letI := proper_H1_zero n false (regionB n) (regionB_proper n)
  letI := (oldH1Equiv (selected n false (regionA n)).complex).symm.injective.subsingleton
  letI := (oldH1Equiv (selected n false (regionB n)).complex).symm.injective.subsingleton
  exact (PairHomology.homologyEquiv (selected n false (regionA n)).complex
    (selected n false (regionB n)).complex 1).injective.subsingleton
omit [NeZero n] in
/-- 同じ粗二領域の標準H¹は元空辺から零。 -/
theorem coarse_pair_standard_H1_zero : Subsingleton ((widthCoarseRow n).X₂.homology (1:ℤ)) := by
  letI := coarse_H1_zero n (regionA n)
  letI := coarse_H1_zero n (regionB n)
  letI := (oldH1Equiv ((coarse n).targetSubsetComplex (regionA n))).symm.injective.subsingleton
  letI := (oldH1Equiv ((coarse n).targetSubsetComplex (regionB n))).symm.injective.subsingleton
  exact (PairHomology.homologyEquiv ((coarse n).targetSubsetComplex (regionA n))
    ((coarse n).targetSubsetComplex (regionB n)) 1).injective.subsingleton
/-- 同じ細Pは実二領域H¹の核なので零。 -/
theorem fine_P_zero (hn : 2 ≤ n) : Subsingleton (QuotientKernelRow.P (widthFineRow n)) := by
  letI := fine_pair_standard_H1_zero n hn
  infer_instance
omit [NeZero n] in
/-- 同じ粗Pは実二領域H¹の核なので零。 -/
theorem coarse_P_zero : Subsingleton (QuotientKernelRow.P (widthCoarseRow n)) := by
  letI := coarse_pair_standard_H1_zero n
  infer_instance
omit [NeZero n] in
/-- 元の粗交差標準H¹は空辺から零。 -/
theorem coarse_intersection_standard_H1_zero : Subsingleton ((widthCoarseRow n).X₃.homology (1:ℤ)) := by
  have hz : Subsingleton ((CellSelection.region (coarse n) (regionA n)).inter
    (CellSelection.region (coarse n) (regionB n))).complex.H1 := by
    apply AtlasCoefficientFiber.h1_subsingleton_of_d0_surjective
    intro z
    exact ⟨0, by funext e; exact e.1.elim⟩
  letI := hz
  exact (oldH1Equiv ((CellSelection.region (coarse n) (regionA n)).inter
    (CellSelection.region (coarse n) (regionB n))).complex).symm.injective.subsingleton
/-- 同じ原始二行比較のZは元の粗交差H¹内で零。 -/
theorem width_Z_zero : QuotientKernelRow.Z (widthCoarseRow n) (widthRowComparison n) = ⊥ := by
  letI := coarse_intersection_standard_H1_zero n
  exact Subsingleton.elim _ _
/-- 同じQ比較は零粗Qから来る零射。 -/
theorem width_q_zero (hn : 2 ≤ n) :
    QuotientKernelRow.q (widthCoarseRow n) (widthRowComparison n) = 0 := by
  letI := coarse_Q_zero n hn
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0, map_zero]
  rfl

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
