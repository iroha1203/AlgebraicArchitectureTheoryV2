import ResearchLean.AG.AtlasGluingWidth.WidthMayerVietoris
import ResearchLean.AG.AtlasCoefficientFiber.HomologyRepresentatives

/-! # 指定交差類の標準接続像

GOAL E / witnesses §4。実交差値zをAへ持ち上げ、微分の局所値を同じ和へ
貼り合わせる。この元を標準δへ渡し、符号付きa₀ cochainと同定する。

## Implementation notes

Aの持ち上げはw₀だけでz(true)、他でz(false)、Bは零とする。
単にQとH¹の同次元から同型を選ぶ案は、標準δの符号を保持しないため採らない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
variable (n : ℕ) [NeZero n]

/-- 真交差の二値を同じ実次数0 cochainへ移す。 -/
def intersectionValues (hn : 2 ≤ n) (z : Bool → ℚ) : (intersection n).complex.C0 :=
  fun v => z (intersectionChartEquiv n hn v)
/-- 空実交差辺から生成されるcocycle条件。 -/
theorem intersection_values_closed (hn : 2 ≤ n) (z : Bool → ℚ) :
    (intersection n).complex.d0 (intersectionValues n hn z) = 0 := by
  letI := intersection_edges_empty n
  funext e
  exact isEmptyElim e
/-- Aの実chart上の指定持ち上げ。 -/
def aLift (z : Bool → ℚ) : (selected n false (regionA n)).complex.C0 :=
  fun v => if v.1 = (0,true) then z true else z false
/-- 同じ二領域次数0への指定持ち上げ。 -/
def intersectionLift (z : Bool → ℚ) :
    (pairComplex (selected n false (regionA n)).complex (selected n false (regionB n)).complex).C0 :=
  (aLift n z, 0)
/-- 元の差制限は指定持ち上げを元の交差cochainへ返す。 -/
theorem intersection_lift (hn : 2 ≤ n) (z : Bool → ℚ) :
    (CellSelection.intersectionDifference (selected n false (regionA n))
      (selected n false (regionB n))).f0 (intersectionLift n z) = intersectionValues n hn z := by
  funext v
  have hv := (intersection_chart n hn v.1).mp v.2
  rcases v with ⟨⟨i,b⟩,hp⟩
  change b = true ∧ (i = -1 ∨ i = 0) at hv
  rcases hv with ⟨rfl,hi | hi⟩
  · subst i
    change (if ((-1 : Concept n),true) = (0,true) then z true else z false) - 0 =
      z (if (-1 : Concept n) = 0 then true else false)
    simp [neg_one_ne_zero n hn]
  · subst i
    change (if ((0 : Concept n),true) = (0,true) then z true else z false) - 0 =
      z (if (0 : Concept n) = 0 then true else false)
    simp
/-- 同じ元辺名による和上の符号付きa₀ cochain。 -/
def unionGenerator (z : Bool → ℚ) :
    ((selected n false (regionA n)).union (selected n false (regionB n))).complex.C1 :=
  fun e => endpointDifference z * generatorAt n 0 e.1.1
/-- Aの実微分はa₀でのみ順序付き値差となる。 -/
theorem a_lift_d0 (hn : 2 ≤ n) (z : Bool → ℚ) (e : (selected n false (regionA n)).Edge) :
    (selected n false (regionA n)).complex.d0 (aLift n z) e =
      endpointDifference z * generatorAt n 0 e.1.1 := by
  have he := (edge_selected n false (regionA n) e.1).mp e.2
  rcases e with ⟨⟨⟨i,b⟩,hcut⟩,hp⟩
  cases b
  · have hi : i = 0 := he
    subst i
    simp [CellSelection.complex_d0_apply, aLift, CellSelection.left_val,
      CellSelection.right_val, left_apply, right_apply, endpointDifference_apply, generatorAt_apply]
  · have hi : i = -1 := add_eq_zero_iff_eq_neg.mp he
    subst i
    simp [CellSelection.complex_d0_apply, aLift, CellSelection.left_val,
      CellSelection.right_val, left_apply, right_apply, endpointDifference_apply,
      generatorAt_apply, neg_one_ne_zero n hn]
/-- Bにa₀は選択されず、指定貼り合わせcochainはBで零。 -/
theorem b_generator_zero (z : Bool → ℚ) (e : (selected n false (regionB n)).Edge) :
    endpointDifference z * generatorAt n 0 e.1.1 = 0 := by
  have he := (edge_selected n false (regionB n) e.1).mp e.2
  have hne : e.1.1 ≠ (0,false) := by
    intro h
    rw [h] at he
    exact he rfl
  simp [generatorAt_apply, hne]
/-- 指定和のcochainを制限すると持ち上げの実微分になる。 -/
theorem intersection_lift_derivative (hn : 2 ≤ n) (z : Bool → ℚ) :
    (CellSelection.unionInclusion (selected n false (regionA n))
      (selected n false (regionB n))).f1 (unionGenerator n z) =
      (pairComplex (selected n false (regionA n)).complex
        (selected n false (regionB n)).complex).d0 (intersectionLift n z) := by
  apply Prod.ext
  · funext e
    exact (a_lift_d0 n hn z e).symm
  · funext e
    change endpointDifference z * generatorAt n 0 e.1.1 =
      (selected n false (regionB n)).complex.d0 0 e
    simpa only [map_zero, Pi.zero_apply] using b_generator_zero n z e
/-- 空元面から指定貼り合わせcochainは閉じている。 -/
theorem union_generator_closed (z : Bool → ℚ) :
    ((selected n false (regionA n)).union (selected n false (regionB n))).complex.d1
      (unionGenerator n z) = 0 := by
  funext f
  exact f.1.elim
/-- 指定交差の標準homology class。 -/
def intersectionClass (hn : 2 ≤ n) (z : Bool → ℚ) : (widthFineRow n).X₃.homology (0:ℤ) :=
  oldH0Equiv (intersection n).complex ⟨intersectionValues n hn z, intersection_values_closed n hn z⟩
/-- 指定和の標準homology classは同じ実a₀ cochain商から生成される。 -/
def unionGeneratorClass (z : Bool → ℚ) : (widthFineRow n).X₁.homology (1:ℤ) :=
  oldH1Equiv _ (Submodule.Quotient.mk ⟨unionGenerator n z, union_generator_closed n z⟩)
/-- 指定交差classを標準δへ渡すと同じ符号付きa₀ classが得られる。 -/
theorem standard_connecting_generator (hn : 2 ≤ n) (z : Bool → ℚ) :
    StandardLES.connecting (widthFineRow n) (StandardRow.cellRow_shortExact _ _) 0
      (intersectionClass n hn z) = unionGeneratorClass n z := by
  have hz : (widthFineRow n).X₃.d 0 1 (intersectionValues n hn z) = 0 :=
    intersection_values_closed n hn z
  have hwc : (widthFineRow n).X₁.d 1 2 (unionGenerator n z) = 0 :=
    union_generator_closed n z
  have hc := CohomologyRepresentatives.connecting_cycleClass (widthFineRow n)
    (StandardRow.cellRow_shortExact _ _) 0 (intersectionValues n hn z) hz
    (intersectionLift n z) (intersection_lift n hn z)
    (unionGenerator n z) (intersection_lift_derivative n hn z) hwc
  have h0' : CohomologyRepresentatives.cycleClass (widthFineRow n).X₃ 0
      (intersectionValues n hn z) hz = intersectionClass n hn z :=
    CohomologyRepresentatives.cycleClass_zeroExtension_H0 _ _ _
  have h1' : CohomologyRepresentatives.cycleClass (widthFineRow n).X₁ 1
      (unionGenerator n z) hwc = unionGeneratorClass n z :=
    CohomologyRepresentatives.cycleClass_zeroExtension_H1 _ _ _
  rw [h0'] at hc
  exact hc.trans h1'

/-- 指定A/Bの和は同じ元セルで全領域選択となる。 -/
theorem union_full_eq : (selected n false (regionA n)).union (selected n false (regionB n)) =
    selected n false Set.univ := by
  simp only [selected, ← CellSelection.region_union]
  congr 1
  ext v
  simp only [Set.mem_union, region, Set.mem_preimage, Set.mem_univ, iff_true, regionB]
  exact Classical.em _
/-- 全セル等号に沿う実cocycle核の同型。 -/
def selectionCyclesEquiv {T : Type} {q : Reading T} {D : TargetSupportedNerve q}
    (S S' : CellSelection D) (he : S = S') : LinearMap.ker S.complex.d1 ≃ₗ[ℚ]
      LinearMap.ker S'.complex.d1 := by
  subst S'
  exact LinearEquiv.refl ℚ _
/-- 全セル輸送は同じ元辺のcochain値を保つ。 -/
theorem selectionCyclesEquiv_val {T : Type} {q : Reading T} {D : TargetSupportedNerve q}
    (S S' : CellSelection D) (he : S = S') (z : LinearMap.ker S.complex.d1) (e : S'.Edge) :
    (selectionCyclesEquiv S S' he z).1 e = z.1 ⟨e.1, he.symm ▸ e.2⟩ := by
  subst S'
  rfl
/-- 全セル等号に沿う実H¹商の同型。 -/
def selectionH1Equiv {T : Type} {q : Reading T} {D : TargetSupportedNerve q}
    (S S' : CellSelection D) (he : S = S') : S.complex.H1 ≃ₗ[ℚ] S'.complex.H1 := by
  subst S'
  exact LinearEquiv.refl ℚ _
/-- 全セル同定は全実cocycle商代表元を保つ。 -/
theorem selectionH1Equiv_mk {T : Type} {q : Reading T} {D : TargetSupportedNerve q}
    (S S' : CellSelection D) (he : S = S') (z : LinearMap.ker S.complex.d1) :
    selectionH1Equiv S S' he (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (selectionCyclesEquiv S S' he z) := by
  subst S'
  rfl
/-- 指定の同じ和標準H¹を全閉路の実periodへ移す。 -/
def unionPeriodEquiv : (widthFineRow n).X₁.homology (1:ℤ) ≃ₗ[ℚ] ℚ :=
  (oldH1Equiv ((selected n false (regionA n)).union (selected n false (regionB n))).complex).symm.trans
    ((selectionH1Equiv _ _ (union_full_eq n)).trans (fullH1Equiv n))
/-- 指定貼り合わせclassはperiod評価で同じ順序付き値差。 -/
theorem union_generator_value (z : Bool → ℚ) :
    unionPeriodEquiv n (unionGeneratorClass n z) = endpointDifference z := by
  dsimp only [unionPeriodEquiv, unionGeneratorClass, LinearEquiv.trans_apply]
  erw [LinearEquiv.symm_apply_apply, selectionH1Equiv_mk, fullH1Equiv_mk]
  have he : fullCyclesEquiv n (selectionCyclesEquiv _ _ (union_full_eq n)
      ⟨unionGenerator n z, union_generator_closed n z⟩) =
      endpointDifference z • generatorAt n 0 := by
    funext e
    change (selectionCyclesEquiv _ _ (union_full_eq n)
      ⟨unionGenerator n z, union_generator_closed n z⟩).1 (fullEdge n e) = _
    rw [selectionCyclesEquiv_val]
    rfl
  rw [he, map_smul, period_generatorAt]
  exact mul_one _
/-- 同じ細Q代表元の評価は実交差の順序付き値差。 -/
theorem intersection_Q_value (hn : 2 ≤ n) (z : Bool → ℚ) :
    fineQEquiv n hn ((LinearMap.range (homologyMap (widthFineRow n).g 0).hom).mkQ
      (intersectionClass n hn z)) = endpointDifference z := by
  rw [fine_Q_mk]
  congr 1
  rw [intersectionClass, fineIntersectionStandardH0Equiv_oldH0Equiv]
  exact (intersectionH0Equiv n hn).apply_symm_apply z
/-- 指定(0,1)の標準δ像は同じperiod1を持つ。 -/
theorem standard_connecting_period_one (hn : 2 ≤ n) :
    unionPeriodEquiv n (StandardLES.connecting (widthFineRow n)
      (StandardRow.cellRow_shortExact _ _) 0
      (intersectionClass n hn (fun b => if b then 1 else 0))) = 1 := by
  rw [standard_connecting_generator, union_generator_value]
  simp [endpointDifference_apply]
/-- 同じ指定交差classの標準δ像は非零。 -/
theorem standard_connecting_nonzero (hn : 2 ≤ n) :
    StandardLES.connecting (widthFineRow n) (StandardRow.cellRow_shortExact _ _) 0
      (intersectionClass n hn (fun b => if b then 1 else 0)) ≠ 0 := by
  intro hz
  have h := standard_connecting_period_one n hn
  rw [hz, map_zero] at h
  exact zero_ne_one h

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
