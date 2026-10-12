import ResearchLean.AG.AtlasGluingWidth.WidthHidden
import ResearchLean.AG.AtlasCoefficientFiber.GammaForest
import ResearchLean.AG.AtlasCoefficientFiber.LocalCoefficientSingle
import ResearchLean.AG.AtlasCoefficientFiber.LocalNaturality

/-! # 指定閉路の実Φと連結成分

GOAL E / witnesses §4。全辺が同じ原始比較で退化するため、唯一粗chartのΦは
元の細領域複体と同じincidenceを持つ。H⁰の実値一定性からΦ成分の一意性を導く。

## Implementation notes

Φの追加所属subtypeを忘却・付加して同じ元セルへ戻す。H¹零から連結性を
推論する代替は成立しない。成分指示関数の零微分を実辺incidenceで生成する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition AtlasCoefficientFiber
variable (n : ℕ) [NeZero n]

/-- 元のG-135とG-134が用いる生成因子の実細領域選択。 -/
abbrev actualSelected (X : Set (Concept n)) := CellSelection.region (fine n false)
  (comparisonFactor (coarseReading n) (fineReading n) (coarser n) ⁻¹' X)
/-- 全退化比較の実Φ chartは同じ選択細chartと両方向同じ。 -/
def phiChartEquiv (X : Set (Concept n)) (c : (coarse n).ChartInTargetSubset X) :
    PhiChart (comparison n false) X c ≃ (actualSelected n X).Chart where
  toFun := Subtype.val
  invFun v := ⟨v, Subsingleton.elim _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- 全退化比較の実Φ辺は同じ選択細辺と両方向同じ。 -/
def phiEdgeEquiv (X : Set (Concept n)) (c : (coarse n).ChartInTargetSubset X) :
    PhiEdge (comparison n false) X c ≃ (actualSelected n X).Edge where
  toFun := Subtype.val
  invFun e := ⟨e, rfl, Subsingleton.elim _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- 同じ実Φ面は原始空面なので空である。 -/
instance width_phi_faces_empty (X : Set (Concept n)) (c : (coarse n).ChartInTargetSubset X) :
    IsEmpty (PhiFace (comparison n false) X c) := ⟨fun f => f.1.1.elim⟩
/-- Φの忘却は同じ原端点を保持する。 -/
theorem phi_endpoint_same (X : Set (Concept n)) (c : (coarse n).ChartInTargetSubset X)
    (e : (actualSelected n X).Edge) (b : Bool) :
    phiChartEquiv n X c (phiEndpoint (comparison n false) X ((phiEdgeEquiv n X c).symm e) b) =
      (if b then (actualSelected n X).right e else (actualSelected n X).left e) := by
  cases b <;> rfl
/-- 同じ全三成分・実微分を保つΦと実細領域のcochain同型。 -/
def phiActualEquiv (X : Set (Concept n)) (c : (coarse n).ChartInTargetSubset X) :
    ThreeCochainComplex.CochainEquiv (phiComplex (comparison n false) X c) (actualSelected n X).complex where
  e0 := cochainEquivOfIndexEquiv (phiChartEquiv n X c).symm
  e1 := cochainEquivOfIndexEquiv (phiEdgeEquiv n X c).symm
  e2 := by
    letI : Subsingleton (phiComplex (comparison n false) X c).C2 := by
      change Subsingleton (PhiFace (comparison n false) X c → ℚ)
      infer_instance
    letI : IsEmpty (actualSelected n X).Face := ⟨fun f => f.1.elim⟩
    letI : Subsingleton (actualSelected n X).complex.C2 := by
      change Subsingleton ((actualSelected n X).Face → ℚ)
      infer_instance
    exact LinearEquiv.ofSubsingleton _ _
  comm0 x := by
    funext e
    change x (phiEndpoint (comparison n false) X ((phiEdgeEquiv n X c).symm e) true) -
      x (phiEndpoint (comparison n false) X ((phiEdgeEquiv n X c).symm e) false) =
      x ((phiChartEquiv n X c).symm ((actualSelected n X).right e)) -
        x ((phiChartEquiv n X c).symm ((actualSelected n X).left e))
    rfl
  comm1 _ := by funext f; exact f.1.elim
/-- 非空実領域は同じ細v chartを少なくとも一つ選ぶ。 -/
theorem actual_chart_nonempty (X : Set (Concept n)) (hx : X.Nonempty) :
    Nonempty (actualSelected n X).Chart := by
  unfold actualSelected
  rw [factor]
  obtain ⟨i,hi⟩ := hx
  exact ⟨⟨(i,false), (chart_selected n false X _).mpr (Or.inl hi)⟩⟩
/-- 原始細H⁰一定性を同じ生成因子の実選択へ輸送する。 -/
theorem actual_zero_constant (X : Set (Concept n))
    (hc : ∀ z : LinearMap.ker (selected n false X).complex.d0, ∀ v w, z.1 v = z.1 w) :
    ∀ z : LinearMap.ker (actualSelected n X).complex.d0, ∀ v w, z.1 v = z.1 w := by
  unfold actualSelected
  rw [factor]
  exact hc
/-- 実Φの各辺の両端は同じincidence連結成分を持つ。 -/
theorem phi_endpoint_component (X : Set (Concept n)) (c : (coarse n).ChartInTargetSubset X)
    (e : PhiEdge (comparison n false) X c) :
    (CategoryTheory.ConnectedComponents.mk (.inl (phiEndpoint (comparison n false) X e true)) :
      CategoryTheory.ConnectedComponents (PhiInc (comparison n false) X c)) =
        CategoryTheory.ConnectedComponents.mk (.inl (phiEndpoint (comparison n false) X e false)) :=
  Quotient.sound ((Zigzag.of_hom (phiEndpointIncidence (comparison n false) X c e true)).trans
    (Zigzag.of_hom (phiEndpointIncidence (comparison n false) X c e false)).symm)
/-- 実H⁰一定性は原始成分指示関数を通じ実Φの成分一意性を与える。 -/
theorem phi_components_subsingleton (X : Set (Concept n)) (c : (coarse n).ChartInTargetSubset X)
    (hc : ∀ z : LinearMap.ker (actualSelected n X).complex.d0, ∀ v w, z.1 v = z.1 w) :
    Subsingleton (CategoryTheory.ConnectedComponents (PhiInc (comparison n false) X c)) := by
  classical
  constructor
  intro a b
  obtain ⟨va,ha⟩ := phiComponent_chart_representative (comparison n false) X c a
  obtain ⟨vb,hb⟩ := phiComponent_chart_representative (comparison n false) X c b
  let x : (actualSelected n X).complex.C0 := fun v =>
    if (CategoryTheory.ConnectedComponents.mk (.inl ((phiChartEquiv n X c).symm v)) :
      CategoryTheory.ConnectedComponents (PhiInc (comparison n false) X c)) = a then 1 else 0
  have hx : (actualSelected n X).complex.d0 x = 0 := by
    funext e
    rw [CellSelection.complex_d0_apply]
    have hp := phi_endpoint_component n X c ((phiEdgeEquiv n X c).symm e)
    have ht' : phiEndpoint (comparison n false) X ((phiEdgeEquiv n X c).symm e) true =
        (phiChartEquiv n X c).symm ((actualSelected n X).right e) := by
      apply (phiChartEquiv n X c).injective
      exact phi_endpoint_same n X c e true
    have hf' : phiEndpoint (comparison n false) X ((phiEdgeEquiv n X c).symm e) false =
        (phiChartEquiv n X c).symm ((actualSelected n X).left e) := by
      apply (phiChartEquiv n X c).injective
      exact phi_endpoint_same n X c e false
    change (if CategoryTheory.ConnectedComponents.mk (.inl ((phiChartEquiv n X c).symm ((actualSelected n X).right e))) = a then 1 else 0) -
      (if CategoryTheory.ConnectedComponents.mk (.inl ((phiChartEquiv n X c).symm ((actualSelected n X).left e))) = a then 1 else 0) = 0
    rw [← ht', ← hf', hp, sub_self]
  have hval := hc ⟨x,hx⟩ (phiChartEquiv n X c vb) (phiChartEquiv n X c va)
  change x (phiChartEquiv n X c vb) = x (phiChartEquiv n X c va) at hval
  dsimp only [x] at hval
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, ha, hb] at hval
  by_cases h : b = a
  · exact h.symm
  · simp [h] at hval
/-- 非空実細領域から実Φ成分の非空性を生成する。 -/
theorem phi_components_nonempty (X : Set (Concept n)) (hx : X.Nonempty)
    (c : (coarse n).ChartInTargetSubset X) :
    Nonempty (CategoryTheory.ConnectedComponents (PhiInc (comparison n false) X c)) := by
  obtain ⟨v⟩ := actual_chart_nonempty n X hx
  exact ⟨CategoryTheory.ConnectedComponents.mk (.inl ((phiChartEquiv n X c).symm v))⟩
/-- 原始H⁰一定性から実右Kan chart係数の定数射が全単射。 -/
theorem width_chart_coefficient_bijective (X : Set (Concept n)) (hx : X.Nonempty)
    (hc : ∀ z : LinearMap.ker (actualSelected n X).complex.d0, ∀ v w, z.1 v = z.1 w)
    (c : (coarse n).ChartInTargetSubset X) :
    Function.Bijective (coefficientConstant (Carrier.preimageFunctor (comparison n false) X) (.chart c)) :=
  chartCoefficientConstant_bijective _ _ _ (phi_components_nonempty n X hx c)
    (phi_components_subsingleton n X c hc)

/-- Aの実選択H⁰一定性は原始二辺から生成される。 -/
theorem a_actual_zero_constant :
    ∀ z : LinearMap.ker (actualSelected n (regionA n)).complex.d0, ∀ v w, z.1 v = z.1 w :=
  actual_zero_constant n (regionA n) (fun z v w => (a_zero_constant n z v).trans (a_zero_constant n z w).symm)
/-- Bの実選択H⁰一定性は原始path帰納から生成される。 -/
theorem b_actual_zero_constant (hn : 2 ≤ n) :
    ∀ z : LinearMap.ker (actualSelected n (regionB n)).complex.d0, ∀ v w, z.1 v = z.1 w :=
  actual_zero_constant n (regionB n) (fun z v w => (b_zero_constant n hn z v).trans (b_zero_constant n hn z w).symm)
/-- Uの実選択H⁰一定性は原始全閉路から生成される。 -/
theorem full_actual_zero_constant :
    ∀ z : LinearMap.ker (actualSelected n Set.univ).complex.d0, ∀ v w, z.1 v = z.1 w :=
  actual_zero_constant n Set.univ (fun z v w => (full_zero_constant n z v).trans (full_zero_constant n z w).symm)
/-- 指定Uの実chart右Kan係数は原定数射の逆によってℚに同定される。 -/
def fullChartCoefficientEquiv (c : (coarse n).ChartInTargetSubset Set.univ) :
    (pushforwardCoefficients (comparison n false) Set.univ).obj (.chart c) ≃ₗ[ℚ] ℚ :=
  (LinearEquiv.ofBijective (coefficientConstant (Carrier.preimageFunctor (comparison n false) Set.univ) (.chart c))
    (width_chart_coefficient_bijective n Set.univ ⟨0,Set.mem_univ _⟩ (full_actual_zero_constant n) c)).symm
/-- 指定局所Aの実chart右Kan係数も原二辺の連結性からℚと同型。 -/
def aChartCoefficientEquiv (c : (coarse n).ChartInTargetSubset (regionA n)) :
    (pushforwardCoefficients (comparison n false) (regionA n)).obj (.chart c) ≃ₗ[ℚ] ℚ :=
  (LinearEquiv.ofBijective (coefficientConstant (Carrier.preimageFunctor (comparison n false) (regionA n)) (.chart c))
    (width_chart_coefficient_bijective n (regionA n) ⟨0,rfl⟩ (a_actual_zero_constant n) c)).symm
/-- 指定局所Bの実chart右Kan係数も原path連結性からℚと同型。 -/
def bChartCoefficientEquiv (hn : 2 ≤ n) (c : (coarse n).ChartInTargetSubset (regionB n)) :
    (pushforwardCoefficients (comparison n false) (regionB n)).obj (.chart c) ≃ₗ[ℚ] ℚ :=
  (LinearEquiv.ofBijective (coefficientConstant (Carrier.preimageFunctor (comparison n false) (regionB n)) (.chart c))
    (width_chart_coefficient_bijective n (regionB n) (regionB_nonempty n hn) (b_actual_zero_constant n hn) c)).symm
/-- 全退化比較の同じU fiber H¹は元閉路periodでℚと両方向同型。 -/
def fullPhiH1Equiv (c : (coarse n).ChartInTargetSubset Set.univ) :
    (phiComplex (comparison n false) Set.univ c).H1 ≃ₗ[ℚ] ℚ :=
  (phiActualEquiv n Set.univ c).h1Equiv.trans (fullH1Equiv n)
/-- 同じ原始A fiber H¹はpath微分の全射性から零。 -/
theorem a_phi_H1_zero (hn : 2 ≤ n) (c : (coarse n).ChartInTargetSubset (regionA n)) :
    Subsingleton (phiComplex (comparison n false) (regionA n) c).H1 := by
  letI : Subsingleton (actualSelected n (regionA n)).complex.H1 := proper_actual_H1_zero n false (regionA n) (regionA_proper n hn)
  exact (phiActualEquiv n (regionA n) c).h1Equiv.injective.subsingleton
/-- 同じ原始B fiber H¹はpath微分の全射性から零。 -/
theorem b_phi_H1_zero (c : (coarse n).ChartInTargetSubset (regionB n)) :
    Subsingleton (phiComplex (comparison n false) (regionB n) c).H1 := by
  letI : Subsingleton (actualSelected n (regionB n)).complex.H1 := proper_actual_H1_zero n false (regionB n) (regionB_proper n)
  exact (phiActualEquiv n (regionB n) c).h1Equiv.injective.subsingleton

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
