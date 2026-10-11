import ResearchLean.AG.AtlasGluingWidth.WidthIntegration
import ResearchLean.AG.AtlasCoefficientFiber.PhiInterval
import Formal.Util.AssertStandardAxioms

/-! # 指定原始選択の実微分の全射性

選択辺値を閉路全体へ零延長し、選択されないa辺だけでperiodを補正する。
一般閉路の累積積分を元chartへ制限することで実d⁰の原像を構成する。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Width
open ResolutionInvariance CanonicalResolution TwoPhase
variable (n : ℕ) [NeZero n]

/-- 指定細原始領域複体。 -/
abbrev selected (cut : Bool) (X : Set (Concept n)) :=
  CellSelection.region (fine n cut) (region n X)
/-- 指定任意a辺の単位cochain。 -/
def generatorAt (j : Concept n) : Cochain n := fun e => if e = (j, false) then 1 else 0
/-- 各a辺のperiodは同じ1。 -/
theorem period_generatorAt (j : Concept n) : period n (generatorAt n j) = 1 := by
  classical
  simp [period, generatorAt]
/-- 選択辺値の同じ元辺への零延長。 -/
def extendEdges (cut : Bool) (X : Set (Concept n))
    (z : (selected n cut X).Edge → ℚ) : Cochain n := by
  classical
  exact fun e =>
   if hc : cut = true → e ≠ (0, false) then
     if hx : (if e.2 then e.1 + 1 else e.1) ∈ X then
       z ⟨⟨e, hc⟩, (edge_selected n cut X _).mpr hx⟩
     else 0
   else 0
/-- 零延長は選択された全辺の値を保つ。 -/
theorem extendEdges_selected (cut : Bool) (X : Set (Concept n))
    (z : (selected n cut X).Edge → ℚ) (e : (selected n cut X).Edge) :
    extendEdges n cut X z e.1.1 = z e := by
  classical
  unfold extendEdges
  rw [dif_pos e.1.2, dif_pos ((edge_selected n cut X e.1).mp e.2)]
/-- 選択されないa辺を使うperiod補正は全選択辺を保つ。 -/
theorem selected_d0_surjective (cut : Bool) (X : Set (Concept n)) (j : Concept n)
    (hj : ∀ e : (selected n cut X).Edge, e.1.1 ≠ (j, false)) :
    Function.Surjective (selected n cut X).complex.d0 := by
  classical
  intro z
  let ext := extendEdges n cut X z
  let corrected : Cochain n := ext - period n ext • generatorAt n j
  have hp : period n corrected = 0 := by
    simp [corrected, map_sub, map_smul, period_generatorAt]
  let x : (selected n cut X).complex.C0 := fun v => potential n corrected v.1
  refine ⟨x, ?_⟩
  funext e
  have hd := congrFun (difference_potential n corrected hp) e.1.1
  change potential n corrected (right n e.1.1) -
    potential n corrected (left n e.1.1) = z e
  change potential n corrected (right n e.1.1) -
    potential n corrected (left n e.1.1) = corrected e.1.1 at hd
  rw [hd]
  simp [corrected, generatorAt, hj e, ext, extendEdges_selected]
/-- 真部分集合は欠けた概念のa辺を選ばない。 -/
theorem proper_d0_surjective (cut : Bool) (X : Set (Concept n)) (hX : X ≠ Set.univ) :
    Function.Surjective (selected n cut X).complex.d0 := by
  have hmissing : ∃ j : Concept n, j ∉ X := by
    by_contra h
    apply hX
    ext j
    simp only [Set.mem_univ, iff_true]
    exact Classical.byContradiction (fun hj => h ⟨j, hj⟩)
  obtain ⟨j, hj⟩ := hmissing
  apply selected_d0_surjective n cut X j
  intro e he
  have hs := (edge_selected n cut X e.1).mp e.2
  rw [he] at hs
  exact hj hs
/-- plusは全領域で削除a₀を選ばない。 -/
theorem plus_d0_surjective (X : Set (Concept n)) :
    Function.Surjective (selected n true X).complex.d0 := by
  apply selected_d0_surjective n true X 0
  intro e
  exact e.1.2 rfl
/-- 同じ真部分集合の実H¹商は零。 -/
theorem proper_H1_zero (cut : Bool) (X : Set (Concept n)) (hX : X ≠ Set.univ) :
    Subsingleton (selected n cut X).complex.H1 :=
  AtlasCoefficientFiber.h1_subsingleton_of_d0_surjective _ (proper_d0_surjective n cut X hX)
/-- plusの全領域の実H¹商は零。 -/
theorem plus_H1_zero (X : Set (Concept n)) : Subsingleton (selected n true X).complex.H1 :=
  AtlasCoefficientFiber.h1_subsingleton_of_d0_surjective _ (plus_d0_surjective n X)

/-- 全閉路で各元辺を選択辺へ入れる。 -/
def fullEdge (e : Concept n × Bool) : (selected n false Set.univ).Edge :=
  ⟨⟨e, by simp⟩, (edge_selected n false Set.univ _).mpr (Set.mem_univ _)⟩
/-- 全閉路で各元chartを選択chartへ入れる。 -/
def fullChart (v : Chart n) : (selected n false Set.univ).Chart :=
  ⟨v, (chart_selected n false Set.univ v).mpr (Or.inl (Set.mem_univ _))⟩
/-- 空面により全閉路の実cocycleは同じ全辺値と両方向同型。 -/
def fullCyclesEquiv : LinearMap.ker (selected n false Set.univ).complex.d1 ≃ₗ[ℚ]
    Cochain n where
  toFun z e := z.1 (fullEdge n e)
  invFun z := ⟨fun e => z e.1.1, by funext f; exact f.1.elim⟩
  left_inv z := by apply Subtype.ext; funext e; rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 全閉路の元chartと実chartの微分値は同じ。 -/
theorem full_boundary (x : (selected n false Set.univ).complex.C0) :
    fullCyclesEquiv n ((selected n false Set.univ).complex.boundaryToCycles x) =
      difference n (fun v => x (fullChart n v)) := by
  funext e
  rfl
/-- 実境界の像と指定全閉路微分の像を両方向で同定する。 -/
theorem full_image :
    (LinearMap.range (selected n false Set.univ).complex.boundaryToCycles).map
      (fullCyclesEquiv n).toLinearMap = LinearMap.range (difference n) := by
  ext z
  constructor
  · rintro ⟨cycle, ⟨x, rfl⟩, rfl⟩
    exact ⟨fun v => x (fullChart n v), (full_boundary n x).symm⟩
  · rintro ⟨x, rfl⟩
    let actual : (selected n false Set.univ).complex.C0 := fun v => x v.1
    refine ⟨(selected n false Set.univ).complex.boundaryToCycles actual,
      ⟨actual, rfl⟩, ?_⟩
    exact full_boundary n actual
/-- 同じ閉路商をperiodの核商へ輸送する。 -/
def periodQuotientEquiv :
    (Cochain n ⧸ LinearMap.range (difference n)) ≃ₗ[ℚ]
      (Cochain n ⧸ LinearMap.ker (period n)) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl ℚ (Cochain n)) (by
    simpa using (period_ker n).symm)
/-- 全閉路の実H¹は指定periodによるℚと両方向同型。 -/
def fullH1Equiv : (selected n false Set.univ).complex.H1 ≃ₗ[ℚ] ℚ :=
  (Submodule.Quotient.equiv _ _ (fullCyclesEquiv n) (full_image n)).trans
    ((periodQuotientEquiv n).trans ((period n).quotKerEquivOfSurjective (period_surjective n)))
/-- 全実代表元における同型は同じperiodを返す。 -/
theorem fullH1Equiv_mk (z : LinearMap.ker (selected n false Set.univ).complex.d1) :
    fullH1Equiv n ((LinearMap.range (selected n false Set.univ).complex.boundaryToCycles).mkQ z) =
      period n (fullCyclesEquiv n z) := rfl
/-- 指定a₀生成元を同じ実H¹商へ入れる。 -/
def fullGenerator : (selected n false Set.univ).complex.H1 :=
  (LinearMap.range (selected n false Set.univ).complex.boundaryToCycles).mkQ
    ((fullCyclesEquiv n).symm (generator n))
/-- 指定実生成元の同型値は1。 -/
theorem fullGenerator_value : fullH1Equiv n (fullGenerator n) = 1 := by
  rw [fullGenerator, fullH1Equiv_mk, LinearEquiv.apply_symm_apply, period_generator]
/-- 指定実H¹生成元は非零。 -/
theorem fullGenerator_ne_zero : fullGenerator n ≠ 0 := by
  intro hz
  have hv := fullGenerator_value n
  rw [hz, map_zero] at hv
  exact zero_ne_one hv

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
