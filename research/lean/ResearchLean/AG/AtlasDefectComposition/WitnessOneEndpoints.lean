import ResearchLean.AG.AtlasDefectComposition.WitnessOneCancellation
import ResearchLean.AG.AtlasDefectComposition.WitnessThreeActual
import Formal.Util.AssertStandardAxioms
/-! # W1の追加次数の実比較

chart差分の定数核と空の面成分から、三比較のH⁰同型とH²零性を導く。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open ResolutionInvariance TwoPhase
/-- W1粗段の次数0核の定数値同型。 -/
def constants₀ : LinearMap.ker (namedComplex N₀).d0 ≃ₗ[ℚ] ℚ :=
  WitnessThree.triangleConstants
/-- W1細段の次数0核の定数値同型。 -/
def constants₂ : LinearMap.ker (namedComplex N₂).d0 ≃ₗ[ℚ] ℚ := constants₀
/-- W1中間段の二三角形にも一つの共通定数核がある。 -/
def constants₁ : LinearMap.ker (namedComplex N₁).d0 ≃ₗ[ℚ] ℚ where
  toFun x := x.val 0
  invFun r := ⟨fun _ => r,by funext e; change r-r=0; exact sub_self r⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have h (e : Fin 6) : x.val (twoTriangles.edgeRight e)-
        x.val (twoTriangles.edgeLeft e)=0 := congrFun x.property e
    fin_cases i
    · rfl
    · exact (sub_eq_zero.mp (h 0)).symm
    · exact (sub_eq_zero.mp (h 1)).symm
    · exact (sub_eq_zero.mp (h 3)).symm
    · exact (sub_eq_zero.mp (h 4)).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- W1第一比較を同じ実blockの全成分同型で名付きセルへ移す。 -/
def named₀₁ (l : LawValueLabel laws) := namedComparisonHom M₀₁ laws adequate₀ adequate₁
  chartSupport_univ₀ edgeSupport_univ₀ (fun f => f.elim)
  chartSupport_univ₁ edgeSupport_univ₁ (fun f => f.elim) l
/-- W1第二比較を同じ実blockの全成分同型で名付きセルへ移す。 -/
def named₁₂ (l : LawValueLabel laws) := namedComparisonHom M₁₂ laws adequate₁ adequate₂
  chartSupport_univ₁ edgeSupport_univ₁ (fun f => f.elim)
  chartSupport_univ₂ edgeSupport_univ₂ (fun f => f.elim) l
/-- W1直接比較を同じ実blockの全成分同型で名付きセルへ移す。 -/
def named₀₂ (l : LawValueLabel laws) := namedComparisonHom M₀₂ laws adequate₀ adequate₂
  chartSupport_univ₀ edgeSupport_univ₀ (fun f => f.elim)
  chartSupport_univ₂ edgeSupport_univ₂ (fun f => f.elim) l
/-- 第一比較の次数0核は同じ定数値を保つ。 -/
theorem constants_forward (l : LawValueLabel laws) (x : LinearMap.ker (namedComplex N₀).d0) :
    constants₁ (oldH0Map (named₀₁ l) x) = constants₀ x :=
  namedComparisonHom_f0 M₀₁ laws adequate₀ adequate₁
    chartSupport_univ₀ edgeSupport_univ₀ (fun f => f.elim)
    chartSupport_univ₁ edgeSupport_univ₁ (fun f => f.elim) l x.val 0
/-- 第二比較の次数0核は同じ定数値を保つ。 -/
theorem constants_backward (l : LawValueLabel laws) (x : LinearMap.ker (namedComplex N₁).d0) :
    constants₂ (oldH0Map (named₁₂ l) x) = constants₁ x :=
  namedComparisonHom_f0 M₁₂ laws adequate₁ adequate₂
    chartSupport_univ₁ edgeSupport_univ₁ (fun f => f.elim)
    chartSupport_univ₂ edgeSupport_univ₂ (fun f => f.elim) l x.val 0
/-- 直接比較の次数0核は同じ定数値を保つ。 -/
theorem constants_direct (l : LawValueLabel laws) (x : LinearMap.ker (namedComplex N₀).d0) :
    constants₂ (oldH0Map (named₀₂ l) x) = constants₀ x := by
  exact namedComparisonHom_f0 M₀₂ laws adequate₀ adequate₂
    chartSupport_univ₀ edgeSupport_univ₀ (fun f => f.elim)
    chartSupport_univ₂ edgeSupport_univ₂ (fun f => f.elim) l x.val 0
/-- 三つの名付き実比較の標準H⁰欠損はすべて零。 -/
theorem named_H0_defects (l : LawValueLabel laws) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₀₁ l)) 0).hom = (0,0) ∧
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₁₂ l)) 0).hom = (0,0) ∧
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₀₂ l)) 0).hom = (0,0) := by
  have hf : Function.Bijective (oldH0Map (named₀₁ l)) :=
    (LinearConjugation.bijective_iff _ (LinearMap.id : ℚ →ₗ[ℚ] ℚ) constants₀ constants₁
      (constants_forward l)).mpr Function.bijective_id
  have hg : Function.Bijective (oldH0Map (named₁₂ l)) :=
    (LinearConjugation.bijective_iff _ (LinearMap.id : ℚ →ₗ[ℚ] ℚ) constants₁ constants₂
      (constants_backward l)).mpr Function.bijective_id
  have hh : Function.Bijective (oldH0Map (named₀₂ l)) :=
    (LinearConjugation.bijective_iff _ (LinearMap.id : ℚ →ₗ[ℚ] ℚ) constants₀ constants₂
      (constants_direct l)).mpr Function.bijective_id
  exact ⟨(blockDefect_eq_zero_iff_bijective _).mpr ((standardH0_bijective_iff _).mpr hf),
    (blockDefect_eq_zero_iff_bijective _).mpr ((standardH0_bijective_iff _).mpr hg),
    (blockDefect_eq_zero_iff_bijective _).mpr ((standardH0_bijective_iff _).mpr hh)⟩
/-- 空の面を持つW1の三段の標準H²は零次元。 -/
theorem H2_dimensions :
    Module.finrank ℚ ((zeroExtension (namedComplex N₀)).homology 2)=0 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex N₁)).homology 2)=0 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex N₂)).homology 2)=0 := by
  have h0 := standardH2_dimension (namedComplex N₀)
  have h1 := standardH2_dimension (namedComplex N₁)
  have h2 := standardH2_dimension (namedComplex N₂)
  have c0 : Module.finrank ℚ (namedComplex N₀).C2=0 := by change Module.finrank ℚ (Empty → ℚ)=0; simp
  have c1 : Module.finrank ℚ (namedComplex N₁).C2=0 := by change Module.finrank ℚ (Empty → ℚ)=0; simp
  have c2 : Module.finrank ℚ (namedComplex N₂).C2=0 := by change Module.finrank ℚ (Empty → ℚ)=0; simp
  omega
/-- 三つの名付き実比較の標準H²欠損はすべて零。 -/
theorem named_H2_defects (l : LawValueLabel laws) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₀₁ l)) 2).hom = (0,0) ∧
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₁₂ l)) 2).hom = (0,0) ∧
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap (named₀₂ l)) 2).hom = (0,0) := by
  simp only [blockDefect_eq_finrank_sub_range,H2_dimensions.1,H2_dimensions.2.1,H2_dimensions.2.2,
    Nat.zero_sub]
  exact ⟨True.intro,True.intro,True.intro⟩
end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
