import ResearchLean.AG.AtlasDefectComposition.WitnessOneInput
import ResearchLean.AG.AtlasDefectComposition.FullSupportCoordinates
import ResearchLean.AG.ResolutionInvariance.GeneratedComparisonMap
import Formal.Util.AssertStandardAxioms

/-!
# W1 の直接生成比較と標準Law座標

原始二射から生成した直接Homが、同じセル名と発生ラベルの標準座標で全三次数の恒等に
なることを証明する。readingを同一視せず、既存K0座標の線形同型を通して述べる。
-/

noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase

/-- W1 の段階₀の全chart支持を確認するAPI。 -/
theorem chartSupport_univ₀ (c : N₀.nerve.Chart) : N₀.chartSupport c = Set.univ := rfl

/-- W1 の段階₀の全edge支持はK1から出る。 -/
theorem edgeSupport_univ₀ (e : N₀.nerve.EdgeComponent) : N₀.edgeSupport e = Set.univ := by
  ext t
  rw [N₀.mem_edgeSupport_iff e t]
  simp only [Set.mem_univ, and_self]

/-- W1 の段階₀の空face型から全face支持を確認する。 -/
theorem faceSupport_univ₀ (c : N₀.nerve.FaceComponent) : N₀.faceSupport c = Set.univ := c.elim

/-- W1 の段階₁の全chart支持を確認するAPI。 -/
theorem chartSupport_univ₁ (c : N₁.nerve.Chart) : N₁.chartSupport c = Set.univ := rfl

/-- W1 の段階₁の全edge支持はK1から出る。 -/
theorem edgeSupport_univ₁ (e : N₁.nerve.EdgeComponent) : N₁.edgeSupport e = Set.univ := by
  ext t
  rw [N₁.mem_edgeSupport_iff e t]
  simp only [Set.mem_univ, and_self]

/-- W1 の段階₁の空face型から全face支持を確認する。 -/
theorem faceSupport_univ₁ (c : N₁.nerve.FaceComponent) : N₁.faceSupport c = Set.univ := c.elim

/-- W1 の段階₂の全chart支持を確認するAPI。 -/
theorem chartSupport_univ₂ (c : N₂.nerve.Chart) : N₂.chartSupport c = Set.univ := rfl

/-- W1 の段階₂の全edge支持はK1から出る。 -/
theorem edgeSupport_univ₂ (e : N₂.nerve.EdgeComponent) : N₂.edgeSupport e = Set.univ := by
  ext t
  rw [N₂.mem_edgeSupport_iff e t]
  simp only [Set.mem_univ, and_self]

/-- W1 の段階₂の空face型から全face支持を確認する。 -/
theorem faceSupport_univ₂ (c : N₂.nerve.FaceComponent) : N₂.faceSupport c = Set.univ := c.elim

/-- W1 の段階₀・次数0の名付きセルと発生Lawラベルへの座標同定。 -/
def coordinate0₀ := fullCoordinateEquiv laws q₀ adequate₀ N₀.chartSupport chartSupport_univ₀

/-- W1 の段階₀・次数0の標準Law cochain座標。 -/
def standard0₀ := fullCochainEquiv laws q₀ adequate₀ N₀.chartSupport chartSupport_univ₀

/-- W1 の段階₀・次数1の名付きセルと発生Lawラベルへの座標同定。 -/
def coordinate1₀ := fullCoordinateEquiv laws q₀ adequate₀ N₀.edgeSupport edgeSupport_univ₀

/-- W1 の段階₀・次数1の標準Law cochain座標。 -/
def standard1₀ := fullCochainEquiv laws q₀ adequate₀ N₀.edgeSupport edgeSupport_univ₀

/-- W1 の段階₀・次数2の名付きセルと発生Lawラベルへの座標同定。 -/
def coordinate2₀ := fullCoordinateEquiv laws q₀ adequate₀ N₀.faceSupport faceSupport_univ₀

/-- W1 の段階₀・次数2の標準Law cochain座標。 -/
def standard2₀ := fullCochainEquiv laws q₀ adequate₀ N₀.faceSupport faceSupport_univ₀

/-- W1 の段階₂・次数0の名付きセルと発生Lawラベルへの座標同定。 -/
def coordinate0₂ := fullCoordinateEquiv laws q₂ adequate₂ N₂.chartSupport chartSupport_univ₂

/-- W1 の段階₂・次数0の標準Law cochain座標。 -/
def standard0₂ := fullCochainEquiv laws q₂ adequate₂ N₂.chartSupport chartSupport_univ₂

/-- W1 の段階₂・次数1の名付きセルと発生Lawラベルへの座標同定。 -/
def coordinate1₂ := fullCoordinateEquiv laws q₂ adequate₂ N₂.edgeSupport edgeSupport_univ₂

/-- W1 の段階₂・次数1の標準Law cochain座標。 -/
def standard1₂ := fullCochainEquiv laws q₂ adequate₂ N₂.edgeSupport edgeSupport_univ₂

/-- W1 の段階₂・次数2の名付きセルと発生Lawラベルへの座標同定。 -/
def coordinate2₂ := fullCoordinateEquiv laws q₂ adequate₂ N₂.faceSupport faceSupport_univ₂

/-- W1 の段階₂・次数2の標準Law cochain座標。 -/
def standard2₂ := fullCochainEquiv laws q₂ adequate₂ N₂.faceSupport faceSupport_univ₂

/-- W1 の直接chart座標写像は標準indexを保つ。 -/
theorem direct_chartCoordinate (p : Fin 3 × LawValueLabel laws) :
    M₀₂.chartCoordinateMap laws adequate₀ adequate₂ (coordinate0₂.symm p) =
      coordinate0₀.symm p := by
  apply CellCoordinate.ext
  · exact direct_chart p.1
  · rfl
  · rfl

/-- W1 の直接edge座標写像は標準indexを保つ。 -/
theorem direct_edgeCoordinate (p : Fin 3 × LawValueLabel laws) :
    M₀₂.edgeCoordinateMapOption laws adequate₀ adequate₂ (coordinate1₂.symm p) =
      some (coordinate1₀.symm p) := by
  rw [M₀₂.edgeCoordinateMapOption_eq_some laws adequate₀ adequate₂
    (coordinate1₂.symm p) p.1 (direct_edge p.1)]
  rfl

/-- W1 の直接生成Homの次数0作用は標準Law座標で恒等。 -/
theorem direct_standard0 (x : (N₀.lawGeneratedComplex laws adequate₀).C0) :
    standard0₂ (M₀₂.generatedPullback0 laws adequate₀ adequate₂ x) = standard0₀ x := by
  funext p
  change fullCochainEquiv laws q₂ adequate₂ N₂.chartSupport chartSupport_univ₂
    (M₀₂.generatedPullback0 laws adequate₀ adequate₂ x) p =
    fullCochainEquiv laws q₀ adequate₀ N₀.chartSupport chartSupport_univ₀ x p
  rw [fullCochainEquiv_apply, fullCochainEquiv_apply,
    M₀₂.generatedPullback0_apply laws adequate₀ adequate₂]
  exact congrArg x (direct_chartCoordinate p)

/-- W1 の直接生成Homの次数1作用は標準Law座標で恒等。 -/
theorem direct_standard1 (x : (N₀.lawGeneratedComplex laws adequate₀).C1) :
    standard1₂ (M₀₂.generatedPullback1 laws adequate₀ adequate₂ x) = standard1₀ x := by
  funext p
  change fullCochainEquiv laws q₂ adequate₂ N₂.edgeSupport edgeSupport_univ₂
    (M₀₂.generatedPullback1 laws adequate₀ adequate₂ x) p =
    fullCochainEquiv laws q₀ adequate₀ N₀.edgeSupport edgeSupport_univ₀ x p
  rw [fullCochainEquiv_apply, fullCochainEquiv_apply,
    M₀₂.generatedPullback1_apply laws adequate₀ adequate₂]
  change (M₀₂.edgeCoordinateMapOption laws adequate₀ adequate₂ (coordinate1₂.symm p)).elim 0 x =
    x (coordinate1₀.symm p)
  rw [direct_edgeCoordinate p]
  rfl

/-- W1 の直接生成Homの次数2作用は標準Law座標で恒等。 -/
theorem direct_standard2 (x : (N₀.lawGeneratedComplex laws adequate₀).C2) :
    standard2₂ (M₀₂.generatedPullback2 laws adequate₀ adequate₂ x) = standard2₀ x := by
  funext p
  exact p.1.elim

end AAT.AG.AtlasDefectComposition.WitnessOne
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessOne
