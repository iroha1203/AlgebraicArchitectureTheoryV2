import ResearchLean.AG.AtlasDefectComposition.FullSupportIncidence
import ResearchLean.AG.AtlasDefectComposition.FullSupportPullback
import ResearchLean.AG.AtlasDefectComposition.ConeEquivalence
import Formal.Util.AssertStandardAxioms
/-! # 全台blockの実比較を名付きセルへ移す

実生成Homを全三成分同値で移し、元の部分セル表による全成分評価を証明する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source] {q r : Reading Source} {h : q.CoarserThan r}
variable {D : TargetSupportedNerve q} {E : TargetSupportedNerve r}
variable (M : TargetSupportedNerveMorphism q r h D E)
variable (laws : FiniteLawFamily Source) (hq : laws.Adequate q) (hr : laws.Adequate r)
variable (hD0 : ∀ c, D.chartSupport c = Set.univ) (hD1 : ∀ e, D.edgeSupport e = Set.univ)
variable (hD2 : ∀ f, D.faceSupport f = Set.univ)
variable (hE0 : ∀ c, E.chartSupport c = Set.univ) (hE1 : ∀ e, E.edgeSupport e = Set.univ)
variable (hE2 : ∀ f, E.faceSupport f = Set.univ) (label : LawValueLabel laws)
/-- 実生成block Homを名付き原始セル複体へ移す。微分の可換性は生成定理から保つ。 -/
def namedComparisonHom : ThreeCochainComplex.Hom (namedComplex D) (namedComplex E) :=
  cochainComp (fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).symm.toHom
    (cochainComp (M.generatedBlockComparisonHom laws hq hr label)
      (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label).toHom)
/-- 元の実生成Homと名付き比較は全三成分同値の正方形を満たす。 -/
theorem namedComparisonHom_square :
    cochainComp (M.generatedBlockComparisonHom laws hq hr label)
      (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label).toHom =
    cochainComp (fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).toHom
      (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label) := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro x
  · change _ = (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label).e0
      ((M.generatedBlockComparisonHom laws hq hr label).f0
        ((fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).e0.symm
          ((fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).e0 x)))
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · change _ = (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label).e1
      ((M.generatedBlockComparisonHom laws hq hr label).f1
        ((fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).e1.symm
          ((fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).e1 x)))
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · change _ = (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label).e2
      ((M.generatedBlockComparisonHom laws hq hr label).f2
        ((fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).e2.symm
          ((fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).e2 x)))
    rw [LinearEquiv.symm_apply_apply]
    rfl
/-- 名付き比較の次数0は原始chart写像との合成である。 -/
theorem namedComparisonHom_f0 (x : D.nerve.Chart → ℚ) (c : E.nerve.Chart) :
    (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label).f0 x c = x (M.chartMap c) := by
  change fullBlockCochainEquiv laws r hr E.chartSupport hE0 label
    (M.generatedBlockPullback0 laws hq hr label
      ((fullBlockCochainEquiv laws q hq D.chartSupport hD0 label).symm x)) c = _
  rw [fullBlock_pullback0 M laws hq hr label hD0 hE0]
  exact congrFun ((fullBlockCochainEquiv laws q hq D.chartSupport hD0 label).apply_symm_apply x) _
/-- 名付き比較の次数1は原始some辺を同名座標へ写す。 -/
theorem namedComparisonHom_f1_some (x : D.nerve.EdgeComponent → ℚ)
    (e : E.nerve.EdgeComponent) (d : D.nerve.EdgeComponent) (he : M.edgeMap e = some d) :
    (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label).f1 x e = x d := by
  change fullBlockCochainEquiv laws r hr E.edgeSupport hE1 label
    (M.generatedBlockPullback1 laws hq hr label
      ((fullBlockCochainEquiv laws q hq D.edgeSupport hD1 label).symm x)) e = _
  rw [fullBlock_pullback1_some M laws hq hr hD1 hE1 label _ e d he]
  exact congrFun ((fullBlockCochainEquiv laws q hq D.edgeSupport hD1 label).apply_symm_apply x) _
/-- 名付き比較の次数1は原始none辺を零へ写す。 -/
theorem namedComparisonHom_f1_none (x : D.nerve.EdgeComponent → ℚ)
    (e : E.nerve.EdgeComponent) (he : M.edgeMap e = none) :
    (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label).f1 x e = 0 := by
  exact fullBlock_pullback1_none M laws hq hr hE1 label _ e he
/-- 名付き比較の次数2は原始some面を同名座標へ写す。 -/
theorem namedComparisonHom_f2_some (x : D.nerve.FaceComponent → ℚ)
    (f : E.nerve.FaceComponent) (d : D.nerve.FaceComponent) (hf : M.faceMap f = some d) :
    (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label).f2 x f = x d := by
  change fullBlockCochainEquiv laws r hr E.faceSupport hE2 label
    (M.generatedBlockPullback2 laws hq hr label
      ((fullBlockCochainEquiv laws q hq D.faceSupport hD2 label).symm x)) f = _
  rw [fullBlock_pullback2_some M laws hq hr label hD2 hE2 _ f d hf]
  exact congrFun ((fullBlockCochainEquiv laws q hq D.faceSupport hD2 label).apply_symm_apply x) _
/-- 名付き比較の次数2は原始none面を零へ写す。 -/
theorem namedComparisonHom_f2_none (x : D.nerve.FaceComponent → ℚ)
    (f : E.nerve.FaceComponent) (hf : M.faceMap f = none) :
    (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label).f2 x f = 0 := by
  exact fullBlock_pullback2_none M laws hq hr label hE2 _ f hf
/-- 名付き比較の全成分正方形を標準零延長の可換正方形へ移す。 -/
theorem namedComparison_zeroExtension_square :
    zeroExtensionMap (M.generatedBlockComparisonHom laws hq hr label) ≫
      (cochainEquivZeroExtensionIso (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label)).hom =
    (cochainEquivZeroExtensionIso (fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label)).hom ≫
      zeroExtensionMap (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label) := by
  change zeroExtensionMap (M.generatedBlockComparisonHom laws hq hr label) ≫
    zeroExtensionMap (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label).toHom =
    zeroExtensionMap (fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label).toHom ≫
    zeroExtensionMap (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label)
  rw [← zeroExtensionMap_comp,← zeroExtensionMap_comp,namedComparisonHom_square]
/-- 実生成全台blockの標準錐と名付き原始比較の標準錐の同型。 -/
def fullBlockNamedConeIso :
    comparisonCone (M.generatedBlockComparisonHom laws hq hr label) ≅
      comparisonCone (namedComparisonHom M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label) :=
  coneMapIso _ _
    (cochainEquivZeroExtensionIso (fullBlockNamedEquivalence D laws hq hD0 hD1 hD2 label))
    (cochainEquivZeroExtensionIso (fullBlockNamedEquivalence E laws hr hE0 hE1 hE2 label))
    (namedComparison_zeroExtension_square M laws hq hr hD0 hD1 hD2 hE0 hE1 hE2 label)

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
