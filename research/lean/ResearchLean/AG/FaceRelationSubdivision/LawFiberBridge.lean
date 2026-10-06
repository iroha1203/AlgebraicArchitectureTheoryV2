import ResearchLean.AG.AtlasDefectComposition.CochainEquivalence
import ResearchLean.AG.AtlasDefectComposition.ConeEquivalence
import ResearchLean.AG.FaceRelationSubdivision.SubsetComposition
import ResearchLean.AG.AtlasDefectComposition.LawFiberDecomposition
import Formal.Util.AssertStandardAxioms
/-! # 実Law blockと同じ原始部分集合比較への接続

Implementation notes: 対象の同定はG-133の既存同型を使い、新比較クラスの実射に対して三次数の可換式を証明する。旧hereditary比較を入力にする案は採らず、混在比較から生成した同じblock/fiber Homを接続する。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : IncidenceSupportedComparison q r h N E) (hr : laws.Adequate r)
variable (l : LawValueLabel laws)
/-- 全三成分で、実block比較と実fiber比較が同じ可換図式に入る。 -/
theorem lawBlockFiber_comparison_square :
    cochainComp (M.generatedBlockComparisonHom laws ha hr l)
      (E.lawValueBlockTargetSubsetComplexEquiv laws hr l).toHom =
    cochainComp (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom
      (M.labelFiberComparisonHom laws ha hr l) := by
  apply cochain_ext
  · apply LinearMap.ext;exact M.labelFiberComparison_naturality0 laws ha hr l
  · apply LinearMap.ext;exact M.labelFiberComparison_naturality1 laws ha hr l
  · apply LinearMap.ext;exact M.labelFiberComparison_naturality2 laws ha hr l
/-- ラベルblock零延長の同型は全次数で実fiber比較と可換である。 -/
theorem lawBlockFiberZeroExtensionIso_natural :
    zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l) ≫
      (lawBlockFiberZeroExtensionIso E laws hr l).hom =
    (lawBlockFiberZeroExtensionIso N laws ha l).hom ≫
      zeroExtensionMap (M.labelFiberComparisonHom laws ha hr l) := by
  have hs := congrArg zeroExtensionMap (lawBlockFiber_comparison_square N E laws ha M hr l)
  rw [zeroExtensionMap_comp,zeroExtensionMap_comp] at hs
  exact hs
/-- 実block比較錐は同じラベルfiber比較の標準錐である。 -/
def lawBlockFiberConeIso : mappingCone (zeroExtensionMap
    (M.generatedBlockComparisonHom laws ha hr l)) ≅
    mappingCone (zeroExtensionMap (M.labelFiberComparisonHom laws ha hr l)) :=
  coneMapIso _ _ (lawBlockFiberZeroExtensionIso N laws ha l)
    (lawBlockFiberZeroExtensionIso E laws hr l)
      (lawBlockFiberZeroExtensionIso_natural N E laws ha M hr l)
/-- 細fiberをcanonical逆像へ移すと、全三成分で独立生成aSubnerve比較になる。 -/
theorem lawFiberComparison_canonical :
    subsetTransportHom (congrArg E.targetSubsetComplex
      (labelValueFiber_eq_preimage laws q r ha hr h l))
      (M.labelFiberComparisonHom laws ha hr l) =
        M.aSubnerveComparisonHom (labelValueFiber laws q ha l) :=
  targetSubsetComparisonHom_transport M _ _ _
    (labelValueFiber_eq_preimage laws q r ha hr h l)
    (labelValueFiber_mapsTo laws q r ha hr h l) (fun _ ht => ht)
omit [Fintype Source] in
/-- 同じ原始subset比較の両側等号を零延長の実正方形へ移す。 -/
theorem subsetComparisonZeroExtension_square (A A' : Set q.Target) (B B' : Set r.Target)
    (hA : A = A') (hB : B = B')
    (hs : ∀ t, t ∈ B → comparisonFactor q r h t ∈ A)
    (hs' : ∀ t, t ∈ B' → comparisonFactor q r h t ∈ A') :
    zeroExtensionMap (M.targetSubsetComparisonHom A B hs) ≫
        (eqToIso (congrArg (fun B => zeroExtension (E.targetSubsetComplex B)) hB)).hom =
      (eqToIso (congrArg (fun A => zeroExtension (N.targetSubsetComplex A)) hA)).hom ≫
        zeroExtensionMap (M.targetSubsetComparisonHom A' B' hs') := by
  cases hA
  cases hB
  simp only [eqToIso_refl,Iso.refl_hom,Category.comp_id,Category.id_comp]
/-- 指定した同じfiber集合へ、実block零延長を全次数で同定する。 -/
def lawBlockSelectedSubsetZeroExtensionIso (A : Set q.Target)
    (hA : labelValueFiber laws q ha l = A) :
    zeroExtension (N.lawValueBlockComplex laws ha l) ≅ zeroExtension (N.targetSubsetComplex A) :=
  lawBlockFiberZeroExtensionIso N laws ha l ≪≫
    eqToIso (congrArg (fun A => zeroExtension (N.targetSubsetComplex A)) hA)
/-- 選んだ同じ両fiberへの同定は、全次数で実部分集合比較と可換である。 -/
theorem lawBlockSelectedSubsetZeroExtensionIso_natural (A : Set q.Target) (B : Set r.Target)
    (hA : labelValueFiber laws q ha l = A) (hB : labelValueFiber laws r hr l = B)
    (hs : ∀ t, t ∈ B → comparisonFactor q r h t ∈ A) :
    zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l) ≫
      (lawBlockSelectedSubsetZeroExtensionIso E laws hr l B hB).hom =
    (lawBlockSelectedSubsetZeroExtensionIso N laws ha l A hA).hom ≫
      zeroExtensionMap (M.targetSubsetComparisonHom A B hs) := by
  dsimp only [lawBlockSelectedSubsetZeroExtensionIso,Iso.trans_hom]
  rw [← Category.assoc,lawBlockFiberZeroExtensionIso_natural,Category.assoc]
  have ht := subsetComparisonZeroExtension_square N E M _ A _ B hA hB
    (labelValueFiber_mapsTo laws q r ha hr h l) hs
  change zeroExtensionMap (M.labelFiberComparisonHom laws ha hr l) ≫ _ = _ at ht
  simpa only [Category.assoc] using
    congrArg (fun f => (lawBlockFiberZeroExtensionIso N laws ha l).hom ≫ f) ht
/-- 指定した両fiber比較と実block比較の標準錐は元と微分を保つ同型を持つ。 -/
def lawBlockSelectedSubsetConeIso (A : Set q.Target) (B : Set r.Target)
    (hA : labelValueFiber laws q ha l = A) (hB : labelValueFiber laws r hr l = B)
    (hs : ∀ t, t ∈ B → comparisonFactor q r h t ∈ A) :
    mappingCone (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) ≅
      mappingCone (zeroExtensionMap (M.targetSubsetComparisonHom A B hs)) :=
  coneMapIso _ _ (lawBlockSelectedSubsetZeroExtensionIso N laws ha l A hA)
    (lawBlockSelectedSubsetZeroExtensionIso E laws hr l B hB)
      (lawBlockSelectedSubsetZeroExtensionIso_natural N E laws ha M hr l A B hA hB hs)
/-- 一ラベルの標準錐を、同じ粗fiberとそのcanonical逆像の独立生成錐へ接続する。 -/
def lawBlockCanonicalConeIso :
    mappingCone (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) ≅
      mappingCone (zeroExtensionMap (M.aSubnerveComparisonHom (labelValueFiber laws q ha l))) :=
  lawBlockSelectedSubsetConeIso N E laws ha M hr l _ _ rfl
    (labelValueFiber_eq_preimage laws q r ha hr h l) (fun _ ht => ht)
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
