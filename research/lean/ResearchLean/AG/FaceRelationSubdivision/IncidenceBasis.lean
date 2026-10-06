import ResearchLean.AG.FaceRelationSubdivision.ChainDualMap
import ResearchLean.AG.AtlasDefectComposition.SubsetComparisonIdentity
import Formal.Util.AssertStandardAxioms

/-!
# 同じreadingの原始比較を支持基底射へ

## Implementation notes

既存primitive chart/Option表を直接基底像へ送る。実cochain射を双対化して
chain射を定義する案は生成順を逆転させるため採らない。
台包含はprimitive比較から導出済みの支持輸送と、同じreadingの因子恒等を使う。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source} {Nc Nf : TargetSupportedNerve q}
namespace IncidenceSupportedComparison
variable (M : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) Nc Nf)

/-- chartのprimitive像を同じreadingの支持基底射へ送る。 -/
def basis0 : SupportedBasisMap Nf.chartSupport Nc.chartSupport :=
  SupportedBasisMap.ofSingle M.chartMap (by
    intro i t ht
    simpa only [AtlasDefectComposition.comparisonFactor_self, id_eq] using
      M.chartSupport_compatible i t ht)

/-- 辺のprimitive Option像を支持基底射へ送る。 -/
def basis1 : SupportedBasisMap Nf.edgeSupport Nc.edgeSupport :=
  SupportedBasisMap.ofOption M.edgeMap (by
    intro i j hij t ht
    simpa only [AtlasDefectComposition.comparisonFactor_self, id_eq] using
      M.edgeSupport_compatible hij ht)

/-- 面のprimitive Option像を支持基底射へ送る。 -/
def basis2 : SupportedBasisMap Nf.faceSupport Nc.faceSupport :=
  SupportedBasisMap.ofOption M.faceMap (by
    intro i j hij t ht
    simpa only [AtlasDefectComposition.comparisonFactor_self, id_eq] using
      M.faceSupport_compatible hij ht)

/-- 同じ原始chart像の基底評価。 -/
@[simp] theorem basis0_image (i : Nf.nerve.Chart) :
    M.basis0.basisImage i = Finsupp.single (M.chartMap i) 1 := rfl

/-- 同じ原始辺像の基底評価。 -/
@[simp] theorem basis1_image (i : Nf.nerve.EdgeComponent) :
    M.basis1.basisImage i = rationalOptionCell (M.edgeMap i) := rfl

/-- 同じ原始面像の基底評価。 -/
@[simp] theorem basis2_image (i : Nf.nerve.FaceComponent) :
    M.basis2.basisImage i = rationalOptionCell (M.faceMap i) := rfl


/-- 同じreadingでのAへのmaps-toを因子恒等から生成する。 -/
def selfSubsetMapsTo (A : Set q.Target) :
    ∀ t, t ∈ A → comparisonFactor q q (Reading.coarserThan_refl q) t ∈ A := by
  intro t ht
  simpa only [AtlasDefectComposition.comparisonFactor_self, id_eq] using ht

/-- 原始頂点有限和を選択した射は、既存生成chain比較と同じ。 -/
theorem selected_basis0_eq (A : Set q.Target) :
    M.basis0.selected A = M.supportedChainMap0 A A (selfSubsetMapsTo A) := by
  apply Finsupp.lhom_ext
  intro v a
  rw [SupportedBasisMap.selected_single, basis0_image, supportedChainMap0_single]
  congr 1
  exact subtypeDomain_single_selected Nc.chartSupport A
    (M.targetSubsetChartMap A A (selfSubsetMapsTo A) v) 1

/-- 原始辺有限和を選択した射は、既存生成chain比較と同じ。 -/
theorem selected_basis1_eq (A : Set q.Target) :
    M.basis1.selected A = M.supportedChainMap1 A A (selfSubsetMapsTo A) := by
  apply Finsupp.lhom_ext
  intro v a
  rw [SupportedBasisMap.selected_single, basis1_image, supportedChainMap1_single]
  cases h : M.edgeMap v.1 with
  | none =>
    rw [rationalOptionCell_none, Finsupp.subtypeDomain_zero,
      M.targetSubsetEdgeMapOption_eq_none A A (selfSubsetMapsTo A) v h, rationalOptionCell_none]
  | some j =>
    rw [rationalOptionCell_some,
      M.targetSubsetEdgeMapOption_eq_some A A (selfSubsetMapsTo A) v j h, rationalOptionCell_some]
    congr 1
    exact subtypeDomain_single_selected Nc.edgeSupport A
      (M.targetSubsetEdgeMap A A (selfSubsetMapsTo A) v j h) 1

/-- 原始面有限和を選択した射は、既存生成chain比較と同じ。 -/
theorem selected_basis2_eq (A : Set q.Target) :
    M.basis2.selected A = M.supportedChainMap2 A A (selfSubsetMapsTo A) := by
  apply Finsupp.lhom_ext
  intro v a
  rw [SupportedBasisMap.selected_single, basis2_image, supportedChainMap2_single]
  cases h : M.faceMap v.1 with
  | none =>
    rw [rationalOptionCell_none, Finsupp.subtypeDomain_zero,
      M.targetSubsetFaceMapOption_eq_none A A (selfSubsetMapsTo A) v h, rationalOptionCell_none]
  | some j =>
    rw [rationalOptionCell_some,
      M.targetSubsetFaceMapOption_eq_some A A (selfSubsetMapsTo A) v j h, rationalOptionCell_some]
    congr 1
    exact subtypeDomain_single_selected Nc.faceSupport A
      (M.targetSubsetFaceMap A A (selfSubsetMapsTo A) v j h) 1

/-- 原始基底射を双対化した同じ実Hom。chain可換式を旧生成chainと照合して導く。 -/
def basisHom (A : Set q.Target) :=
  dualSubsetHom A A (M.basis0.selected A) (M.basis1.selected A) (M.basis2.selected A)
    (by
      rw [M.selected_basis0_eq, M.selected_basis1_eq]
      apply LinearMap.ext
      intro x
      exact (M.supportedChainMap_comm1 A A (selfSubsetMapsTo A) x).symm)
    (by
      rw [M.selected_basis1_eq, M.selected_basis2_eq]
      apply LinearMap.ext
      intro x
      exact (M.supportedChainMap_comm2 A A (selfSubsetMapsTo A) x).symm)

/-- 原始有限和の双対Homは、独立生成した同じ実subset Homに全次数で一致する。 -/
theorem basisHom_eq_generated (A : Set q.Target) :
    M.basisHom A = M.targetSubsetComparisonHom A A (selfSubsetMapsTo A) := by
  apply AtlasDefectComposition.cochain_ext
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (M.basis0.selected A) z) x =
      freeDualEquiv _ (M.targetSubsetPullback0 A A (selfSubsetMapsTo A) z) x
    rw [dualCellMap_dual, M.selected_basis0_eq, M.supportedChainMap0_dual]
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (M.basis1.selected A) z) x =
      freeDualEquiv _ (M.targetSubsetPullback1 A A (selfSubsetMapsTo A) z) x
    rw [dualCellMap_dual, M.selected_basis1_eq, M.supportedChainMap1_dual]
  · apply LinearMap.ext
    intro z
    apply (freeDualEquiv _).injective
    apply LinearMap.ext
    intro x
    change freeDualEquiv _ (dualCellMap (M.basis2.selected A) z) x =
      freeDualEquiv _ (M.targetSubsetPullback2 A A (selfSubsetMapsTo A) z) x
    rw [dualCellMap_dual, M.selected_basis2_eq, M.supportedChainMap2_dual]

end IncidenceSupportedComparison
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
