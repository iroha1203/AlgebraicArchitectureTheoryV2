import ResearchLean.AG.AtlasDefectComposition.FiniteRawPath
import ResearchLean.AG.AtlasDefectComposition.SubsetComparisonIdentity
import ResearchLean.AG.AtlasDefectComposition.FiniteConeFiltration
import Formal.Util.AssertStandardAxioms
/-! # 全有限段の同じ q₀ 部分集合からの実生成 diagram

Implementation notes: 全段署名と元のセル比較を使い、各対の Hom を独立に生成する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {n : ℕ} (P : Fin (n+1) ⥤ RawResolution Source)
/-- 全段署名に使う元の reading 族。 -/
def pathReadings (i : Fin (n+1)) := (P.obj i).reading
/-- 全段署名に使う元の nerve 族。 -/
def pathNerves (i : Fin (n+1)) := (P.obj i).nerve
/-- 全段共通の基底 subset における実部分集合比較。 -/
def subsetPathDiagram (A : Set (P.obj 0).reading.Target) :
    Fin (n+1) ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ where
  obj i := zeroExtension (SupportStages.stageComplex (pathReadings P) (pathNerves P) (pathCoarser P) A i)
  map {i j} f := zeroExtensionMap (SupportStages.pairComparison
    (pathReadings P) (pathNerves P) (pathCoarser P) i j (P.map f).1 (P.map f).2 A)
  map_id i := by
    rw [P.map_id]
    change zeroExtensionMap ((TargetSupportedNerveMorphism.identityMorphism
      (P.obj i).reading (P.obj i).nerve).targetSubsetComparisonHom _ _ _) = _
    rw [identity_targetSubsetComparisonHom,zeroExtensionMap_id]
    rfl
  map_comp {i j k} f g := by
    rw [P.map_comp]
    change zeroExtensionMap (SupportStages.pairComparison (pathReadings P) (pathNerves P)
      (pathCoarser P) i k (Reading.coarserThan_trans (P.map f).1 (P.map g).1)
      (comparisonComp (P.map f).2 (P.map g).2) A) = _
    rw [SupportStages.pairComparison_comp (pathReadings P) (pathNerves P) (pathCoarser P)
      i j k (P.map f).1 (P.map g).1 (P.map f).2 (P.map g).2 A,zeroExtensionMap_comp]
/-- 全有限段の対象の公開式。元の名付きセルと canonical 逆像を保持する。 -/
@[simp] theorem subsetPathDiagram_obj (A : Set (P.obj 0).reading.Target) (i : Fin (n+1)) :
    (subsetPathDiagram P A).obj i = zeroExtension ((P.obj i).nerve.targetSubsetComplex
      (comparisonFactor (P.obj 0).reading (P.obj i).reading (pathCoarser P i) ⁻¹' A)) := rfl
/-- 全有限対射の公開式。元の独立生成部分集合比較を読む。 -/
@[simp] theorem subsetPathDiagram_map (A : Set (P.obj 0).reading.Target)
    {i j : Fin (n+1)} (f : i ⟶ j) :
    (subsetPathDiagram P A).map f = zeroExtensionMap (SupportStages.pairComparison
      (pathReadings P) (pathNerves P) (pathCoarser P) i j (P.map f).1 (P.map f).2 A) := rfl
/-- 初段の逆像は同じ基底 subset そのものである。 -/
theorem path_initial_preimage (A : Set (P.obj 0).reading.Target) :
    comparisonFactor (P.obj 0).reading (P.obj 0).reading (pathCoarser P 0) ⁻¹' A = A := by
  rw [comparisonFactor_self]
  rfl
/-- 初段の実複体を元の q₀ subset 複体へ戻す指定同型。 -/
def subsetPathInitialIso (A : Set (P.obj 0).reading.Target) :
    (subsetPathDiagram P A).obj 0 ≅ zeroExtension ((P.obj 0).nerve.targetSubsetComplex A) :=
  eqToIso (congrArg (fun S => zeroExtension ((P.obj 0).nerve.targetSubsetComplex S))
    (path_initial_preimage P A))
/-- 全段共通署名の包含から同じ原始入力の実自然変換を生成する。 -/
def subsetPathRestriction {A B : Set (P.obj 0).reading.Target}
    (hAB : SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) A ⊆
      SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) B) :
    subsetPathDiagram P B ⟶ subsetPathDiagram P A where
  app i := zeroExtensionMap (SupportStages.stageRestriction
    (pathReadings P) (pathNerves P) (pathCoarser P) hAB i)
  naturality {i j} f := by
    have hh := congrArg zeroExtensionMap (SupportStages.pairComparison_square
      (pathReadings P) (pathNerves P) (pathCoarser P) i j (P.map f).1 (P.map f).2 hAB)
    simpa only [zeroExtensionMap_comp] using hh
/-- 共通台の制限の各成分は同じ原始セル制限の零延長である。 -/
@[simp] theorem subsetPathRestriction_app {A B : Set (P.obj 0).reading.Target}
    (hAB : SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) A ⊆
      SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) B) (i : Fin (n+1)) :
    (subsetPathRestriction P hAB).app i = zeroExtensionMap
      (SupportStages.stageRestriction (pathReadings P) (pathNerves P) (pathCoarser P) hAB i) := rfl
/-- 同じ全段台の反射的制限は実図式の恒等射である。 -/
theorem subsetPathRestriction_id (A : Set (P.obj 0).reading.Target) :
    subsetPathRestriction P (Set.Subset.refl _) = 𝟙 (subsetPathDiagram P A) := by
  apply NatTrans.ext
  funext i
  rw [subsetPathRestriction_app,SupportStages.stageRestriction_id]
  exact zeroExtensionMap_id _
/-- 全段台の推移的制限は元の実図式制限の合成である。 -/
theorem subsetPathRestriction_comp {A B D : Set (P.obj 0).reading.Target}
    (hAB : SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) A ⊆
      SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) B)
    (hBD : SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) B ⊆
      SupportStages.alpha (pathReadings P) (pathNerves P) (pathCoarser P) D) :
    subsetPathRestriction P (hAB.trans hBD) = subsetPathRestriction P hBD ≫ subsetPathRestriction P hAB := by
  apply NatTrans.ext
  funext i
  rw [subsetPathRestriction_app,SupportStages.stageRestriction_comp,zeroExtensionMap_comp]
  rfl
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
