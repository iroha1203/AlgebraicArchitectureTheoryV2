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
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
