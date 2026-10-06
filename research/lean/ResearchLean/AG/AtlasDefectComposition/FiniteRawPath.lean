import ResearchLean.AG.AtlasDefectComposition.RawComparisonCategory
import ResearchLean.AG.AtlasDefectComposition.LawStandardDecomposition
import ResearchLean.AG.AtlasDefectComposition.SupportStageSixTerm
import Formal.Util.AssertStandardAxioms
/-! # 有限原始 path と全Lawの独立生成 diagram

Implementation notes: 入力は同じ Source の各 reading/nerve と隣接原始比較である。
任意の有限段数と零段を含み、直接比較も原始圏で生成する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {n : ℕ}
/-- 全有限段の隣接原始比較から作る path。 -/
def rawPath (X : Fin (n+1) → RawResolution Source)
    (adj : ∀ i : Fin n, X i.castSucc ⟶ X i.succ) :
    Fin (n+1) ⥤ RawResolution Source := ComposableArrows.mkOfObjOfMapSucc X adj
/-- path の各対象は入力 reading と nerve そのものである。 -/
@[simp] theorem rawPath_obj (X : Fin (n+1) → RawResolution Source)
    (adj : ∀ i : Fin n, X i.castSucc ⟶ X i.succ) (i : Fin (n+1)) :
    (rawPath X adj).obj i = X i := rfl
/-- path の各隣接射は入力の全原始セル射である。 -/
theorem rawPath_adjacent (X : Fin (n+1) → RawResolution Source)
    (adj : ∀ i : Fin n, X i.castSucc ⟶ X i.succ) (i : Fin n) :
    (rawPath X adj).map (homOfLE (show i.castSucc ≤ i.succ from Fin.le_def.mpr (Nat.le_succ i.val))) = adj i :=
  ComposableArrows.mkOfObjOfMapSucc_map_succ X adj i i.isLt
variable (P : Fin (n+1) ⥤ RawResolution Source)
/-- 同じ最初の reading から各段への粗細順序は原始 path から得る。 -/
theorem pathCoarser (i : Fin (n+1)) : (P.obj 0).reading.CoarserThan (P.obj i).reading :=
  (P.map (homOfLE (Fin.zero_le i))).1
variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate (P.obj 0).reading)
omit [Fintype Source] in
include ha in
/-- 全段の Law adequacy は最初の同じ Law 入力から導く。 -/
theorem pathAdequate (i : Fin (n+1)) : laws.Adequate (P.obj i).reading :=
  adequate_of_coarser laws (pathCoarser P i) ha
/-- 各対の全Law複体を独立に生成する diagram。 -/
def lawPathDiagram : Fin (n+1) ⥤ CochainComplex (ModuleCat.{u} ℚ) ℤ where
  obj i := zeroExtension ((P.obj i).nerve.lawGeneratedComplex laws (pathAdequate P laws ha i))
  map {i j} f := zeroExtensionMap ((P.map f).2.generatedComparisonHom laws
    (pathAdequate P laws ha i) (pathAdequate P laws ha j))
  map_id i := by
    rw [P.map_id]
    change zeroExtensionMap ((TargetSupportedNerveMorphism.identityMorphism
      (P.obj i).reading (P.obj i).nerve).generatedComparisonHom laws
      (pathAdequate P laws ha i) (pathAdequate P laws ha i)) = _
    rw [identity_generatedComparisonHom,zeroExtensionMap_id]
  map_comp {i j k} f g := by
    rw [P.map_comp]
    dsimp only [CategoryStruct.comp,rawResolutionCategory,RawResolution.compose,PSigma.snd]
    rw [generatedComparisonHom_comp (P.map f).2 (P.map g).2 laws
      (pathAdequate P laws ha i) (pathAdequate P laws ha j) (pathAdequate P laws ha k),
      zeroExtensionMap_comp]
    rfl
/-- 全Law図式の対象は同じ段の実独立生成複体である。 -/
@[simp] theorem lawPathDiagram_obj (i : Fin (n+1)) :
    (lawPathDiagram P laws ha).obj i =
      zeroExtension ((P.obj i).nerve.lawGeneratedComplex laws (pathAdequate P laws ha i)) := rfl
/-- 全Law図式の全対射は原始比較から独立に生成した射である。 -/
@[simp] theorem lawPathDiagram_map {i j : Fin (n+1)} (f : i ⟶ j) :
    (lawPathDiagram P laws ha).map f = zeroExtensionMap ((P.map f).2.generatedComparisonHom
      laws (pathAdequate P laws ha i) (pathAdequate P laws ha j)) := rfl
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
