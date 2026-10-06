import ResearchLean.AG.FaceRelationSubdivision.SubdivisionReconstruction
import ResearchLean.AG.FaceRelationSubdivision.ContractionTransport
import ResearchLean.AG.FaceRelationSubdivision.SubsetComposition
import Formal.Util.AssertStandardAxioms

/-!
# 原始辺分割逆patternの同じ支持収縮

## Implementation notes

旧入力・表示同型・収縮を受け取らず、全接続を持つ原始patternから順に生成する。
任意Aでrは正操作のrと逆表示、sは正操作のsと順表示、hは同じhの表示共役。
実subset複体の同じ双対射を標準零延長・既存H1商へ渡す。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace SubdivisionInversePattern
variable {N : TargetSupportedNerve.{u, u} q} (P : SubdivisionInversePattern N)

/-- 原始patternの復元入力・正操作・表示から、元入力上の同じr/s/hを生成する。 -/
def chainContraction (A : Set q.Target) : SubsetChainContraction P.restored N A A :=
  (EdgeSubdivision.chainContraction P.restored P.commonEdge A).renameFine
    (P.presentation.sameR0 A) (P.presentation.sameR1 A) (P.presentation.sameR2 A)
    (P.presentation.sameR_comm01 A) (P.presentation.sameR_comm12 A)

/-- r0の計算式は正操作のrと復元表示の逆との合成。 -/
@[simp] theorem chainContraction_r0 (A : Set q.Target) : (P.chainContraction A).r0 =
    ((EdgeSubdivision.r0 P.restored P.commonEdge).selected A).comp
      (P.presentation.sameR0 A).symm.toLinearMap := rfl
/-- r1の同じ原始計算式。 -/
@[simp] theorem chainContraction_r1 (A : Set q.Target) : (P.chainContraction A).r1 =
    ((EdgeSubdivision.r1 P.restored P.commonEdge).selected A).comp
      (P.presentation.sameR1 A).symm.toLinearMap := rfl
/-- r2の同じ原始計算式。 -/
@[simp] theorem chainContraction_r2 (A : Set q.Target) : (P.chainContraction A).r2 =
    ((EdgeSubdivision.r2 P.restored P.commonEdge).selected A).comp
      (P.presentation.sameR2 A).symm.toLinearMap := rfl
/-- s0の計算式は旧sectionと順表示。 -/
@[simp] theorem chainContraction_s0 (A : Set q.Target) : (P.chainContraction A).s0 =
    (P.presentation.sameR0 A).toLinearMap.comp
      ((EdgeSubdivision.s0 P.restored P.commonEdge).selected A) := rfl
/-- s1の同じ旧sectionの計算式。 -/
@[simp] theorem chainContraction_s1 (A : Set q.Target) : (P.chainContraction A).s1 =
    (P.presentation.sameR1 A).toLinearMap.comp
      ((EdgeSubdivision.s1 P.restored P.commonEdge).selected A) := rfl
/-- s2の同じ旧sectionの計算式。 -/
@[simp] theorem chainContraction_s2 (A : Set q.Target) : (P.chainContraction A).s2 =
    (P.presentation.sameR2 A).toLinearMap.comp
      ((EdgeSubdivision.s2 P.restored P.commonEdge).selected A) := rfl
/-- h0は同じconnectorの基底式を表示の両方向で共役したもの。 -/
@[simp] theorem chainContraction_h0 (A : Set q.Target) : (P.chainContraction A).h0 =
    (P.presentation.sameR1 A).toLinearMap.comp
      (((EdgeSubdivision.h0 P.restored P.commonEdge).selected A).comp
        (P.presentation.sameR0 A).symm.toLinearMap) := rfl
/-- h1は同じ各出現の追加面の基底式の表示共役。 -/
@[simp] theorem chainContraction_h1 (A : Set q.Target) : (P.chainContraction A).h1 =
    (P.presentation.sameR2 A).toLinearMap.comp
      (((EdgeSubdivision.h1 P.restored P.commonEdge).selected A).comp
        (P.presentation.sameR1 A).symm.toLinearMap) := rfl

/-- 同じrの実subset cochain比較。 -/
def rHom (A : Set q.Target) := (P.chainContraction A).rHom
/-- 同じsの実subset cochain比較。逆操作ではrとこの射を逆向きに使う。 -/
def sHom (A : Set q.Target) := (P.chainContraction A).sHom
/-- 原始逆patternの同じsection次数0双対射。 -/
@[simp] theorem sHom_f0 (A : Set q.Target) :
    (P.sHom A).f0 = dualCellMap (P.chainContraction A).s0 := rfl
/-- 原始逆patternの同じsection次数1双対射。 -/
@[simp] theorem sHom_f1 (A : Set q.Target) :
    (P.sHom A).f1 = dualCellMap (P.chainContraction A).s1 := rfl
/-- 原始逆patternの同じsection次数2双対射。 -/
@[simp] theorem sHom_f2 (A : Set q.Target) :
    (P.sHom A).f2 = dualCellMap (P.chainContraction A).s2 := rfl

/-- 原始収縮・同じ実双対射の標準ホモトピー同値。 -/
def cochainHomotopyEquiv (A : Set q.Target) := (P.chainContraction A).cochainHomotopyEquiv
/-- 同値の順方向は同じ実rHomの標準零延長。 -/
@[simp] theorem cochainHomotopyEquiv_hom (A : Set q.Target) :
    (P.cochainHomotopyEquiv A).hom = zeroExtensionMap (P.rHom A) := rfl
/-- 同値の逆方向は同じ実sHomの標準零延長。 -/
@[simp] theorem cochainHomotopyEquiv_inv (A : Set q.Target) :
    (P.cochainHomotopyEquiv A).inv = zeroExtensionMap (P.sHom A) := rfl
/-- 全標準次数の同型を同じ原始二射から生成する。 -/
def homologyIso (A : Set q.Target) (n : ℤ) := (P.chainContraction A).homologyIso n
/-- 同型の実順射は同じ生成cochain比較。 -/
@[simp] theorem homologyIso_hom (A : Set q.Target) (n : ℤ) :
    (P.homologyIso A n).hom = HomologicalComplex.homologyMap (zeroExtensionMap (P.rHom A)) n := rfl
/-- 同じ標準次数1同型の既存H1商への読み戻し。 -/
def oldH1ComparisonIso (A : Set q.Target) := (P.chainContraction A).oldH1ComparisonIso
/-- 既存H1商の実写像も同じrHomのh1Map。 -/
theorem oldH1ComparisonIso_hom (A : Set q.Target) :
    (P.oldH1ComparisonIso A).hom = ModuleCat.ofHom (P.rHom A).h1Map :=
  (P.chainContraction A).oldH1ComparisonIso_hom

/-- 復元正操作の原始collapseと逆表示のOption表を直接合成した新比較。 -/
def collapse : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) P.restored N :=
  IncidenceSupportedComparison.comp (EdgeSubdivision.collapse P.restored P.commonEdge)
    P.presentation.symmSelf.comparison

/-- 同じ原始逆patternのcollapse Option表の直接合成式。 -/
@[simp] theorem collapse_eq : P.collapse =
    IncidenceSupportedComparison.comp (EdgeSubdivision.collapse P.restored P.commonEdge)
      P.presentation.symmSelf.comparison := rfl

/-- 実収縮Homは、原始Option表から独立生成した新比較の同じ三次数射である。 -/
theorem rHom_eq_generated (A : Set q.Target) : P.rHom A =
    P.collapse.targetSubsetComparisonHom A A (IncidenceSupportedComparison.selfSubsetMapsTo A) := by
  have hrename := SubsetChainContraction.renameFine_rHom
    (EdgeSubdivision.chainContraction P.restored P.commonEdge A)
    (P.presentation.sameR0 A) (P.presentation.sameR1 A) (P.presentation.sameR2 A)
    (P.presentation.sameR_comm01 A) (P.presentation.sameR_comm12 A)
  change P.rHom A = _ at hrename
  rw [hrename, P.presentation.inverseDual_eq_symmSelf]
  change cochainComp (EdgeSubdivision.chainContraction P.restored P.commonEdge A).rHom
    (P.presentation.symmSelf.sameHom A) = _
  rw [EdgeSubdivision.chainContraction_rHom, EdgeSubdivision.rHom_eq_generated,
    P.presentation.symmSelf.sameHom_eq_generated]
  exact (targetSubsetComparisonHom_comp
    (EdgeSubdivision.collapse P.restored P.commonEdge) P.presentation.symmSelf.comparison
    A A A (IncidenceSupportedComparison.selfSubsetMapsTo A)
    (IncidenceSupportedComparison.selfSubsetMapsTo A)).symm

/-- 全標準次数同型の実順射も同じ新比較から生成する。 -/
theorem homologyIso_hom_generated (A : Set q.Target) (n : ℤ) :
    (P.homologyIso A n).hom = HomologicalComplex.homologyMap
      (zeroExtensionMap (P.collapse.targetSubsetComparisonHom A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A))) n := by
  rw [P.homologyIso_hom, P.rHom_eq_generated]

/-- 既存H1商の実写像は同じ新比較の生成h1Mapである。 -/
theorem oldH1ComparisonIso_hom_generated (A : Set q.Target) :
    (P.oldH1ComparisonIso A).hom = ModuleCat.ofHom
      (P.collapse.targetSubsetComparisonHom A A
        (IncidenceSupportedComparison.selfSubsetMapsTo A)).h1Map := by
  rw [P.oldH1ComparisonIso_hom, P.rHom_eq_generated]

/-- 逆操作の方向では、同じ構成済み二射と二homotopyを交換する。 -/
def inverseCochainHomotopyEquiv (A : Set q.Target) := (P.cochainHomotopyEquiv A).symm
/-- 逆操作の実順射は同じsHom。 -/
@[simp] theorem inverseCochainHomotopyEquiv_hom (A : Set q.Target) :
    (P.inverseCochainHomotopyEquiv A).hom = zeroExtensionMap (P.sHom A) := rfl
/-- 逆操作の実逆射は同じrHom。 -/
@[simp] theorem inverseCochainHomotopyEquiv_inv (A : Set q.Target) :
    (P.inverseCochainHomotopyEquiv A).inv = zeroExtensionMap (P.rHom A) := rfl
/-- 逆縮約方向の全標準次数同型。 -/
def inverseHomologyIso (A : Set q.Target) (n : ℤ) :=
  (P.inverseCochainHomotopyEquiv A).toHomologyIso n
/-- 逆縮約方向の全標準次数実写像も同じsHom。 -/
@[simp] theorem inverseHomologyIso_hom (A : Set q.Target) (n : ℤ) :
    (P.inverseHomologyIso A n).hom = HomologicalComplex.homologyMap
      (zeroExtensionMap (P.sHom A)) n := rfl
/-- 逆縮約方向を既存H1商へ読み戻す同型。 -/
def inverseOldH1ComparisonIso (A : Set q.Target) :=
  oldH1Iso (N.targetSubsetComplex A) ≪≫ P.inverseHomologyIso A 1 ≪≫
    (oldH1Iso (P.restored.targetSubsetComplex A)).symm
/-- 逆方向の既存H1商写像も同じsHomのh1Mapである。 -/
theorem inverseOldH1ComparisonIso_hom (A : Set q.Target) :
    (P.inverseOldH1ComparisonIso A).hom = ModuleCat.ofHom (P.sHom A).h1Map := by
  change ((oldH1Iso (N.targetSubsetComplex A)).hom ≫
    HomologicalComplex.homologyMap (zeroExtensionMap (P.sHom A)) 1) ≫
      (oldH1Iso (P.restored.targetSubsetComplex A)).inv = _
  rw [oldH1Iso_natural]
  simp only [CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id,
    CategoryTheory.Category.comp_id]

end SubdivisionInversePattern
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
