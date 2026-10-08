import ResearchLean.AG.AtlasDefectComposition.ZeroExtension
import Formal.Util.AssertStandardAxioms
/-! # 三項複体の端homologyとの同定

標準零延長のH⁰を元のd⁰の核、H²を元のd¹の像の商に同定する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open TwoPhase
universe w
/-- 三項の次数0端を明示零加群から始まる短複体へ置く。 -/
def oldZeroShort (C : ThreeCochainComplex.{0,w} ℚ) : ShortComplex (ModuleCat.{w} ℚ) :=
  ShortComplex.moduleCatMk (0 : PUnit.{w+1} →ₗ[ℚ] C.C0) C.d0 (by simp)
/-- 三項の次数2端を明示零加群へ終わる短複体へ置く。 -/
def oldTwoShort (C : ThreeCochainComplex.{0,w} ℚ) : ShortComplex (ModuleCat.{w} ℚ) :=
  ShortComplex.moduleCatMk C.d1 (0 : C.C2 →ₗ[ℚ] PUnit.{w+1}) (by simp)
/-- 零延長の次数0短複体を元の端短複体へ同定する。 -/
def zeroExtensionZeroScIso (C : ThreeCochainComplex.{0,w} ℚ) :
    (zeroExtension C).sc (0 : ℤ) ≅ oldZeroShort C :=
  (zeroExtension C).isoSc' (i := -1) (j := 0) (k := 1) (by simp) (by simp) ≪≫
    eqToIso (by rfl)
/-- 零延長の次数2短複体を元の端短複体へ同定する。 -/
def zeroExtensionTwoScIso (C : ThreeCochainComplex.{0,w} ℚ) :
    (zeroExtension C).sc (2 : ℤ) ≅ oldTwoShort C :=
  (zeroExtension C).isoSc' (i := 1) (j := 2) (k := 3) (by simp) (by simp) ≪≫
    eqToIso (by rfl)
/-- 元のd⁰の核から標準H⁰への両方向同型。 -/
def oldH0Iso (C : ThreeCochainComplex.{0,w} ℚ) :
    ModuleCat.of ℚ (LinearMap.ker C.d0) ≅ (zeroExtension C).homology (0 : ℤ) :=
  (oldZeroShort C).moduleCatCyclesIso.symm ≪≫
    (oldZeroShort C).asIsoHomologyπ (by rfl) ≪≫
    (ShortComplex.homologyMapIso (zeroExtensionZeroScIso C)).symm

/-- 元H⁰の同型と短複体比較を合成した所有公開API。 -/
theorem oldH0Iso_hom_comp (C : ThreeCochainComplex.{0,w} ℚ) :
    (oldH0Iso C).hom ≫ (ShortComplex.homologyMapIso (zeroExtensionZeroScIso C)).hom =
      (oldZeroShort C).moduleCatCyclesIso.inv ≫
        ((oldZeroShort C).asIsoHomologyπ (by rfl)).hom := by
  simp only [oldH0Iso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
/-- 元の終端商から標準H²への両方向同型。 -/
def oldH2Iso (C : ThreeCochainComplex.{0,w} ℚ) :
    ModuleCat.of ℚ (C.C2 ⧸ LinearMap.range C.d1) ≅ (zeroExtension C).homology (2 : ℤ) :=
  (oldTwoShort C).moduleCatOpcyclesIso.symm ≪≫
    ((oldTwoShort C).asIsoHomologyι (by rfl)).symm ≪≫
    (ShortComplex.homologyMapIso (zeroExtensionTwoScIso C)).symm

/-- 元H²の同型と短複体比較を合成した値を返す所有公開API。 -/
theorem oldH2Iso_hom_comp (C : ThreeCochainComplex.{0,w} ℚ) :
    (oldH2Iso C).hom ≫ (ShortComplex.homologyMapIso (zeroExtensionTwoScIso C)).hom =
      (oldTwoShort C).moduleCatOpcyclesIso.inv ≫
        ((oldTwoShort C).asIsoHomologyι (by rfl)).inv := by
  simp only [oldH2Iso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
/-- 元のd⁰核を標準H⁰へ移す線形同型。 -/
def oldH0Equiv (C : ThreeCochainComplex.{0,w} ℚ) := (oldH0Iso C).toLinearEquiv
/-- 元のd¹像の商を標準H²へ移す線形同型。 -/
def oldH2Equiv (C : ThreeCochainComplex.{0,w} ℚ) := (oldH2Iso C).toLinearEquiv
end AAT.AG.AtlasDefectComposition

#print axioms AAT.AG.AtlasDefectComposition.oldZeroShort
#print axioms AAT.AG.AtlasDefectComposition.oldTwoShort
#print axioms AAT.AG.AtlasDefectComposition.zeroExtensionZeroScIso
#print axioms AAT.AG.AtlasDefectComposition.zeroExtensionTwoScIso
#print axioms AAT.AG.AtlasDefectComposition.oldH0Iso
#print axioms AAT.AG.AtlasDefectComposition.oldH0Iso_hom_comp
#print axioms AAT.AG.AtlasDefectComposition.oldH2Iso
#print axioms AAT.AG.AtlasDefectComposition.oldH2Iso_hom_comp
#print axioms AAT.AG.AtlasDefectComposition.oldH0Equiv
#print axioms AAT.AG.AtlasDefectComposition.oldH2Equiv
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
