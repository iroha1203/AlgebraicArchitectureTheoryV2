import ResearchLean.AG.FaceRelationSubdivision.ElementaryLawHomotopy
import ResearchLean.AG.AtlasDefectComposition.LawFiberDecomposition
import Formal.Util.AssertStandardAxioms

/-!
# 独立block有限和と同じfiberホモトピー

## Implementation notes

支持fiberで原始表から生成した標準同値を既存block座標同型で移す。
移した射と独立生成block射の等号は既存の三成分正方形から別途証明する。
対象同値だけを保存根拠とする方法を採らない。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u

/-- 同じ標準二射とホモトピーを指定した対象同型で移す一般API。 -/
def transportHomotopyEquiv
    {C D X Y : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (E : HomotopyEquiv X Y) (a : C ≅ X) (b : D ≅ Y) : HomotopyEquiv C D :=
  ((HomotopyEquiv.ofIso a).trans E).trans (HomotopyEquiv.ofIso b.symm)

/-- 移した順方向の具体的な三射合成。 -/
@[simp] theorem transportHomotopyEquiv_hom
    {C D X Y : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (E : HomotopyEquiv X Y) (a : C ≅ X) (b : D ≅ Y) :
    (transportHomotopyEquiv E a b).hom = (a.hom ≫ E.hom) ≫ b.inv := rfl

/-- 移した逆方向も同じ二射と対象同型の合成。 -/
@[simp] theorem transportHomotopyEquiv_inv
    {C D X Y : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (E : HomotopyEquiv X Y) (a : C ≅ X) (b : D ≅ Y) :
    (transportHomotopyEquiv E a b).inv = b.hom ≫ (E.inv ≫ a.inv) := rfl

/-- 指定実射の可換正方形は移した順方向をその同じ射へ同定する。 -/
theorem transportHomotopyEquiv_hom_eq
    {C D X Y : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (E : HomotopyEquiv X Y) (a : C ≅ X) (b : D ≅ Y) (f : C ⟶ D)
    (h : f ≫ b.hom = a.hom ≫ E.hom) :
    (transportHomotopyEquiv E a b).hom = f := by
  rw [transportHomotopyEquiv_hom, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 指定逆実射の正方形も移した逆方向を同じ射へ同定する。 -/
theorem transportHomotopyEquiv_inv_eq
    {C D X Y : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (E : HomotopyEquiv X Y) (a : C ≅ X) (b : D ≅ Y) (g : D ⟶ C)
    (h : g ≫ a.hom = b.hom ≫ E.inv) :
    (transportHomotopyEquiv E a b).inv = g := by
  rw [transportHomotopyEquiv_inv, ← Category.assoc, ← h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {Source : Type u} [Fintype Source] {q : Reading Source}

namespace TriangleAddition
variable (N : ResolutionInvariance.TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q) (l : LawValueLabel laws)

/-- 三角形追加の原始r有限和を独立生成した同じ実block Hom。 -/
def blockR := blockFiniteHom laws ha (r0 N e) (r1 N e) (r2 N e)
  (r_comm01 N e) (r_comm12 N e) l
/-- 三角形追加の原始s有限和を独立生成した同じ逆block Hom。 -/
def blockS := blockFiniteHom laws ha (s0 N e) (s1 N e) (s2 N e)
  (s_comm01 N e) (s_comm12 N e) l

/-- 同じblock比較は全三成分で原始fiber収縮へ接続する。 -/
theorem blockR_fiber :
    cochainComp (blockR N e laws ha l) ((supported N e).lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom =
      cochainComp (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom
        (chainContraction N e (labelValueFiber laws q ha l)).rHom := by
  have h := blockFiniteFiber_square laws ha (r0 N e) (r1 N e) (r2 N e)
    (r_comm01 N e) (r_comm12 N e) l
  rw [rSubsetFiniteHom_eq] at h
  exact h

/-- 同じ逆block有限和も全三成分で原始fiber切断へ接続する。 -/
theorem blockS_fiber :
    cochainComp (blockS N e laws ha l) (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom =
      cochainComp ((supported N e).lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom
        (chainContraction N e (labelValueFiber laws q ha l)).sHom := by
  have h := blockFiniteFiber_square laws ha (s0 N e) (s1 N e) (s2 N e)
    (s_comm01 N e) (s_comm12 N e) l
  rw [sSubsetFiniteHom_eq] at h
  exact h

/-- 任意ラベルの同じr/sを持つ標準ホモトピー同値。 -/
def blockHomotopyEquiv := transportHomotopyEquiv
  (chainContraction N e (labelValueFiber laws q ha l)).cochainHomotopyEquiv
  (lawBlockFiberZeroExtensionIso N laws ha l)
  (lawBlockFiberZeroExtensionIso (supported N e) laws ha l)

/-- 移送後の順方向は独立生成した同じ実block r。 -/
theorem blockHomotopyEquiv_hom : (blockHomotopyEquiv N e laws ha l).hom =
    zeroExtensionMap (blockR N e laws ha l) := by
  apply transportHomotopyEquiv_hom_eq
  rw [lawBlockFiberZeroExtensionIso_hom, lawBlockFiberZeroExtensionIso_hom,
    SubsetChainContraction.cochainHomotopyEquiv_hom, ← zeroExtensionMap_comp,
    ← zeroExtensionMap_comp, blockR_fiber]

/-- 移送後の逆方向も独立生成した同じ実block s。 -/
theorem blockHomotopyEquiv_inv : (blockHomotopyEquiv N e laws ha l).inv =
    zeroExtensionMap (blockS N e laws ha l) := by
  apply transportHomotopyEquiv_inv_eq
  rw [lawBlockFiberZeroExtensionIso_hom, lawBlockFiberZeroExtensionIso_hom,
    SubsetChainContraction.cochainHomotopyEquiv_inv, ← zeroExtensionMap_comp,
    ← zeroExtensionMap_comp, blockS_fiber]

end TriangleAddition

namespace EdgeSubdivision
variable (N : ResolutionInvariance.TargetSupportedNerve q) (e : N.nerve.EdgeComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q) (l : LawValueLabel laws)

/-- 面付き辺分割の原始r有限和を独立生成した同じ実block Hom。 -/
def blockR := blockFiniteHom laws ha (r0 N e) (r1 N e) (r2 N e)
  (r_comm01 N e) (r_comm12 N e) l
/-- 面付き辺分割の原始s有限和を独立生成した同じ逆block Hom。 -/
def blockS := blockFiniteHom laws ha (s0 N e) (s1 N e) (s2 N e)
  (s_comm01 N e) (s_comm12 N e) l

/-- 同じblock比較は全三成分で原始fiber収縮へ接続する。 -/
theorem blockR_fiber :
    cochainComp (blockR N e laws ha l) ((supported N e).lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom =
      cochainComp (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom
        (chainContraction N e (labelValueFiber laws q ha l)).rHom := by
  have h := blockFiniteFiber_square laws ha (r0 N e) (r1 N e) (r2 N e)
    (r_comm01 N e) (r_comm12 N e) l
  rw [rSubsetFiniteHom_eq] at h
  exact h

/-- 同じ逆block有限和も全三成分で原始fiber切断へ接続する。 -/
theorem blockS_fiber :
    cochainComp (blockS N e laws ha l) (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom =
      cochainComp ((supported N e).lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom
        (chainContraction N e (labelValueFiber laws q ha l)).sHom := by
  have h := blockFiniteFiber_square laws ha (s0 N e) (s1 N e) (s2 N e)
    (s_comm01 N e) (s_comm12 N e) l
  rw [sSubsetFiniteHom_eq] at h
  exact h

/-- 全出現の原始収縮から得る同じラベルblock標準同値。 -/
def blockHomotopyEquiv := transportHomotopyEquiv
  (chainContraction N e (labelValueFiber laws q ha l)).cochainHomotopyEquiv
  (lawBlockFiberZeroExtensionIso N laws ha l)
  (lawBlockFiberZeroExtensionIso (supported N e) laws ha l)

/-- 移送後の順方向は独立生成した同じ実block r。 -/
theorem blockHomotopyEquiv_hom : (blockHomotopyEquiv N e laws ha l).hom =
    zeroExtensionMap (blockR N e laws ha l) := by
  apply transportHomotopyEquiv_hom_eq
  rw [lawBlockFiberZeroExtensionIso_hom, lawBlockFiberZeroExtensionIso_hom,
    SubsetChainContraction.cochainHomotopyEquiv_hom, ← zeroExtensionMap_comp,
    ← zeroExtensionMap_comp, blockR_fiber]

/-- 移送後の逆方向も独立生成した同じ実block s。 -/
theorem blockHomotopyEquiv_inv : (blockHomotopyEquiv N e laws ha l).inv =
    zeroExtensionMap (blockS N e laws ha l) := by
  apply transportHomotopyEquiv_inv_eq
  rw [lawBlockFiberZeroExtensionIso_hom, lawBlockFiberZeroExtensionIso_hom,
    SubsetChainContraction.cochainHomotopyEquiv_inv, ← zeroExtensionMap_comp,
    ← zeroExtensionMap_comp, blockS_fiber]

end EdgeSubdivision
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
