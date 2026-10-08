import ResearchLean.AG.AtlasDefectComposition.EndpointHomology
import Mathlib.Algebra.Module.ULift

/-!
# G-135 B：標準homologyの実代表

零延長の標準cycle射と、元三項複体の商類を照合する。

## Implementation notes

代表の入力射には任意universeの有理単位加群のULiftを用い、mathlibのcycle射へ
そのまま渡す。元を別の標準homologyと定義する案は、既存商類との照合を失うため
採用しない。同型の合成は定義所有者の公開APIで計算する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory AtlasDefectComposition TwoPhase
universe u
variable (C : ThreeCochainComplex.{0,u} ℚ)

/-- 標準短複体のcycle射は元の核・商射と可換である。 -/
theorem shortComplex_liftCycles_class (S : ShortComplex (ModuleCat.{u} ℚ))
    {B : ModuleCat.{u} ℚ} (x : B ⟶ S.X₂) (hx : x ≫ S.g = 0) :
    S.liftCycles x hx ≫ S.homologyπ ≫ S.moduleCatHomologyIso.hom =
      S.moduleCatLeftHomologyData.liftK x hx ≫ S.moduleCatLeftHomologyData.π := by
  rw [S.π_moduleCatCyclesIso_hom, ← Category.assoc]
  congr 1
  rw [← cancel_mono S.moduleCatLeftHomologyData.i]
  simp

/-- 元のd¹閉代表射が標準次数1homologyへ送る実商類。 -/
theorem zeroExtension_liftCycles_H1 {B : ModuleCat.{u} ℚ}
    (x : B ⟶ (zeroExtension C).X (1 : ℤ))
    (hx : x ≫ (zeroExtension C).d 1 2 = 0) :
    (zeroExtension C).liftCycles x 2 (by simp) hx ≫ (zeroExtension C).homologyπ 1 =
      (oldShort C).moduleCatLeftHomologyData.liftK x hx ≫
        (oldShort C).moduleCatLeftHomologyData.π ≫ (oldH1Iso C).hom := by
  rw [← cancel_mono (ShortComplex.homologyMapIso (zeroExtensionScIso C)).hom]
  simp only [Category.assoc, oldH1Iso_hom_comp]
  change ((zeroExtension C).sc (1 : ℤ)).liftCycles x (by
      change x ≫ (zeroExtension C).d 1 ((ComplexShape.up ℤ).next 1) = 0
      rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 1 2 from rfl)]
      exact hx) ≫
    ((zeroExtension C).sc (1 : ℤ)).homologyπ ≫
    ShortComplex.homologyMap (zeroExtensionScIso C).hom = _
  rw [ShortComplex.homologyπ_naturality]
  rw [← Category.assoc, ShortComplex.liftCycles_comp_cyclesMap]
  change (oldShort C).liftCycles x hx ≫ (oldShort C).homologyπ = _
  rw [← cancel_mono (oldShort C).moduleCatHomologyIso.hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    shortComplex_liftCycles_class (oldShort C) x hx

/-- 元の次数2代表射が標準homologyへ送る実像商類。 -/
theorem zeroExtension_liftCycles_H2 {B : ModuleCat.{u} ℚ}
    (x : B ⟶ (zeroExtension C).X (2 : ℤ))
    (hx : x ≫ (zeroExtension C).d 2 3 = 0) :
    (zeroExtension C).liftCycles x 3 (by simp) hx ≫ (zeroExtension C).homologyπ 2 =
      x ≫ ModuleCat.ofHom (LinearMap.range C.d1).mkQ ≫ (oldH2Iso C).hom := by
  rw [← cancel_mono (ShortComplex.homologyMapIso (zeroExtensionTwoScIso C)).hom]
  simp only [Category.assoc, oldH2Iso_hom_comp]
  change ((zeroExtension C).sc (2 : ℤ)).liftCycles x (by
    change x ≫ (zeroExtension C).d 2 ((ComplexShape.up ℤ).next 2) = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 2 3 from rfl)]
    exact hx) ≫ ((zeroExtension C).sc (2 : ℤ)).homologyπ ≫
      ShortComplex.homologyMap (zeroExtensionTwoScIso C).hom = _
  rw [ShortComplex.homologyπ_naturality, ← Category.assoc,
    ShortComplex.liftCycles_comp_cyclesMap]
  change (oldTwoShort C).liftCycles x hx ≫ (oldTwoShort C).homologyπ = _
  rw [← cancel_mono (oldTwoShort C).homologyι]
  rw [Category.assoc, ShortComplex.homology_π_ι, ShortComplex.liftCycles_i_assoc]
  change x ≫ (oldTwoShort C).pOpcycles =
    x ≫ ModuleCat.ofHom (LinearMap.range C.d1).mkQ ≫
    (oldTwoShort C).moduleCatOpcyclesIso.inv ≫
    ((oldTwoShort C).asIsoHomologyι (by rfl)).inv ≫
    ((oldTwoShort C).asIsoHomologyι (by rfl)).hom
  rw [Iso.inv_hom_id, Category.comp_id]
  rw [← cancel_mono (oldTwoShort C).moduleCatOpcyclesIso.hom]
  simp only [Category.assoc, ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom,
    Iso.inv_hom_id, Category.comp_id]
  rfl

/-- 元のd⁰閉代表射が標準H⁰へ送る同じ核元。 -/
theorem zeroExtension_liftCycles_H0 {B : ModuleCat.{u} ℚ}
    (x : B ⟶ (zeroExtension C).X (0 : ℤ))
    (hx : x ≫ (zeroExtension C).d 0 1 = 0) :
    (zeroExtension C).liftCycles x 1 (by simp) hx ≫ (zeroExtension C).homologyπ 0 =
      (oldZeroShort C).moduleCatLeftHomologyData.liftK x hx ≫ (oldH0Iso C).hom := by
  rw [← cancel_mono (ShortComplex.homologyMapIso (zeroExtensionZeroScIso C)).hom]
  simp only [Category.assoc, oldH0Iso_hom_comp]
  change ((zeroExtension C).sc (0 : ℤ)).liftCycles x (by
    change x ≫ (zeroExtension C).d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
    exact hx) ≫ ((zeroExtension C).sc (0 : ℤ)).homologyπ ≫
      ShortComplex.homologyMap (zeroExtensionZeroScIso C).hom = _
  rw [ShortComplex.homologyπ_naturality, ← Category.assoc,
    ShortComplex.liftCycles_comp_cyclesMap]
  change (oldZeroShort C).liftCycles x hx ≫ (oldZeroShort C).homologyπ = _
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (oldZeroShort C).iCycles]
  simp

/-- 元を指定する射は、同じ有理単位加群のスカラー倍として生成する。 -/
def elementArrow {X : ModuleCat.{u} ℚ} (x : X) : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ X :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℚ X x).comp ULift.moduleEquiv.toLinearMap)

/-- 単位元での代表射評価は指定された元。 -/
@[simp] theorem elementArrow_one {X : ModuleCat.{u} ℚ} (x : X) :
    elementArrow x (ULift.up (1 : ℚ)) = x := by simp [elementArrow]

/-- 元の射を後で適用しても、同じ指定元の代表射になる。 -/
@[simp] theorem elementArrow_comp {X Y : ModuleCat.{u} ℚ} (x : X) (f : X ⟶ Y) :
    elementArrow x ≫ f = elementArrow (f x) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change f (r.down • x) = r.down • f x
  exact map_smul f.hom _ _

/-- 零元の代表射は零射。 -/
@[simp] theorem elementArrow_zero (X : ModuleCat.{u} ℚ) : elementArrow (0 : X) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change r.down • (0 : X) = 0
  exact smul_zero _

/-- 標準次数1の代表射を任意元で評価すると元の閉代表商になる。 -/
theorem zeroExtension_liftCycles_H1_apply {B : ModuleCat.{u} ℚ}
    (x : B ⟶ (zeroExtension C).X (1 : ℤ))
    (hx : x ≫ (zeroExtension C).d 1 2 = 0) (v : B) :
    (zeroExtension C).homologyπ 1 ((zeroExtension C).liftCycles x 2 (by simp) hx v) =
      oldH1Equiv C (Submodule.Quotient.mk
        (⟨x v, by exact congrArg (fun f => f v) hx⟩ : LinearMap.ker C.d1)) := by
  exact congrArg (fun f => f v) (zeroExtension_liftCycles_H1 C x hx)

/-- 標準次数2の代表射を任意元で評価すると元の像商になる。 -/
theorem zeroExtension_liftCycles_H2_apply {B : ModuleCat.{u} ℚ}
    (x : B ⟶ (zeroExtension C).X (2 : ℤ))
    (hx : x ≫ (zeroExtension C).d 2 3 = 0) (v : B) :
    (zeroExtension C).homologyπ 2 ((zeroExtension C).liftCycles x 3 (by simp) hx v) =
      oldH2Equiv C (Submodule.Quotient.mk (x v)) := by
  exact congrArg (fun f => f v) (zeroExtension_liftCycles_H2 C x hx)

/-- 標準次数0の代表射評価は元の閉chart核値。 -/
theorem zeroExtension_liftCycles_H0_apply {B : ModuleCat.{u} ℚ}
    (x : B ⟶ (zeroExtension C).X (0 : ℤ))
    (hx : x ≫ (zeroExtension C).d 0 1 = 0) (v : B) :
    (zeroExtension C).homologyπ 0 ((zeroExtension C).liftCycles x 1 (by simp) hx v) =
      oldH0Equiv C (⟨x v, by exact congrArg (fun f => f v) hx⟩ : LinearMap.ker C.d0) := by
  exact congrArg (fun f => f v) (zeroExtension_liftCycles_H0 C x hx)

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.shortComplex_liftCycles_class
#print axioms AAT.AG.AtlasCoefficientFiber.zeroExtension_liftCycles_H1
#print axioms AAT.AG.AtlasCoefficientFiber.zeroExtension_liftCycles_H2
#print axioms AAT.AG.AtlasCoefficientFiber.zeroExtension_liftCycles_H0
#print axioms AAT.AG.AtlasCoefficientFiber.elementArrow
#print axioms AAT.AG.AtlasCoefficientFiber.elementArrow_one
#print axioms AAT.AG.AtlasCoefficientFiber.elementArrow_comp
#print axioms AAT.AG.AtlasCoefficientFiber.elementArrow_zero
#print axioms AAT.AG.AtlasCoefficientFiber.zeroExtension_liftCycles_H1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.zeroExtension_liftCycles_H2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.zeroExtension_liftCycles_H0_apply
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
