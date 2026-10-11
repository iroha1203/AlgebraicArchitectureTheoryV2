import ResearchLean.AG.AtlasGluingWidth.StandardShortExact
import ResearchLean.AG.AtlasGluingWidth.ConeShortExact
import ResearchLean.AG.AtlasGluingWidth.ConeBiprod
import ResearchLean.AG.AtlasGluingWidth.ConnectingRepresentatives
import ResearchLean.AG.AtlasDefectComposition.ConeExactSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Formal.Util.AssertStandardAxioms
/-! # 原始図式からの全整数次数Mayer–Vietoris列

GOAL B／設計 exact-sequence §2 の全整数次数 LES、標準 δ、同じ G-133 核余核列を接続する。
一般選択の hs/ht は所属輸送条件であり、任意領域 A/B の経路では SelectionCompatible.region が生成する。
SES は A の三次数構成から cellRow_shortExact、coneRow_shortExact、coneBiprodRow_shortExact の順に生成し、
region_cone_shortExact の入口に追加完全性引数を置かない。
Implementation notes: 標準 homology と標準 δ を使い、端点恒等の短複体同型で中間項を実直和へ輸送する。
独自 δ を選択定義する案は自然性・符号の再同定を要するため退けた。合併の比較は全 CellSelection 等号に
沿って輸送する。H¹ 成分だけを同定する案は、同じ全 Hom を要求する固定仕様を満たさないため退けた。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasGluingWidth
namespace StandardLES
universe u
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)) (hS : S.ShortExact)
/-- 全整数次数の標準連結射。 -/
def connecting (m : ℤ) : S.X₃.homology m ⟶ S.X₁.homology (m+1) := hS.δ m (m+1) rfl
include hS in
/-- SES中間項の標準homology列は全整数次数で完全。 -/
theorem exact_middle (m : ℤ) : Function.Exact (homologyMap S.f m) (homologyMap S.g m) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₂ m)
/-- 交差homologyから連結射への位置も全整数次数で完全。 -/
theorem exact_before (m : ℤ) : Function.Exact (homologyMap S.g m) (connecting S hS m) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₃ m (m+1) rfl)
/-- 連結射から次次数の合併制限への位置も全整数次数で完全。 -/
theorem exact_after (m : ℤ) : Function.Exact (connecting S hS m) (homologyMap S.f (m+1)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₁ m (m+1) rfl)
end StandardLES

namespace AtlasMayerVietoris
open TwoPhase AtlasDefectComposition ResolutionInvariance CanonicalResolution
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : FaceRelationSubdivision.IncidenceSupportedComparison qc qf h Nc Nf)
variable {Sc Tc : CellSelection Nc} {Sf Tf : CellSelection Nf}
variable (hs : SelectionCompatible M Sc Sf) (ht : SelectionCompatible M Tc Tf)
/-- 同じ原始二行SESから標準錐の三項短複体を構成する。 -/
def coneRow := ConeRow.row (StandardRow.cellRow Sc Tc) (StandardRow.cellRow Sf Tf)
  (StandardRow.cellRowMap M hs ht)
/-- 原始選択と比較から標準錐SESを生成し、完全性を新入力にしない。 -/
theorem coneRow_shortExact : (coneRow M hs ht).ShortExact :=
  ConeRow.row_shortExact _ _ _ (StandardRow.cellRow_shortExact Sc Tc)
    (StandardRow.cellRow_shortExact Sf Tf)
/-- 錐の全整数次数LESの三つの完全性。 -/
theorem cone_les (m : ℤ) :
    Function.Exact (homologyMap (coneRow M hs ht).f m) (homologyMap (coneRow M hs ht).g m) ∧
    Function.Exact (homologyMap (coneRow M hs ht).g m)
      (StandardLES.connecting (coneRow M hs ht) (coneRow_shortExact M hs ht) m) ∧
    Function.Exact (StandardLES.connecting (coneRow M hs ht) (coneRow_shortExact M hs ht) m)
      (homologyMap (coneRow M hs ht).f (m+1)) :=
  ⟨StandardLES.exact_middle _ (coneRow_shortExact M hs ht) m,
    StandardLES.exact_before _ _ m, StandardLES.exact_after _ _ m⟩
/-- 同じ原始cochain SESにも全整数次数の三つのLES完全性を与える。 -/
theorem cochain_les (S T : CellSelection Nc) (m : ℤ) :
    Function.Exact (homologyMap (StandardRow.cellRow S T).f m)
      (homologyMap (StandardRow.cellRow S T).g m) ∧
    Function.Exact (homologyMap (StandardRow.cellRow S T).g m)
      (StandardLES.connecting (StandardRow.cellRow S T) (StandardRow.cellRow_shortExact S T) m) ∧
    Function.Exact (StandardLES.connecting (StandardRow.cellRow S T) (StandardRow.cellRow_shortExact S T) m)
      (homologyMap (StandardRow.cellRow S T).f (m+1)) :=
  ⟨StandardLES.exact_middle _ (StandardRow.cellRow_shortExact S T) m,
    StandardLES.exact_before _ _ m, StandardLES.exact_after _ _ m⟩
/-- 原始Mの二行図式は、標準連結射の全整数次数の自然性を生成する。 -/
theorem cochain_connecting_natural (m : ℤ) :
    StandardLES.connecting (StandardRow.cellRow Sc Tc) (StandardRow.cellRow_shortExact Sc Tc) m ≫
      homologyMap (zeroExtensionMap (hs.union M ht).hom) (m+1) =
    homologyMap (zeroExtensionMap (hs.inter M ht).hom) m ≫
      StandardLES.connecting (StandardRow.cellRow Sf Tf) (StandardRow.cellRow_shortExact Sf Tf) m :=
  HomologySequence.δ_naturality (StandardRow.cellRowMap M hs ht)
    (StandardRow.cellRow_shortExact Sc Tc) (StandardRow.cellRow_shortExact Sf Tf) m (m+1) rfl
/-- 真の二領域錐直和を中間項とする同じ原始図式の短複体。 -/
def coneBiprodRow : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk ((coneRow M hs ht).f ≫ (ConeBiprod.iso hs.hom ht.hom).hom)
    ((ConeBiprod.iso hs.hom ht.hom).inv ≫ (coneRow M hs ht).g) (by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact (coneRow M hs ht).zero)
/-- 中間項だけを同じ二領域錐の標準直和へ移す、全短複体同型。 -/
def coneBiprodRowIso : coneRow M hs ht ≅ coneBiprodRow M hs ht :=
  ShortComplex.isoMk (Iso.refl _) (ConeBiprod.iso hs.hom ht.hom) (Iso.refl _) (by
    simp only [coneBiprodRow, Iso.refl_hom, Category.id_comp]) (by
    simp only [coneBiprodRow, Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
/-- D_U→D_A⊕D_B→D_Iは同じ原始図式から生成された標準SES。 -/
theorem coneBiprodRow_shortExact : (coneBiprodRow M hs ht).ShortExact :=
  ShortComplex.shortExact_of_iso (coneBiprodRowIso M hs ht) (coneRow_shortExact M hs ht)
/-- 直和同定は端点を固定し、符号込みの標準連結射そのものを保つ。 -/
theorem coneBiprod_connecting_eq (m : ℤ) :
    StandardLES.connecting (coneRow M hs ht) (coneRow_shortExact M hs ht) m =
      StandardLES.connecting (coneBiprodRow M hs ht) (coneBiprodRow_shortExact M hs ht) m := by
  have heq := HomologySequence.δ_naturality (coneBiprodRowIso M hs ht).hom
    (coneRow_shortExact M hs ht) (coneBiprodRow_shortExact M hs ht) m (m+1) rfl
  change (coneRow_shortExact M hs ht).δ m (m+1) rfl ≫ homologyMap (𝟙 _) (m+1) =
    homologyMap (𝟙 _) m ≫ (coneBiprodRow_shortExact M hs ht).δ m (m+1) rfl at heq
  simpa only [homologyMap_id, Category.comp_id, Category.id_comp] using heq
/-- 実D_A⊕D_Bを使った全整数次数のMayer–Vietoris LES。 -/
theorem coneBiprod_les (m : ℤ) :
    Function.Exact (homologyMap (coneBiprodRow M hs ht).f m)
      (homologyMap (coneBiprodRow M hs ht).g m) ∧
    Function.Exact (homologyMap (coneBiprodRow M hs ht).g m)
      (StandardLES.connecting (coneBiprodRow M hs ht) (coneBiprodRow_shortExact M hs ht) m) ∧
    Function.Exact (StandardLES.connecting (coneBiprodRow M hs ht) (coneBiprodRow_shortExact M hs ht) m)
      (homologyMap (coneBiprodRow M hs ht).f (m+1)) :=
  ⟨StandardLES.exact_middle _ (coneBiprodRow_shortExact M hs ht) m,
    StandardLES.exact_before _ _ m, StandardLES.exact_after _ _ m⟩
/-- GOAL B／設計 exact-sequence §2: 任意原始領域 A/B の実標準錐 Mayer–Vietoris SES。
所属輸送は region、両 SES は cellRow_shortExact、錐 SES は coneRow_shortExact、
実直和への輸送は coneBiprodRowIso が生成し、入口に追加完全性仮定を置かない。 -/
theorem region_cone_shortExact (A B : Set qc.Target) :
    (coneBiprodRow M (SelectionCompatible.region M A) (SelectionCompatible.region M B)).ShortExact :=
  coneBiprodRow_shortExact M _ _
/-- 原始図式の実錐SESから、任意交差cocycleの持ち上げ・微分貼り合わせを構成する。 -/
theorem coneBiprod_lift_cocycle (m : ℤ) (z : (coneBiprodRow M hs ht).X₃.X m)
    (hz : (coneBiprodRow M hs ht).X₃.d m (m+1) z = 0) :
    ∃ (p : (coneBiprodRow M hs ht).X₂.X m) (w : (coneBiprodRow M hs ht).X₁.X (m+1)),
      (coneBiprodRow M hs ht).g.f m p = z ∧
      (coneBiprodRow M hs ht).f.f (m+1) w = (coneBiprodRow M hs ht).X₂.d m (m+1) p ∧
      (coneBiprodRow M hs ht).X₁.d (m+1) (m+1+1) w = 0 :=
  CohomologyRepresentatives.lift_cocycle _ (coneBiprodRow_shortExact M hs ht) m z hz
/-- 実二領域錐直和の持ち上げ・微分・合併貼り合わせは標準δの同じclassを与える。 -/
theorem coneBiprod_connecting_representative (m : ℤ)
    (z : (coneBiprodRow M hs ht).X₃.X m)
    (hz : (coneBiprodRow M hs ht).X₃.d m (m+1) z = 0)
    (p : (coneBiprodRow M hs ht).X₂.X m)
    (hp : (coneBiprodRow M hs ht).g.f m p = z)
    (w : (coneBiprodRow M hs ht).X₁.X (m+1))
    (hw : (coneBiprodRow M hs ht).f.f (m+1) w =
      (coneBiprodRow M hs ht).X₂.d m (m+1) p)
    (hwc : (coneBiprodRow M hs ht).X₁.d (m+1) (m+1+1) w = 0) :
    StandardLES.connecting (coneBiprodRow M hs ht) (coneBiprodRow_shortExact M hs ht) m
      (CohomologyRepresentatives.cycleClass (coneBiprodRow M hs ht).X₃ m z hz) =
      CohomologyRepresentatives.cycleClass (coneBiprodRow M hs ht).X₁ (m+1) w hwc :=
  CohomologyRepresentatives.connecting_cycleClass _ (coneBiprodRow_shortExact M hs ht)
    m z hz p hp w hw hwc
/-- 原始図式の合併錐微分はfineのd+uとcoarseの負dを保持する。 -/
theorem cone_union_d (m : ℤ)
    (x : (comparisonCone (hs.union M ht).hom).X m) :
    coneCoordinateEquiv (zeroExtensionMap (hs.union M ht).hom) (m+1)
      ((comparisonCone (hs.union M ht).hom).d m (m+1) x) =
      ((zeroExtension (Sf.union Tf).complex).d m (m+1)
          (coneCoordinateEquiv (zeroExtensionMap (hs.union M ht).hom) m x).1 +
        (zeroExtensionMap (hs.union M ht).hom).f (m+1)
          (coneCoordinateEquiv (zeroExtensionMap (hs.union M ht).hom) m x).2,
        -(zeroExtension (Sc.union Tc).complex).d (m+1) (m+1+1)
          (coneCoordinateEquiv (zeroExtensionMap (hs.union M ht).hom) m x).2) :=
  coneCoordinateEquiv_d_apply _ m x
/-- 同じA/B/U/I比較の四錐に、隣接次数を保つG-133 SESを適用する。 -/
theorem comparison_cone_shortExact (m : ℤ) :
    (coneShortComplex (zeroExtensionMap hs.hom) m).ShortExact ∧
    (coneShortComplex (zeroExtensionMap ht.hom) m).ShortExact ∧
    (coneShortComplex (zeroExtensionMap (hs.union M ht).hom) m).ShortExact ∧
    (coneShortComplex (zeroExtensionMap (hs.inter M ht).hom) m).ShortExact :=
  ⟨cone_short_exact _ m, cone_short_exact _ m, cone_short_exact _ m, cone_short_exact _ m⟩
/-- セル選択全体の等号に沿って、同じ原始比較の全cochain Homを輸送する。 -/
def selectionHomCongr {Sc' : CellSelection Nc} {Sf' : CellSelection Nf}
    (hc : Sc = Sc') (hf : Sf = Sf') : ThreeCochainComplex.Hom Sc'.complex Sf'.complex := by
  subst Sc'; subst Sf'; exact hs.hom
/-- 輸送した全Homは、同じ選択への同じ原始Mの生成Homそのもの。 -/
theorem selectionHomCongr_eq {Sc' : CellSelection Nc} {Sf' : CellSelection Nf}
    (hc : Sc = Sc') (hf : Sf = Sf') (hs' : SelectionCompatible M Sc' Sf') :
    selectionHomCongr M hs hc hf = hs'.hom := by
  subst Sc'; subst Sf'; rfl
/-- 原始二行図式の合併比較を、Aの全セル等号で通常領域Uの型へ輸送する。 -/
def regionUnionHom (A B : Set qc.Target) : ThreeCochainComplex.Hom
    (Nc.targetSubsetComplex (A ∪ B))
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' (A ∪ B))) :=
  selectionHomCongr M (Sc' := CellSelection.region Nc (A ∪ B))
    (Sf' := CellSelection.region Nf (comparisonFactor qc qf h ⁻¹' (A ∪ B)))
    ((SelectionCompatible.region M A).union M (SelectionCompatible.region M B))
    (CellSelection.region_union Nc A B).symm (by
      rw [← CellSelection.region_union, ← Set.preimage_union])
/-- 原始二行図式の合併比較は輸送込みの全HomとしてG-134の同じ通常領域比較。 -/
theorem regionUnionHom_eq (A B : Set qc.Target) :
    regionUnionHom M A B = M.aSubnerveComparisonHom (A ∪ B) := by
  exact (selectionHomCongr_eq M _ _ _ (SelectionCompatible.region M (A ∪ B))).trans
    (SelectionCompatible.region_hom_eq (M := M) (A ∪ B))
/-- 合併比較の全Hom同定は標準零延長の同じ全複体射を保つ。 -/
theorem region_union_comparison (A B : Set qc.Target) :
    zeroExtensionMap (regionUnionHom M A B) =
      zeroExtensionMap (M.aSubnerveComparisonHom (A ∪ B)) := by rw [regionUnionHom_eq]
/-- 普通領域での標準比較はG-134の同じ全Homの零延長である。 -/
theorem region_comparison (A : Set qc.Target) :
    zeroExtensionMap (SelectionCompatible.region M A).hom =
      zeroExtensionMap (M.aSubnerveComparisonHom A) := by
  rw [SelectionCompatible.region_hom_eq]
end AtlasMayerVietoris
end AAT.AG.AtlasGluingWidth
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
