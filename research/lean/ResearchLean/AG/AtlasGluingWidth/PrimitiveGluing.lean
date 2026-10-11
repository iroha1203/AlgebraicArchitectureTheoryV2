import ResearchLean.AG.AtlasGluingWidth.PairHomology
import ResearchLean.AG.AtlasGluingWidth.GluingDefect
import ResearchLean.AG.UniformInvariance.DefectSemantics
import Formal.Util.AssertStandardAxioms
/-! # 原始Mと任意領域の同じ一次欠損へのQ/P貼り合わせ

GOAL C／設計 exact-sequence §3–4。Aの生成cellRowと同じcellRowMapを使い、
通常UのG-134 H¹射、その実核、実余核へ全射と商の同定を通して接続する。
Implementation notes: G-133 oldH1Equiv_natural とA/Bの全セル等号・全Hom等号を採用する。
同次元だけの別phantom/hiddenや任意分裂は、元の比較と代表式を保持しないため退けた。
一般SES・可換性は入力fieldへ移さず、AのcellRow_shortExactと原始Mから生成する。
局所J零は特殊化の方向仮定で、元の局所H¹射の全単射性と二領域積同型へ変換して使う。
H⁰局所比較と交差比較は元の射を保持し、交差比較同型の追加仮定を要求しない。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.PrimitiveGluing
open AAT.AG.AtlasGluingWidth AAT.AG.AtlasDefectComposition AAT.AG.TwoPhase
open AAT.AG.ResolutionInvariance AAT.AG.CanonicalResolution
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison qc qf h Nc Nf)
variable {Sc Tc : CellSelection Nc} {Sf Tf : CellSelection Nf}
variable (hs : SelectionCompatible M Sc Sf) (ht : SelectionCompatible M Tc Tf)
/-- 同じ局所J零から実二領域H¹比較の全単射性を導く。 -/
theorem cell_local_bijective
    (hA : blockDefect hs.hom.h1Map = (0,0)) (hB : blockDefect ht.hom.h1Map = (0,0)) :
    Function.Bijective (homologyMap (StandardRow.cellRowMap M hs ht).τ₂ (1:ℤ)) :=
  PairHomology.homologyMap_pair_bijective hs.hom ht.hom 1
    ((PairHomology.oldH1_bijective_iff hs.hom).mp ((blockDefect_eq_zero_iff_bijective _).mp hA))
    ((PairHomology.oldH1_bijective_iff ht.hom).mp ((blockDefect_eq_zero_iff_bijective _).mp hB))

/-- 全セル等号に沿い、同じ選択H¹商を元の標準H¹へ移す。 -/
def selectionOldEquiv {q : Reading Source} {D : TargetSupportedNerve q}
    (S S' : CellSelection D) (he : S = S') : S'.complex.H1 ≃ₗ[ℚ] (zeroExtension S.complex).homology (1:ℤ) := by
  subst S'
  exact oldH1Equiv S.complex

/-- 全セル輸送とG-133自然性により同じ全H¹射を保持する。 -/
theorem selectionHomCongr_natural {Sc' : CellSelection Nc} {Sf' : CellSelection Nf}
    (hc : Sc = Sc') (hf : Sf = Sf') (x : Sc'.complex.H1) :
    selectionOldEquiv Sf Sf' hf ((AtlasMayerVietoris.selectionHomCongr M hs hc hf).h1Map x) =
      homologyMap (zeroExtensionMap hs.hom) (1:ℤ) (selectionOldEquiv Sc Sc' hc x) := by
  subst Sc'
  subst Sf'
  exact oldH1Equiv_natural hs.hom x

/-- 原始粗領域和と真のセル和の全セル等号。 -/
def coarseUnionEq (A B : Set qc.Target) :
    (CellSelection.region Nc A).union (CellSelection.region Nc B) = CellSelection.region Nc (A ∪ B) :=
  (CellSelection.region_union Nc A B).symm

/-- 元の因子の逆像和と細セル和の全セル等号。 -/
def fineUnionEq (A B : Set qc.Target) :
    (CellSelection.region Nf (comparisonFactor qc qf h ⁻¹' A)).union
      (CellSelection.region Nf (comparisonFactor qc qf h ⁻¹' B)) =
      CellSelection.region Nf (comparisonFactor qc qf h ⁻¹' (A ∪ B)) := by
  rw [← CellSelection.region_union, ← Set.preimage_union]

/-- 通常粗Uの同じ旧H¹商からセル和標準H¹への同型。 -/
def coarseUnionEquiv (A B : Set qc.Target) :=
  selectionOldEquiv _ _ (coarseUnionEq (Nc := Nc) A B)
/-- 通常細Uの同じ旧H¹商からセル和標準H¹への同型。 -/
def fineUnionEquiv (A B : Set qc.Target) :=
  selectionOldEquiv _ _ (fineUnionEq (h := h) (Nf := Nf) A B)

/-- 通常UのG-134同じH¹射と原始二行図式の合併H¹比較が可換。 -/
theorem regionUnion_natural (A B : Set qc.Target) (x : (Nc.targetSubsetComplex (A ∪ B)).H1) :
    fineUnionEquiv (h := h) (Nf := Nf) A B ((M.aSubnerveComparisonHom (A ∪ B)).h1Map x) =
      homologyMap (StandardRow.cellRowMap M (SelectionCompatible.region M A)
        (SelectionCompatible.region M B)).τ₁ (1:ℤ) (coarseUnionEquiv (Nc := Nc) A B x) := by
  rw [← AtlasMayerVietoris.regionUnionHom_eq M A B]
  exact selectionHomCongr_natural M ((SelectionCompatible.region M A).union M (SelectionCompatible.region M B))
    (coarseUnionEq (Nc := Nc) A B) (fineUnionEq (h := h) (Nf := Nf) A B) x
/-- 任意A/Bの粗原始cochain短完全列の同じ標準短複体。 -/
def coarseRow (A B : Set qc.Target) :=
  StandardRow.cellRow (CellSelection.region Nc A) (CellSelection.region Nc B)
/-- 任意A/Bの因子逆像の細原始cochain短完全列の同じ標準短複体。 -/
def fineRow (A B : Set qc.Target) :=
  StandardRow.cellRow (CellSelection.region Nf (comparisonFactor qc qf h ⁻¹' A))
    (CellSelection.region Nf (comparisonFactor qc qf h ⁻¹' B))
/-- 元のMから生成する同じ粗細二行比較。 -/
def comparison (A B : Set qc.Target) : coarseRow (Nc := Nc) A B ⟶ fineRow (h := h) (Nf := Nf) A B :=
  StandardRow.cellRowMap M (SelectionCompatible.region M A) (SelectionCompatible.region M B)
/-- 全次数の実二領域homology積から真のセル交差への同じ差制限。 -/
def difference (D : TargetSupportedNerve qc) (A B : Set qc.Target) (m : ℤ) :
    ((zeroExtension (D.targetSubsetComplex A)).homology m ×
      (zeroExtension (D.targetSubsetComplex B)).homology m) →ₗ[ℚ]
      (zeroExtension (CellSelection.intersectionComplex D A B)).homology m :=
  (homologyMap (StandardRow.cellRow (CellSelection.region D A) (CellSelection.region D B)).g m).hom.comp
    (PairHomology.homologyEquiv (D.targetSubsetComplex A) (D.targetSubsetComplex B) m).symm.toLinearMap

/-- 二領域積同型により同じ原始差制限を全元で保持する。 -/
theorem difference_natural (A B : Set qc.Target) (m : ℤ)
    (x : (zeroExtension (pairComplex (Nc.targetSubsetComplex A) (Nc.targetSubsetComplex B))).homology m) :
    difference Nc A B m (PairHomology.homologyEquiv _ _ m x) =
      homologyMap (coarseRow (Nc := Nc) A B).g m x := by
  change homologyMap (coarseRow (Nc := Nc) A B).g m
    ((PairHomology.homologyEquiv _ _ m).symm (PairHomology.homologyEquiv _ _ m x)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- 局所homology比較と交差homology比較の実差制限square。 -/
theorem difference_comparison (A B : Set qc.Target) (m : ℤ)
    (x : (zeroExtension (Nc.targetSubsetComplex A)).homology m ×
      (zeroExtension (Nc.targetSubsetComplex B)).homology m) :
    homologyMap (comparison M A B).τ₃ m (difference Nc A B m x) =
      difference Nf (comparisonFactor qc qf h ⁻¹' A) (comparisonFactor qc qf h ⁻¹' B) m
        (homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) m x.1,
         homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom B)) m x.2) := by
  let z := (PairHomology.homologyEquiv (Nc.targetSubsetComplex A) (Nc.targetSubsetComplex B) m).symm x
  have hc := congrArg (fun f => f z) (QuotientKernelRow.homology_comm23
    (coarseRow (Nc := Nc) A B) (comparison M A B) m)
  change homologyMap (comparison M A B).τ₃ m (difference Nc A B m x) =
    homologyMap (fineRow (h := h) (Nf := Nf) A B).g m
      (homologyMap (comparison M A B).τ₂ m z) at hc
  rw [hc]
  erw [← difference_natural (Nc := Nf)
    (comparisonFactor qc qf h ⁻¹' A) (comparisonFactor qc qf h ⁻¹' B) m]
  have hp := PairHomology.homologyMap_pair (SelectionCompatible.region M A).hom
    (SelectionCompatible.region M B).hom m z
  change PairHomology.homologyEquiv
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' B)) m
    (homologyMap (comparison M A B).τ₂ m z) =
      (homologyMap (zeroExtensionMap (SelectionCompatible.region M A).hom) m
        (PairHomology.homologyEquiv (Nc.targetSubsetComplex A) (Nc.targetSubsetComplex B) m z).1,
       homologyMap (zeroExtensionMap (SelectionCompatible.region M B).hom) m
        (PairHomology.homologyEquiv (Nc.targetSubsetComplex A) (Nc.targetSubsetComplex B) m z).2) at hp
  have he : PairHomology.homologyEquiv (Nc.targetSubsetComplex A) (Nc.targetSubsetComplex B) m z = x :=
    LinearEquiv.apply_symm_apply _ _
  rw [he, SelectionCompatible.region_hom_eq, SelectionCompatible.region_hom_eq] at hp
  exact congrArg (difference Nf (comparisonFactor qc qf h ⁻¹' A)
    (comparisonFactor qc qf h ⁻¹' B) m) hp

/-- 実Qは二領域H⁰積上の同じ差制限の余核と同型。 -/
def qProductEquiv (A B : Set qc.Target) : QuotientKernelRow.Q (coarseRow (Nc := Nc) A B) ≃ₗ[ℚ]
    ((coarseRow (Nc := Nc) A B).X₃.homology (0:ℤ) ⧸ LinearMap.range (difference Nc A B 0)) :=
  LinearConjugation.cokernelEquiv _ _ (PairHomology.homologyEquiv _ _ 0) (LinearEquiv.refl ℚ _)
    (fun x => (difference_natural (Nc := Nc) A B 0 x).symm)
/-- 実Pは二領域H¹積上の同じ差制限の核と同型。 -/
def pProductEquiv (A B : Set qc.Target) : QuotientKernelRow.P (coarseRow (Nc := Nc) A B) ≃ₗ[ℚ]
    LinearMap.ker (difference Nc A B (1:ℤ)) :=
  LinearConjugation.kernelEquiv _ _ (PairHomology.homologyEquiv _ _ 1) (LinearEquiv.refl ℚ _)
    (fun x => (difference_natural (Nc := Nc) A B 1 x).symm)
/-- Qの二領域積表示への同定は交差H⁰の全商代表元を固定する。 -/
@[simp] theorem qProductEquiv_mk (A B : Set qc.Target)
    (z : (coarseRow (Nc := Nc) A B).X₃.homology (0:ℤ)) :
    qProductEquiv (Nc := Nc) A B ((LinearMap.range (homologyMap (coarseRow (Nc := Nc) A B).g 0).hom).mkQ z) =
      (LinearMap.range (difference Nc A B 0)).mkQ z := rfl
/-- Pの二領域積表示への同定は元の二領域H¹成分を保持する。 -/
@[simp] theorem pProductEquiv_val (A B : Set qc.Target) (z : QuotientKernelRow.P (coarseRow (Nc := Nc) A B)) :
    (pProductEquiv (Nc := Nc) A B z).val = PairHomology.homologyEquiv _ _ 1 z.val := rfl

/-- 通常Uの同じ旧H¹比較の実核を標準合併比較核へ同定する。 -/
def phantomEquiv (A B : Set qc.Target) : LinearMap.ker (M.aSubnerveComparisonHom (A ∪ B)).h1Map ≃ₗ[ℚ]
    GluingDefect.Phantom (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B) (comparison M A B) :=
  LinearConjugation.kernelEquiv _ _ (coarseUnionEquiv (Nc := Nc) A B)
    (fineUnionEquiv (h := h) (Nf := Nf) A B) (regionUnion_natural M A B)
/-- 通常Uの同じ旧H¹比較の実余核を標準合併比較余核へ同定する。 -/
def hiddenEquiv (A B : Set qc.Target) :
    ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' (A ∪ B))).H1 ⧸
      LinearMap.range (M.aSubnerveComparisonHom (A ∪ B)).h1Map) ≃ₗ[ℚ]
      GluingDefect.Hidden (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B) (comparison M A B) :=
  LinearConjugation.cokernelEquiv _ _ (coarseUnionEquiv (Nc := Nc) A B)
    (fineUnionEquiv (h := h) (Nf := Nf) A B) (regionUnion_natural M A B)
/-- 実核同定は元の粗H¹ classを保持する。 -/
@[simp] theorem phantomEquiv_val (A B : Set qc.Target)
    (x : LinearMap.ker (M.aSubnerveComparisonHom (A ∪ B)).h1Map) :
    (phantomEquiv M A B x).val = coarseUnionEquiv (Nc := Nc) A B x.val := rfl
/-- 実余核同定は元の細H¹商代表元を保持する。 -/
@[simp] theorem hiddenEquiv_mk (A B : Set qc.Target)
    (y : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' (A ∪ B))).H1) :
    hiddenEquiv M A B ((LinearMap.range (M.aSubnerveComparisonHom (A ∪ B)).h1Map).mkQ y) =
      (LinearMap.range (homologyMap (comparison M A B).τ₁ (1:ℤ)).hom).mkQ
        (fineUnionEquiv (h := h) (Nf := Nf) A B y) := rfl

/-- 通常Uの実phantomへ入る第一snake射。 -/
def first (A B : Set qc.Target) :=
  ModuleCat.ofHom (GluingDefect.first _ _ (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B)) ≫ (phantomEquiv M A B).symm.toModuleIso.hom
/-- 通常Uの実phantomからP比較核への第二snake射。 -/
def second (A B : Set qc.Target) :=
  (phantomEquiv M A B).toModuleIso.hom ≫ ModuleCat.ofHom (GluingDefect.second _ _
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B))
/-- 原始二行Q/P図式から生成した標準snake連結射。 -/
def connecting (A B : Set qc.Target) :=
  ModuleCat.ofHom (GluingDefect.connecting _ _ (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B))
/-- Q比較余核から通常Uの実hiddenへの第四snake射。 -/
def fourth (A B : Set qc.Target) :=
  ModuleCat.ofHom (GluingDefect.fourth _ _ (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B)) ≫ (hiddenEquiv M A B).symm.toModuleIso.hom
/-- 通常Uの実hiddenからP比較余核への第五snake射。 -/
def fifth (A B : Set qc.Target) :=
  (hiddenEquiv M A B).toModuleIso.hom ≫ ModuleCat.ofHom (GluingDefect.fifth _ _
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B))
/-- 原始入力だけから同じ通常U snake列の第一位置完全性を導く。 -/
theorem exact1 (A B : Set qc.Target) : Function.Exact (first M A B) (second M A B) := by
  have he := LinearSnake.conjugate_exact
    (ModuleCat.ofHom (GluingDefect.first _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B)))
    (ModuleCat.ofHom (GluingDefect.second _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B)))
    (GluingDefect.exact₁ _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B))
    (Iso.refl _) ((phantomEquiv M A B).symm.toModuleIso) (Iso.refl _)
  simpa only [LinearSnake.conjugate, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] using he
/-- 原始入力だけから同じ通常U snake列の第二位置完全性を導く。 -/
theorem exact2 (A B : Set qc.Target) : Function.Exact (second M A B) (connecting M A B) := by
  have he := LinearSnake.conjugate_exact
    (ModuleCat.ofHom (GluingDefect.second _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B)))
    (ModuleCat.ofHom (GluingDefect.connecting _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B)))
    (GluingDefect.exact₂ _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B))
    ((phantomEquiv M A B).symm.toModuleIso) (Iso.refl _) (Iso.refl _)
  simpa only [LinearSnake.conjugate, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] using he
/-- 原始入力だけから同じ通常U snake列の第三位置完全性を導く。 -/
theorem exact3 (A B : Set qc.Target) : Function.Exact (connecting M A B) (fourth M A B) := by
  have he := LinearSnake.conjugate_exact
    (ModuleCat.ofHom (GluingDefect.connecting _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B)))
    (ModuleCat.ofHom (GluingDefect.fourth _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B)))
    (GluingDefect.exact₃ _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B))
    (Iso.refl _) (Iso.refl _) ((hiddenEquiv M A B).symm.toModuleIso)
  simpa only [LinearSnake.conjugate, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] using he
/-- 原始入力だけから同じ通常U snake列の第四位置完全性を導く。 -/
theorem exact4 (A B : Set qc.Target) : Function.Exact (fourth M A B) (fifth M A B) := by
  have he := LinearSnake.conjugate_exact
    (ModuleCat.ofHom (GluingDefect.fourth _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B)))
    (ModuleCat.ofHom (GluingDefect.fifth _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B)))
    (GluingDefect.exact₄ _ _ (StandardRow.cellRow_shortExact _ _)
      (StandardRow.cellRow_shortExact _ _) (comparison M A B))
    (Iso.refl _) ((hiddenEquiv M A B).symm.toModuleIso) (Iso.refl _)
  simpa only [LinearSnake.conjugate, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] using he
/-- 原始Q/P短完全列から第一snake射の単射性を導く。 -/
theorem first_injective (A B : Set qc.Target) : Function.Injective (first M A B) :=
  (phantomEquiv M A B).symm.injective.comp (GluingDefect.first_injective _ _
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B))
/-- 原始Q/P短完全列から第五snake射の全射性を導く。 -/
theorem fifth_surjective (A B : Set qc.Target) : Function.Surjective (fifth M A B) :=
  (GluingDefect.fifth_surjective _ _ (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B)).comp (hiddenEquiv M A B).surjective
/-- 第一snake射の代表式は同じ粗Q包含。 -/
theorem first_val (A B : Set qc.Target)
    (a : LinearMap.ker (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B))) :
    (phantomEquiv M A B (first M A B a)).val =
      QuotientKernelRow.inclusion (coarseRow (Nc := Nc) A B) (StandardRow.cellRow_shortExact _ _) a.val := by
  change (phantomEquiv M A B ((phantomEquiv M A B).symm (GluingDefect.first (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) a))).val = _
  rw [LinearEquiv.apply_symm_apply, GluingDefect.first_val]
/-- 第二snake射の代表式は同じ粗U制限。 -/
theorem second_val (A B : Set qc.Target)
    (a : LinearMap.ker (M.aSubnerveComparisonHom (A ∪ B)).h1Map) :
    (second M A B a).val = QuotientKernelRow.projection (coarseRow (Nc := Nc) A B)
      (StandardRow.cellRow_shortExact _ _) (coarseUnionEquiv (Nc := Nc) A B a.val) :=
  GluingDefect.second_val (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) (phantomEquiv M A B a)
/-- 第四snake射は同じ細Q包含のclassを通常Uの実余核へ送る。 -/
theorem fourth_mk (A B : Set qc.Target)
    (z : QuotientKernelRow.Q (fineRow (h := h) (Nf := Nf) A B)) :
    fourth M A B ((LinearMap.range (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B))).mkQ z) =
      (hiddenEquiv M A B).symm ((LinearMap.range (homologyMap (comparison M A B).τ₁ (1:ℤ)).hom).mkQ
        (QuotientKernelRow.inclusion (fineRow (h := h) (Nf := Nf) A B) (StandardRow.cellRow_shortExact _ _) z)) := by
  change (hiddenEquiv M A B).symm (GluingDefect.fourth (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) _) = _
  exact congrArg (hiddenEquiv M A B).symm (GluingDefect.fourth_mk
    (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) z)
/-- 第五snake射は通常細Uのclassを同じ細P制限の余核へ送る。 -/
theorem fifth_mk (A B : Set qc.Target)
    (y : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' (A ∪ B))).H1) :
    fifth M A B ((LinearMap.range (M.aSubnerveComparisonHom (A ∪ B)).h1Map).mkQ y) =
      (LinearMap.range (QuotientKernelRow.p (coarseRow (Nc := Nc) A B) (comparison M A B))).mkQ
        (QuotientKernelRow.projection (fineRow (h := h) (Nf := Nf) A B) (StandardRow.cellRow_shortExact _ _)
          (fineUnionEquiv (h := h) (Nf := Nf) A B y)) := by
  change GluingDefect.fifth (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) (hiddenEquiv M A B _) = _
  rw [hiddenEquiv_mk]
  exact GluingDefect.fifth_mk (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) _
/-- 同じ旧粗H¹元の持ち上げと同じ細Q包含から標準snake代表式を与える。 -/
theorem connecting_representative (A B : Set qc.Target)
    (a : LinearMap.ker (QuotientKernelRow.p (coarseRow (Nc := Nc) A B) (comparison M A B)))
    (b : (Nc.targetSubsetComplex (A ∪ B)).H1)
    (hb : QuotientKernelRow.projection (coarseRow (Nc := Nc) A B) (StandardRow.cellRow_shortExact _ _)
      (coarseUnionEquiv (Nc := Nc) A B b) = a.val)
    (z : QuotientKernelRow.Q (fineRow (h := h) (Nf := Nf) A B))
    (hz : QuotientKernelRow.inclusion (fineRow (h := h) (Nf := Nf) A B) (StandardRow.cellRow_shortExact _ _) z =
      fineUnionEquiv (h := h) (Nf := Nf) A B ((M.aSubnerveComparisonHom (A ∪ B)).h1Map b)) :
    connecting M A B a =
      (LinearMap.range (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B))).mkQ z := by
  rw [regionUnion_natural M A B] at hz
  exact GluingDefect.connecting_representative (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) a _ hb z hz
/-- 任意P比較核元について同じ旧H¹持ち上げと細Q元を原始SESから生成する。 -/
theorem connecting_lift (A B : Set qc.Target)
    (a : LinearMap.ker (QuotientKernelRow.p (coarseRow (Nc := Nc) A B) (comparison M A B))) :
    ∃ b : (Nc.targetSubsetComplex (A ∪ B)).H1, ∃ z : QuotientKernelRow.Q (fineRow (h := h) (Nf := Nf) A B),
      QuotientKernelRow.projection (coarseRow (Nc := Nc) A B) (StandardRow.cellRow_shortExact _ _)
        (coarseUnionEquiv (Nc := Nc) A B b) = a.val ∧
      QuotientKernelRow.inclusion (fineRow (h := h) (Nf := Nf) A B) (StandardRow.cellRow_shortExact _ _) z =
        fineUnionEquiv (h := h) (Nf := Nf) A B ((M.aSubnerveComparisonHom (A ∪ B)).h1Map b) ∧
      connecting M A B a = (LinearMap.range (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B))).mkQ z := by
  obtain ⟨b,hb,z,hz,hc⟩ := GluingDefect.connecting_lift (coarseRow (Nc := Nc) A B)
    (fineRow (h := h) (Nf := Nf) A B) (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B) a
  refine ⟨(coarseUnionEquiv (Nc := Nc) A B).symm b,z,?_,?_,hc⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hb
  · rw [regionUnion_natural M A B, LinearEquiv.apply_symm_apply]
    exact hz

/-- 元の通常A/BのJ零から同じ二領域標準H¹比較の全単射性を放電する。 -/
theorem local_bijective (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    Function.Bijective (homologyMap (comparison M A B).τ₂ (1:ℤ)) := by
  apply cell_local_bijective M (SelectionCompatible.region M A) (SelectionCompatible.region M B)
  · simpa only [SelectionCompatible.region_hom_eq] using hA
  · simpa only [SelectionCompatible.region_hom_eq] using hB

/-- 通常Uの元のblockDefectを核商同型で標準合併比較欠損へ同定する。 -/
theorem defect_standard (A B : Set qc.Target) :
    blockDefect (M.aSubnerveComparisonHom (A ∪ B)).h1Map =
      blockDefect (homologyMap (comparison M A B).τ₁ (1:ℤ)).hom :=
  Prod.ext (phantomEquiv M A B).finrank_eq (hiddenEquiv M A B).finrank_eq

/-- 局所J零下で通常Uの元のphantomとQ比較核を実射に沿って同定する。 -/
def localPhantomEquiv (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    LinearMap.ker (M.aSubnerveComparisonHom (A ∪ B)).h1Map ≃ₗ[ℚ]
      LinearMap.ker (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B)) :=
  (phantomEquiv M A B).trans (GluingDefect.phantomEquiv _ _
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _)
    (comparison M A B) (local_bijective M A B hA hB))

/-- 局所J零から生成された標準hidden/Z短複体。 -/
def localHiddenRow (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :=
  GluingDefect.hiddenZRow _ _ (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B) (local_bijective M A B hA hB)
/-- 局所J零から生成された標準hidden/Z短完全列。 -/
theorem localHiddenRow_shortExact (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    (localHiddenRow M A B hA hB).ShortExact :=
  GluingDefect.hiddenZRow_shortExact _ _ (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B) (local_bijective M A B hA hB)

/-- 同じ通常Uの旧H¹実余核を中間項とするQ比較余核/Z短複体。 -/
def oldHiddenRow (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.mk ((localHiddenRow M A B hA hB).f ≫ (hiddenEquiv M A B).symm.toModuleIso.hom)
    ((hiddenEquiv M A B).toModuleIso.hom ≫ (localHiddenRow M A B hA hB).g) (by
      rw [Category.assoc, ← Category.assoc (hiddenEquiv M A B).symm.toModuleIso.hom,
        show (hiddenEquiv M A B).symm.toModuleIso.hom ≫ (hiddenEquiv M A B).toModuleIso.hom = 𝟙 _ from
          (hiddenEquiv M A B).toModuleIso.inv_hom_id, Category.id_comp]
      exact (localHiddenRow M A B hA hB).zero)
/-- 中間項の実商同型に沿い両端項と両射を保つ短複体同型。 -/
def oldHiddenRowIso (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    localHiddenRow M A B hA hB ≅ oldHiddenRow M A B hA hB :=
  ShortComplex.isoMk (Iso.refl _) (hiddenEquiv M A B).symm.toModuleIso (Iso.refl _)
    (by simp only [oldHiddenRow, Iso.refl_hom, Category.id_comp])
    (by simp only [oldHiddenRow, Iso.refl_hom, Category.comp_id, ← Category.assoc,
      show (hiddenEquiv M A B).symm.toModuleIso.hom ≫ (hiddenEquiv M A B).toModuleIso.hom = 𝟙 _ from
        (hiddenEquiv M A B).toModuleIso.inv_hom_id]
        erw [Category.id_comp])
/-- GOAL Cの通常Uの実hiddenと実Zの短完全列。 -/
theorem oldHiddenRow_shortExact (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    (oldHiddenRow M A B hA hB).ShortExact :=
  ShortComplex.shortExact_of_iso (oldHiddenRowIso M A B hA hB) (localHiddenRow_shortExact M A B hA hB)

/-- 実hiddenへの包含は同じ細δ包含の商代表元。 -/
theorem oldHiddenRow_f_mk (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0))
    (z : QuotientKernelRow.Q (fineRow (h := h) (Nf := Nf) A B)) :
    (oldHiddenRow M A B hA hB).f
      ((LinearMap.range (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B))).mkQ z) =
      (hiddenEquiv M A B).symm ((LinearMap.range (homologyMap (comparison M A B).τ₁ (1:ℤ)).hom).mkQ
        (QuotientKernelRow.inclusion (fineRow (h := h) (Nf := Nf) A B) (StandardRow.cellRow_shortExact _ _) z)) := by
  change (hiddenEquiv M A B).symm (GluingDefect.fourth (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) _) = _
  exact congrArg (hiddenEquiv M A B).symm (GluingDefect.fourth_mk
    (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B) z)

/-- 実hiddenからZへの射は同じ細制限・局所逆比較・粗差制限の代表式。 -/
theorem oldHiddenRow_g_mk (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0))
    (y : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' (A ∪ B))).H1) :
    ((oldHiddenRow M A B hA hB).g ((LinearMap.range (M.aSubnerveComparisonHom (A ∪ B)).h1Map).mkQ y)).val =
      homologyMap (coarseRow (Nc := Nc) A B).g 1
        ((QuotientKernelRow.localEquiv (coarseRow (Nc := Nc) A B) (comparison M A B)
          (local_bijective M A B hA hB)).symm
            (homologyMap (fineRow (h := h) (Nf := Nf) A B).f 1 (fineUnionEquiv (h := h) (Nf := Nf) A B y))) := by
  change (GluingDefect.hiddenZProjection (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B)
    (StandardRow.cellRow_shortExact _ _) (StandardRow.cellRow_shortExact _ _) (comparison M A B)
    (local_bijective M A B hA hB)
    (hiddenEquiv M A B ((LinearMap.range (M.aSubnerveComparisonHom (A ∪ B)).h1Map).mkQ y))).val = _
  rw [hiddenEquiv_mk, GluingDefect.hiddenZProjection_mk]

/-- GOAL Cの同じ通常Uの実二成分J次元式。一般SESと局所比較は原始入力と局所J零から放電済み。 -/
theorem defect_dimension (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    blockDefect (M.aSubnerveComparisonHom (A ∪ B)).h1Map =
      (Module.finrank ℚ (LinearMap.ker (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B))),
       Module.finrank ℚ (QuotientKernelRow.Q (fineRow (h := h) (Nf := Nf) A B) ⧸
         LinearMap.range (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B))) +
       Module.finrank ℚ (QuotientKernelRow.Z (coarseRow (Nc := Nc) A B) (comparison M A B))) := by
  rw [defect_standard M A B]
  letI : FiniteDimensional ℚ ((fineRow (h := h) (Nf := Nf) A B).X₁.homology (1:ℤ)) := by
    change FiniteDimensional ℚ ((zeroExtension _).homology (1:ℤ))
    infer_instance
  exact GluingDefect.defect_dimension (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B) (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B) (local_bijective M A B hA hB)

/-- GOAL Cの同じ通常UのJ零は実q全単射かつ実Z零と同値。交差比較同型は追加しない。 -/
theorem defect_zero_iff (A B : Set qc.Target)
    (hA : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0))
    (hB : blockDefect (M.aSubnerveComparisonHom B).h1Map = (0,0)) :
    blockDefect (M.aSubnerveComparisonHom (A ∪ B)).h1Map = (0,0) ↔
      Function.Bijective (QuotientKernelRow.q (coarseRow (Nc := Nc) A B) (comparison M A B)) ∧
        QuotientKernelRow.Z (coarseRow (Nc := Nc) A B) (comparison M A B) = ⊥ := by
  rw [defect_standard M A B]
  letI : FiniteDimensional ℚ ((fineRow (h := h) (Nf := Nf) A B).X₁.homology (1:ℤ)) := by
    change FiniteDimensional ℚ ((zeroExtension _).homology (1:ℤ))
    infer_instance
  letI : FiniteDimensional ℚ ((coarseRow (Nc := Nc) A B).X₃.homology (0:ℤ)) := by
    change FiniteDimensional ℚ ((zeroExtension _).homology (0:ℤ))
    infer_instance
  letI : FiniteDimensional ℚ ((fineRow (h := h) (Nf := Nf) A B).X₃.homology (0:ℤ)) := by
    change FiniteDimensional ℚ ((zeroExtension _).homology (0:ℤ))
    infer_instance
  letI : FiniteDimensional ℚ ((coarseRow (Nc := Nc) A B).X₃.homology (1:ℤ)) := by
    change FiniteDimensional ℚ ((zeroExtension _).homology (1:ℤ))
    infer_instance
  exact GluingDefect.defect_zero_iff (coarseRow (Nc := Nc) A B) (fineRow (h := h) (Nf := Nf) A B) (StandardRow.cellRow_shortExact _ _)
    (StandardRow.cellRow_shortExact _ _) (comparison M A B) (local_bijective M A B hA hB)
end AAT.AG.AtlasGluingWidth.PrimitiveGluing

#assert_standard_axioms_only AAT.AG.AtlasGluingWidth
