import ResearchLean.AG.AtlasGluingWidth.LawGluing
import ResearchLean.AG.AtlasGluingWidth.CoefficientBridge
import Formal.Util.AssertStandardAxioms
/-! # 同じ実Law核商のsnakeと局所J零下の貼り合わせ

GOAL D／設計exact-sequence §5。各labelにA–Cを適用した有限族を同じ実generatedLawH¹へ戻す。
Implementation notes: Cの全snakeと実核商同型で射と代表元を輸送する。
同次元の別商の選択や支え集合へのlabel圧縮は退けた。局所J零は各labelでの方向仮定に限る。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.LawDefect
open AAT.AG.CanonicalResolution AAT.AG.ResolutionInvariance AAT.AG.TwoPhase
open AAT.AG.AtlasDefectComposition AAT.AG.FaceRelationSubdivision
universe u
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
/-- 実全Lawの実phantomへ入る第一snake射。 -/
def first (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :=
  ModuleCat.ofHom (GluingDefect.first _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)) ≫ (LawGluing.phantomEquiv M laws ha A B hc).symm.toModuleIso.hom
/-- 実全Lawの実phantomからP比較核への第二snake射。 -/
def second (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :=
  (LawGluing.phantomEquiv M laws ha A B hc).toModuleIso.hom ≫ ModuleCat.ofHom (GluingDefect.second _ _
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B))
/-- 全label二行Q/P図式から生成した標準snake連結射。 -/
def connecting (A B : Set qc.Target) :=
  ModuleCat.ofHom (GluingDefect.connecting _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B))
/-- Q比較余核から実全Lawの実hiddenへの第四snake射。 -/
def fourth (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :=
  ModuleCat.ofHom (GluingDefect.fourth _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)) ≫ (LawGluing.hiddenEquiv M laws ha A B hc).symm.toModuleIso.hom
/-- 実全Lawの実hiddenからP比較余核への第五snake射。 -/
def fifth (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :=
  (LawGluing.hiddenEquiv M laws ha A B hc).toModuleIso.hom ≫ ModuleCat.ofHom (GluingDefect.fifth _ _
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B))
/-- 原始入力だけから同じ実全Law snake列の第一位置完全性を導く。 -/
theorem exact1 (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) : Function.Exact (first M laws ha A B hc) (second M laws ha A B hc) := by
  have he := LinearSnake.conjugate_exact
    (ModuleCat.ofHom (GluingDefect.first _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (ModuleCat.ofHom (GluingDefect.second _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (GluingDefect.exact₁ _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B))
    (Iso.refl _) ((LawGluing.phantomEquiv M laws ha A B hc).symm.toModuleIso) (Iso.refl _)
  simpa only [LinearSnake.conjugate_refl_left, LinearSnake.conjugate_refl_right,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id] using he
/-- 原始入力だけから同じ実全Law snake列の第二位置完全性を導く。 -/
theorem exact2 (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) : Function.Exact (second M laws ha A B hc) (connecting M laws ha A B) := by
  have he := LinearSnake.conjugate_exact
    (ModuleCat.ofHom (GluingDefect.second _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (ModuleCat.ofHom (GluingDefect.connecting _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (GluingDefect.exact₂ _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B))
    ((LawGluing.phantomEquiv M laws ha A B hc).symm.toModuleIso) (Iso.refl _) (Iso.refl _)
  simpa only [LinearSnake.conjugate_refl_left, LinearSnake.conjugate_refl_right,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id] using he
/-- 原始入力だけから同じ実全Law snake列の第三位置完全性を導く。 -/
theorem exact3 (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) : Function.Exact (connecting M laws ha A B) (fourth M laws ha A B hc) := by
  have he := LinearSnake.conjugate_exact
    (ModuleCat.ofHom (GluingDefect.connecting _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (ModuleCat.ofHom (GluingDefect.fourth _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (GluingDefect.exact₃ _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B))
    (Iso.refl _) (Iso.refl _) ((LawGluing.hiddenEquiv M laws ha A B hc).symm.toModuleIso)
  simpa only [LinearSnake.conjugate_refl_left, LinearSnake.conjugate_refl_right,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id] using he
/-- 原始入力だけから同じ実全Law snake列の第四位置完全性を導く。 -/
theorem exact4 (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) : Function.Exact (fourth M laws ha A B hc) (fifth M laws ha A B hc) := by
  have he := LinearSnake.conjugate_exact
    (ModuleCat.ofHom (GluingDefect.fourth _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (ModuleCat.ofHom (GluingDefect.fifth _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (GluingDefect.exact₄ _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B))
    (Iso.refl _) ((LawGluing.hiddenEquiv M laws ha A B hc).symm.toModuleIso) (Iso.refl _)
  simpa only [LinearSnake.conjugate_refl_left, LinearSnake.conjugate_refl_right,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id] using he
/-- 有限label Q/P短完全列から第一snake射の単射性を導く。 -/
theorem first_injective (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) : Function.Injective (first M laws ha A B hc) :=
  (LawGluing.phantomEquiv M laws ha A B hc).symm.injective.comp (GluingDefect.first_injective _ _
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B))
/-- 有限label Q/P短完全列から第五snake射の全射性を導く。 -/
theorem fifth_surjective (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) : Function.Surjective (fifth M laws ha A B hc) :=
  (GluingDefect.fifth_surjective _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)).comp (LawGluing.hiddenEquiv M laws ha A B hc).surjective
/-- 第一snake射の代表式は同じ粗Q包含。 -/
theorem first_val (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (a : LinearMap.ker (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))) :
    (LawGluing.phantomEquiv M laws ha A B hc (first M laws ha A B hc a)).val =
      QuotientKernelRow.inclusion (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) a.val := by
  change (LawGluing.phantomEquiv M laws ha A B hc ((LawGluing.phantomEquiv M laws ha A B hc).symm (GluingDefect.first (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) a))).val = _
  rw [LinearEquiv.apply_symm_apply, GluingDefect.first_val]
/-- 第二snake射の代表式は同じ粗Law制限。 -/
theorem second_val (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (a : LinearMap.ker (M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha))) :
    (second M laws ha A B hc a).val = QuotientKernelRow.projection (LawGluing.coarseRow (Nc := Nc) laws ha A B)
      (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.coarseH1Equiv (Nc := Nc) laws ha A B hc a.val) :=
  GluingDefect.second_val (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) (LawGluing.phantomEquiv M laws ha A B hc a)
/-- 第四snake射は同じ細Q包含のclassを実全Lawの実余核へ送る。 -/
theorem fourth_mk (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (z : QuotientKernelRow.Q (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)) :
    fourth M laws ha A B hc ((LinearMap.range (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))).mkQ z) =
      (LawGluing.hiddenEquiv M laws ha A B hc).symm ((LinearMap.range (homologyMap (LawGluing.comparison M laws ha A B).τ₁ (1:ℤ)).hom).mkQ
        (QuotientKernelRow.inclusion (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) z)) := by
  change (LawGluing.hiddenEquiv M laws ha A B hc).symm (GluingDefect.fourth (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) _) = _
  exact congrArg (LawGluing.hiddenEquiv M laws ha A B hc).symm (GluingDefect.fourth_mk
    (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) z)
/-- 第五snake射は実細Lawのclassを同じ細P制限の余核へ送る。 -/
theorem fifth_mk (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (y : (Nf.lawGeneratedComplex laws (LawGluing.fine_adequate (h := h) laws ha)).H1) :
    fifth M laws ha A B hc ((LinearMap.range (M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha))).mkQ y) =
      (LinearMap.range (QuotientKernelRow.p (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))).mkQ
        (QuotientKernelRow.projection (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B)
          (LawGluing.fineH1Equiv (Nf := Nf) laws ha A B hc y)) := by
  change GluingDefect.fifth (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) (LawGluing.hiddenEquiv M laws ha A B hc _) = _
  rw [LawGluing.hiddenEquiv_mk]
  exact GluingDefect.fifth_mk (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) _
/-- 同じ旧粗H¹元の持ち上げと同じ細Q包含から標準snake代表式を与える。 -/
theorem connecting_representative (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (a : LinearMap.ker (QuotientKernelRow.p (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B)))
    (b : (Nc.lawGeneratedComplex laws ha).H1)
    (hb : QuotientKernelRow.projection (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
      (LawGluing.coarseH1Equiv (Nc := Nc) laws ha A B hc b) = a.val)
    (z : QuotientKernelRow.Q (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B))
    (hz : QuotientKernelRow.inclusion (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) z =
      LawGluing.fineH1Equiv (Nf := Nf) laws ha A B hc ((M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha)) b)) :
    connecting M laws ha A B a =
      (LinearMap.range (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))).mkQ z := by
  rw [LawGluing.h1_natural M laws ha A B hc] at hz
  exact GluingDefect.connecting_representative (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) a _ hb z hz
/-- 任意P比較核元について同じ旧H¹持ち上げと細Q元を原始SESから生成する。 -/
theorem connecting_lift (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (a : LinearMap.ker (QuotientKernelRow.p (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))) :
    ∃ b : (Nc.lawGeneratedComplex laws ha).H1, ∃ z : QuotientKernelRow.Q (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B),
      QuotientKernelRow.projection (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
        (LawGluing.coarseH1Equiv (Nc := Nc) laws ha A B hc b) = a.val ∧
      QuotientKernelRow.inclusion (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) z =
        LawGluing.fineH1Equiv (Nf := Nf) laws ha A B hc ((M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha)) b) ∧
      connecting M laws ha A B a = (LinearMap.range (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))).mkQ z := by
  obtain ⟨b,hb,z,hz,hδ⟩ := GluingDefect.connecting_lift (LawGluing.coarseRow (Nc := Nc) laws ha A B)
    (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) a
  refine ⟨(LawGluing.coarseH1Equiv (Nc := Nc) laws ha A B hc).symm b,z,?_,?_,hδ⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hb
  · rw [LawGluing.h1_natural M laws ha A B hc, LinearEquiv.apply_symm_apply]
    exact hz

/-- 各labelの局所J零だけから全label対の実比較全単射性を導く。 -/
theorem local_bijective (A B : Set qc.Target)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) :
    Function.Bijective (homologyMap (LawGluing.comparison M laws ha A B).τ₂ (1:ℤ)) :=
  FiniteGluing.homology_bijective _ _ _ 1 (fun l =>
    PrimitiveGluing.local_bijective M _ _ (hA l) (hB l))

/-- 実全Lawの元のblockDefectを核商同型で標準合併比較欠損へ同定する。 -/
theorem defect_standard (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    blockDefect (M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha)) =
      blockDefect (homologyMap (LawGluing.comparison M laws ha A B).τ₁ (1:ℤ)).hom :=
  Prod.ext (LawGluing.phantomEquiv M laws ha A B hc).finrank_eq (LawGluing.hiddenEquiv M laws ha A B hc).finrank_eq

/-- 局所J零下で実全Lawの元のphantomとQ比較核を実射に沿って同定する。 -/
def localPhantomEquiv (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) :
    LinearMap.ker (M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha)) ≃ₗ[ℚ]
      LinearMap.ker (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B)) :=
  (LawGluing.phantomEquiv M laws ha A B hc).trans (GluingDefect.phantomEquiv _ _
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.comparison M laws ha A B) (local_bijective M laws ha A B hA hB))

/-- 局所J零から生成された標準hidden/Z短複体。 -/
def localHiddenRow (A B : Set qc.Target)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) :=
  GluingDefect.hiddenZRow _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) (local_bijective M laws ha A B hA hB)
/-- 局所J零から生成された標準hidden/Z短完全列。 -/
theorem localHiddenRow_shortExact (A B : Set qc.Target)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) :
    (localHiddenRow M laws ha A B hA hB).ShortExact :=
  GluingDefect.hiddenZRow_shortExact _ _ (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) (local_bijective M laws ha A B hA hB)

/-- 同じ実全Lawの実Law H¹実余核を中間項とするQ比較余核/Z短複体。 -/
def oldHiddenRow (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) : ShortComplex (ModuleCat.{u} ℚ) :=
  ShortComplex.mk ((localHiddenRow M laws ha A B hA hB).f ≫ (LawGluing.hiddenEquiv M laws ha A B hc).symm.toModuleIso.hom)
    ((LawGluing.hiddenEquiv M laws ha A B hc).toModuleIso.hom ≫ (localHiddenRow M laws ha A B hA hB).g) (by
      rw [Category.assoc, ← Category.assoc (LawGluing.hiddenEquiv M laws ha A B hc).symm.toModuleIso.hom,
        show (LawGluing.hiddenEquiv M laws ha A B hc).symm.toModuleIso.hom ≫ (LawGluing.hiddenEquiv M laws ha A B hc).toModuleIso.hom = 𝟙 _ from
          (LawGluing.hiddenEquiv M laws ha A B hc).toModuleIso.inv_hom_id, Category.id_comp]
      exact (localHiddenRow M laws ha A B hA hB).zero)
/-- 中間項の実商同型に沿い両端項と両射を保つ短複体同型。 -/
def oldHiddenRowIso (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) :
    localHiddenRow M laws ha A B hA hB ≅ oldHiddenRow M laws ha A B hc hA hB :=
  ShortComplex.isoMk (Iso.refl _) (LawGluing.hiddenEquiv M laws ha A B hc).symm.toModuleIso (Iso.refl _)
    (by simp only [oldHiddenRow, Iso.refl_hom, Category.id_comp])
    (by simp only [oldHiddenRow, Iso.refl_hom, Category.comp_id, ← Category.assoc,
      show (LawGluing.hiddenEquiv M laws ha A B hc).symm.toModuleIso.hom ≫ (LawGluing.hiddenEquiv M laws ha A B hc).toModuleIso.hom = 𝟙 _ from
        (LawGluing.hiddenEquiv M laws ha A B hc).toModuleIso.inv_hom_id]
        erw [Category.id_comp])
/-- GOAL Dの実全Lawの実hiddenと実Zの短完全列。 -/
theorem oldHiddenRow_shortExact (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) :
    (oldHiddenRow M laws ha A B hc hA hB).ShortExact :=
  ShortComplex.shortExact_of_iso (oldHiddenRowIso M laws ha A B hc hA hB) (localHiddenRow_shortExact M laws ha A B hA hB)

/-- 実hiddenへの包含は同じ細δ包含の商代表元。 -/
theorem oldHiddenRow_f_mk (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0))
    (z : QuotientKernelRow.Q (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)) :
    (oldHiddenRow M laws ha A B hc hA hB).f
      ((LinearMap.range (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))).mkQ z) =
      (LawGluing.hiddenEquiv M laws ha A B hc).symm ((LinearMap.range (homologyMap (LawGluing.comparison M laws ha A B).τ₁ (1:ℤ)).hom).mkQ
        (QuotientKernelRow.inclusion (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) z)) := by
  change (LawGluing.hiddenEquiv M laws ha A B hc).symm (GluingDefect.fourth (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) _) = _
  exact congrArg (LawGluing.hiddenEquiv M laws ha A B hc).symm (GluingDefect.fourth_mk
    (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) z)

/-- 実hiddenからZへの射は同じ細制限・局所逆比較・粗差制限の代表式。 -/
theorem oldHiddenRow_g_mk (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0))
    (y : (Nf.lawGeneratedComplex laws (LawGluing.fine_adequate (h := h) laws ha)).H1) :
    ((oldHiddenRow M laws ha A B hc hA hB).g ((LinearMap.range (M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha))).mkQ y)).val =
      homologyMap (LawGluing.coarseRow (Nc := Nc) laws ha A B).g 1
        ((QuotientKernelRow.localEquiv (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B)
          (local_bijective M laws ha A B hA hB)).symm
            (homologyMap (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B).f 1 (LawGluing.fineH1Equiv (Nf := Nf) laws ha A B hc y))) := by
  change (GluingDefect.hiddenZProjection (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B)
    (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B) (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B)
    (local_bijective M laws ha A B hA hB)
    (LawGluing.hiddenEquiv M laws ha A B hc ((LinearMap.range (M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha))).mkQ y))).val = _
  rw [LawGluing.hiddenEquiv_mk, GluingDefect.hiddenZProjection_mk]

/-- GOAL Dの同じ実全Lawの実二成分J次元式。一般SESと局所比較は原始入力と局所J零から放電済み。 -/
theorem defect_dimension (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) :
    blockDefect (M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha)) =
      (Module.finrank ℚ (LinearMap.ker (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))),
       Module.finrank ℚ (QuotientKernelRow.Q (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) ⧸
         LinearMap.range (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))) +
       Module.finrank ℚ (QuotientKernelRow.Z (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B))) := by
  rw [defect_standard M laws ha A B hc]
  letI : ∀ l : LawValueLabel laws, FiniteDimensional ℚ
      ((LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₁.homology (1:ℤ)) := fun l => by
    change FiniteDimensional ℚ ((zeroExtension _).homology (1:ℤ))
    infer_instance
  letI : FiniteDimensional ℚ ((LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B).X₁.homology (1:ℤ)) :=
    FiniteDimensional.of_injective (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₁) 1).toLinearMap
      (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₁) 1).injective
  exact GluingDefect.defect_dimension (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) (local_bijective M laws ha A B hA hB)

/-- GOAL Dの同じ実全LawのJ零は実q全単射かつ実Z零と同値。交差比較同型は追加しない。 -/
theorem defect_zero_iff (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (hA : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelA laws ha A l)).h1Map = (0,0))
    (hB : ∀ l, blockDefect (M.aSubnerveComparisonHom (LawGluing.labelB laws ha B l)).h1Map = (0,0)) :
    blockDefect (M.generatedComparisonH1Map laws ha (LawGluing.fine_adequate (h := h) laws ha)) = (0,0) ↔
      Function.Bijective (QuotientKernelRow.q (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B)) ∧
        QuotientKernelRow.Z (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.comparison M laws ha A B) = ⊥ := by
  rw [defect_standard M laws ha A B hc]
  letI : ∀ l : LawValueLabel laws, FiniteDimensional ℚ
      ((LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₁.homology (1:ℤ)) := fun l => by
    change FiniteDimensional ℚ ((zeroExtension _).homology (1:ℤ))
    infer_instance
  letI : FiniteDimensional ℚ ((LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B).X₁.homology (1:ℤ)) :=
    FiniteDimensional.of_injective (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₁) 1).toLinearMap
      (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₁) 1).injective
  letI : ∀ l : LawValueLabel laws, FiniteDimensional ℚ
      ((LawGluing.coarseLabelRow (Nc := Nc) laws ha A B l).X₃.homology (0:ℤ)) := fun l => by
    change FiniteDimensional ℚ ((zeroExtension _).homology (0:ℤ))
    infer_instance
  letI : FiniteDimensional ℚ ((LawGluing.coarseRow (Nc := Nc) laws ha A B).X₃.homology (0:ℤ)) :=
    FiniteDimensional.of_injective (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.coarseLabelRow (Nc := Nc) laws ha A B l).X₃) 0).toLinearMap
      (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.coarseLabelRow (Nc := Nc) laws ha A B l).X₃) 0).injective
  letI : ∀ l : LawValueLabel laws, FiniteDimensional ℚ
      ((LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₃.homology (0:ℤ)) := fun l => by
    change FiniteDimensional ℚ ((zeroExtension _).homology (0:ℤ))
    infer_instance
  letI : FiniteDimensional ℚ ((LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B).X₃.homology (0:ℤ)) :=
    FiniteDimensional.of_injective (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₃) 0).toLinearMap
      (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₃) 0).injective
  letI : ∀ l : LawValueLabel laws, FiniteDimensional ℚ
      ((LawGluing.coarseLabelRow (Nc := Nc) laws ha A B l).X₃.homology (1:ℤ)) := fun l => by
    change FiniteDimensional ℚ ((zeroExtension _).homology (1:ℤ))
    infer_instance
  letI : FiniteDimensional ℚ ((LawGluing.coarseRow (Nc := Nc) laws ha A B).X₃.homology (1:ℤ)) :=
    FiniteDimensional.of_injective (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.coarseLabelRow (Nc := Nc) laws ha A B l).X₃) 1).toLinearMap
      (FiniteComplexFamily.homologyEquiv (fun l : LawValueLabel laws => (LawGluing.coarseLabelRow (Nc := Nc) laws ha A B l).X₃) 1).injective
  exact GluingDefect.defect_zero_iff (LawGluing.coarseRow (Nc := Nc) laws ha A B) (LawGluing.fineRow (h := h) (Nf := Nf) laws ha A B) (LawGluing.coarseRow_shortExact (Nc := Nc) laws ha A B)
    (LawGluing.fineRow_shortExact (h := h) (Nf := Nf) laws ha A B) (LawGluing.comparison M laws ha A B) (local_bijective M laws ha A B hA hB)
end AAT.AG.AtlasGluingWidth.LawDefect
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.LawDefect
