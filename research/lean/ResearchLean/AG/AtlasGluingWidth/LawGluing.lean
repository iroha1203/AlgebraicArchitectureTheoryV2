import ResearchLean.AG.AtlasGluingWidth.FiniteGluing
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonFiberDiagnostics
import ResearchLean.AG.AtlasDefectComposition.FiniteConeFamily
import Formal.Util.AssertStandardAxioms
/-! # 原始二領域貼り合わせから同じ実Lawへの有限ラベル和

GOAL D／設計exact-sequence §5。幾何の後に任意粗adequateLawと任意A/Bを量化する。
細adequacyは粗adequacyとreading順序から生成し、各発生値ラベルのfiberと二領域を交差する。
Implementation notes: G134の全Law零延長squareと生成blockの全chain同定を使う。
有限族は発生ラベルそのものを添字とし、同じ支持の異なるラベルを同一視しない。
同次元の別Law空間へ置換する案、H¹squareだけで全chain同定を済ませる案は退けた。
-/
noncomputable section
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasGluingWidth.LawGluing
open AAT.AG.CanonicalResolution AAT.AG.ResolutionInvariance AAT.AG.TwoPhase
open AAT.AG.AtlasDefectComposition AAT.AG.FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
/-- 同じ選択セル全体の等号に沿う全次数零延長同型。 -/
def selectionZeroExtensionIso {q : Reading Source} {N : TargetSupportedNerve q}
    (S T : CellSelection N) (he : S = T) : zeroExtension T.complex ≅ zeroExtension S.complex :=
  (eqToIso (congrArg (fun R => zeroExtension R.complex) he)).symm
/-- 元の全比較Homは選択等号による全chain同定を保つ。 -/
theorem selection_zeroExtension_natural {Sc Sc' : CellSelection Nc} {Sf Sf' : CellSelection Nf}
    (hs : SelectionCompatible M Sc Sf) (hc : Sc = Sc') (hf : Sf = Sf') :
    zeroExtensionMap (AtlasMayerVietoris.selectionHomCongr M hs hc hf) ≫
        (selectionZeroExtensionIso Sf Sf' hf).hom =
      (selectionZeroExtensionIso Sc Sc' hc).hom ≫ zeroExtensionMap hs.hom := by
  subst Sc'
  subst Sf'
  rw [AtlasMayerVietoris.selectionHomCongr_eq M hs rfl rfl hs]
  simp only [selectionZeroExtensionIso,eqToIso_refl,Iso.refl_symm,Iso.refl_hom,
    Category.comp_id,Category.id_comp]
/-- 通常領域和の複体を同じ真のセル和の複体へ移す全次数同型。 -/
def unionZeroExtensionIso {q : Reading Source} (N : TargetSupportedNerve q) (A B : Set q.Target) :
    zeroExtension (N.targetSubsetComplex (A ∪ B)) ≅
      (PrimitiveGluing.coarseRow (Nc := N) A B).X₁ :=
  selectionZeroExtensionIso _ _ (PrimitiveGluing.coarse_union_eq (Nc := N) A B)
/-- 通常領域和と真のセル和の同定は同じ原始Mの全比較で可換。 -/
theorem union_zeroExtension_natural (A B : Set qc.Target) :
    zeroExtensionMap (M.aSubnerveComparisonHom (A ∪ B)) ≫
      (unionZeroExtensionIso Nf (comparisonFactor qc qf h ⁻¹' A)
        (comparisonFactor qc qf h ⁻¹' B)).hom =
    (unionZeroExtensionIso Nc A B).hom ≫ (PrimitiveGluing.comparison M A B).τ₁ := by
  rw [← AtlasMayerVietoris.regionUnionHom_eq M A B]
  exact selection_zeroExtension_natural M
    ((SelectionCompatible.region M A).union M (SelectionCompatible.region M B))
    (PrimitiveGluing.coarse_union_eq (Nc := Nc) A B) (PrimitiveGluing.fine_union_eq (h := h) (Nf := Nf) A B)

variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
omit [Fintype Source] in
include h ha in
/-- 粗adequacyとreading順序から同じLawの細adequacyを生成する。 -/
theorem fine_adequate : laws.Adequate qf := adequate_of_coarser laws h ha
/-- 各発生ラベルに対する元のAとその値fiberの交差。 -/
def labelA (A : Set qc.Target) (l : LawValueLabel laws) : Set qc.Target :=
  A ∩ labelValueFiber laws qc ha l
/-- 各発生ラベルに対する元のBとその値fiberの交差。 -/
def labelB (B : Set qc.Target) (l : LawValueLabel laws) : Set qc.Target :=
  B ∩ labelValueFiber laws qc ha l
omit [Fintype Source] in
/-- 各fiberを覆うなら同じ二交差領域の和が元のfiberそのもの。 -/
theorem fiber_union (A B : Set qc.Target)
    (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) (l : LawValueLabel laws) :
    labelValueFiber laws qc ha l = labelA laws ha A l ∪ labelB laws ha B l := by
  ext t
  constructor
  · intro ht
    rcases hc l ht with htA | htB
    · exact Or.inl ⟨htA,ht⟩
    · exact Or.inr ⟨htB,ht⟩
  · rintro (ht | ht)
    · exact ht.2
    · exact ht.2
omit [Fintype Source] in
/-- 同じ細fiberは同じ粗fiber領域和のcanonical逆像である。 -/
theorem fine_fiber_union (A B : Set qc.Target)
    (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) (l : LawValueLabel laws) :
    labelValueFiber laws qf (fine_adequate (h := h) laws ha) l =
      comparisonFactor qc qf h ⁻¹' (labelA laws ha A l ∪ labelB laws ha B l) := by
  rw [labelValueFiber_eq_preimage laws qc qf ha (fine_adequate (h := h) laws ha) h l,
    fiber_union laws ha A B hc l]
/-- 各labelの粗二領域の真のセルSES。 -/
def coarseLabelRow (A B : Set qc.Target) (l : LawValueLabel laws) :=
  PrimitiveGluing.coarseRow (Nc := Nc) (labelA laws ha A l) (labelB laws ha B l)
/-- 各labelの細逆像二領域の真のセルSES。 -/
def fineLabelRow (A B : Set qc.Target) (l : LawValueLabel laws) :=
  PrimitiveGluing.fineRow (h := h) (Nf := Nf) (labelA laws ha A l) (labelB laws ha B l)
/-- 各labelの同じ原始比較による二行図式。 -/
def labelComparison (A B : Set qc.Target) (l : LawValueLabel laws) :
    coarseLabelRow (Nc := Nc) laws ha A B l ⟶ fineLabelRow (h := h) (Nf := Nf) laws ha A B l :=
  PrimitiveGluing.comparison M (labelA laws ha A l) (labelB laws ha B l)
/-- 全発生ラベルの粗cochain短複体を元の成分から作る。 -/
def coarseRow (A B : Set qc.Target) := FiniteGluing.row (coarseLabelRow (Nc := Nc) laws ha A B)
/-- 全発生ラベルの細cochain短複体を元の成分から作る。 -/
def fineRow (A B : Set qc.Target) := FiniteGluing.row (fineLabelRow (h := h) (Nf := Nf) laws ha A B)
omit [Fintype Source] in
/-- 原始入力から全labelの粗SESを生成する。 -/
theorem coarseRow_shortExact (A B : Set qc.Target) : (coarseRow (Nc := Nc) laws ha A B).ShortExact :=
  FiniteGluing.row_shortExact _ (fun _ => StandardRow.cellRow_shortExact _ _)
omit [Fintype Source] in
/-- 原始入力から全labelの細SESを生成する。 -/
theorem fineRow_shortExact (A B : Set qc.Target) : (fineRow (h := h) (Nf := Nf) laws ha A B).ShortExact :=
  FiniteGluing.row_shortExact _ (fun _ => StandardRow.cellRow_shortExact _ _)
/-- 全labelの原始二行比較を同じ族の三射へ集める。 -/
def comparison (A B : Set qc.Target) :
    coarseRow (Nc := Nc) laws ha A B ⟶ fineRow (h := h) (Nf := Nf) laws ha A B :=
  FiniteGluing.rowMap _ (labelComparison M laws ha A B)
omit [Fintype Source] in
/-- 各labelの実Q/H¹/PのSESは追加完全性引数を要さない。 -/
theorem label_qp_shortExact (A B : Set qc.Target) (l : LawValueLabel laws) :
    (QuotientKernelRow.row (coarseLabelRow (Nc := Nc) laws ha A B l)
      (StandardRow.cellRow_shortExact _ _)).ShortExact ∧
    (QuotientKernelRow.row (fineLabelRow (h := h) (Nf := Nf) laws ha A B l)
      (StandardRow.cellRow_shortExact _ _)).ShortExact :=
  ⟨QuotientKernelRow.row_shortExact _ _,QuotientKernelRow.row_shortExact _ _⟩

/-- 粗生成label-blockを同じfiber領域和の真のセル複体へ移す。 -/
def coarseBlockIso (A B : Set qc.Target)
    (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) (l : LawValueLabel laws) :
    zeroExtension (Nc.lawValueBlockComplex laws ha l) ≅ (coarseLabelRow (Nc := Nc) laws ha A B l).X₁ :=
  FaceRelationSubdivision.lawBlockSelectedSubsetZeroExtensionIso Nc laws ha l _ (fiber_union laws ha A B hc l) ≪≫
    unionZeroExtensionIso Nc _ _
/-- 細生成label-blockを同じ二領域逆像の真のセル複体へ移す。 -/
def fineBlockIso (A B : Set qc.Target)
    (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) (l : LawValueLabel laws) :
    zeroExtension (Nf.lawValueBlockComplex laws (fine_adequate (h := h) laws ha) l) ≅
      (fineLabelRow (h := h) (Nf := Nf) laws ha A B l).X₁ :=
  FaceRelationSubdivision.lawBlockSelectedSubsetZeroExtensionIso Nf laws (fine_adequate (h := h) laws ha) l _
    (fine_fiber_union laws ha A B hc l) ≪≫
    selectionZeroExtensionIso _ _ (PrimitiveGluing.fine_union_eq (h := h) (Nf := Nf)
      (labelA laws ha A l) (labelB laws ha B l))
/-- 各labelの同じ生成block比較と真のセル和比較は全chainで可換。 -/
theorem block_natural (A B : Set qc.Target)
    (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) (l : LawValueLabel laws) :
    zeroExtensionMap (M.generatedBlockComparisonHom laws ha (fine_adequate (h := h) laws ha) l) ≫
      (fineBlockIso (Nf := Nf) laws ha A B hc l).hom =
    (coarseBlockIso (Nc := Nc) laws ha A B hc l).hom ≫ (labelComparison M laws ha A B l).τ₁ := by
  simp only [fineBlockIso,coarseBlockIso,Iso.trans_hom]
  rw [← Category.assoc,FaceRelationSubdivision.lawBlockSelectedSubsetZeroExtensionIso_natural,
    Category.assoc]
  exact congrArg (fun f => (FaceRelationSubdivision.lawBlockSelectedSubsetZeroExtensionIso Nc laws ha l _
    (fiber_union laws ha A B hc l)).hom ≫ f)
    (union_zeroExtension_natural M (labelA laws ha A l) (labelB laws ha B l))
/-- 同じ全Law粗複体を全labelの真のセル和複体へ移す全次数同型。 -/
def coarseLawIso (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    zeroExtension (Nc.lawGeneratedComplex laws ha) ≅ (coarseRow (Nc := Nc) laws ha A B).X₁ :=
  lawZeroExtensionIso Nc laws ha ≪≫ FiniteComplexFamily.iso _ _ (coarseBlockIso (Nc := Nc) laws ha A B hc)
/-- 同じ全Law細複体を全labelの真のセル和複体へ移す全次数同型。 -/
def fineLawIso (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    zeroExtension (Nf.lawGeneratedComplex laws (fine_adequate (h := h) laws ha)) ≅
      (fineRow (h := h) (Nf := Nf) laws ha A B).X₁ :=
  lawZeroExtensionIso Nf laws (fine_adequate (h := h) laws ha) ≪≫
    FiniteComplexFamily.iso _ _ (fineBlockIso (Nf := Nf) laws ha A B hc)
/-- G134の同じ実generatedLawHomを全整数次数のlabel族比較へ同定する。 -/
theorem law_natural (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    zeroExtensionMap (M.generatedComparisonHom laws ha (fine_adequate (h := h) laws ha)) ≫
      (fineLawIso (Nf := Nf) laws ha A B hc).hom =
    (coarseLawIso (Nc := Nc) laws ha A B hc).hom ≫ (comparison M laws ha A B).τ₁ := by
  simp only [coarseLawIso,fineLawIso,Iso.trans_hom]
  rw [← Category.assoc,M.lawZeroExtension_square laws ha (fine_adequate (h := h) laws ha),Category.assoc,
    FiniteComplexFamily.iso_natural _ _ _ _ _ _ (block_natural M laws ha A B hc)]
  simp only [Category.assoc]
  rfl
/-- 同じ旧全Law粗H¹を全ラベル真セル和の標準H¹へ移す。 -/
def coarseH1Equiv (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    (Nc.lawGeneratedComplex laws ha).H1 ≃ₗ[ℚ] (coarseRow (Nc := Nc) laws ha A B).X₁.homology (1:ℤ) :=
  (oldH1Equiv _).trans (homologyMapIso (coarseLawIso (Nc := Nc) laws ha A B hc) 1).toLinearEquiv
/-- 同じ旧全Law細H¹を全ラベル真セル和の標準H¹へ移す。 -/
def fineH1Equiv (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    (Nf.lawGeneratedComplex laws (fine_adequate (h := h) laws ha)).H1 ≃ₗ[ℚ]
      (fineRow (h := h) (Nf := Nf) laws ha A B).X₁.homology (1:ℤ) :=
  (oldH1Equiv _).trans (homologyMapIso (fineLawIso (Nf := Nf) laws ha A B hc) 1).toLinearEquiv
/-- 実generatedLaw旧H¹比較は同じ全label合併H¹比較と可換する。 -/
theorem h1_natural (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (x : (Nc.lawGeneratedComplex laws ha).H1) :
    fineH1Equiv (Nf := Nf) laws ha A B hc
      (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha) x) =
    homologyMap (comparison M laws ha A B).τ₁ 1 (coarseH1Equiv (Nc := Nc) laws ha A B hc x) := by
  have hs := congrArg (fun f => homologyMap f (1:ℤ)) (law_natural M laws ha A B hc)
  simp only [homologyMap_comp] at hs
  have hx := congrArg (fun f => f (oldH1Equiv _ x)) hs
  simp only [ModuleCat.comp_apply] at hx
  change homologyMap (fineLawIso (Nf := Nf) laws ha A B hc).hom 1
      (oldH1Equiv _ ((M.generatedComparisonHom laws ha (fine_adequate (h := h) laws ha)).h1Map x)) = _
  rw [oldH1Equiv_natural]
  exact hx
/-- 実全Law比較の同じ核から全label真セル和比較核への同型。 -/
def phantomEquiv (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    LinearMap.ker (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha)) ≃ₗ[ℚ]
      GluingDefect.Phantom (coarseRow (Nc := Nc) laws ha A B) (fineRow (h := h) (Nf := Nf) laws ha A B)
        (comparison M laws ha A B) :=
  LinearConjugation.kernelEquiv _ _ (coarseH1Equiv (Nc := Nc) laws ha A B hc)
    (fineH1Equiv (Nf := Nf) laws ha A B hc) (h1_natural M laws ha A B hc)
/-- 実全Law比較の同じ余核から全label真セル和比較余核への同型。 -/
def hiddenEquiv (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    ((Nf.lawGeneratedComplex laws (fine_adequate (h := h) laws ha)).H1 ⧸
      LinearMap.range (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha))) ≃ₗ[ℚ]
      GluingDefect.Hidden (coarseRow (Nc := Nc) laws ha A B) (fineRow (h := h) (Nf := Nf) laws ha A B)
        (comparison M laws ha A B) :=
  LinearConjugation.cokernelEquiv _ _ (coarseH1Equiv (Nc := Nc) laws ha A B hc)
    (fineH1Equiv (Nf := Nf) laws ha A B hc) (h1_natural M laws ha A B hc)
/-- 実Law核の同定は同じ粗旧H¹classを読む。 -/
@[simp] theorem phantomEquiv_val (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (x : LinearMap.ker (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha))) :
    (phantomEquiv M laws ha A B hc x).val = coarseH1Equiv (Nc := Nc) laws ha A B hc x.val := rfl
/-- 実Law余核の同定は同じ細旧H¹全商代表元を読む。 -/
@[simp] theorem hiddenEquiv_mk (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (x : (Nf.lawGeneratedComplex laws (fine_adequate (h := h) laws ha)).H1) :
    hiddenEquiv M laws ha A B hc
      ((LinearMap.range (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha))).mkQ x) =
      (LinearMap.range (homologyMap (comparison M laws ha A B).τ₁ 1).hom).mkQ
        (fineH1Equiv (Nf := Nf) laws ha A B hc x) := rfl
/-- 同じ実Lawphantomを全発生ラベルの実phantomへ同定する。 -/
def phantomFamilyEquiv (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :=
  (phantomEquiv M laws ha A B hc).trans
    (FiniteGluing.phantomEquiv _ (labelComparison M laws ha A B))
/-- 同じ実Lawhiddenを全発生ラベルの実hiddenへ同定する。 -/
def hiddenFamilyEquiv (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :=
  (hiddenEquiv M laws ha A B hc).trans
    (FiniteGluing.hiddenEquiv _ (labelComparison M laws ha A B))
/-- 核族の元は実粗Lawclassの同じ各label標準H¹を読む。 -/
@[simp] theorem phantomFamilyEquiv_val (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (x : LinearMap.ker (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha)))
    (l : LawValueLabel laws) :
    (phantomFamilyEquiv M laws ha A B hc x l).val =
      FiniteComplexFamily.homologyEquiv _ 1 (coarseH1Equiv (Nc := Nc) laws ha A B hc x.val) l := rfl
/-- 余核族の代表元は実細Lawclassの同じ各label商を読む。 -/
@[simp] theorem hiddenFamilyEquiv_mk (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (x : (Nf.lawGeneratedComplex laws (fine_adequate (h := h) laws ha)).H1) (l : LawValueLabel laws) :
    hiddenFamilyEquiv M laws ha A B hc
      ((LinearMap.range (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha))).mkQ x) l =
      (LinearMap.range (homologyMap (labelComparison M laws ha A B l).τ₁ 1).hom).mkQ
        (FiniteComplexFamily.homologyEquiv _ 1 (fineH1Equiv (Nf := Nf) laws ha A B hc x) l) := rfl
/-- 元の全Law欠損はG134の同じ実fiber部分集合欠損の重複込みの和である。 -/
theorem defect_subset_sum : blockDefect (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha)) =
    (∑ l, (blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l)).h1Map).1,
     ∑ l, (blockDefect (M.aSubnerveComparisonHom (labelValueFiber laws qc ha l)).h1Map).2) :=
  lawH1Defect_subset_sum Nc Nf laws ha M (fine_adequate (h := h) laws ha)
/-- 各labelのA–C欠損は同じ実全Law欠損の重複込みの有限和である。 -/
theorem defect_gluing_sum (A B : Set qc.Target)
    (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    blockDefect (M.generatedComparisonH1Map laws ha (fine_adequate (h := h) laws ha)) =
      (∑ l, (blockDefect (homologyMap (labelComparison M laws ha A B l).τ₁ (1:ℤ)).hom).1,
       ∑ l, (blockDefect (homologyMap (labelComparison M laws ha A B l).τ₁ (1:ℤ)).hom).2) := by
  rw [defect_subset_sum M laws ha]
  apply Prod.ext
  · apply Finset.sum_congr rfl
    intro l _
    have he := PrimitiveGluing.defect_standard M (labelA laws ha A l) (labelB laws ha B l)
    rw [← fiber_union laws ha A B hc l] at he
    exact congrArg Prod.fst he
  · apply Finset.sum_congr rfl
    intro l _
    have he := PrimitiveGluing.defect_standard M (labelA laws ha A l) (labelB laws ha B l)
    rw [← fiber_union laws ha A B hc l] at he
    exact congrArg Prod.snd he
/-- 同じ実Law標準錐から全label真セル和比較の標準錐への同型。 -/
def lawConeIso (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha (fine_adequate (h := h) laws ha))) ≅
      mappingCone (comparison M laws ha A B).τ₁ :=
  coneMapIso _ _ (coarseLawIso (Nc := Nc) laws ha A B hc) (fineLawIso (Nf := Nf) laws ha A B hc)
    (law_natural M laws ha A B hc)
/-- 全labelの実二領域錐直和SESを同じ有限族へ集めた短複体。 -/
def coneRow (A B : Set qc.Target) :=
  FiniteGluing.row (fun l : LawValueLabel laws => AtlasMayerVietoris.coneBiprodRow M
    (SelectionCompatible.region M (labelA laws ha A l)) (SelectionCompatible.region M (labelB laws ha B l)))
omit [Fintype Source] in
/-- 全labelの錐SESを原始生成定理から放電する。 -/
theorem coneRow_shortExact (A B : Set qc.Target) : (coneRow M laws ha A B).ShortExact :=
  FiniteGluing.row_shortExact _ (fun _ => AtlasMayerVietoris.coneBiprodRow_shortExact M _ _)
/-- 同じ全Law錐を全labelの同じ真セル和錐へ移す。 -/
def lawConeFamilyIso (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha (fine_adequate (h := h) laws ha))) ≅
      (coneRow M laws ha A B).X₁ :=
  lawConeIso M laws ha A B hc ≪≫ FiniteConeFamily.iso (fun l => (labelComparison M laws ha A B l).τ₁)
/-- 元の全Law錐を重複込みの標準有限直和へ移す。 -/
def lawConeDirectSumIso (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :=
  lawConeFamilyIso M laws ha A B hc ≪≫ FiniteComplexFamily.directSumIso _
/-- 同じ全Law錐の全整数次数homologyを各同じ合併錐homologyへ移す。 -/
def lawConeHomologyEquiv (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) (m : ℤ) :=
  (homologyMapIso (lawConeFamilyIso M laws ha A B hc) m).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ m)
omit [Fintype Source] in
/-- 全発生labelの二領域合併錐族のMayer–Vietoris列は全整数次数で完全。
全Law標準錐への被覆下の同定とLESはactualCone_lesが担う。 -/
theorem cone_les (A B : Set qc.Target) (m : ℤ) :
    Function.Exact (homologyMap (coneRow M laws ha A B).f m) (homologyMap (coneRow M laws ha A B).g m) ∧
    Function.Exact (homologyMap (coneRow M laws ha A B).g m)
      (StandardLES.connecting (coneRow M laws ha A B) (coneRow_shortExact M laws ha A B) m) ∧
    Function.Exact (StandardLES.connecting (coneRow M laws ha A B) (coneRow_shortExact M laws ha A B) m)
      (homologyMap (coneRow M laws ha A B).f (m+1)) :=
  ⟨StandardLES.exact_middle _ (coneRow_shortExact M laws ha A B) m,
    StandardLES.exact_before _ _ m,StandardLES.exact_after _ _ m⟩
/-- 合併項を元の実generatedLaw標準錐に戻した短複体。 -/
def actualConeRow (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :=
  ShortComplex.mk ((lawConeFamilyIso M laws ha A B hc).hom ≫ (coneRow M laws ha A B).f)
    (coneRow M laws ha A B).g (by
      rw [Category.assoc, (coneRow M laws ha A B).zero, comp_zero])
/-- 元の全Law錐の実射と有限label錐SESを両端・中間射ごと保つ同型。 -/
def actualConeRowIso (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    coneRow M laws ha A B ≅ actualConeRow M laws ha A B hc :=
  ShortComplex.isoMk (lawConeFamilyIso M laws ha A B hc).symm (Iso.refl _) (Iso.refl _)
    (by simp only [actualConeRow, Iso.symm_hom, Iso.refl_hom, Category.comp_id,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp])
    (by simp only [actualConeRow, Iso.refl_hom, Category.id_comp, Category.comp_id])
/-- 実全Law錐を合併項とするSESを原始成分から生成する。 -/
theorem actualConeRow_shortExact (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) :
    (actualConeRow M laws ha A B hc).ShortExact :=
  ShortComplex.shortExact_of_iso (actualConeRowIso M laws ha A B hc)
    (coneRow_shortExact M laws ha A B)
/-- 同じ実Law錐の全整数次数の三位置完全性。 -/
theorem actualCone_les (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) (m : ℤ) :
    Function.Exact (homologyMap (actualConeRow M laws ha A B hc).f m)
      (homologyMap (actualConeRow M laws ha A B hc).g m) ∧
    Function.Exact (homologyMap (actualConeRow M laws ha A B hc).g m)
      (StandardLES.connecting (actualConeRow M laws ha A B hc) (actualConeRow_shortExact M laws ha A B hc) m) ∧
    Function.Exact (StandardLES.connecting (actualConeRow M laws ha A B hc) (actualConeRow_shortExact M laws ha A B hc) m)
      (homologyMap (actualConeRow M laws ha A B hc).f (m+1)) :=
  ⟨StandardLES.exact_middle _ (actualConeRow_shortExact M laws ha A B hc) m,
    StandardLES.exact_before _ _ m, StandardLES.exact_after _ _ m⟩
/-- 同じ実Law錐への標準δは同じlabel錐族δの輸送そのものであり符号を保つ。 -/
theorem actualCone_connecting_natural (A B : Set qc.Target)
    (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B) (m : ℤ) :
    StandardLES.connecting (coneRow M laws ha A B) (coneRow_shortExact M laws ha A B) m ≫
      homologyMap (lawConeFamilyIso M laws ha A B hc).inv (m+1) =
      StandardLES.connecting (actualConeRow M laws ha A B hc)
        (actualConeRow_shortExact M laws ha A B hc) m := by
  have hn := HomologySequence.δ_naturality (actualConeRowIso M laws ha A B hc).hom
    (coneRow_shortExact M laws ha A B) (actualConeRow_shortExact M laws ha A B hc) m (m+1) rfl
  change _ = homologyMap (𝟙 _) m ≫ _ at hn
  simpa only [homologyMap_id, Category.id_comp] using hn
/-- 任意実交差錐cocycleから持ち上げ・微分・実Law錐への貼り合わせを生成する。 -/
theorem actualCone_lift (A B : Set qc.Target) (hc : ∀ l, labelValueFiber laws qc ha l ⊆ A ∪ B)
    (m : ℤ) (z : (actualConeRow M laws ha A B hc).X₃.X m)
    (hz : (actualConeRow M laws ha A B hc).X₃.d m (m+1) z = 0) :
    ∃ (p : (actualConeRow M laws ha A B hc).X₂.X m)
      (w : (actualConeRow M laws ha A B hc).X₁.X (m+1)),
      (actualConeRow M laws ha A B hc).g.f m p = z ∧
      (actualConeRow M laws ha A B hc).f.f (m+1) w =
        (actualConeRow M laws ha A B hc).X₂.d m (m+1) p ∧
      ∃ hwc : (actualConeRow M laws ha A B hc).X₁.d (m+1) (m+1+1) w = 0,
        StandardLES.connecting (actualConeRow M laws ha A B hc)
          (actualConeRow_shortExact M laws ha A B hc) m
          (CohomologyRepresentatives.cycleClass _ m z hz) =
            CohomologyRepresentatives.cycleClass _ (m+1) w hwc := by
  obtain ⟨p,w,hp,hw,hwc⟩ := CohomologyRepresentatives.lift_cocycle _
    (actualConeRow_shortExact M laws ha A B hc) m z hz
  exact ⟨p,w,hp,hw,hwc,CohomologyRepresentatives.connecting_cycleClass _
    (actualConeRow_shortExact M laws ha A B hc) m z hz p hp w hw hwc⟩
end AAT.AG.AtlasGluingWidth.LawGluing
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.LawGluing
