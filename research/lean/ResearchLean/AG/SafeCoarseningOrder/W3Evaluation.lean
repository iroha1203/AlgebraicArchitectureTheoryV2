import ResearchLean.AG.SafeCoarseningOrder.W3Comparison
import ResearchLean.AG.SafeCoarseningOrder.FiniteClassification
import ResearchLean.AG.AtlasGluingWidth.WidthCoefficient

/-! # W3 の全領域診断と同じ hidden 類

指定Rのplus/proper/full実診断を有限判定へ入力し、同じMV類をG-135のfiber項へ接続する。

## Implementation notes

全AをtargetEquivの画像と逆像で尽くす。既存proper/full/plusと同じMV類を実比較同定に沿い再利用し、全幅成果を新規計上しない。数値Jだけでhidden類を取り替える代替は採らない。
-/
set_option maxHeartbeats 1200000
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W3
open CanonicalResolution ResolutionInvariance TwoPhase AtlasGluingWidth AtlasDefectComposition

/-- plus全領域Jを同じ旧plus_defectから(0,0)と評価する。 -/
theorem plus_defect (X : Set (Width.Concept 2)) :
    blockDefect (((input true).quotientComparison coarsening).aSubnerveComparisonHom
      (region X)).h1Map = (0,0) := by
  rw [actual_defect,Width.plus_defect]
/-- minusの全真部分領域Jを同じ旧proper_defectから(0,0)と評価する。 -/
theorem proper_defect (X : Set (Width.Concept 2)) (hX : X ≠ Set.univ) :
    blockDefect (((input false).quotientComparison coarsening).aSubnerveComparisonHom
      (region X)).h1Map = (0,0) := by
  rw [actual_defect,Width.proper_defect 2 X hX]
/-- minus全領域Jを同じ旧full_defectから(0,1)と評価する。 -/
theorem full_defect :
    blockDefect (((input false).quotientComparison coarsening).aSubnerveComparisonHom
      (region Set.univ)).h1Map = (0,1) := by
  rw [actual_defect,Width.full_defect]
/-- 商targetの任意領域を元領域の逆像として尽くす。空も含む。 -/
theorem region_surjective (A : Set (Quotient coarsening.1)) :
    region (targetEquiv '' A) = A := Set.preimage_image_eq _ targetEquiv.injective
/-- plus指定Rは全A実比較を保存する。領域同定から全Aを尽くす。 -/
theorem plus_safe : (input true).Safe coarsening := by
  apply (PrimitiveInput.safe_iff_zeroDefect _ _).mpr
  intro A
  rw [← region_surjective A]
  exact plus_defect _
/-- 元商targetの全真部分領域でminusの同じ実比較はJ零。 -/
theorem proper_actual_defects (A : Set (Quotient coarsening.1)) (hA : A ≠ Set.univ) :
    blockDefect (((input false).quotientComparison coarsening).aSubnerveComparisonHom A).h1Map = (0,0) := by
  have hx : targetEquiv '' A ≠ Set.univ := by
    intro h
    apply hA
    rw [← region_surjective A,h]
    exact Set.preimage_univ
  rw [← region_surjective A]
  exact proper_defect _ hx
/-- 同じ元商targetのfullは実余核欠損一を返す。 -/
theorem full_actual_defect :
    blockDefect (((input false).quotientComparison coarsening).aSubnerveComparisonHom
      Set.univ).h1Map = (0,1) := full_defect
/-- minus指定Rはfullの同じ実余核欠損により不安全。 -/
theorem minus_not_safe : ¬ (input false).Safe coarsening := by
  intro h
  have hh := (PrimitiveInput.safe_iff_zeroDefect _ _).mp h (region Set.univ)
  rw [full_defect] at hh
  exact Nat.one_ne_zero (congrArg Prod.snd hh)
/-- 指定Rを全粗化有限構成へ入力する。 -/
theorem candidate_mem_all : coarsening ∈ (allCoarsenings : Finset (Coarsening Point Chart)) :=
  mem_allCoarsenings _
/-- 全安全有限表は同じplus指定Rを含む。 -/
theorem plus_mem_safe : coarsening ∈ (input true).safeCoarsenings :=
  ((input true).mem_safeCoarsenings coarsening).mpr plus_safe
/-- 全安全有限表は同じminus指定Rを含まない。 -/
theorem minus_not_mem_safe : coarsening ∉ (input false).safeCoarsenings :=
  fun h => minus_not_safe (((input false).mem_safeCoarsenings coarsening).mp h)
/-- 全A有理行列判定は同じplus比較の保存を返す。 -/
theorem plus_decision_true :
    AtlasCoefficientFiber.allAPreservationDecision ((input true).quotientComparison coarsening) = true :=
  (PrimitiveInput.safe_iff_decision _ _).mp plus_safe
/-- 全A有理行列判定は同じminus比較の失敗を返す。 -/
theorem minus_decision_false :
    AtlasCoefficientFiber.allAPreservationDecision ((input false).quotientComparison coarsening) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact minus_not_safe ((PrimitiveInput.safe_iff_decision _ _).mpr h)
/-- 元G136二領域の和。分割のjoinと区別する。 -/
abbrev gluingRegion : Set (Width.Concept 2) := Width.regionA 2 ∪ Width.regionB 2
/-- 同じ旧MV類を元セル生成fine同型の逆で新実H¹へ戻す。 -/
def gluingFineClass (z : Bool → ℚ) :=
  (actualFineCochainEquiv false gluingRegion).h1Equiv.symm
    (Width.gluingOldClass 2 (by decide) z)
/-- 同じ新実比較のliteral余核へ元MV類を入れる。 -/
def gluingHiddenClass (z : Bool → ℚ) :=
  (LinearMap.range (((input false).quotientComparison coarsening).aSubnerveComparisonHom
    (region gluingRegion)).h1Map).mkQ (gluingFineClass z)
/-- gluingFineClassの基本API。同じ元MV類へ細セル同型で戻る。 -/
theorem gluing_fine_same (z : Bool → ℚ) :
    (actualFineCochainEquiv false gluingRegion).h1Equiv (gluingFineClass z) =
      Width.gluingOldClass 2 (by decide) z := LinearEquiv.apply_symm_apply _ _
/-- gluingHiddenClassの基本API。同じ実比較の商へ元代表を入れる。 -/
theorem gluingHiddenClass_eq_mk (z : Bool → ℚ) :
    gluingHiddenClass z =
      (LinearMap.range (((input false).quotientComparison coarsening).aSubnerveComparisonHom
        (region gluingRegion)).h1Map).mkQ (gluingFineClass z) := rfl
/-- 旧指定hiddenのliteral商代表への接続API。既存類を取り替えない。 -/
theorem old_hiddenClass_eq_mk (z : Bool → ℚ) :
    Width.gluingHiddenClass 2 (by decide) z =
      (LinearMap.range (Width.actualMap 2 false gluingRegion)).mkQ
        (Width.gluingOldClass 2 (by decide) z) := rfl
/-- 新literal余核の指定類は同じ旧gluingHiddenClassへ写る。 -/
theorem gluing_hidden_same (z : Bool → ℚ) :
    actualCokernelEquiv false gluingRegion (gluingHiddenClass z) =
      Width.gluingHiddenClass 2 (by decide) z := by
  rw [gluingHiddenClass_eq_mk,actualCokernelEquiv_mk,gluing_fine_same,
    old_hiddenClass_eq_mk]
/-- 旧非零hidden類と実余核同型から新指定類の非零性を導く。 -/
theorem gluing_hidden_nonzero : gluingHiddenClass (fun b => if b then 1 else 0) ≠ 0 := by
  intro h
  have hh := congrArg (actualCokernelEquiv false gluingRegion) h
  rw [gluing_hidden_same] at hh
  exact Width.gluing_hidden_nonzero 2 (by decide)
    (hh.trans (actualCokernelEquiv false gluingRegion).map_zero)
/-- 新指定hidden類を同じ旧係数列とG135 fiberRestrictionH1の元類へ接続する。 -/
theorem coefficient_hidden_same (z : Bool → ℚ) :
    ((AtlasGluingWidth.CoefficientBridge.oldCoefficientRow (Width.comparison 2 false)
      gluingRegion).g (actualCokernelEquiv false gluingRegion (gluingHiddenClass z))).val =
      AtlasCoefficientFiber.fiberRestrictionH1 (Width.comparison 2 false) gluingRegion
        (oldH1Equiv _ (Width.gluingOldClass 2 (by decide) z)) := by
  rw [gluing_hidden_same]
  exact Width.coefficient_hidden_same 2 (by decide) z

end AAT.AG.SafeCoarseningOrder.W3
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
