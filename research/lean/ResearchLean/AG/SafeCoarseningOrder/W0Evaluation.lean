import ResearchLean.AG.SafeCoarseningOrder.FixedSelectionInstances
/-! # E W0 の全候補・定数Law評価

指定一辺・Unit reading・全支持入力を同じ有限判定へ通す。

## Implementation notes

元Sourceに定数Lawを一つ明示し全商readingへdescendさせる。
全候補の実H¹/Jは受理済み単一辺比較から導き、答えを入力fieldに置かない。
最大元は同じtrueで一般producerを発火させ、元topとの等号を示す。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W0Evaluation
open CanonicalResolution ResolutionInvariance TwoPhase
/-- W0 の一つの定数Law。 -/
def constantLaw : FiniteLawFamily Unit where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Unit
  valueDecidableEq _ := inferInstance
  eval _ _ := ()
/-- constantLawの元評価は指定Unit値。定義の基本評価API。 -/
@[simp] theorem constant_eval (l : constantLaw.Law) (v : Unit) :
    constantLaw.eval l v = () := rfl
/-- 元商の全readingに指定定数値をdescendさせる。 -/
theorem constant_adequate (R : Coarsening Unit Bool) :
    constantLaw.Adequate (w0.quotientReading R) :=
  fun _ => ⟨fun _ => (),fun _ => rfl⟩
/-- 元Sourceで生成した唯一の発生label。 -/
def constantLabel : LawValueLabel constantLaw := LawValueLabel.ofSource constantLaw () ()
/-- 一定Lawのlabelは一つ。 -/
instance constantLabelsUnique : Unique (LawValueLabel constantLaw) where
  default := constantLabel
  uniq l := by cases l with | mk law value h => cases law; cases value; apply LawValueLabel.ext <;> rfl
/-- 指定唯一labelの値blockは元商target全体。 -/
theorem constant_fiber (R : Coarsening Unit Bool) (l : LawValueLabel constantLaw) :
    labelValueFiber constantLaw (w0.quotientReading R) (constant_adequate R) l = Set.univ := by
  ext c
  simp only [Set.mem_univ,iff_true]
  rw [mem_labelValueFiber]
  letI : Subsingleton (constantLaw.Value l.law) := inferInstanceAs (Subsingleton Unit)
  exact Subsingleton.elim _ _
/-- 同じ全A実比較のJを全候補で評価する。 -/
theorem all_actual_defects (R : Coarsening Unit Bool) (A : Set (Quotient R.1)) :
    blockDefect ((w0.quotientComparison R).aSubnerveComparisonHom A).h1Map = (0,0) :=
  (w0.safe_iff_zeroDefect R).mp (w0_safe R) A
/-- 同じ定数Lawの実H¹射。 -/
def lawMap (R : Coarsening Unit Bool) :=
  (w0.quotientMorphism R).generatedComparisonH1Map constantLaw (constant_adequate R)
    (AtlasDefectComposition.adequate_of_coarser constantLaw (w0.quotient_coarser R)
      (constant_adequate R))
/-- lawMapの基本API。同じ元generatedComparisonH1Mapを保持する。 -/
theorem lawMap_eq (R : Coarsening Unit Bool) :
    lawMap R =
      (w0.quotientMorphism R).generatedComparisonH1Map constantLaw (constant_adequate R)
        (AtlasDefectComposition.adequate_of_coarser constantLaw (w0.quotient_coarser R)
          (constant_adequate R)) := rfl
/-- 全候補の同じ定数Law射は実全単射。 -/
theorem law_bijective (R : Coarsening Unit Bool) : Function.Bijective (lawMap R) := by
  rw [lawMap_eq]
  exact (w0.safe_iff_laws R).mp (w0_safe R) constantLaw (constant_adequate R)
/-- 全候補の同じ定数Law診断は零。 -/
theorem law_defect (R : Coarsening Unit Bool) : blockDefect (lawMap R) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (law_bijective R)
/-- 指定全候補が同じSafe有限表に属する。 -/
theorem safeCoarsenings_eq_all : w0.safeCoarsenings = allCoarsenings := by
  classical
  apply Finset.ext
  intro R
  rw [w0.mem_safeCoarsenings]
  exact ⟨fun _ => mem_allCoarsenings _, fun _ => w0_safe _⟩
/-- 同じtrueから生成したB最大元出力。 -/
def greatestOutput : w0.GreatestWitness := w0.greatestWitness w0_greatestDecision
/-- 生成した出力は指定全関係そのもの。 -/
theorem greatestOutput_top : greatestOutput.coarsening = ⊤ :=
  greatestOutput.greatest.unique w0_greatest
/-- 全W0安全対のjoinは安全。 -/
theorem join_closure (R Q : Coarsening Unit Bool) (hR : w0.Safe R) (hQ : w0.Safe Q) :
    w0.Safe (R ⊔ Q) :=
  w0.joinDecision_eq_true.mp w0_joinDecision R Q hR hQ
/-- 同じtrueから生成した全Aut固定極大のB出力。 -/
def fixedOutput : w0.FixedMaximalWitness := w0GeneratedFixedOutput
/-- 生成固定出力も指定の元topである。 -/
theorem fixedOutput_top : fixedOutput.coarsening = ⊤ := w0GeneratedFixedOutput_eq_top
/-- 指定最大元は全原始Autで固定される。 -/
theorem top_fixed (a : PrimitiveIso w0 w0) : a.coarseningOrderIso ⊤ = ⊤ := w0_top_fixed a
/-- 指定定数Lawは一発生labelを保持する。 -/
theorem constant_labels_card : Fintype.card (LawValueLabel constantLaw) = 1 :=
  Fintype.card_unique
/-- W0の全候補を同じ全A有理行列判定へ入力するとtrueを返す。 -/
theorem all_decision_true (R : Coarsening Unit Bool) :
    AtlasCoefficientFiber.allAPreservationDecision (w0.quotientComparison R) = true :=
  (w0.safe_iff_decision R).mp (w0_safe R)
end AAT.AG.SafeCoarseningOrder.W0Evaluation

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
