import ResearchLean.AG.AtlasGluingWidth.WidthObservation
import ResearchLean.AG.UniformInvariance.IndicatorLawFamily
import Formal.Util.AssertStandardAxioms

/-! # 同じ全低幅Law族と定数Lawによる検出

幅は全発生ラベルの概念fiberのcardinalityで測る。空Lawも含め、全Law商を
既存の実fiber族同定へ戻す。指定定数Lawは同じSource上の一ラベルである。

## Implementation notes

全発生labelを既存の実Law商とfiber族同型で読む。同じ台を持つlabelを
まとめる代替は、その多重度を消すため採らない。indicatorのfalse値も同じSourceから生成する。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance AtlasDefectComposition FaceRelationSubdivision
variable (n : ℕ) [NeZero n]

omit [NeZero n] in
/-- 粗adequacyから同じSource上の細adequacyを生成する。 -/
theorem fineAdequate (laws : FiniteLawFamily (Source n)) (ha : laws.Adequate (coarseReading n)) :
    laws.Adequate (fineReading n) :=
  adequate_of_coarser laws (coarser n) ha
/-- 同じ全Law実H¹比較。 -/
abbrev lawMap (cut : Bool) (laws : FiniteLawFamily (Source n))
    (ha : laws.Adequate (coarseReading n)) :=
  (comparison n cut).generatedComparisonH1Map laws ha (fineAdequate n laws ha)
/-- 粗全Law商は全発生fiberの実零H¹から零となる。 -/
theorem coarse_law_H1_zero (laws : FiniteLawFamily (Source n))
    (ha : laws.Adequate (coarseReading n)) :
    Subsingleton ((coarse n).lawGeneratedComplex laws ha).H1 := by
  letI : ∀ l : LawValueLabel laws,
    Subsingleton ((coarse n).targetSubsetComplex (labelValueFiber laws (coarseReading n) ha l)).H1 :=
    fun l => coarse_H1_zero n _
  exact (lawFiberH1FamilyEquiv (coarse n) laws ha).injective.subsingleton
/-- 各fiberが真部分集合なら、同じ細全Law実商も零。 -/
theorem fine_law_H1_zero (cut : Bool) (laws : FiniteLawFamily (Source n))
    (ha : laws.Adequate (coarseReading n))
    (hw : ∀ l, labelValueFiber laws (coarseReading n) ha l ≠ Set.univ) :
    Subsingleton ((fine n cut).lawGeneratedComplex laws (fineAdequate n laws ha)).H1 := by
  letI : ∀ l : LawValueLabel laws, Subsingleton ((fine n cut).targetSubsetComplex
    (labelValueFiber laws (fineReading n) (fineAdequate n laws ha) l)).H1 := fun l => by
      rw [labelValueFiber_eq_preimage laws (coarseReading n) (fineReading n) ha
        (fineAdequate n laws ha) (coarser n) l]
      exact proper_actual_H1_zero n cut _ (hw l)
  exact (lawFiberH1FamilyEquiv (fine n cut) laws (fineAdequate n laws ha)).injective.subsingleton
/-- plusは幅制限によらず同じ全Law実商が零。 -/
theorem plus_law_H1_zero (laws : FiniteLawFamily (Source n))
    (ha : laws.Adequate (coarseReading n)) :
    Subsingleton ((fine n true).lawGeneratedComplex laws (fineAdequate n laws ha)).H1 := by
  letI : ∀ l : LawValueLabel laws, Subsingleton ((fine n true).targetSubsetComplex
    (labelValueFiber laws (fineReading n) (fineAdequate n laws ha) l)).H1 := fun l => by
      rw [labelValueFiber_eq_preimage laws (coarseReading n) (fineReading n) ha
        (fineAdequate n laws ha) (coarser n) l]
      exact plus_actual_H1_zero n _
  exact (lawFiberH1FamilyEquiv (fine n true) laws (fineAdequate n laws ha)).injective.subsingleton
/-- plusの同じ全Law実Jは常に零。 -/
theorem plus_law_defect (laws : FiniteLawFamily (Source n))
    (ha : laws.Adequate (coarseReading n)) : blockDefect (lawMap n true laws ha) = (0, 0) := by
  letI := coarse_law_H1_zero n laws ha
  letI := plus_law_H1_zero n laws ha
  rw [defect_zero_domain, Module.finrank_zero_of_subsingleton]
/-- 全発生labelが幅k以下である同じLaw族の細商は零。 -/
theorem width_law_H1_zero (k : ℕ) (cut : Bool) (laws : FiniteLawFamily (Source (size k)))
    (ha : laws.Adequate (coarseReading (size k)))
    (hw : ∀ l, (labelValueFiber laws (coarseReading (size k)) ha l).ncard ≤ k) :
    Subsingleton ((fine (size k) cut).lawGeneratedComplex laws (fineAdequate (size k) laws ha)).H1 :=
  fine_law_H1_zero (size k) cut laws ha (fun l => low_proper k _ (hw l))
/-- 同じ低幅Lawの細実H¹零空間の明示同型。 -/
def width_law_equiv (k : ℕ) (laws : FiniteLawFamily (Source (size k)))
    (ha : laws.Adequate (coarseReading (size k)))
    (hw : ∀ l, (labelValueFiber laws (coarseReading (size k)) ha l).ncard ≤ k) :
    ((fine (size k) true).lawGeneratedComplex laws (fineAdequate (size k) laws ha)).H1 ≃ₗ[ℚ]
      ((fine (size k) false).lawGeneratedComplex laws (fineAdequate (size k) laws ha)).H1 := by
  letI := width_law_H1_zero k true laws ha hw
  letI := width_law_H1_zero k false laws ha hw
  exact LinearEquiv.ofSubsingleton _ _
/-- 全低幅Lawの同じgenerated H¹比較は明示同型により可換。 -/
theorem width_law_square (k : ℕ) (laws : FiniteLawFamily (Source (size k)))
    (ha : laws.Adequate (coarseReading (size k)))
    (hw : ∀ l, (labelValueFiber laws (coarseReading (size k)) ha l).ncard ≤ k)
    (x : ((coarse (size k)).lawGeneratedComplex laws ha).H1) :
    width_law_equiv k laws ha hw (lawMap (size k) true laws ha x) = lawMap (size k) false laws ha x := by
  letI := width_law_H1_zero k false laws ha hw
  exact Subsingleton.elim _ _
/-- 任意の全低幅Lawは両側の同じ実J零を持つ。 -/
theorem width_law_defect (k : ℕ) (cut : Bool) (laws : FiniteLawFamily (Source (size k)))
    (ha : laws.Adequate (coarseReading (size k)))
    (hw : ∀ l, (labelValueFiber laws (coarseReading (size k)) ha l).ncard ≤ k) :
    blockDefect (lawMap (size k) cut laws ha) = (0, 0) := by
  letI := coarse_law_H1_zero (size k) laws ha
  letI := width_law_H1_zero k cut laws ha hw
  rw [defect_zero_domain, Module.finrank_zero_of_subsingleton]

/-- 同じSource上の指定定数Law。 -/
def constantLaw : FiniteLawFamily (Source n) where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Unit
  valueDecidableEq _ := inferInstance
  eval _ _ := ()
omit [NeZero n] in
/-- 定数Lawの粗adequacyは指定評価から構成する。 -/
theorem constantAdequate : (constantLaw n).Adequate (coarseReading n) :=
  fun _ => ⟨fun _ => (), fun _ => rfl⟩
/-- 定数Lawの唯一の発生labelを同じSourceから作る。 -/
def constantLabel : LawValueLabel (constantLaw n) :=
  LawValueLabel.ofSource (constantLaw n) () (0, false)
/-- 定数Lawの値とlawが同じなら発生点によらず同じlabel。 -/
instance constantLabelsUnique : Unique (LawValueLabel (constantLaw n)) where
  default := constantLabel n
  uniq l := by cases l with | mk law value h => cases law; cases value; apply LawValueLabel.ext <;> rfl
omit [NeZero n] in
/-- 唯一の粗値クラスは全概念集合。 -/
theorem constantFiber (l : LawValueLabel (constantLaw n)) :
    labelValueFiber (constantLaw n) (coarseReading n) (constantAdequate n) l = Set.univ := by
  ext c
  simp only [Set.mem_univ, iff_true]
  change lawDescend (constantLaw n) (coarseReading n) (constantAdequate n) l.law c = l.value
  letI : Subsingleton ((constantLaw n).Value l.law) := inferInstanceAs (Subsingleton Unit)
  exact Subsingleton.elim _ _
/-- 同じ実定数Law比較はplusで零欠損。 -/
theorem constant_plus_defect :
    blockDefect (lawMap n true (constantLaw n) (constantAdequate n)) = (0, 0) :=
  plus_law_defect n _ _
/-- 同じ実定数Law比較はminusで(0,1)。 -/
theorem constant_minus_defect :
    blockDefect (lawMap n false (constantLaw n) (constantAdequate n)) = (0, 1) := by
  rw [FaceRelationSubdivision.lawH1Defect_subset_sum]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [constantFiber]
  change ((blockDefect (actualMap n false Set.univ)).1,
    (blockDefect (actualMap n false Set.univ)).2) = (0, 1)
  rw [full_defect]

/-- 同じ指定indicator Lawを既存生成APIから作る。 -/
abbrev indicator (X : Set (Concept n)) := indicatorLawFamily (coarseReading n) X
omit [NeZero n] in
/-- 指定indicatorの粗adequacyはfstによる評価の因子化。 -/
theorem indicatorAdequate (X : Set (Concept n)) :
    (indicator n X).Adequate (coarseReading n) := indicatorLawFamily_adequate (coarseReading n) X
omit [NeZero n] in
/-- 全発生indicator値クラスはtrueでX、falseで補集合。 -/
theorem indicatorFiber (X : Set (Concept n)) (l : LawValueLabel (indicator n X)) :
    labelValueFiber (indicator n X) (coarseReading n) (indicatorAdequate n X) l =
      if l.value.down then X else Xᶜ := by
  classical
  rcases l with ⟨law, ⟨b⟩, hg⟩
  cases law
  ext c
  rw [mem_labelValueFiber, indicatorLawFamily_lawDescend_eq]
  cases b <;> by_cases hc : c ∈ X <;> simp [targetSubsetIndicator, hc]
    <;> intro he <;> cases congrArg ULift.down he
/-- 非空補集合のfalse値も同じSourceから発生する。 -/
def indicatorFalseLabel (X : Set (Concept n)) (hX : Xᶜ.Nonempty) :
    LawValueLabel (indicator n X) := by
  classical
  let c := Classical.choose hX
  have hc : c ∉ X := Classical.choose_spec hX
  refine ⟨PUnit.unit, ULift.up false, (c, false), ?_⟩
  simp [indicator, indicatorLawFamily_eval, targetSubsetIndicator, hc]
/-- 非空Xのtrue値は既存生成labelで発生する。 -/
abbrev indicatorTrueLabel (X : Set (Concept n)) (hX : X.Nonempty) :=
  indicatorLawFamilyTrueLabel (coarseReading n) X hX
omit [NeZero n] in
/-- 指定falseラベルの値。 -/
theorem indicatorFalseLabel_value (X : Set (Concept n)) (hX : Xᶜ.Nonempty) :
    (indicatorFalseLabel n X hX).value = ULift.up false := by
  rfl
omit [NeZero n] in
/-- 補集合値クラスも正確に元の補集合である。 -/
theorem indicatorFalseFiber (X : Set (Concept n)) (hX : Xᶜ.Nonempty) :
    labelValueFiber (indicator n X) (coarseReading n) (indicatorAdequate n X)
      (indicatorFalseLabel n X hX) = Xᶜ := by
  rw [indicatorFiber, indicatorFalseLabel_value]
  rfl
/-- k≥1では指定n=k+1。 -/
theorem size_positive (k : ℕ) (hk : 0 < k) : size k = k + 1 := by
  exact Nat.max_eq_right (by omega)
/-- 非自明indicatorの全発生クラスは、補集合も含め幅k以下。 -/
theorem indicator_width (k : ℕ) (hk : 0 < k) (X : Set (Concept (size k)))
    (hpos : 0 < X.ncard) (hproper : X.ncard < size k) :
    ∀ l : LawValueLabel (indicator (size k) X),
      (labelValueFiber (indicator (size k) X) (coarseReading (size k))
        (indicatorAdequate (size k) X) l).ncard ≤ k := by
  have hc : X.ncard + Xᶜ.ncard = size k := by
    simpa [Concept, Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl X
  have hn := size_positive k hk
  intro l
  rw [indicatorFiber]
  split <;> omega
/-- 空Xまたは全Xのindicatorの発生クラスは全Cであり低幅に入らない。 -/
theorem indicator_endpoint_fiber (k : ℕ) (X : Set (Concept (size k)))
    (hX : X = ∅ ∨ X = Set.univ) (l : LawValueLabel (indicator (size k) X)) :
    labelValueFiber (indicator (size k) X) (coarseReading (size k))
      (indicatorAdequate (size k) X) l = Set.univ := by
  have hn := labelValueFiber_nonempty (indicator (size k) X) (coarseReading (size k))
    (indicatorAdequate (size k) X) l
  rw [indicatorFiber] at hn ⊢
  rcases hX with rfl | rfl <;> cases hb : l.value.down <;> simp_all
/-- 空/全indicatorの唯一発生クラスの幅はkより大きい。 -/
theorem indicator_endpoint_not_width (k : ℕ) (X : Set (Concept (size k)))
    (hX : X = ∅ ∨ X = Set.univ) (l : LawValueLabel (indicator (size k) X)) :
    k < (labelValueFiber (indicator (size k) X) (coarseReading (size k))
      (indicatorAdequate (size k) X) l).ncard := by
  rw [indicator_endpoint_fiber k X hX l]
  simpa [Concept] using size_gt k
/-- 幅0の同じ粗adequate Law族は空Law族しかない。 -/
theorem width_zero_laws_empty (laws : FiniteLawFamily (Source (size 0)))
    (ha : laws.Adequate (coarseReading (size 0)))
    (hw : ∀ l, (labelValueFiber laws (coarseReading (size 0)) ha l).ncard ≤ 0) :
    IsEmpty laws.Law := by
  refine ⟨fun law => ?_⟩
  let l := LawValueLabel.ofSource laws law (0, false)
  have hp := (labelValueFiber_nonempty laws (coarseReading (size 0)) ha l).ncard_pos
  have hz := hw l
  omega

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
