import ResearchLean.AG.RelativeRepairComposition.W3OrdinarySeams
import ResearchLean.AG.RelativeRepairComposition.W3Classes

/-! # Whole actual W3 comparison with the restricted ordinary diagram

Every independent unrestricted repair gives the original seam (v,-u).
Every original gauge label gives actual local arrows (-b_s,-b_t). The
comparison is full, faithful and essentially surjective on the whole comma.
-/
namespace AAT.AG.RelativeRepairComposition.W3OrdinaryComparison
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3AuthoredOperations
open W3ActualRepairs W3GaugeLabels W3GaugeAction W3ActualArrows W3Classes
open W3LocalRepairs W3LocalLabels W3RestrictionDiagram W3OrdinarySeams
attribute [local instance] actualAction localAction

/-- The actual original seam keeps both complete corrections of the unrestricted repair. -/
noncomputable def comparisonObject {sheared : Bool} (R : ActualCategory sheared candidates) :
    Ordinary sheared := seamObject sheared ((parameters R.back).2,-(parameters R.back).1)

/-- Each entire original gauge label gives the two full local arrows satisfying the actual comma square. -/
noncomputable def comparisonMap {sheared : Bool} {R Q : ActualCategory sheared candidates}
    (f : R ⟶ Q) : comparisonObject R ⟶ comparisonObject Q where
  left := leftArrow sheared (leftLabel sheared (-f.1.toAdd.1 vertexS))
  right := rightArrow sheared (rightLabel sheared (-f.1.toAdd.1 vertexT))
  w := by
    apply (square_iff _ _ _ _).mpr
    apply Prod.ext
    · change (parameters Q.back).2 + (-f.1.toAdd.1 vertexS) =
        linearAction sheared (-f.1.toAdd.1 vertexT) + (parameters R.back).2
      rw [← hom_second f, map_neg]
      abel_nf
    · change -(parameters Q.back).1 + (-f.1.toAdd.1 vertexS) =
        -f.1.toAdd.1 vertexT + (-(parameters R.back).1)
      rw [← hom_first f]
      abel_nf

/-- The comparison maps every independent original repair and every full actual gauge arrow. -/
noncomputable def comparisonFunctor (sheared : Bool) :
    ActualCategory sheared candidates ⥤ Ordinary sheared where
  obj := comparisonObject
  map := comparisonMap
  map_id R := by
    apply Comma.hom_ext
    · apply Subtype.ext
      apply Multiplicative.toAdd.injective
      apply (leftLabelEquiv sheared).injective
      exact neg_zero
    · apply Subtype.ext
      apply Multiplicative.toAdd.injective
      apply (rightLabelEquiv sheared).injective
      exact neg_zero
  map_comp f g := by
    apply Comma.hom_ext
    · apply Subtype.ext
      apply Multiplicative.toAdd.injective
      apply (leftLabelEquiv sheared).injective
      exact neg_add _ _
    · apply Subtype.ext
      apply Multiplicative.toAdd.injective
      apply (rightLabelEquiv sheared).injective
      exact neg_add _ _

/-- Every compatible actual ordinary arrow restores its complete original global label. -/
theorem comparison_full (sheared : Bool) : (comparisonFunctor sheared).Full where
  map_surjective := by
    intro R Q f
    let l := leftLabelEquiv sheared f.left.1.toAdd
    let r := rightLabelEquiv sheared f.right.1.toAdd
    let b := unrestrictedLabel sheared (-l) (-r)
    have h := hom_square f
    have h1 : (parameters Q.back).2 + l =
        linearAction sheared r + (parameters R.back).2 := congrArg Prod.fst h
    have h2 : -(parameters Q.back).1 + l = r + (-(parameters R.back).1) := congrArg Prod.snd h
    have hb : b +ᵥ R.back = Q.back := by
      apply (gauge_eq_iff_parameters sheared candidates b R.back Q.back).mpr
      constructor
      · rw [unrestricted_source, unrestricted_target]
        calc
          (parameters R.back).1 + (-r) - (-l) = -(r + (-(parameters R.back).1)) + l := by abel_nf
          _ = -(-(parameters Q.back).1 + l) + l := by rw [← h2]
          _ = (parameters Q.back).1 := by abel_nf
      · rw [unrestricted_source, unrestricted_target, map_neg]
        calc
          (parameters R.back).2 + (-l) - (-linearAction sheared r) =
              linearAction sheared r + (parameters R.back).2 - l := by abel_nf
          _ = (parameters Q.back).2 := (eq_sub_of_add_eq h1).symm
    refine ⟨⟨Multiplicative.ofAdd b,hb⟩, ?_⟩
    apply Comma.hom_ext
    · apply Subtype.ext
      apply Multiplicative.toAdd.injective
      apply (leftLabelEquiv sheared).injective
      exact neg_neg l
    · apply Subtype.ext
      apply Multiplicative.toAdd.injective
      apply (rightLabelEquiv sheared).injective
      exact neg_neg r

/-- No full original gauge label is identified by the ordinary comparison. -/
theorem comparison_faithful (sheared : Bool) : (comparisonFunctor sheared).Faithful where
  map_injective := by
    intro R Q f g h
    have hl := congrArg (fun k => leftLabelEquiv sheared k.left.1.toAdd) h
    have hr := congrArg (fun k => rightLabelEquiv sheared k.right.1.toAdd) h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply (unrestrictedLabelEquiv sheared).injective
    apply Prod.ext
    · exact neg_injective hl
    · exact neg_injective hr

/-- Every original actual ordinary object and compatible arrow is in the complete comparison. -/
noncomputable def comparisonEquivalence (sheared : Bool) :
    ActualCategory sheared candidates ≌ Ordinary sheared := by
  let F := comparisonFunctor sheared
  letI : F.Full := comparison_full sheared
  letI : F.Faithful := comparison_faithful sheared
  letI : F.EssSurj := {
    mem_essImage := by
      intro D
      let p : Parameters := (-(seam D).2,(seam D).1)
      let R : ActualCategory sheared candidates := (unrestrictedParametersEquiv sheared).symm p
      have hp : parameters R.back = p := (unrestrictedParametersEquiv sheared).apply_symm_apply p
      refine ⟨R, ⟨eqToIso ?_⟩⟩
      apply (objectEquiv sheared).injective
      change ((parameters R.back).2,-(parameters R.back).1) = seam D
      rw [hp]
      exact Prod.ext rfl (neg_neg _) }
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

/-- Forward U arrows retain the full original source label with the stated sign. -/
theorem comparison_source {sheared : Bool} {R Q : ActualCategory sheared candidates} (f : R ⟶ Q) :
    leftLabelEquiv sheared ((comparisonFunctor sheared).map f).left.1.toAdd =
      -f.1.toAdd.1 vertexS := rfl

/-- Forward V arrows retain the full original target label with the stated sign. -/
theorem comparison_target {sheared : Bool} {R Q : ActualCategory sheared candidates} (f : R ⟶ Q) :
    rightLabelEquiv sheared ((comparisonFunctor sheared).map f).right.1.toAdd =
      -f.1.toAdd.1 vertexT := rfl

end AAT.AG.RelativeRepairComposition.W3OrdinaryComparison
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3OrdinaryComparison
