import ResearchLean.AG.DoctrineFiberProduct.ExactBottomCoverageSchema

/-!
# G-112 exact-bottom coverage closure

This module proves the branch-independent, anchor-relative closure obligations.
The witness producers below use the finite presentations stored in the operand
anchors and arrows.  They do not recover output witnesses by applying
`ExactBottomCoverageRegime.covers` to a separately proved membership fact.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory CategoryTheory.Limits AtomFoundation

/-- Membership together with the generated anchored witness at one output. -/
structure ExactBottomCoverageClosureResult {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (regime : ExactBottomCoverageRegime U)
    (input : CartSemanticInput U) where
  membership : regime.Holds input
  witness : AnchoredCoverageWitness input

/--
The pullback closure output keeps one generated pullback anchor shared by both
projection witnesses.
-/
structure ExactBottomPullbackClosureResult {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (regime : ExactBottomCoverageRegime U)
    (cospan : SharedBaseAnchorCospan (U := U)) where
  object_anchor : CoveredObjectWitness
    (pointedPullback cospan.first cospan.second)
  fst_membership : regime.Holds cospan.pullbackFstInput
  snd_membership : regime.Holds cospan.pullbackSndInput
  fst_arrow : CoverageWitnessOver cospan.pullbackFstInput object_anchor
    cospan.leftAnchor
  snd_arrow : CoverageWitnessOver cospan.pullbackSndInput object_anchor
    cospan.rightAnchor

/-- Identity membership is derived from the named regime branch. -/
theorem exact_bottom_identity_membership {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (regime : ExactBottomCoverageRegime U)
    (object : ExtractionInstance U) (anchor : CoveredObjectWitness object) :
    regime.Holds (cartSemanticInputOfHom (𝟙 object)) := by
  rcases regime with ⟨artifact⟩
  cases artifact with
  | global _ => trivial
  | characterized proof =>
      exact proof.qualification.identity_mem U object anchor

/-- Composition membership is derived from the named regime branch. -/
theorem exact_bottom_composition_membership {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (regime : ExactBottomCoverageRegime U)
    (pair : SharedAnchorComposablePair (U := U))
    (firstMembership : regime.Holds pair.firstInput)
    (secondMembership : regime.Holds pair.secondInput) :
    regime.Holds pair.compositeInput := by
  rcases regime with ⟨artifact⟩
  cases artifact with
  | global _ => trivial
  | characterized proof =>
      exact proof.qualification.comp_mem U pair firstMembership secondMembership

/-- First pullback-projection membership is derived from the named branch. -/
theorem exact_bottom_pullback_fst_membership {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (regime : ExactBottomCoverageRegime U)
    (cospan : SharedBaseAnchorCospan (U := U))
    (firstMembership : regime.Holds cospan.firstInput)
    (secondMembership : regime.Holds cospan.secondInput) :
    regime.Holds cospan.pullbackFstInput := by
  rcases regime with ⟨artifact⟩
  cases artifact with
  | global _ => trivial
  | characterized proof =>
      exact proof.qualification.pullback_fst_mem U cospan
        firstMembership secondMembership

/-- Second pullback-projection membership is derived from the named branch. -/
theorem exact_bottom_pullback_snd_membership {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (regime : ExactBottomCoverageRegime U)
    (cospan : SharedBaseAnchorCospan (U := U))
    (firstMembership : regime.Holds cospan.firstInput)
    (secondMembership : regime.Holds cospan.secondInput) :
    regime.Holds cospan.pullbackSndInput := by
  rcases regime with ⟨artifact⟩
  cases artifact with
  | global _ => trivial
  | characterized proof =>
      exact proof.qualification.pullback_snd_mem U cospan
        firstMembership secondMembership

/-- The typed identity presentation decodes to the categorical identity. -/
@[simp]
theorem to_semantic_cart_id_typed_presentation_hom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (code : FiniteInstanceCode U) :
    (toSemanticCart (idTypedPresentation code).toPresentation).hom =
      𝟙 code.toSemantic := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · exact AtomPermutationCode.toEquiv_refl

/-- Construct the anchored identity witness from the supplied object anchor. -/
def exact_bottom_identity_closure {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (regime : ExactBottomCoverageRegime U)
    (object : ExtractionInstance U) (anchor : CoveredObjectWitness object) :
    ExactBottomCoverageClosureResult regime
      (cartSemanticInputOfHom (𝟙 object)) where
  membership := exact_bottom_identity_membership regime object anchor
  witness :=
    { sourceAnchor := anchor
      targetAnchor := anchor
      arrow :=
        { presentation := idTypedPresentation anchor.code
          square :=
            { sourceIso := anchor.iso
              targetIso := anchor.iso
              hom_comm := by
                change anchor.iso.hom ≫ 𝟙 object =
                  (toSemanticCart
                    (idTypedPresentation anchor.code).toPresentation).hom ≫
                    anchor.iso.hom
                rw [to_semantic_cart_id_typed_presentation_hom]
                exact (Category.id_comp _).symm }
          sourceIso_eq := rfl
          targetIso_eq := rfl } }

/--
Construct the anchored composite from the two operand presentations and their
shared middle anchor.
-/
def exact_bottom_composition_closure {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (regime : ExactBottomCoverageRegime U)
    (pair : SharedAnchorComposablePair (U := U))
    (firstMembership : regime.Holds pair.firstInput)
    (secondMembership : regime.Holds pair.secondInput) :
    ExactBottomCoverageClosureResult regime pair.compositeInput := by
  have hfirst := pair.firstArrow.square.hom_comm
  rw [pair.firstArrow.sourceIso_eq,
    pair.firstArrow.targetIso_eq] at hfirst
  change pair.sourceAnchor.iso.hom ≫ pair.first =
    (toSemanticCart pair.firstArrow.presentation.toPresentation).hom ≫
      pair.middleAnchor.iso.hom at hfirst
  have hsecond := pair.secondArrow.square.hom_comm
  rw [pair.secondArrow.sourceIso_eq,
    pair.secondArrow.targetIso_eq] at hsecond
  change pair.middleAnchor.iso.hom ≫ pair.second =
    (toSemanticCart pair.secondArrow.presentation.toPresentation).hom ≫
      pair.targetAnchor.iso.hom at hsecond
  refine
    { membership := exact_bottom_composition_membership regime pair
        firstMembership secondMembership
      witness :=
        { sourceAnchor := pair.sourceAnchor
          targetAnchor := pair.targetAnchor
          arrow :=
            { presentation := compPresentation pair.firstArrow.presentation
                pair.secondArrow.presentation
              square :=
                { sourceIso := pair.sourceAnchor.iso
                  targetIso := pair.targetAnchor.iso
                  hom_comm := ?_ }
              sourceIso_eq := rfl
              targetIso_eq := rfl } } }
  change pair.sourceAnchor.iso.hom ≫ (pair.first ≫ pair.second) =
    (toSemanticCart (compPresentation pair.firstArrow.presentation
      pair.secondArrow.presentation).toPresentation).hom ≫
      pair.targetAnchor.iso.hom
  calc
    _ = (pair.sourceAnchor.iso.hom ≫ pair.first) ≫ pair.second := by
      simp [Category.assoc]
    _ = ((toSemanticCart pair.firstArrow.presentation.toPresentation).hom ≫
        pair.middleAnchor.iso.hom) ≫ pair.second := by rw [hfirst]
    _ = (toSemanticCart pair.firstArrow.presentation.toPresentation).hom ≫
        (pair.middleAnchor.iso.hom ≫ pair.second) := by simp [Category.assoc]
    _ = (toSemanticCart pair.firstArrow.presentation.toPresentation).hom ≫
        ((toSemanticCart pair.secondArrow.presentation.toPresentation).hom ≫
          pair.targetAnchor.iso.hom) := by rw [hsecond]
    _ = ((toSemanticCart pair.firstArrow.presentation.toPresentation).hom ≫
        (toSemanticCart pair.secondArrow.presentation.toPresentation).hom) ≫
          pair.targetAnchor.iso.hom := by simp [Category.assoc]
    _ = _ := by rw [toSemanticCart_compPresentation_hom]

/-- The decoded code cospan, transported to the semantic cospan, is a pullback. -/
theorem exact_bottom_transported_code_pullback_is_pullback
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (cospan : SharedBaseAnchorCospan (U := U)) :
    IsPullback
      ((toSemanticCart (pullbackFstPresentation
        cospan.firstArrow.presentation cospan.secondArrow.presentation).toPresentation).hom ≫
          cospan.leftAnchor.iso.hom)
      ((toSemanticCart (pullbackSndPresentation
        cospan.firstArrow.presentation cospan.secondArrow.presentation).toPresentation).hom ≫
          cospan.rightAnchor.iso.hom)
      cospan.first cospan.second := by
  have hfirst : cospan.leftAnchor.iso.hom ≫ cospan.first =
      (toSemanticCart cospan.firstArrow.presentation.toPresentation).hom ≫
        cospan.baseAnchor.iso.hom := by
    calc
      _ = cospan.firstArrow.square.sourceIso.hom ≫ cospan.first := by
        rw [cospan.firstArrow.sourceIso_eq]
      _ = (toSemanticCart cospan.firstArrow.presentation.toPresentation).hom ≫
          cospan.firstArrow.square.targetIso.hom :=
        cospan.firstArrow.square.hom_comm
      _ = _ := by rw [cospan.firstArrow.targetIso_eq]
  have hsecond : cospan.rightAnchor.iso.hom ≫ cospan.second =
      (toSemanticCart cospan.secondArrow.presentation.toPresentation).hom ≫
        cospan.baseAnchor.iso.hom := by
    calc
      _ = cospan.secondArrow.square.sourceIso.hom ≫ cospan.second := by
        rw [cospan.secondArrow.sourceIso_eq]
      _ = (toSemanticCart cospan.secondArrow.presentation.toPresentation).hom ≫
          cospan.secondArrow.square.targetIso.hom :=
        cospan.secondArrow.square.hom_comm
      _ = _ := by rw [cospan.secondArrow.targetIso_eq]
  have codePullback := pullbackPresentation_isPullback
    cospan.firstArrow.presentation cospan.secondArrow.presentation
  refine IsPullback.of_iso'
    (P' := (pullbackInstanceCode cospan.firstArrow.presentation
      cospan.secondArrow.presentation).toSemantic)
    (X' := cospan.left) (Y' := cospan.right) (Z' := cospan.base)
    codePullback (Iso.refl _)
      cospan.leftAnchor.iso.symm cospan.rightAnchor.iso.symm
        cospan.baseAnchor.iso.symm
      ?_ ?_ ?_ ?_
  · simp
  · simp
  · apply (Iso.inv_comp_eq cospan.leftAnchor.iso).2
    rw [← Category.assoc, hfirst]
    simp
  · apply (Iso.inv_comp_eq cospan.rightAnchor.iso).2
    rw [← Category.assoc, hsecond]
    simp

/-- Canonical comparison from the generated code pullback to the semantic one. -/
noncomputable def exact_bottom_pullback_object_iso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (cospan : SharedBaseAnchorCospan (U := U)) :
    (pullbackInstanceCode cospan.firstArrow.presentation
      cospan.secondArrow.presentation).toSemantic ≅
      pointedPullback cospan.first cospan.second :=
  (exact_bottom_transported_code_pullback_is_pullback cospan).isoIsPullback
    cospan.left cospan.right
    (pointedPullback_isPullback cospan.first cospan.second)

/-- Construct the common pullback anchor and both anchored projections. -/
noncomputable def exact_bottom_pullback_closure
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : ExactBottomCoverageRegime U)
    (cospan : SharedBaseAnchorCospan (U := U))
    (firstMembership : regime.Holds cospan.firstInput)
    (secondMembership : regime.Holds cospan.secondInput) :
    ExactBottomPullbackClosureResult regime cospan where
  object_anchor :=
    { code := pullbackInstanceCode cospan.firstArrow.presentation
        cospan.secondArrow.presentation
      iso := exact_bottom_pullback_object_iso cospan }
  fst_membership := exact_bottom_pullback_fst_membership regime cospan
    firstMembership secondMembership
  snd_membership := exact_bottom_pullback_snd_membership regime cospan
    firstMembership secondMembership
  fst_arrow :=
    { presentation := pullbackFstPresentation cospan.firstArrow.presentation
        cospan.secondArrow.presentation
      square :=
        { sourceIso := exact_bottom_pullback_object_iso cospan
          targetIso := cospan.leftAnchor.iso
          hom_comm := by
            exact (exact_bottom_transported_code_pullback_is_pullback cospan
              ).isoIsPullback_hom_fst cospan.left cospan.right
                (pointedPullback_isPullback cospan.first cospan.second) }
      sourceIso_eq := rfl
      targetIso_eq := rfl }
  snd_arrow :=
    { presentation := pullbackSndPresentation cospan.firstArrow.presentation
        cospan.secondArrow.presentation
      square :=
        { sourceIso := exact_bottom_pullback_object_iso cospan
          targetIso := cospan.rightAnchor.iso
          hom_comm := by
            exact (exact_bottom_transported_code_pullback_is_pullback cospan
              ).isoIsPullback_hom_snd cospan.left cospan.right
                (pointedPullback_isPullback cospan.first cospan.second) }
      sourceIso_eq := rfl
      targetIso_eq := rfl }

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
