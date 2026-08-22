import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import ResearchLean.AG.AtomFoundation.Doctrine

/-!
# Pullbacks of exact extraction doctrines

This module constructs the fiber product of an arbitrary cospan in the exact
doctrine category `Doct_U`.  Its source is the subtype of compatible source
pairs.  The second projection uses the forced Atom equivalence
`sigmaOne.atomEquiv.trans sigmaTwo.atomEquiv.symm`.

The universal lift is constructed from every semantic doctrine cone.  In
particular, its Atom equivalence is the actual Atom equivalence of the cone's
first leg; no identity-Atom restriction, finite presentation, selected point,
or caller-supplied pullback certificate occurs in the construction.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory CategoryTheory.Limits
open AtomFoundation

/-- Source pairs whose images agree under an arbitrary exact doctrine cospan. -/
abbrev DoctrinePullbackSource
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base) : Type u :=
  {pair : DOne.Source × DTwo.Source //
    sigmaOne.sourceMap pair.1 = sigmaTwo.sourceMap pair.2}

/--
The exact-doctrine pullback object generated from an arbitrary cospan.

The visible reading data is copied from the first doctrine, while the source
and normalization are the compatible-pair subtype and componentwise
normalization.  Exactness of the second projection below proves that this
asymmetric presentation carries the required invariant extraction relation.
-/
def doctrinePullback
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base) :
    ExtractionDoctrine U where
  Source := DoctrinePullbackSource sigmaOne sigmaTwo
  Vocabulary := DOne.Vocabulary
  SemanticReading := DOne.SemanticReading
  Resolution := DOne.Resolution
  vocabulary := DOne.vocabulary
  semanticReading := DOne.semanticReading
  resolution := DOne.resolution
  vocabularyAllows := DOne.vocabularyAllows
  semanticAllows := fun reading source atom =>
    DOne.semanticAllows reading source.val.1 atom
  resolutionAllows := fun resolution source atom =>
    DOne.resolutionAllows resolution source.val.1 atom
  sourceSemantics := fun source atom =>
    DOne.sourceSemantics source.val.1 atom
  normalize := fun source =>
    ⟨(DOne.normalize source.val.1, DTwo.normalize source.val.2), by
      rw [← sigmaOne.normalize_eq source.val.1,
        ← sigmaTwo.normalize_eq source.val.2, source.property]⟩

/-- Pullback extraction is exactly extraction from the first source component. -/
@[simp]
theorem doctrinePullback_extracts_iff
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base)
    (source : (doctrinePullback sigmaOne sigmaTwo).Source)
    (atom : U.Atom) :
    (doctrinePullback sigmaOne sigmaTwo).extracts source atom ↔
      DOne.extracts source.val.1 atom :=
  Iff.rfl

/-- First projection from the generated doctrine pullback. -/
def doctrinePullbackFst
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base) :
    doctrinePullback sigmaOne sigmaTwo ⟶ DOne where
  sourceMap := fun source => source.val.1
  atomEquiv := Equiv.refl U.Atom
  normalize_eq _ := rfl
  extraction_iff source atom := by
    exact doctrinePullback_extracts_iff sigmaOne sigmaTwo source atom

/--
Second projection from the generated doctrine pullback.  Its Atom component is
forced by the two cospan Atom equivalences and is not restricted to identity.
-/
def doctrinePullbackSnd
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base) :
    doctrinePullback sigmaOne sigmaTwo ⟶ DTwo where
  sourceMap := fun source => source.val.2
  atomEquiv := sigmaOne.atomEquiv.trans sigmaTwo.atomEquiv.symm
  normalize_eq _ := rfl
  extraction_iff source atom := by
    rw [doctrinePullback_extracts_iff]
    let targetAtom := sigmaTwo.atomEquiv.symm (sigmaOne.atomEquiv atom)
    calc
      DOne.extracts source.val.1 atom ↔
          Base.extracts (sigmaOne.sourceMap source.val.1)
            (sigmaOne.atomEquiv atom) :=
        sigmaOne.extraction_iff source.val.1 atom
      _ ↔ Base.extracts (sigmaTwo.sourceMap source.val.2)
            (sigmaOne.atomEquiv atom) := by
        rw [source.property]
      _ ↔ DTwo.extracts source.val.2 targetAtom := by
        simpa [targetAtom] using
          (sigmaTwo.extraction_iff source.val.2 targetAtom).symm
      _ ↔ DTwo.extracts source.val.2
          ((sigmaOne.atomEquiv.trans sigmaTwo.atomEquiv.symm) atom) :=
        Iff.rfl

/-- The two generated projections form a commuting square over the cospan. -/
theorem doctrinePullback_commutes
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base) :
    doctrinePullbackFst sigmaOne sigmaTwo ≫ sigmaOne =
      doctrinePullbackSnd sigmaOne sigmaTwo ≫ sigmaTwo := by
  apply ExactDoctrineHom.ext
  · funext source
    exact source.property
  · change (Equiv.refl U.Atom).trans sigmaOne.atomEquiv =
      (sigmaOne.atomEquiv.trans sigmaTwo.atomEquiv.symm).trans
        sigmaTwo.atomEquiv
    apply Equiv.ext
    intro atom
    simp

/-- Compatible source pair induced by an arbitrary cone in `Doct_U`. -/
def doctrinePullbackSourceOfCone
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base)
    (cone : PullbackCone sigmaOne sigmaTwo) (source : cone.pt.Source) :
    DoctrinePullbackSource sigmaOne sigmaTwo :=
  ⟨(cone.fst.sourceMap source, cone.snd.sourceMap source), by
    have sourceMaps := congrArg (fun hom => hom.sourceMap source) cone.condition
    change sigmaOne.sourceMap (cone.fst.sourceMap source) =
      sigmaTwo.sourceMap (cone.snd.sourceMap source) at sourceMaps
    exact sourceMaps⟩

/--
Universal morphism from an arbitrary doctrine cone to the generated pullback.
Its Atom equivalence is copied directly from the first cone leg.
-/
def doctrinePullbackLift
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base)
    (cone : PullbackCone sigmaOne sigmaTwo) :
    cone.pt ⟶ doctrinePullback sigmaOne sigmaTwo where
  sourceMap := doctrinePullbackSourceOfCone sigmaOne sigmaTwo cone
  atomEquiv := cone.fst.atomEquiv
  normalize_eq source := by
    apply Subtype.ext
    apply Prod.ext
    · exact cone.fst.normalize_eq source
    · exact cone.snd.normalize_eq source
  extraction_iff source atom := by
    rw [doctrinePullback_extracts_iff]
    exact cone.fst.extraction_iff source atom

/-- The universal lift retains the arbitrary Atom equivalence of the first cone leg. -/
@[simp]
theorem doctrinePullbackLift_atomEquiv
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base)
    (cone : PullbackCone sigmaOne sigmaTwo) :
    (doctrinePullbackLift sigmaOne sigmaTwo cone).atomEquiv =
      cone.fst.atomEquiv :=
  rfl

/-- The universal lift factors through the first generated projection. -/
theorem doctrinePullbackLift_fst
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base)
    (cone : PullbackCone sigmaOne sigmaTwo) :
    doctrinePullbackLift sigmaOne sigmaTwo cone ≫
        doctrinePullbackFst sigmaOne sigmaTwo =
      cone.fst := by
  apply ExactDoctrineHom.ext
  · rfl
  · apply Equiv.ext
    intro atom
    rfl

/-- The universal lift factors through the second generated projection. -/
theorem doctrinePullbackLift_snd
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base)
    (cone : PullbackCone sigmaOne sigmaTwo) :
    doctrinePullbackLift sigmaOne sigmaTwo cone ≫
        doctrinePullbackSnd sigmaOne sigmaTwo =
      cone.snd := by
  apply ExactDoctrineHom.ext
  · rfl
  · have atomMaps := congrArg (fun hom => hom.atomEquiv) cone.condition
    change cone.fst.atomEquiv.trans sigmaOne.atomEquiv =
      cone.snd.atomEquiv.trans sigmaTwo.atomEquiv at atomMaps
    change cone.fst.atomEquiv.trans
        (sigmaOne.atomEquiv.trans sigmaTwo.atomEquiv.symm) =
      cone.snd.atomEquiv
    apply Equiv.ext
    intro atom
    apply sigmaTwo.atomEquiv.injective
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      congrArg (fun equiv : Equiv.Perm U.Atom => equiv atom) atomMaps

/--
Every morphism satisfying both projection equations is the generated universal
lift.  The equations are uniqueness hypotheses, not producer certificates.
-/
theorem doctrinePullbackLift_unique
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base)
    (cone : PullbackCone sigmaOne sigmaTwo)
    (candidate : cone.pt ⟶ doctrinePullback sigmaOne sigmaTwo)
    (hfst : candidate ≫ doctrinePullbackFst sigmaOne sigmaTwo = cone.fst)
    (hsnd : candidate ≫ doctrinePullbackSnd sigmaOne sigmaTwo = cone.snd) :
    candidate = doctrinePullbackLift sigmaOne sigmaTwo cone := by
  apply ExactDoctrineHom.ext
  · funext source
    apply Subtype.ext
    apply Prod.ext
    · have sourceMaps := congrArg (fun hom => hom.sourceMap source) hfst
      change (candidate.sourceMap source).val.1 =
        cone.fst.sourceMap source at sourceMaps
      exact sourceMaps
    · have sourceMaps := congrArg (fun hom => hom.sourceMap source) hsnd
      change (candidate.sourceMap source).val.2 =
        cone.snd.sourceMap source at sourceMaps
      exact sourceMaps
  · change candidate.atomEquiv = cone.fst.atomEquiv
    have atomMaps := congrArg (fun hom => hom.atomEquiv) hfst
    change candidate.atomEquiv.trans (Equiv.refl U.Atom) =
      cone.fst.atomEquiv at atomMaps
    apply Equiv.ext
    intro atom
    have atomPoint :=
      congrArg (fun equiv : Equiv.Perm U.Atom => equiv atom) atomMaps
    change candidate.atomEquiv atom = cone.fst.atomEquiv atom at atomPoint
    exact atomPoint

/--
Every exact doctrine cospan has the generated categorical pullback in `Doct_U`.
Universality ranges over all semantic doctrine cones and assumes no decidable
Atom equality or finite-presentation provenance.
-/
theorem doctrinePullback_isPullback
    {U : AtomCarrier.{u}} {DOne DTwo Base : ExtractionDoctrine U}
    (sigmaOne : DOne ⟶ Base) (sigmaTwo : DTwo ⟶ Base) :
    IsPullback
      (doctrinePullbackFst sigmaOne sigmaTwo)
      (doctrinePullbackSnd sigmaOne sigmaTwo)
      sigmaOne sigmaTwo := by
  apply IsPullback.of_isLimit'
    ⟨doctrinePullback_commutes sigmaOne sigmaTwo⟩
  refine PullbackCone.IsLimit.mk _
    (fun cone => doctrinePullbackLift sigmaOne sigmaTwo cone) ?_ ?_ ?_
  · intro cone
    exact doctrinePullbackLift_fst sigmaOne sigmaTwo cone
  · intro cone
    exact doctrinePullbackLift_snd sigmaOne sigmaTwo cone
  · intro cone candidate hfst hsnd
    exact doctrinePullbackLift_unique sigmaOne sigmaTwo cone candidate hfst hsnd

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
