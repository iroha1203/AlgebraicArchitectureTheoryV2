import ResearchLean.AG.AtomFoundation.FiniteTransportWitness

/-!
# Reviewed FiniteModel-backed cartesian presentation schema for G-110

This module fixes the cartesian half of the G-110 F0 typing layer without
inventing a new family of semantic tags.  A raw presentation has exactly four
authored fields:

1. a source instance description,
2. a target instance description,
3. a finite source-map table, and
4. a finite Atom-map table.

Every value in those fields comes from the reviewed `FiniteModel` vocabulary.
The validated domain admits only the two reviewed doctrine frames: the original
finite extraction doctrine and the G-101 transported doctrine.  The semantic
decoder constructs their actual `ExactDoctrineHom` / `ExtInstHom` laws.

Consequently this first schema contains no manufactured noninvertible map.  Its
source maps are identities, so their source-level pullbacks remain the reviewed
two-element source rather than escaping to a four-element code invented after
the target was fixed.  If G-110's right branch is later required, its
noninvertible positive-family qualification remains a separate unresolved gate;
it is not hidden in this F0 layer.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## The reviewed finite vocabulary and its two doctrine frames -/

/-- Explicit enumeration of the reviewed two source values. -/
def finiteExtractionSourceAll : List FiniteModel.ExtractionSource :=
  [.all, .withoutComponentC]

/-- The reviewed source enumeration is exhaustive. -/
theorem finiteExtractionSource_mem_all
    (source : FiniteModel.ExtractionSource) :
    source ∈ finiteExtractionSourceAll := by
  cases source <;> simp [finiteExtractionSourceAll]

instance finiteExtractionSourceFintype :
    Fintype FiniteModel.ExtractionSource :=
  Fintype.ofList finiteExtractionSourceAll finiteExtractionSource_mem_all

/-- The reviewed Atom swap written as an executable finite table. -/
def finiteReviewedAtomSwap :
    FiniteModel.FiniteAtom → FiniteModel.FiniteAtom
  | .componentC => .dependsAB
  | .dependsAB => .componentC
  | atom => atom

/-- The executable reviewed swap is involutive. -/
@[simp]
theorem finiteReviewedAtomSwap_involutive
    (atom : FiniteModel.FiniteAtom) :
    finiteReviewedAtomSwap (finiteReviewedAtomSwap atom) = atom := by
  cases atom <;> rfl

/-- The executable table as an Atom equivalence. -/
def finiteReviewedAtomSwapEquiv :
    Equiv.Perm FiniteModel.FiniteAtom where
  toFun := finiteReviewedAtomSwap
  invFun := finiteReviewedAtomSwap
  left_inv := finiteReviewedAtomSwap_involutive
  right_inv := finiteReviewedAtomSwap_involutive

/-- The reviewed G-101 swap fixes every Atom outside its two-point support. -/
theorem finiteTransportAtomEquiv_apply_of_ne
    (atom : FiniteModel.FiniteAtom)
    (hcomponentC : atom ≠ FiniteModel.FiniteAtom.componentC)
    (hdependsAB : atom ≠ FiniteModel.FiniteAtom.dependsAB) :
    finiteTransportAtomEquiv atom = atom := by
  unfold finiteTransportAtomEquiv
  exact @Equiv.swap_apply_of_ne_of_ne _ (Classical.decEq _)
    FiniteModel.FiniteAtom.componentC FiniteModel.FiniteAtom.dependsAB atom
    hcomponentC hdependsAB

/-- The executable table is exactly the reviewed G-101 transport. -/
theorem finiteReviewedAtomSwapEquiv_eq_reviewed :
    finiteReviewedAtomSwapEquiv = finiteTransportAtomEquiv := by
  apply Equiv.ext
  intro atom
  cases atom with
  | componentA =>
      change FiniteModel.FiniteAtom.componentA =
        finiteTransportAtomEquiv FiniteModel.FiniteAtom.componentA
      exact (finiteTransportAtomEquiv_apply_of_ne _
        (by decide) (by decide)).symm
  | componentB =>
      change FiniteModel.FiniteAtom.componentB =
        finiteTransportAtomEquiv FiniteModel.FiniteAtom.componentB
      exact (finiteTransportAtomEquiv_apply_of_ne _
        (by decide) (by decide)).symm
  | componentC => exact finiteTransportAtomEquiv_componentC.symm
  | dependsAB => exact finiteTransportAtomEquiv_dependsAB.symm
  | dependsBC => exact finiteTransportAtomEquiv_dependsBC.symm
  | dependsCA => exact finiteTransportAtomEquiv_dependsCA.symm
  | contractBase =>
      change FiniteModel.FiniteAtom.contractBase =
        finiteTransportAtomEquiv FiniteModel.FiniteAtom.contractBase
      exact (finiteTransportAtomEquiv_apply_of_ne _
        (by decide) (by decide)).symm
  | contractImpl =>
      change FiniteModel.FiniteAtom.contractImpl =
        finiteTransportAtomEquiv FiniteModel.FiniteAtom.contractImpl
      exact (finiteTransportAtomEquiv_apply_of_ne _
        (by decide) (by decide)).symm
  | substitutesImplBase =>
      change FiniteModel.FiniteAtom.substitutesImplBase =
        finiteTransportAtomEquiv FiniteModel.FiniteAtom.substitutesImplBase
      exact (finiteTransportAtomEquiv_apply_of_ne _
        (by decide) (by decide)).symm

/-- The only excluded-Atom fields occurring in the reviewed two-frame schema. -/
def ReviewedExcludedAtom (atom : FiniteModel.FiniteAtom) : Prop :=
  atom = .componentC ∨ atom = .dependsAB

instance reviewedExcludedAtomDecidable
    (atom : FiniteModel.FiniteAtom) : Decidable (ReviewedExcludedAtom atom) :=
  by
    unfold ReviewedExcludedAtom
    infer_instance

/--
The unique finite Atom equivalence between two reviewed doctrine frames.

Equal frames use the identity.  The only unequal reviewed pair is
`componentC` / `dependsAB`, so it uses the reviewed involution.
-/
def finiteFrameEquiv (sourceExcluded targetExcluded : FiniteModel.FiniteAtom) :
    Equiv.Perm FiniteModel.FiniteAtom :=
  if sourceExcluded = targetExcluded then Equiv.refl _
  else finiteReviewedAtomSwapEquiv

/-- The authored finite Atom-map table generated by the two frame fields. -/
def finiteFrameMap (sourceExcluded targetExcluded : FiniteModel.FiniteAtom) :
    FiniteModel.FiniteAtom → FiniteModel.FiniteAtom :=
  finiteFrameEquiv sourceExcluded targetExcluded

/-- A reviewed frame map carries its excluded Atom to the target excluded Atom. -/
theorem finiteFrameEquiv_excluded
    {sourceExcluded targetExcluded : FiniteModel.FiniteAtom}
    (hsource : ReviewedExcludedAtom sourceExcluded)
    (htarget : ReviewedExcludedAtom targetExcluded) :
    finiteFrameEquiv sourceExcluded targetExcluded sourceExcluded =
      targetExcluded := by
  rcases hsource with rfl | rfl <;>
    rcases htarget with rfl | rfl <;>
    simp [finiteFrameEquiv, finiteReviewedAtomSwapEquiv,
      finiteReviewedAtomSwap]

/-- Extraction away from the excluded Atom is preserved and reflected. -/
theorem finiteFrameEquiv_ne_excluded_iff
    {sourceExcluded targetExcluded : FiniteModel.FiniteAtom}
    (hsource : ReviewedExcludedAtom sourceExcluded)
    (htarget : ReviewedExcludedAtom targetExcluded)
    (atom : FiniteModel.FiniteAtom) :
    atom ≠ sourceExcluded ↔
      finiteFrameEquiv sourceExcluded targetExcluded atom ≠ targetExcluded := by
  rcases hsource with rfl | rfl <;>
    rcases htarget with rfl | rfl <;>
    cases atom <;>
    simp [finiteFrameEquiv, finiteReviewedAtomSwapEquiv,
      finiteReviewedAtomSwap]

/-! ## Universe-polymorphic representation backing -/

/--
Representation provenance identifying the ambient primitive Atom type with
the universe lift of the reviewed finite Atom type.

This contains no doctrine, morphism, checker result, lift, or target
certificate.  All authored finite data remains in `CartRawCode` below.
-/
structure FiniteModelBacking (U : AtomCarrier.{u}) where
  atomEquiv : ULift.{u, 0} FiniteModel.FiniteAtom ≃ U.Atom

/-- The original reviewed carrier has its canonical representation backing. -/
def finiteModelBacking : FiniteModelBacking FiniteModel.carrier where
  atomEquiv := Equiv.ulift

namespace FiniteModelBacking

/-- Lift one reviewed finite Atom permutation through an ambient backing. -/
def liftAtomEquiv {U : AtomCarrier.{u}} (backing : FiniteModelBacking U)
    (equiv : Equiv.Perm FiniteModel.FiniteAtom) : U.Atom ≃ U.Atom := by
  let lifted : ULift.{u, 0} FiniteModel.FiniteAtom ≃
      ULift.{u, 0} FiniteModel.FiniteAtom := {
    toFun := fun atom => ⟨equiv atom.down⟩
    invFun := fun atom => ⟨equiv.symm atom.down⟩
    left_inv := by
      intro atom
      apply ULift.ext
      exact equiv.symm_apply_apply atom.down
    right_inv := by
      intro atom
      apply ULift.ext
      exact equiv.apply_symm_apply atom.down
  }
  exact backing.atomEquiv.symm.trans (lifted.trans backing.atomEquiv)

/-- Pulling a lifted finite permutation back through the backing recovers it. -/
@[simp]
theorem atomEquiv_symm_liftAtomEquiv {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U)
    (equiv : Equiv.Perm FiniteModel.FiniteAtom) (atom : U.Atom) :
    (backing.atomEquiv.symm (backing.liftAtomEquiv equiv atom)).down =
      equiv (backing.atomEquiv.symm atom).down := by
  simp [liftAtomEquiv]

/-- On the original carrier, lifting a reviewed permutation changes no data. -/
@[simp]
theorem finiteModelBacking_liftAtomEquiv
    (equiv : Equiv.Perm FiniteModel.FiniteAtom) :
    finiteModelBacking.liftAtomEquiv equiv = equiv := by
  apply Equiv.ext
  intro atom
  rfl

end FiniteModelBacking

/-! ## Four-field raw code and validated decoder domain -/

/--
A finite instance description is the standard product of an excluded Atom
field and a selected reviewed source field.  It is an abbreviation, not a new
semantic code family.
-/
abbrev FiniteInstanceDescription :=
  FiniteModel.FiniteAtom × FiniteModel.ExtractionSource

/-- The four authored fields of one finite pointed exact morphism. -/
structure CartRawCode where
  /-- Source instance: excluded Atom frame and selected source. -/
  source : FiniteInstanceDescription
  /-- Target instance: excluded Atom frame and selected source. -/
  target : FiniteInstanceDescription
  /-- Finite table for the source map. -/
  sourceMap :
    FiniteModel.ExtractionSource → FiniteModel.ExtractionSource
  /-- Finite table for the Atom map. -/
  atomMap : FiniteModel.FiniteAtom → FiniteModel.FiniteAtom
  deriving DecidableEq

/-- Raw codes are a finite product of existing reviewed finite value types. -/
def cartRawCodeEquiv :
    (((FiniteInstanceDescription × FiniteInstanceDescription) ×
        (FiniteModel.ExtractionSource → FiniteModel.ExtractionSource)) ×
      (FiniteModel.FiniteAtom → FiniteModel.FiniteAtom)) ≃ CartRawCode where
  toFun code := ⟨code.1.1.1, code.1.1.2, code.1.2, code.2⟩
  invFun code := (((code.source, code.target), code.sourceMap), code.atomMap)
  left_inv _ := rfl
  right_inv _ := rfl

instance cartRawCodeFintype : Fintype CartRawCode :=
  Fintype.ofEquiv
    (((FiniteInstanceDescription × FiniteInstanceDescription) ×
        (FiniteModel.ExtractionSource → FiniteModel.ExtractionSource)) ×
      (FiniteModel.FiniteAtom → FiniteModel.FiniteAtom))
    cartRawCodeEquiv

namespace CartRawCode

/--
Decoder-domain condition for the reviewed finite schema.

It admits only the two reviewed doctrine frames, the identity source table,
point preservation, and the Atom table generated by the endpoint frames.
-/
def WellFormed (code : CartRawCode) : Prop :=
  ReviewedExcludedAtom code.source.1 ∧
    ReviewedExcludedAtom code.target.1 ∧
    code.sourceMap = id ∧
    code.target.2 = code.source.2 ∧
    code.atomMap = finiteFrameMap code.source.1 code.target.1

instance wellFormedDecidable (code : CartRawCode) :
    Decidable code.WellFormed := by
  unfold WellFormed ReviewedExcludedAtom
  infer_instance

end CartRawCode

/-- The validated subtype is the entire semantic decoder domain. -/
abbrev ValidatedCartCode := {code : CartRawCode // code.WellFormed}

/-- Every validated source table is the reviewed identity source map. -/
theorem validatedCartCode_sourceMap_eq_id (code : ValidatedCartCode) :
    code.1.sourceMap = id :=
  code.2.2.2.1

/-- Raw identity at the selective reviewed point. -/
def finiteIdentityRawCode : CartRawCode where
  source := (.componentC, .withoutComponentC)
  target := (.componentC, .withoutComponentC)
  sourceMap := id
  atomMap := id

/-- The reviewed identity code is accepted. -/
theorem finiteIdentityRawCode_wellFormed :
    finiteIdentityRawCode.WellFormed := by
  simp [CartRawCode.WellFormed, finiteIdentityRawCode,
    ReviewedExcludedAtom, finiteFrameMap, finiteFrameEquiv]

/-- Raw code for the reviewed G-101 nonidentity Atom transport. -/
def finiteAtomTransportRawCode : CartRawCode where
  source := (.componentC, .withoutComponentC)
  target := (.dependsAB, .withoutComponentC)
  sourceMap := id
  atomMap := finiteReviewedAtomSwap

/-- The reviewed transport code is accepted. -/
theorem finiteAtomTransportRawCode_wellFormed :
    finiteAtomTransportRawCode.WellFormed := by
  simp [CartRawCode.WellFormed, finiteAtomTransportRawCode,
    ReviewedExcludedAtom, finiteFrameMap, finiteFrameEquiv,
    finiteReviewedAtomSwapEquiv]

/-- A point-changing raw code rejected by `ExtInstHom.source_eq`. -/
def finitePointMismatchRawCode : CartRawCode where
  source := (.componentC, .withoutComponentC)
  target := (.componentC, .all)
  sourceMap := id
  atomMap := id

/-- The point-changing raw code is rejected before decoding. -/
theorem finitePointMismatchRawCode_not_wellFormed :
    ¬ finitePointMismatchRawCode.WellFormed := by
  decide

/-- Validated reviewed identity. -/
def finiteIdentityCode : ValidatedCartCode :=
  ⟨finiteIdentityRawCode, finiteIdentityRawCode_wellFormed⟩

/-- Validated reviewed Atom transport. -/
def finiteAtomTransportCode : ValidatedCartCode :=
  ⟨finiteAtomTransportRawCode,
    finiteAtomTransportRawCode_wellFormed⟩

/-! ## Actual semantic realization -/

/--
The reviewed finite extraction doctrine in one of its two frames, transported
through the ambient representation backing.
-/
def finiteFramedDoctrine {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U)
    (excluded : FiniteModel.FiniteAtom) : ExtractionDoctrine U where
  Source := ULift.{u, 0} FiniteModel.ExtractionSource
  Vocabulary := ULift.{u, 0} PUnit
  SemanticReading := ULift.{u, 0} PUnit
  Resolution := ULift.{u, 0} PUnit
  vocabulary := ⟨PUnit.unit⟩
  semanticReading := ⟨PUnit.unit⟩
  resolution := ⟨PUnit.unit⟩
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ source atom =>
    source.down = FiniteModel.ExtractionSource.all ∨
      (backing.atomEquiv.symm atom).down ≠ excluded
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- Decode one endpoint description to an actual pointed doctrine. -/
def decodeFiniteInstance {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U)
    (description : FiniteInstanceDescription) : ExtractionInstance U where
  doctrine := finiteFramedDoctrine backing description.1
  source := ⟨description.2⟩

/-- The untransported frame reads exactly the reviewed FiniteModel doctrine. -/
theorem finiteFramedDoctrine_componentC_extracts_iff_reviewed
    (source : FiniteModel.ExtractionSource)
    (atom : FiniteModel.FiniteAtom) :
    (finiteFramedDoctrine finiteModelBacking
        FiniteModel.FiniteAtom.componentC).extracts
        (show ULift FiniteModel.ExtractionSource from ⟨source⟩) atom ↔
      FiniteModel.extractionDoctrine.extracts source atom := by
  change
    (True ∧
      (source = FiniteModel.ExtractionSource.all ∨
        atom ≠ FiniteModel.FiniteAtom.componentC) ∧ True ∧ True) ↔
    (True ∧
      (source = FiniteModel.ExtractionSource.all ∨
        atom ≠ FiniteModel.FiniteAtom.componentC) ∧ True ∧ True)
  rfl

/-- The transported frame reads exactly the reviewed G-101 target doctrine. -/
theorem finiteFramedDoctrine_dependsAB_extracts_iff_reviewed
    (source : FiniteModel.ExtractionSource)
    (atom : FiniteModel.FiniteAtom) :
    (finiteFramedDoctrine finiteModelBacking
        FiniteModel.FiniteAtom.dependsAB).extracts
        (show ULift FiniteModel.ExtractionSource from ⟨source⟩) atom ↔
      finiteTransportTargetDoctrine.extracts source atom := by
  change
    (True ∧
      (source = FiniteModel.ExtractionSource.all ∨
        atom ≠ FiniteModel.FiniteAtom.dependsAB) ∧ True ∧ True) ↔
    (True ∧
      (source = FiniteModel.ExtractionSource.all ∨
        finiteTransportAtomEquiv.symm atom ≠
          FiniteModel.FiniteAtom.componentC) ∧ True ∧ True)
  simp only [true_and, and_true]
  cases source with
  | all => simp
  | withoutComponentC =>
      simp only [reduceCtorEq, false_or]
      constructor
      · intro hne heq
        apply hne
        calc
          atom = finiteTransportAtomEquiv
              (finiteTransportAtomEquiv.symm atom) :=
            (finiteTransportAtomEquiv.apply_symm_apply atom).symm
          _ = finiteTransportAtomEquiv
              FiniteModel.FiniteAtom.componentC := congrArg _ heq
          _ = FiniteModel.FiniteAtom.dependsAB :=
            finiteTransportAtomEquiv_componentC
      · intro hne heq
        apply hne
        calc
          finiteTransportAtomEquiv.symm atom =
              finiteTransportAtomEquiv.symm
                FiniteModel.FiniteAtom.dependsAB := congrArg _ heq
          _ = FiniteModel.FiniteAtom.componentC := by
            rw [← finiteTransportAtomEquiv_componentC]
            exact finiteTransportAtomEquiv.symm_apply_apply _

/-- The named semantic pointed-arrow layer required by G-110. -/
structure CartSemanticInput (U : AtomCarrier.{u}) where
  source : ExtractionInstance U
  target : ExtractionInstance U
  hom : source ⟶ target

/--
Finite presentation of one semantic pointed arrow.

`backing` is representation provenance.  The authored payload is exactly the
validated four-field finite code; neither field contains a lift, mate, checker
bit, or cartesianness certificate.
-/
structure CartPresentation (U : AtomCarrier.{u}) where
  backing : FiniteModelBacking U
  code : ValidatedCartCode

/-- Decode a validated four-field code to an actual pointed exact morphism. -/
def decodeCartHom {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) (code : ValidatedCartCode) :
    ExtInstHom (decodeFiniteInstance backing code.1.source)
      (decodeFiniteInstance backing code.1.target) := by
  rcases code with
    ⟨⟨source, target, sourceMap, atomMap⟩,
      hsource, htarget, hsourceMap, hpoint, hatomMap⟩
  change ReviewedExcludedAtom source.1 at hsource
  change ReviewedExcludedAtom target.1 at htarget
  change sourceMap = id at hsourceMap
  change target.2 = source.2 at hpoint
  change atomMap = finiteFrameMap source.1 target.1 at hatomMap
  subst sourceMap
  subst atomMap
  exact {
    doctrineHom := {
      sourceMap := id
      atomEquiv := backing.liftAtomEquiv
        (finiteFrameEquiv source.1 target.1)
      normalize_eq := by intro; rfl
      extraction_iff := by
        intro finiteSource atom
        change
          (True ∧
            (finiteSource.down = FiniteModel.ExtractionSource.all ∨
              (backing.atomEquiv.symm atom).down ≠ source.1) ∧
            True ∧ True) ↔
          (True ∧
            (finiteSource.down = FiniteModel.ExtractionSource.all ∨
              (backing.atomEquiv.symm
                (backing.liftAtomEquiv
                  (finiteFrameEquiv source.1 target.1) atom)).down ≠
                target.1) ∧
            True ∧ True)
        simp only [true_and, and_true,
          backing.atomEquiv_symm_liftAtomEquiv]
        exact or_congr Iff.rfl
          (finiteFrameEquiv_ne_excluded_iff hsource htarget
            (backing.atomEquiv.symm atom).down)
    }
    source_eq := by
      apply ULift.ext
      exact hpoint.symm
  }

/-- The decoder's Atom equivalence is generated by the two endpoint frames. -/
theorem decodeCartHom_atomEquiv {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) (code : ValidatedCartCode) :
    (decodeCartHom backing code).doctrineHom.atomEquiv =
      backing.liftAtomEquiv
        (finiteFrameEquiv code.1.source.1 code.1.target.1) := by
  rcases code with
    ⟨⟨source, target, sourceMap, atomMap⟩,
      hsource, htarget, hsourceMap, hpoint, hatomMap⟩
  change ReviewedExcludedAtom source.1 at hsource
  change ReviewedExcludedAtom target.1 at htarget
  change sourceMap = id at hsourceMap
  change target.2 = source.2 at hpoint
  change atomMap = finiteFrameMap source.1 target.1 at hatomMap
  subst sourceMap
  subst atomMap
  rfl

/-- Decode a finite presentation to its actual semantic pointed arrow. -/
def toSemanticCart {U : AtomCarrier.{u}}
    (presentation : CartPresentation U) : CartSemanticInput U where
  source := decodeFiniteInstance presentation.backing
    presentation.code.1.source
  target := decodeFiniteInstance presentation.backing
    presentation.code.1.target
  hom := decodeCartHom presentation.backing presentation.code

/--
The realization output satisfies the actual G-101 morphism laws.  These proofs
were generated inside `decodeCartHom`; callers supply no separate certificate.
-/
theorem toSemanticCart_sound {U : AtomCarrier.{u}}
    (presentation : CartPresentation U) :
    (∀ source,
      (toSemanticCart presentation).target.doctrine.normalize
          ((toSemanticCart presentation).hom.doctrineHom.sourceMap source) =
        (toSemanticCart presentation).hom.doctrineHom.sourceMap
          ((toSemanticCart presentation).source.doctrine.normalize source)) ∧
    (∀ source atom,
      (toSemanticCart presentation).source.doctrine.extracts source atom ↔
        (toSemanticCart presentation).target.doctrine.extracts
          ((toSemanticCart presentation).hom.doctrineHom.sourceMap source)
          ((toSemanticCart presentation).hom.doctrineHom.atomEquiv atom)) ∧
    (toSemanticCart presentation).hom.doctrineHom.sourceMap
        (toSemanticCart presentation).source.source =
      (toSemanticCart presentation).target.source :=
  ⟨(toSemanticCart presentation).hom.doctrineHom.normalize_eq,
    (toSemanticCart presentation).hom.doctrineHom.extraction_iff,
    (toSemanticCart presentation).hom.source_eq⟩

/-- Presentation of the reviewed identity over an ambient backing. -/
def finiteIdentityPresentation {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) : CartPresentation U where
  backing := backing
  code := finiteIdentityCode

/-- Presentation of the reviewed nonidentity Atom transport. -/
def finiteAtomTransportPresentation {U : AtomCarrier.{u}}
    (backing : FiniteModelBacking U) : CartPresentation U where
  backing := backing
  code := finiteAtomTransportCode

/-- The reviewed transport decoder has the reviewed G-101 Atom equivalence. -/
theorem finiteAtomTransportPresentation_atomEquiv_eq_reviewed :
    (toSemanticCart
      (finiteAtomTransportPresentation finiteModelBacking)).hom.doctrineHom.atomEquiv =
      finiteTransportAtomEquiv := by
  change (decodeCartHom finiteModelBacking finiteAtomTransportCode).doctrineHom.atomEquiv =
    finiteTransportAtomEquiv
  rw [decodeCartHom_atomEquiv]
  simpa [finiteAtomTransportCode, finiteAtomTransportRawCode,
    finiteFrameEquiv] using finiteReviewedAtomSwapEquiv_eq_reviewed

/-- The decoded reviewed transport is genuinely nonidentity on Atoms. -/
theorem finiteAtomTransportPresentation_nonidentity :
    (toSemanticCart
      (finiteAtomTransportPresentation finiteModelBacking)).hom.doctrineHom.atomEquiv ≠
      Equiv.refl FiniteModel.carrier.Atom := by
  rw [finiteAtomTransportPresentation_atomEquiv_eq_reviewed]
  exact finiteTransportAtomEquiv_nonidentity

/-! ## Source-level pullback readiness of the reviewed schema -/

/--
The pullback of two identity finite source tables is the diagonal and remains
the reviewed source type.  This is the code-level closure fact needed before
the later doctrinal `pullbackPresentation` producer is constructed.
-/
def finiteSourceDiagonalPullbackEquiv :
    {pair : FiniteModel.ExtractionSource × FiniteModel.ExtractionSource //
      pair.1 = pair.2} ≃ FiniteModel.ExtractionSource where
  toFun pair := pair.1.1
  invFun source := ⟨(source, source), rfl⟩
  left_inv pair := by
    rcases pair with ⟨⟨left, right⟩, equality⟩
    change left = right at equality
    subst right
    rfl
  right_inv _ := rfl

/-- The finite diagonal pullback has exactly the reviewed two source values. -/
theorem finiteSourceDiagonalPullback_card :
    Fintype.card
      {pair : FiniteModel.ExtractionSource × FiniteModel.ExtractionSource //
        pair.1 = pair.2} = 2 := by
  rw [Fintype.card_congr finiteSourceDiagonalPullbackEquiv]
  decide

/--
The source pullback of any two validated presentation tables is represented by
the same reviewed diagonal source.  This consumes the validation theorem rather
than assuming identity maps separately.
-/
def validatedSourcePullbackEquiv
    (left right : ValidatedCartCode) :
    {pair : FiniteModel.ExtractionSource × FiniteModel.ExtractionSource //
      left.1.sourceMap pair.1 = right.1.sourceMap pair.2} ≃
      FiniteModel.ExtractionSource := by
  rw [validatedCartCode_sourceMap_eq_id left,
    validatedCartCode_sourceMap_eq_id right]
  exact finiteSourceDiagonalPullbackEquiv

/-- Every validated source-table pullback has exactly two elements. -/
theorem validatedSourcePullback_card
    (left right : ValidatedCartCode) :
    Fintype.card
      {pair : FiniteModel.ExtractionSource × FiniteModel.ExtractionSource //
        left.1.sourceMap pair.1 = right.1.sourceMap pair.2} = 2 := by
  rw [Fintype.card_congr (validatedSourcePullbackEquiv left right)]
  decide

/-! ## Realization provenance -/

/-- A semantic arrow together with the presentation that realizes it. -/
structure RealizableHom (U : AtomCarrier.{u}) where
  semantic : CartSemanticInput U
  presentation : CartPresentation U
  realization_eq : toSemanticCart presentation = semantic

/-- Canonical realizable arrow generated by one validated presentation. -/
def realizableHomOf {U : AtomCarrier.{u}}
    (presentation : CartPresentation U) : RealizableHom U where
  semantic := toSemanticCart presentation
  presentation := presentation
  realization_eq := rfl

/-! ## Fixed equality/membership condition language -/

/-- Operand sorts of the four-field condition vocabulary. -/
inductive CartFieldKind
  | source
  | atom
  | sourceMap
  | atomMap

/-- The finite value type of each operand sort. -/
def CartFieldValue : CartFieldKind → Type
  | .source => FiniteModel.ExtractionSource
  | .atom => FiniteModel.FiniteAtom
  | .sourceMap =>
      FiniteModel.ExtractionSource → FiniteModel.ExtractionSource
  | .atomMap => FiniteModel.FiniteAtom → FiniteModel.FiniteAtom

instance cartFieldValueDecidableEq (kind : CartFieldKind) :
    DecidableEq (CartFieldValue kind) := by
  cases kind <;> simp only [CartFieldValue] <;> infer_instance

/--
All component projections of the four raw fields.  Source and target each have
an excluded-Atom and selected-source component; the two table fields are read
as whole finite tables here and cellwise by `allCells` below.
-/
inductive CartProjection : (kind : CartFieldKind) → Type
  | sourceExcluded : CartProjection .atom
  | sourcePoint : CartProjection .source
  | targetExcluded : CartProjection .atom
  | targetPoint : CartProjection .source
  | sourceMap : CartProjection .sourceMap
  | atomMap : CartProjection .atomMap

/-- Read one fixed projection from a raw four-field code. -/
def readCartProjection {kind : CartFieldKind}
    (projection : CartProjection kind) (code : CartRawCode) :
    CartFieldValue kind :=
  match projection with
  | .sourceExcluded => code.source.1
  | .sourcePoint => code.source.2
  | .targetExcluded => code.target.1
  | .targetPoint => code.target.2
  | .sourceMap => code.sourceMap
  | .atomMap => code.atomMap

/-- The only named constants available at this lower cartesian layer. -/
inductive CartNamedConstant : (kind : CartFieldKind) → Type
  | unitSource : CartNamedConstant .source
  | identitySourceMap : CartNamedConstant .sourceMap
  | identityAtomMap : CartNamedConstant .atomMap

/-- Interpret one allowed named constant. -/
def readCartNamedConstant {kind : CartFieldKind}
    (constant : CartNamedConstant kind) : CartFieldValue kind :=
  match constant with
  | .unitSource => .all
  | .identitySourceMap => id
  | .identityAtomMap => id

/-- Terms in field-value equality and membership atoms. -/
inductive CartFieldTerm : (kind : CartFieldKind) → Type
  | projection {kind : CartFieldKind}
      (projection : CartProjection kind) : CartFieldTerm kind
  | constant {kind : CartFieldKind}
      (constant : CartNamedConstant kind) : CartFieldTerm kind

/-- Evaluate one fixed field term. -/
def evalCartFieldTerm {kind : CartFieldKind}
    (term : CartFieldTerm kind) (code : CartRawCode) :
    CartFieldValue kind :=
  match term with
  | .projection projection => readCartProjection projection code
  | .constant constant => readCartNamedConstant constant

/-- Presentation-derived singleton sets available to membership atoms. -/
inductive CartDerivedSet : (kind : CartFieldKind) → Type
  | sourcePoint : CartDerivedSet .source
  | sourceExcluded : CartDerivedSet .atom
  | authoredSourceMap : CartDerivedSet .sourceMap
  | authoredAtomMap : CartDerivedSet .atomMap

/-- Membership in one presentation-derived finite singleton. -/
def evalCartMembership {kind : CartFieldKind}
    (value : CartFieldValue kind) (set : CartDerivedSet kind)
    (code : CartRawCode) : Bool :=
  match set with
  | .sourcePoint => decide (value = code.source.2)
  | .sourceExcluded => decide (value = code.source.1)
  | .authoredSourceMap => decide (value = code.sourceMap)
  | .authoredAtomMap => decide (value = code.atomMap)

/--
The two finite-cell equality atoms.  Both compare a table cell with the
corresponding named identity-table cell; no new property predicate is added.
-/
inductive CartUniversalEquality
  | sourceMapIdentity
  | atomMapIdentity

/-- Evaluate a genuine finite universal equality over the reviewed cell list. -/
def evalCartUniversalEquality
    (equality : CartUniversalEquality) (code : CartRawCode) : Bool :=
  match equality with
  | .sourceMapIdentity =>
      finiteExtractionSourceAll.all
        (fun source => decide (code.sourceMap source = source))
  | .atomMapIdentity =>
      FiniteModel.FiniteAtom.all.all
        (fun atom => decide (code.atomMap atom = atom))

/--
The complete four-constructor cartesian condition syntax fixed by G-110.

Relations are only field-value equality, presentation-derived finite-set
membership, finite universal equality, and conjunction.  No constructor accepts
a proposition, injectivity/surjectivity tag, checker result, lift, mate, or
external finite set.
-/
inductive CartConditionSyntax
  | fieldEq {kind : CartFieldKind}
      (left right : CartFieldTerm kind)
  | fieldMem {kind : CartFieldKind}
      (field : CartFieldTerm kind) (set : CartDerivedSet kind)
  | allCells (equality : CartUniversalEquality)
  | conjunction (left right : CartConditionSyntax)

/-- Evaluate the fixed syntax on the presentation layer, not the semantic layer. -/
def evalCartCondition {U : AtomCarrier.{u}} :
    CartConditionSyntax → CartPresentation U → Bool
  | .fieldEq left right, presentation =>
      decide
        (evalCartFieldTerm left presentation.code.1 =
          evalCartFieldTerm right presentation.code.1)
  | .fieldMem field set, presentation =>
      evalCartMembership
        (evalCartFieldTerm field presentation.code.1) set
        presentation.code.1
  | .allCells equality, presentation =>
      evalCartUniversalEquality equality presentation.code.1
  | .conjunction left right, presentation =>
      evalCartCondition left presentation &&
        evalCartCondition right presentation

/-- The reviewed identity table satisfies the finite source-cell equality. -/
theorem evalCartCondition_identity_sourceMap :
    evalCartCondition (.allCells .sourceMapIdentity)
      (finiteIdentityPresentation finiteModelBacking) = true := by
  decide

/-- The reviewed transport fails the finite Atom-table identity equality. -/
theorem evalCartCondition_transport_atomMap_nonidentity :
    evalCartCondition (.allCells .atomMapIdentity)
      (finiteAtomTransportPresentation finiteModelBacking) = false := by
  decide

/-- Membership can genuinely fail; it is not a name-only self-membership atom. -/
theorem evalCartCondition_transport_targetExcluded_not_sourceExcluded :
    evalCartCondition
      (.fieldMem (.projection .targetExcluded) (.sourceExcluded))
      (finiteAtomTransportPresentation finiteModelBacking) = false := by
  decide

/-- A source projection can be compared with the permitted unit source constant. -/
theorem evalCartCondition_identity_sourcePoint_not_unit :
    evalCartCondition
      (.fieldEq (.projection .sourcePoint) (.constant .unitSource))
      (finiteIdentityPresentation finiteModelBacking) = false := by
  decide

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
