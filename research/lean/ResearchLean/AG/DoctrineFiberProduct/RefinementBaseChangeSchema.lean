import ResearchLean.AG.DoctrineFiberProduct.ExactBottomGlobalLiftCoherence
import ResearchLean.AG.DoctrineFiberProduct.PointedDoctrinePullback
import ResearchLean.AG.DoctrineFiberProduct.RefinementCategory

/-!
# Refinement base-change schema

This module fixes the four G-114 F0 heads: the raw pointed configuration and
its isomorphisms, the one-constructor closed condition language, the regime
signature, and the two-branch artifact.  It also gives names to the mixed
pullback objects needed to type the square.  No regime, branch, qualification,
or counterexample is constructed here.

## Implementation notes

The raw configuration stores only an exact pointed cospan and one pointed
refinement.  Both pullback objects and the pulled refinement are generated
definitions.  The regime records universal refinement cleavages and the
uniquely characterized exact-square route; reverse functors, relative hom
equivalences, and the comparison natural transformation are generated from
factorization uniqueness.  It contains neither a condition-membership field nor
an `IsIso` assertion about that comparison.  A callback-valued condition language
and a supplied pullback/regime certificate were rejected because either would
place the desired conclusion in the input.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Raw configuration and generated mixed pullback -/

/--
The G-114 square input: an exact pointed cospan and a pointed refinement of its
first endpoint.  The two pullback objects, the pulled leg, reverse transport,
and mate data are deliberately absent.
-/
structure LegacyRefinementBCConfiguration (U : AtomCarrier.{u}) where
  /-- Refined first endpoint. -/
  DOnePrime : ExtractionInstance U
  /-- Original first endpoint. -/
  DOne : ExtractionInstance U
  /-- Second endpoint of the exact cospan. -/
  DTwo : ExtractionInstance U
  /-- Base of the exact cospan. -/
  Base : ExtractionInstance U
  /-- First exact cospan leg. -/
  sigmaOne : DOne ⟶ Base
  /-- Second exact cospan leg. -/
  sigmaTwo : DTwo ⟶ Base
  /-- Pointed refinement replacing the first endpoint. -/
  refinement : PointedRefinementHom DOnePrime DOne

namespace LegacyRefinementBCConfiguration

/-- The generated exact pullback `P`. -/
def pullback (C : LegacyRefinementBCConfiguration U) : ExtractionInstance U :=
  pointedPullback C.sigmaOne C.sigmaTwo

/-- Sources of the generated mixed pullback `P'`. -/
abbrev PulledSource (C : LegacyRefinementBCConfiguration U) :=
  {pair : C.DOnePrime.doctrine.Source × C.DTwo.doctrine.Source //
    C.sigmaOne.doctrineHom.sourceMap
        (C.refinement.doctrineHom.sourceMap pair.1) =
      C.sigmaTwo.doctrineHom.sourceMap pair.2}

/-- The mixed pullback doctrine generated from forward refinement preservation. -/
def pulledDoctrine (C : LegacyRefinementBCConfiguration U) : ExtractionDoctrine U where
  Source := C.PulledSource
  Vocabulary := C.DOnePrime.doctrine.Vocabulary
  SemanticReading := C.DOnePrime.doctrine.SemanticReading
  Resolution := C.DOnePrime.doctrine.Resolution
  vocabulary := C.DOnePrime.doctrine.vocabulary
  semanticReading := C.DOnePrime.doctrine.semanticReading
  resolution := C.DOnePrime.doctrine.resolution
  vocabularyAllows := C.DOnePrime.doctrine.vocabularyAllows
  semanticAllows := fun reading source atom =>
    C.DOnePrime.doctrine.semanticAllows reading source.val.1 atom
  resolutionAllows := fun resolution source atom =>
    C.DOnePrime.doctrine.resolutionAllows resolution source.val.1 atom
  sourceSemantics := fun source atom =>
    C.DOnePrime.doctrine.sourceSemantics source.val.1 atom
  normalize := fun source =>
    ⟨(C.DOnePrime.doctrine.normalize source.val.1,
      C.DTwo.doctrine.normalize source.val.2), by
      rw [← C.refinement.doctrineHom.normalize_eq,
        ← C.sigmaOne.doctrineHom.normalize_eq,
        ← C.sigmaTwo.doctrineHom.normalize_eq, source.property]⟩

/-- The selected mixed-pullback source is generated from pointed input data. -/
def pulledSource (C : LegacyRefinementBCConfiguration U) : C.PulledSource :=
  ⟨(C.DOnePrime.source, C.DTwo.source), by
    rw [C.refinement.source_eq, C.sigmaOne.source_eq, C.sigmaTwo.source_eq]⟩

/-- The generated pointed mixed pullback `P'`. -/
def pulled (C : LegacyRefinementBCConfiguration U) : ExtractionInstance U where
  doctrine := C.pulledDoctrine
  source := C.pulledSource

/-- The exact vertical projection `fst' : P' ⟶ D₁'`. -/
def pulledFst (C : LegacyRefinementBCConfiguration U) : C.pulled ⟶ C.DOnePrime where
  doctrineHom :=
    { sourceMap := fun source => source.val.1
      atomEquiv := Equiv.refl U.Atom
      normalize_eq := fun _ => rfl
      extraction_iff := fun _ _ => Iff.rfl }
  source_eq := rfl

/-- The exact vertical projection `fst : P ⟶ D₁`. -/
def pullbackFst (C : LegacyRefinementBCConfiguration U) : C.pullback ⟶ C.DOne :=
  pointedPullbackFst C.sigmaOne C.sigmaTwo

/-- The pulled horizontal refinement `f* : P' → P`. -/
def pulledRefinement (C : LegacyRefinementBCConfiguration U) :
    PointedRefinementHom C.pulled C.pullback where
  doctrineHom :=
    { sourceMap := fun source =>
        ⟨(C.refinement.doctrineHom.sourceMap source.val.1, source.val.2),
          source.property⟩
      atomMap := C.refinement.doctrineHom.atomMap
      atomMap_bijective := C.refinement.doctrineHom.atomMap_bijective
      normalize_eq := by
        intro source
        apply Subtype.ext
        apply Prod.ext
        · exact C.refinement.doctrineHom.normalize_eq source.val.1
        · rfl
      extraction_forward := by
        intro source atom extracted
        exact C.refinement.doctrineHom.extraction_forward
          source.val.1 atom extracted }
  source_eq := by
    apply Subtype.ext
    apply Prod.ext
    · exact C.refinement.source_eq
    · rfl

/-- The generated square commutes in the pointed refinement direction. -/
theorem pulled_square_commutes (C : LegacyRefinementBCConfiguration U) :
    C.pulledRefinement.comp (PointedRefinementHom.ofExact C.pullbackFst) =
      (PointedRefinementHom.ofExact C.pulledFst).comp C.refinement := by
  apply PointedRefinementHom.ext
  apply RefinementDoctrineHom.ext
  · rfl
  · rfl

/-! ## K1 unconditional forward stability of the generated square -/

/-- The generated horizontal pullback leg preserves extraction unconditionally. -/
theorem pulledRefinement_extraction_forward (C : LegacyRefinementBCConfiguration U)
    (source : C.pulled.doctrine.Source) (atom : U.Atom)
    (extracted : C.pulled.doctrine.extracts source atom) :
    C.pullback.doctrine.extracts
      (C.pulledRefinement.doctrineHom.sourceMap source)
      (C.pulledRefinement.doctrineHom.atomMap atom) :=
  C.pulledRefinement.doctrineHom.extraction_forward source atom extracted

/-- The generated exact projection `fst'` preserves extraction. -/
theorem pulledFst_extraction_forward (C : LegacyRefinementBCConfiguration U)
    (source : C.pulled.doctrine.Source) (atom : U.Atom)
    (extracted : C.pulled.doctrine.extracts source atom) :
    C.DOnePrime.doctrine.extracts
      (C.pulledFst.doctrineHom.sourceMap source)
      (C.pulledFst.doctrineHom.atomEquiv atom) :=
  (C.pulledFst.doctrineHom.extraction_iff source atom).mpr extracted

/-- The generated exact projection `fst` preserves extraction. -/
theorem pullbackFst_extraction_forward (C : LegacyRefinementBCConfiguration U)
    (source : C.pullback.doctrine.Source) (atom : U.Atom)
    (extracted : C.pullback.doctrine.extracts source atom) :
    C.DOne.doctrine.extracts
      (C.pullbackFst.doctrineHom.sourceMap source)
      (C.pullbackFst.doctrineHom.atomEquiv atom) :=
  (C.pullbackFst.doctrineHom.extraction_iff source atom).mpr extracted

end LegacyRefinementBCConfiguration

/-! ## Configuration isomorphism head -/

/--
Componentwise configuration isomorphism, including both cospan squares and the
pointed refinement square.  The refinement endpoint uses the dedicated pointed
refinement isomorphism rather than silently requiring exactness.
-/
structure LegacyRefinementBCConfigurationIso
    (C C' : LegacyRefinementBCConfiguration U) where
  /-- Isomorphism of the refined endpoint. -/
  DOnePrimeIso : PointedRefinementIso C.DOnePrime C'.DOnePrime
  /-- Exact isomorphism of the original first endpoint. -/
  DOneIso : C.DOne ≅ C'.DOne
  /-- Exact isomorphism of the second endpoint. -/
  DTwoIso : C.DTwo ≅ C'.DTwo
  /-- Exact isomorphism of the cospan base. -/
  BaseIso : C.Base ≅ C'.Base
  /-- Naturality square for the first exact cospan leg. -/
  sigmaOne_commutes :
    C.sigmaOne ≫ BaseIso.hom = DOneIso.hom ≫ C'.sigmaOne
  /-- Naturality square for the second exact cospan leg. -/
  sigmaTwo_commutes :
    C.sigmaTwo ≫ BaseIso.hom = DTwoIso.hom ≫ C'.sigmaTwo
  /-- Naturality square for the pointed refinement leg. -/
  refinement_commutes :
    C.refinement.comp (PointedRefinementHom.ofExact DOneIso.hom) =
      DOnePrimeIso.hom.comp C'.refinement

/-! ## Closed language and fixed term -/

/-- The unique card-fixed refinement condition constructor. -/
inductive RefinementBCConditionSyntax (U : AtomCarrier.{u})
  | pulledLocusExtractionReflecting

/-- Sources of the refined endpoint that occur in the compatible pullback locus. -/
def InPulledLocus (C : LegacyRefinementBCConfiguration U)
    (source : C.DOnePrime.doctrine.Source) : Prop :=
  ∃ second : C.DTwo.doctrine.Source,
    C.sigmaOne.doctrineHom.sourceMap
        (C.refinement.doctrineHom.sourceMap source) =
      C.sigmaTwo.doctrineHom.sourceMap second

/-- Extraction reflection restricted to the generated compatible locus. -/
def PulledLocusExtractionReflecting (C : LegacyRefinementBCConfiguration U) : Prop :=
  ∀ (source : C.DOnePrime.doctrine.Source), InPulledLocus C source →
    ∀ atom : U.Atom,
      C.DOne.doctrine.extracts
          (C.refinement.doctrineHom.sourceMap source)
          (C.refinement.doctrineHom.atomMap atom) →
        C.DOnePrime.doctrine.extracts source atom

/-- Evaluate the closed language without reading a regime, lift, mate, or certificate. -/
def evalRefinementBCCondition :
    RefinementBCConditionSyntax U → LegacyRefinementBCConfiguration U → Prop
  | .pulledLocusExtractionReflecting, C =>
      PulledLocusExtractionReflecting C

/-- Canonical carrier rebase of the parameter-free one-constructor language. -/
def rebaseRefinementBCCondition
    {V : AtomCarrier.{u}} :
    RefinementBCConditionSyntax U → RefinementBCConditionSyntax V
  | .pulledLocusExtractionReflecting => .pulledLocusExtractionReflecting

/-- Normalization has the unique constructor as its unique normal form. -/
def normalizeRefinementBCCondition :
    RefinementBCConditionSyntax U → RefinementBCConditionSyntax U
  | .pulledLocusExtractionReflecting => .pulledLocusExtractionReflecting

/-- Normalization is complete for the closed evaluator. -/
theorem normalizeRefinementBCCondition_eval_iff
    (term : RefinementBCConditionSyntax U)
    (C : LegacyRefinementBCConfiguration U) :
    evalRefinementBCCondition (normalizeRefinementBCCondition term) C ↔
      evalRefinementBCCondition term C := by
  cases term
  exact Iff.rfl

/-- The mechanically adopted card-fixed predicate term. -/
def pulledLocusExtractionReflectingTerm : RefinementBCConditionSyntax U :=
  .pulledLocusExtractionReflecting

/-- The one-entry registry fixed before every G-114 proof. -/
def refinementBCConditionCandidates : List (RefinementBCConditionSyntax U) :=
  [pulledLocusExtractionReflectingTerm]

/-- The registry head is the card-fixed term. -/
theorem refinementBCConditionCandidates_head :
    (refinementBCConditionCandidates (U := U)).head? =
      some pulledLocusExtractionReflectingTerm :=
  rfl

/-- The fixed registry has no transition target. -/
theorem refinementBCConditionCandidates_second :
    (refinementBCConditionCandidates (U := U)).tail.head? = none :=
  rfl

/-- The evaluator exposes exactly compatible-locus extraction reflection. -/
theorem eval_pulledLocusExtractionReflecting_iff
    (C : LegacyRefinementBCConfiguration U) :
    evalRefinementBCCondition pulledLocusExtractionReflectingTerm C ↔
      PulledLocusExtractionReflecting C :=
  Iff.rfl

/-! ## Relative hom surface and regime head -/

/--
An upper package morphism lying over a pointed refinement.

The lower arrow is the authored lax refinement itself; it is not reconstructed
from the exact base of `PackageTotalHom`.  The upper package change remains
exact and is required to use the Atom equivalence canonically derived from the
refinement.  Thus this type can be inhabited by a genuinely non-exact
refinement whenever the selected package families support the required upper
change.
-/
structure RefinementOverHom
    {X Y : ExtractionInstance U} (f : PointedRefinementHom X Y)
    (source : CoreFiber X) (target : CoreFiber Y) where
  /-- The full lax pointed lower arrow, including its source map. -/
  lower : PointedRefinementHom X Y
  /-- The lower projection is the authored refinement, not merely its Atom map. -/
  lower_eq : lower = f
  /-- Complete upper package change over the fixed lower refinement. -/
  upper : SignedExactCoreReadingHom source.1 target.1
  /-- The upper Atom equivalence is generated by the stored full lower refinement. -/
  atomEquiv_eq : upper.atomEquiv = lower.doctrineHom.atomEquiv

namespace RefinementOverHom

/-- Relative homs are determined by their complete upper package changes. -/
@[ext]
theorem ext
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {target : CoreFiber Y}
    {first second : RefinementOverHom f source target}
    (hupper : first.upper = second.upper) : first = second := by
  rcases first with ⟨lower₁, rfl, upper₁, atom₁⟩
  rcases second with ⟨lower₂, rfl, upper₂, atom₂⟩
  cases hupper
  rfl

/--
Every relative exact upper change reflects extraction along the complete lower
source map at the selected point.  This is generated from `upper.extraction_eq`,
the two fiber point equalities, and `lower.source_eq`; it is not lift input.
-/
theorem selected_extraction_iff
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {target : CoreFiber Y}
    (hom : RefinementOverHom f source target) (atom : U.Atom) :
    Y.doctrine.extracts
        (hom.lower.doctrineHom.sourceMap X.source)
        (hom.lower.doctrineHom.atomMap atom) ↔
      X.doctrine.extracts X.source atom := by
  rcases source with ⟨sourcePackage, hsource⟩
  rcases target with ⟨targetPackage, htarget⟩
  change packagePoint sourcePackage = X at hsource
  change packagePoint targetPackage = Y at htarget
  subst X
  subst Y
  rw [hom.lower.source_eq]
  change targetPackage.reading.doctrine.extracts
      targetPackage.reading.source (hom.lower.doctrineHom.atomMap atom) ↔
    sourcePackage.reading.doctrine.extracts sourcePackage.reading.source atom
  rw [← targetPackage.family_mem_iff_extracts,
    ← sourcePackage.family_mem_iff_extracts]
  change targetPackage.family.mem
      (hom.lower.doctrineHom.atomEquiv atom) ↔ sourcePackage.family.mem atom
  rw [← hom.atomEquiv_eq, hom.upper.extraction_eq]
  constructor
  · rintro ⟨sourceAtom, hmem, heq⟩
    exact (hom.upper.atomEquiv.injective heq).symm ▸ hmem
  · intro hmem
    exact ⟨atom, hmem, rfl⟩

/-- A vertical core-fiber morphism has the identity upper Atom equivalence. -/
theorem vertical_upper_atomEquiv_id
    {X : ExtractionInstance U} {source target : CoreFiber X}
    (vertical : source ⟶ target) :
    vertical.1.upper.atomEquiv = Equiv.refl U.Atom := by
  rw [vertical.1.atomEquiv_eq]
  letI : (packageProjection U).IsHomLift (𝟙 X) vertical.1 := vertical.2
  have hfac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (𝟙 X) vertical.1
  have hatom := congrArg (fun hom => hom.doctrineHom.atomEquiv) hfac
  simpa using hatom

/-- Precompose a relative upper hom by an exact vertical fiber morphism. -/
noncomputable def precomp
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {first second : CoreFiber X} {target : CoreFiber Y}
    (vertical : first ⟶ second) (hom : RefinementOverHom f second target) :
    RefinementOverHom f first target where
  lower := hom.lower
  lower_eq := hom.lower_eq
  upper := vertical.1.upper.comp hom.upper
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    change hom.upper.atomEquiv (vertical.1.upper.atomEquiv atom) = _
    rw [vertical_upper_atomEquiv_id, hom.atomEquiv_eq]
    rfl

/-- Postcompose a relative upper hom by an exact vertical fiber morphism. -/
noncomputable def postcomp
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {first second : CoreFiber Y}
    (hom : RefinementOverHom f source first) (vertical : first ⟶ second) :
    RefinementOverHom f source second where
  lower := hom.lower
  lower_eq := hom.lower_eq
  upper := hom.upper.comp vertical.1.upper
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    change vertical.1.upper.atomEquiv (hom.upper.atomEquiv atom) = _
    rw [vertical_upper_atomEquiv_id, hom.atomEquiv_eq]
    rfl

@[simp]
theorem precomp_id
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {target : CoreFiber Y}
    (hom : RefinementOverHom f source target) :
    precomp (𝟙 source) hom = hom := by
  apply ext
  exact PackageTotalHom.upper_id_comp hom.upper

@[simp]
theorem postcomp_id
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {target : CoreFiber Y}
    (hom : RefinementOverHom f source target) :
    postcomp hom (𝟙 target) = hom := by
  apply ext
  exact PackageTotalHom.upper_comp_id hom.upper

theorem precomp_comp
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {first second third : CoreFiber X} {target : CoreFiber Y}
    (left : first ⟶ second) (right : second ⟶ third)
    (hom : RefinementOverHom f third target) :
    precomp (left ≫ right) hom = precomp left (precomp right hom) := by
  apply ext
  exact PackageTotalHom.upper_comp_assoc left.1.upper right.1.upper hom.upper

theorem postcomp_comp
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {first second third : CoreFiber Y}
    (hom : RefinementOverHom f source first)
    (left : first ⟶ second) (right : second ⟶ third) :
    postcomp hom (left ≫ right) = postcomp (postcomp hom left) right := by
  apply ext
  exact (PackageTotalHom.upper_comp_assoc hom.upper left.1.upper right.1.upper).symm

theorem precomp_postcomp
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {first second : CoreFiber X} {left right : CoreFiber Y}
    (sourceVertical : first ⟶ second)
    (hom : RefinementOverHom f second left)
    (targetVertical : left ⟶ right) :
    precomp sourceVertical (postcomp hom targetVertical) =
      postcomp (precomp sourceVertical hom) targetVertical := by
  apply ext
  exact (PackageTotalHom.upper_comp_assoc
    sourceVertical.1.upper hom.upper targetVertical.1.upper).symm

end RefinementOverHom

/--
An objectwise cartesian lift over a genuinely lax pointed refinement.

Factorization and uniqueness are stated in the fixed relative hom surface.  No
reverse functor, hom equivalence, or mate is supplied here; all three are
generated below from this universal data.
-/
structure LegacyRefinementCartesianLift
    {X Y : ExtractionInstance U} (f : PointedRefinementHom X Y)
    (target : CoreFiber Y) where
  /-- Domain package of the selected cartesian lift. -/
  domain : CoreFiber X
  /-- Selected upper package morphism over the lax lower refinement. -/
  hom : RefinementOverHom f domain target
  /-- Universal vertical factor. -/
  factor : ∀ {source : CoreFiber X}, RefinementOverHom f source target →
    (source ⟶ domain)
  /-- The selected factor has the required triangle. -/
  factor_fac : ∀ {source : CoreFiber X} (candidate : RefinementOverHom f source target),
    RefinementOverHom.precomp (factor candidate) hom = candidate
  /-- The triangle determines the vertical factor uniquely. -/
  factor_unique : ∀ {source : CoreFiber X}
    (candidate : RefinementOverHom f source target) (vertical : source ⟶ domain),
    RefinementOverHom.precomp vertical hom = candidate →
      vertical = factor candidate

/-- A caller-free selection of a cartesian refinement lift at every target package. -/
structure LegacyRefinementCartesianCleavage
    {X Y : ExtractionInstance U} (f : PointedRefinementHom X Y) where
  /-- The only choice: one universal lift at each target package. -/
  lift : ∀ target : CoreFiber Y, LegacyRefinementCartesianLift f target

namespace LegacyRefinementCartesianCleavage

/-- Reverse transport on objects, generated by the selected lift domains. -/
def reverseObject
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f) (target : CoreFiber Y) : CoreFiber X :=
  (cleavage.lift target).domain

/-- Reverse transport on arrows, generated as the unique factor of postcomposition. -/
noncomputable def reverseMap
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f)
    {first second : CoreFiber Y} (vertical : first ⟶ second) :
    cleavage.reverseObject first ⟶ cleavage.reverseObject second :=
  (cleavage.lift second).factor
    (RefinementOverHom.postcomp (cleavage.lift first).hom vertical)

/-- The generated reverse map has its defining cartesian factor triangle. -/
theorem reverseMap_fac
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f)
    {first second : CoreFiber Y} (vertical : first ⟶ second) :
    RefinementOverHom.precomp (cleavage.reverseMap vertical)
        (cleavage.lift second).hom =
      RefinementOverHom.postcomp (cleavage.lift first).hom vertical :=
  (cleavage.lift second).factor_fac _

/-- Generated reverse transport preserves identities by universal uniqueness. -/
theorem reverseMap_id
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f) (target : CoreFiber Y) :
    cleavage.reverseMap (𝟙 target) = 𝟙 (cleavage.reverseObject target) := by
  symm
  apply (cleavage.lift target).factor_unique
  rw [RefinementOverHom.precomp_id, RefinementOverHom.postcomp_id]

/-- Generated reverse transport preserves composition by universal uniqueness. -/
theorem reverseMap_comp
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f)
    {first second third : CoreFiber Y}
    (left : first ⟶ second) (right : second ⟶ third) :
    cleavage.reverseMap (left ≫ right) =
      cleavage.reverseMap left ≫ cleavage.reverseMap right := by
  symm
  apply (cleavage.lift third).factor_unique
  rw [RefinementOverHom.precomp_comp, reverseMap_fac,
    RefinementOverHom.precomp_postcomp, reverseMap_fac,
    ← RefinementOverHom.postcomp_comp]

/-- The contravariant reverse functor generated from refinement cartesian uniqueness. -/
noncomputable def reverseFunctor
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f) : CoreFiber Y ⥤ CoreFiber X where
  obj := cleavage.reverseObject
  map := cleavage.reverseMap
  map_id := cleavage.reverseMap_id
  map_comp := cleavage.reverseMap_comp

/-- Relative hom equivalence generated by the selected cartesian lift. -/
noncomputable def homEquiv
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f)
    (source : CoreFiber X) (target : CoreFiber Y) :
    RefinementOverHom f source target ≃
      (source ⟶ cleavage.reverseFunctor.obj target) where
  toFun := (cleavage.lift target).factor
  invFun vertical := RefinementOverHom.precomp vertical (cleavage.lift target).hom
  left_inv := (cleavage.lift target).factor_fac
  right_inv vertical := by
    symm
    apply (cleavage.lift target).factor_unique
    rfl

/-- The generated hom equivalence has the literal factorization equation. -/
theorem homEquiv_fac
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f)
    (source : CoreFiber X) (target : CoreFiber Y)
    (hom : RefinementOverHom f source target) :
    RefinementOverHom.precomp (cleavage.homEquiv source target hom)
        (cleavage.lift target).hom = hom :=
  (cleavage.lift target).factor_fac hom

/-- Source-variable naturality of the generated relative hom equivalence. -/
theorem homEquiv_natural_source
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f)
    {first second : CoreFiber X} (vertical : first ⟶ second)
    (target : CoreFiber Y) (hom : RefinementOverHom f second target) :
    cleavage.homEquiv first target
        (RefinementOverHom.precomp vertical hom) =
      vertical ≫ cleavage.homEquiv second target hom := by
  symm
  apply (cleavage.lift target).factor_unique
  rw [RefinementOverHom.precomp_comp, homEquiv_fac]

/-- Target-variable naturality of the generated relative hom equivalence. -/
theorem homEquiv_natural_target
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : LegacyRefinementCartesianCleavage f)
    (source : CoreFiber X) {first second : CoreFiber Y}
    (hom : RefinementOverHom f source first) (vertical : first ⟶ second) :
    cleavage.homEquiv source second
        (RefinementOverHom.postcomp hom vertical) =
      cleavage.homEquiv source first hom ≫ cleavage.reverseFunctor.map vertical := by
  symm
  apply (cleavage.lift second).factor_unique
  rw [RefinementOverHom.precomp_comp]
  change RefinementOverHom.precomp (cleavage.homEquiv source first hom)
      (RefinementOverHom.precomp (cleavage.reverseMap vertical)
        (cleavage.lift second).hom) = _
  rw [reverseMap_fac,
    RefinementOverHom.precomp_postcomp, homEquiv_fac]

end LegacyRefinementCartesianCleavage

/--
The G-112 exact selected lift, read with its cartesian universal property
against lax lower refinements.  A candidate over `h` factors through the exact
lift whenever its lower arrow factors as `k` followed by `g`; the factor and
its uniqueness are the apparatus from which the mixed BC route is generated.
-/
structure RefinementExactCartesianLift
    {Y Z : ExtractionInstance U} (g : Y ⟶ Z)
    (target : CoreFiber Z)
    (selected : StrongCartesianLift (cartSemanticInputOfHom g) target) where
  /-- Universal factor through the selected exact lift. -/
  factor : ∀ {W : ExtractionInstance U}
    (h : PointedRefinementHom W Z) (k : PointedRefinementHom W Y),
    k.comp (PointedRefinementHom.ofExact g) = h →
      ∀ {source : CoreFiber W}, RefinementOverHom h source target →
        RefinementOverHom k source selected.domainObject
  /-- The generated factor has the required upper triangle. -/
  factor_fac : ∀ {W : ExtractionInstance U}
    (h : PointedRefinementHom W Z) (k : PointedRefinementHom W Y)
    (square : k.comp (PointedRefinementHom.ofExact g) = h)
    {source : CoreFiber W} (candidate : RefinementOverHom h source target),
    (factor h k square candidate).upper.comp selected.hom.upper = candidate.upper
  /-- The upper triangle uniquely determines the lax relative factor. -/
  factor_unique : ∀ {W : ExtractionInstance U}
    (h : PointedRefinementHom W Z) (k : PointedRefinementHom W Y)
    (square : k.comp (PointedRefinementHom.ofExact g) = h)
    {source : CoreFiber W} (candidate : RefinementOverHom h source target)
    (other : RefinementOverHom k source selected.domainObject),
    other.upper.comp selected.hom.upper = candidate.upper →
      other = factor h k square candidate

/-- Explicit two-sided upper inverse for one G-112 selected exact lift. -/
structure ExactSelectedLiftUpperInverse
    {X Y : ExtractionInstance U} (g : X ⟶ Y)
    (target : CoreFiber Y)
    (selected : StrongCartesianLift (cartSemanticInputOfHom g) target) where
  inv : SignedExactCoreReadingHom target.1 selected.domain
  hom_inv : selected.hom.upper.comp inv =
    SignedExactCoreReadingHom.refl selected.domain
  inv_hom : inv.comp selected.hom.upper =
    SignedExactCoreReadingHom.refl target.1
  inv_atomEquiv_apply : ∀ atom : U.Atom,
    inv.atomEquiv (g.doctrineHom.atomEquiv atom) = atom

namespace ExactSelectedLiftUpperInverse

/-- The selected upper map uses the authored exact lower Atom equivalence. -/
theorem selected_atomEquiv_apply
    {X Y : ExtractionInstance U} {g : X ⟶ Y}
    {target : CoreFiber Y}
    {selected : StrongCartesianLift (cartSemanticInputOfHom g) target}
    (data : ExactSelectedLiftUpperInverse g target selected) (atom : U.Atom) :
    selected.hom.upper.atomEquiv atom = g.doctrineHom.atomEquiv atom := by
  apply data.inv.atomEquiv.injective
  have hcancel := congrArg (fun upper => upper.atomEquiv atom) data.hom_inv
  change data.inv.atomEquiv (selected.hom.upper.atomEquiv atom) = atom at hcancel
  rw [hcancel, data.inv_atomEquiv_apply]

/-- A two-sided upper inverse generates the mixed refinement factorization. -/
noncomputable def toRefinementExactCartesianLift
    {X Y : ExtractionInstance U} {g : X ⟶ Y}
    {target : CoreFiber Y}
    {selected : StrongCartesianLift (cartSemanticInputOfHom g) target}
    (data : ExactSelectedLiftUpperInverse g target selected) :
    RefinementExactCartesianLift g target selected where
  factor := by
    intro W h k square source candidate
    refine {
      lower := k
      lower_eq := rfl
      upper := candidate.upper.comp data.inv
      atomEquiv_eq := ?_
    }
    apply Equiv.ext
    intro atom
    change data.inv.atomEquiv (candidate.upper.atomEquiv atom) =
      k.doctrineHom.atomEquiv atom
    rw [candidate.atomEquiv_eq, candidate.lower_eq]
    have hsquare := congrArg
      (fun lower => lower.doctrineHom.atomMap) square
    have happ := congrFun hsquare atom
    change g.doctrineHom.atomEquiv (k.doctrineHom.atomEquiv atom) =
      h.doctrineHom.atomEquiv atom at happ
    rw [← happ]
    exact data.inv_atomEquiv_apply _
  factor_fac := by
    intro W h k square source candidate
    change (candidate.upper.comp data.inv).comp selected.hom.upper =
      candidate.upper
    rw [PackageTotalHom.upper_comp_assoc, data.inv_hom,
      PackageTotalHom.upper_comp_id]
  factor_unique := by
    intro W h k square source candidate other hfac
    apply RefinementOverHom.ext
    change other.upper = candidate.upper.comp data.inv
    calc
      other.upper = other.upper.comp
          (SignedExactCoreReadingHom.refl selected.domain) :=
        (PackageTotalHom.upper_comp_id other.upper).symm
      _ = other.upper.comp (selected.hom.upper.comp data.inv) := by
        rw [data.hom_inv]
      _ = (other.upper.comp selected.hom.upper).comp data.inv := by
        rw [PackageTotalHom.upper_comp_assoc]
      _ = candidate.upper.comp data.inv := by rw [hfac]

end ExactSelectedLiftUpperInverse

/--
The G-112 selected exact lift exposes the canonical inverse already constructed
by G-110; no regime caller supplies factorization or cancellation data.
-/
noncomputable def exact_bottom_semantic_global_selected_lift_upperInverse
    {X Y : ExtractionInstance U} (g : X ⟶ Y) (target : CoreFiber Y) :
    ExactSelectedLiftUpperInverse g target
      (exact_bottom_semantic_global_selected_lift g target) := by
  rcases target with ⟨Q, hQ⟩
  let aligned : X ⟶ packagePoint Q := g ≫ eqToHom hQ.symm
  let canonical := strongCartesianLiftOfTarget (cartSemanticInputOfHom g) ⟨Q, hQ⟩
  let selected := exact_bottom_semantic_global_selected_lift g ⟨Q, hQ⟩
  let comparison := StrongCartesianLift.domainIso canonical selected
  let canonicalInv := inverseCorePackageBackwardUpper Q aligned
  have hcomparison := congrArg PackageTotalHom.upper
    (StrongCartesianLift.domainIso_hom_fac canonical selected)
  change comparison.hom.upper.comp canonical.hom.upper =
    selected.hom.upper at hcomparison
  have hcanonicalInv : canonical.hom.upper.comp canonicalInv =
      SignedExactCoreReadingHom.refl canonical.domain := by
    exact inverseCorePackageForward_comp_backward Q aligned
  have hcanonicalBack : canonicalInv.comp canonical.hom.upper =
      SignedExactCoreReadingHom.refl Q := by
    exact inverseCorePackageBackward_comp_forward Q aligned
  have hcompHomInv := congrArg PackageTotalHom.upper comparison.hom_inv_id
  have hcompInvHom := congrArg PackageTotalHom.upper comparison.inv_hom_id
  change comparison.hom.upper.comp comparison.inv.upper =
    SignedExactCoreReadingHom.refl selected.domain at hcompHomInv
  change comparison.inv.upper.comp comparison.hom.upper =
    SignedExactCoreReadingHom.refl canonical.domain at hcompInvHom
  let comparisonInvVertical : canonical.domainObject ⟶ selected.domainObject :=
    ⟨comparison.inv,
      StrongCartesianLift.domainIso_inv_isHomLift canonical selected⟩
  have hcomparisonInvAtom :=
    RefinementOverHom.vertical_upper_atomEquiv_id comparisonInvVertical
  refine {
    inv := canonicalInv.comp comparison.inv.upper
    hom_inv := ?_
    inv_hom := ?_
    inv_atomEquiv_apply := ?_
  }
  · calc
      selected.hom.upper.comp (canonicalInv.comp comparison.inv.upper) =
          (comparison.hom.upper.comp canonical.hom.upper).comp
            (canonicalInv.comp comparison.inv.upper) := by rw [hcomparison]
      _ = comparison.hom.upper.comp
          ((canonical.hom.upper.comp canonicalInv).comp comparison.inv.upper) := by
            simp only [PackageTotalHom.upper_comp_assoc]
      _ = comparison.hom.upper.comp comparison.inv.upper := by
            rw [hcanonicalInv, PackageTotalHom.upper_id_comp]
      _ = SignedExactCoreReadingHom.refl selected.domain := hcompHomInv
  · calc
      (canonicalInv.comp comparison.inv.upper).comp selected.hom.upper =
          (canonicalInv.comp comparison.inv.upper).comp
            (comparison.hom.upper.comp canonical.hom.upper) := by rw [hcomparison]
      _ = canonicalInv.comp
          ((comparison.inv.upper.comp comparison.hom.upper).comp
            canonical.hom.upper) := by
            simp only [PackageTotalHom.upper_comp_assoc]
      _ = canonicalInv.comp canonical.hom.upper := by
            rw [hcompInvHom, PackageTotalHom.upper_id_comp]
      _ = SignedExactCoreReadingHom.refl Q := hcanonicalBack
  · intro atom
    change comparison.inv.upper.atomEquiv
        (canonicalInv.atomEquiv (g.doctrineHom.atomEquiv atom)) = atom
    rw [hcomparisonInvAtom]
    change aligned.doctrineHom.atomEquiv.symm
      (g.doctrineHom.atomEquiv atom) = atom
    have haligned : aligned.doctrineHom.atomEquiv atom =
        g.doctrineHom.atomEquiv atom := by
      change (g.doctrineHom.atomEquiv.trans
        (eqToHom hQ.symm).doctrineHom.atomEquiv) atom = _
      simp
    rw [← haligned, Equiv.symm_apply_apply]

/-- Caller-free mixed cartesian factorization generated from the selected inverse. -/
noncomputable def exact_bottom_semantic_global_refinementExactCartesianLift
    {X Y : ExtractionInstance U} (g : X ⟶ Y) (target : CoreFiber Y) :
    RefinementExactCartesianLift g target
      (exact_bottom_semantic_global_selected_lift g target) :=
  ExactSelectedLiftUpperInverse.toRefinementExactCartesianLift
    (exact_bottom_semantic_global_selected_lift_upperInverse g target)

/--
The G-114 regime signature.  Its only reverse-transport inputs are two
cartesian cleavages.  Reverse functors, their actions, and relative hom
equivalences are definitions generated from factorization uniqueness.
-/
structure LegacyRefinementBCRegime (C : LegacyRefinementBCConfiguration U) where
  /-- Universal refinement cleavage over the authored horizontal leg. -/
  baseCleavage : LegacyRefinementCartesianCleavage C.refinement
  /-- Universal refinement cleavage over the generated pulled leg. -/
  pulledCleavage : LegacyRefinementCartesianCleavage C.pulledRefinement

/-- Reverse transport along the authored refinement, generated by its cleavage. -/
noncomputable def LegacyRefinementBCRegime.reverseBase
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C) :
    CoreFiber C.DOne ⥤ CoreFiber C.DOnePrime :=
  regime.baseCleavage.reverseFunctor

/-- Reverse transport along the pulled refinement, generated by its cleavage. -/
noncomputable def LegacyRefinementBCRegime.reversePullback
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C) :
    CoreFiber C.pullback ⥤ CoreFiber C.pulled :=
  regime.pulledCleavage.reverseFunctor

/-- The generated universal lift over the authored refinement. -/
def LegacyRefinementBCRegime.baseLift
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    (target : CoreFiber C.DOne) :=
  (regime.baseCleavage.lift target).hom

/-- The generated universal lift over the pulled refinement. -/
def LegacyRefinementBCRegime.pulledLift
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    (target : CoreFiber C.pullback) :=
  (regime.pulledCleavage.lift target).hom

/-- The relative hom equivalence generated by the base cleavage. -/
noncomputable def LegacyRefinementBCRegime.baseHomEquiv
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    (source : CoreFiber C.DOnePrime) (target : CoreFiber C.DOne) :=
  regime.baseCleavage.homEquiv source target

/-- The relative hom equivalence generated by the pulled cleavage. -/
noncomputable def LegacyRefinementBCRegime.pulledHomEquiv
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    (source : CoreFiber C.pulled) (target : CoreFiber C.pullback) :=
  regime.pulledCleavage.homEquiv source target

/-- The lower refinement carried by the explicit two-step mate candidate. -/
def LegacyRefinementBCConfiguration.mateLowerPath
    (C : LegacyRefinementBCConfiguration U) :
    PointedRefinementHom C.pulled C.DOne :=
  (PointedRefinementHom.ofExact C.pulledFst).comp C.refinement

/--
The explicit path around the pulled side, before factoring through the G-112
selected lift over `pullbackFst`.
-/
noncomputable def LegacyRefinementBCRegime.mateCandidate
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    {source target : CoreFiber C.DOne} (vertical : source ⟶ target) :
    RefinementOverHom C.mateLowerPath
      ((exact_bottom_semantic_global_reindex_functor C.pulledFst).obj
        (regime.baseCleavage.reverseFunctor.obj source)) target where
  lower := C.mateLowerPath
  lower_eq := rfl
  upper := ((exact_bottom_semantic_global_selected_lift C.pulledFst
      (regime.baseCleavage.reverseFunctor.obj source)).hom.upper.comp
    (regime.baseCleavage.lift source).hom.upper).comp vertical.1.upper
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    change vertical.1.upper.atomEquiv
        ((regime.baseCleavage.lift source).hom.upper.atomEquiv
          ((exact_bottom_semantic_global_selected_lift C.pulledFst
            (regime.baseCleavage.reverseFunctor.obj source)).hom.upper.atomEquiv atom)) = _
    rw [RefinementOverHom.vertical_upper_atomEquiv_id,
      (regime.baseCleavage.lift source).hom.atomEquiv_eq,
      (regime.baseCleavage.lift source).hom.lower_eq]
    let inverseData :=
      exact_bottom_semantic_global_selected_lift_upperInverse C.pulledFst
      (regime.baseCleavage.reverseFunctor.obj source)
    rw [inverseData.selected_atomEquiv_apply]
    simp [LegacyRefinementBCConfiguration.mateLowerPath,
      PointedRefinementHom.comp, refinementHomComp,
      PointedRefinementHom.ofExact, exactToRefinement]

/-- The mixed route generated by the exact-refinement cartesian factor. -/
noncomputable def LegacyRefinementBCRegime.mateRouteBetween
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    {source target : CoreFiber C.DOne} (vertical : source ⟶ target) :
    RefinementOverHom C.pulledRefinement
      ((exact_bottom_semantic_global_reindex_functor C.pulledFst).obj
        (regime.baseCleavage.reverseFunctor.obj source))
      ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).obj target) :=
  (exact_bottom_semantic_global_refinementExactCartesianLift
      C.pullbackFst target).factor C.mateLowerPath
    C.pulledRefinement C.pulled_square_commutes (regime.mateCandidate vertical)

/-- The objectwise mixed route is the generated identity-vertical factor. -/
noncomputable def LegacyRefinementBCRegime.mateRoute
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    (target : CoreFiber C.DOne) :=
  regime.mateRouteBetween (𝟙 target)

/-- Every generated mixed route has its defining exact-lift triangle. -/
theorem LegacyRefinementBCRegime.mateRouteBetween_fac
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    {source target : CoreFiber C.DOne} (vertical : source ⟶ target) :
    (regime.mateRouteBetween vertical).upper.comp
        (exact_bottom_semantic_global_selected_lift
          C.pullbackFst target).hom.upper =
      (regime.mateCandidate vertical).upper :=
  (exact_bottom_semantic_global_refinementExactCartesianLift
    C.pullbackFst target).factor_fac _ _ _ _

/-- The generated mixed route has the exact two-path factor graph. -/
theorem LegacyRefinementBCRegime.mateRoute_fac
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    (target : CoreFiber C.DOne) :
    (regime.mateRoute target).upper.comp
        (exact_bottom_semantic_global_selected_lift C.pullbackFst target).hom.upper =
      (exact_bottom_semantic_global_selected_lift C.pulledFst
          (regime.baseCleavage.reverseFunctor.obj target)).hom.upper.comp
        (regime.baseCleavage.lift target).hom.upper := by
  rw [LegacyRefinementBCRegime.mateRoute, regime.mateRouteBetween_fac]
  exact PackageTotalHom.upper_comp_id _

/--
Route naturality generated by the caller-free mixed cartesian factorization,
the two G-112 reindex graphs, and the base refinement factor graph.
-/
theorem LegacyRefinementBCRegime.mateRoute_natural
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    {source target : CoreFiber C.DOne} (vertical : source ⟶ target) :
    RefinementOverHom.precomp
        ((exact_bottom_semantic_global_reindex_functor C.pulledFst).map
          (regime.baseCleavage.reverseFunctor.map vertical))
        (regime.mateRoute target) =
      RefinementOverHom.postcomp
        (regime.mateRoute source)
        ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).map vertical) := by
  let exactLift := exact_bottom_semantic_global_refinementExactCartesianLift
    C.pullbackFst target
  let first := RefinementOverHom.precomp
    ((exact_bottom_semantic_global_reindex_functor C.pulledFst).map
      (regime.baseCleavage.reverseFunctor.map vertical))
    (regime.mateRoute target)
  let second := RefinementOverHom.postcomp
    (regime.mateRoute source)
    ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).map vertical)
  have hfirst : first = regime.mateRouteBetween vertical := by
    apply exactLift.factor_unique C.mateLowerPath C.pulledRefinement
      C.pulled_square_commutes (regime.mateCandidate vertical)
    have hpulled := congrArg PackageTotalHom.upper
      (exact_bottom_semantic_global_reindex_map_fac C.pulledFst
        (regime.baseCleavage.reverseFunctor.map vertical))
    change ((exact_bottom_semantic_global_reindex_functor C.pulledFst).map
          (regime.baseCleavage.reverseFunctor.map vertical)).1.upper.comp
        (exact_bottom_semantic_global_selected_lift C.pulledFst
          (regime.baseCleavage.reverseFunctor.obj target)).hom.upper =
      (exact_bottom_semantic_global_selected_lift C.pulledFst
          (regime.baseCleavage.reverseFunctor.obj source)).hom.upper.comp
        (regime.baseCleavage.reverseFunctor.map vertical).1.upper at hpulled
    have hbase := congrArg RefinementOverHom.upper
      (regime.baseCleavage.reverseMap_fac vertical)
    change (regime.baseCleavage.reverseFunctor.map vertical).1.upper.comp
        (regime.baseCleavage.lift target).hom.upper =
      (regime.baseCleavage.lift source).hom.upper.comp vertical.1.upper at hbase
    change (((exact_bottom_semantic_global_reindex_functor C.pulledFst).map
          (regime.baseCleavage.reverseFunctor.map vertical)).1.upper.comp
        (regime.mateRoute target).upper).comp
          (exact_bottom_semantic_global_selected_lift
            C.pullbackFst target).hom.upper =
      (regime.mateCandidate vertical).upper
    rw [PackageTotalHom.upper_comp_assoc, regime.mateRoute_fac]
    rw [← PackageTotalHom.upper_comp_assoc, hpulled]
    rw [PackageTotalHom.upper_comp_assoc, hbase]
    exact PackageTotalHom.upper_comp_assoc _ _ _
  have hsecond : second = regime.mateRouteBetween vertical := by
    apply exactLift.factor_unique C.mateLowerPath C.pulledRefinement
      C.pulled_square_commutes (regime.mateCandidate vertical)
    have hpullback := congrArg PackageTotalHom.upper
      (exact_bottom_semantic_global_reindex_map_fac C.pullbackFst vertical)
    change ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).map
          vertical).1.upper.comp
        (exact_bottom_semantic_global_selected_lift
          C.pullbackFst target).hom.upper =
      (exact_bottom_semantic_global_selected_lift
          C.pullbackFst source).hom.upper.comp vertical.1.upper at hpullback
    change (((regime.mateRoute source).upper.comp
        ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).map
          vertical).1.upper).comp
          (exact_bottom_semantic_global_selected_lift
            C.pullbackFst target).hom.upper) =
      (regime.mateCandidate vertical).upper
    rw [PackageTotalHom.upper_comp_assoc, hpullback]
    rw [← PackageTotalHom.upper_comp_assoc, regime.mateRoute_fac]
    exact PackageTotalHom.upper_comp_assoc _ _ _
  exact hfirst.trans hsecond.symm

/-- Naturality of the generated mate components, derived before assembly. -/
theorem LegacyRefinementBCRegime.mate_naturality
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C)
    {source target : CoreFiber C.DOne} (vertical : source ⟶ target) :
    (exact_bottom_semantic_global_reindex_functor C.pulledFst).map
          (regime.reverseBase.map vertical) ≫
        regime.pulledHomEquiv _ _ (regime.mateRoute target) =
      regime.pulledHomEquiv _ _ (regime.mateRoute source) ≫
        regime.reversePullback.map
          ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).map vertical) := by
  calc
    _ = regime.pulledCleavage.homEquiv _ _
          (RefinementOverHom.precomp
            ((exact_bottom_semantic_global_reindex_functor C.pulledFst).map
              (regime.baseCleavage.reverseFunctor.map vertical))
            (regime.mateRoute target)) :=
      (regime.pulledCleavage.homEquiv_natural_source _ _ _).symm
    _ = regime.pulledCleavage.homEquiv _ _
          (RefinementOverHom.postcomp
            (regime.mateRoute source)
            ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).map vertical)) := by
      rw [regime.mateRoute_natural vertical]
    _ = _ := regime.pulledCleavage.homEquiv_natural_target _ _ _

/--
The canonical mate generated by the pulled relative universal property.

Its component is not supplied as regime data: it is the unique factor of the
square route through `pulledLift`.  Its naturality is derived from route
naturality and the two generated hom-equivalence naturality laws.
-/
noncomputable def LegacyRefinementBCRegime.mate
    {C : LegacyRefinementBCConfiguration U} (regime : LegacyRefinementBCRegime C) :
    regime.reverseBase ⋙
        exact_bottom_semantic_global_reindex_functor C.pulledFst ⟶
      exact_bottom_semantic_global_reindex_functor C.pullbackFst ⋙
        regime.reversePullback where
  app target := regime.pulledHomEquiv _ _ (regime.mateRoute target)
  naturality _ _ vertical := regime.mate_naturality vertical

/-- Availability of the regime is existence of the fixed regime structure. -/
def RegimeAvailable (C : LegacyRefinementBCConfiguration U) : Prop :=
  Nonempty (LegacyRefinementBCRegime C)

/-! ## Qualification and branch heads -/

/-- A configuration whose refinement belongs to the exact comparison image. -/
def StrictRefinementImage (C : LegacyRefinementBCConfiguration U) : Prop :=
  ∃ exact : C.DOnePrime ⟶ C.DOne,
    PointedRefinementHom.ofExact exact = C.refinement

/-- The authored pointed refinement has no two-sided pointed refinement inverse. -/
def NoninvertiblePointedRefinement (C : LegacyRefinementBCConfiguration U) : Prop :=
  ¬ Nonempty (PointedRefinementIso C.DOnePrime C.DOne)

/-- Raw exact cospan used to form an identity-refinement configuration. -/
structure RefinementBCIdentityData (U : AtomCarrier.{u}) where
  /-- First pointed endpoint. -/
  DOne : ExtractionInstance U
  /-- Second pointed endpoint. -/
  DTwo : ExtractionInstance U
  /-- Pointed base. -/
  Base : ExtractionInstance U
  /-- First exact cospan leg. -/
  sigmaOne : DOne ⟶ Base
  /-- Second exact cospan leg. -/
  sigmaTwo : DTwo ⟶ Base

/-- The identity-refinement configuration generated from one exact cospan. -/
def RefinementBCIdentityData.configuration
    (data : RefinementBCIdentityData U) : LegacyRefinementBCConfiguration U where
  DOnePrime := data.DOne
  DOne := data.DOne
  DTwo := data.DTwo
  Base := data.Base
  sigmaOne := data.sigmaOne
  sigmaTwo := data.sigmaTwo
  refinement := PointedRefinementHom.id data.DOne

/-- Two composable pointed refinements over one fixed exact cospan. -/
structure RefinementBCCompositionData (U : AtomCarrier.{u}) where
  /-- Source of the inner refinement. -/
  DOneDoublePrime : ExtractionInstance U
  /-- Middle refined endpoint. -/
  DOnePrime : ExtractionInstance U
  /-- Original first endpoint. -/
  DOne : ExtractionInstance U
  /-- Second endpoint. -/
  DTwo : ExtractionInstance U
  /-- Exact cospan base. -/
  Base : ExtractionInstance U
  /-- First exact cospan leg. -/
  sigmaOne : DOne ⟶ Base
  /-- Second exact cospan leg. -/
  sigmaTwo : DTwo ⟶ Base
  /-- Outer refinement `f : D₁' → D₁`. -/
  outer : PointedRefinementHom DOnePrime DOne
  /-- Inner refinement `g : D₁'' → D₁'`. -/
  inner : PointedRefinementHom DOneDoublePrime DOnePrime

/-- The configuration of the outer leg `f`. -/
def RefinementBCCompositionData.outerConfiguration
    (data : RefinementBCCompositionData U) : LegacyRefinementBCConfiguration U where
  DOnePrime := data.DOnePrime
  DOne := data.DOne
  DTwo := data.DTwo
  Base := data.Base
  sigmaOne := data.sigmaOne
  sigmaTwo := data.sigmaTwo
  refinement := data.outer

/-- The configuration of the composite leg `f ∘ g`. -/
def RefinementBCCompositionData.compositeConfiguration
    (data : RefinementBCCompositionData U) : LegacyRefinementBCConfiguration U where
  DOnePrime := data.DOneDoublePrime
  DOne := data.DOne
  DTwo := data.DTwo
  Base := data.Base
  sigmaOne := data.sigmaOne
  sigmaTwo := data.sigmaTwo
  refinement := data.inner.comp data.outer

/--
The inner leg reflects extraction on precisely those sources that enter the
compatible locus of the composite configuration.
-/
def InnerReflectingOnCompositeLocus
    (data : RefinementBCCompositionData U) : Prop :=
  ∀ source : data.DOneDoublePrime.doctrine.Source,
    InPulledLocus data.compositeConfiguration source →
      ∀ atom : U.Atom,
        data.DOnePrime.doctrine.extracts
            (data.inner.doctrineHom.sourceMap source)
            (data.inner.doctrineHom.atomMap atom) →
          data.DOneDoublePrime.doctrine.extracts source atom

/-- The induced configuration whose horizontal leg is the generated `f*`. -/
def pulledLegConfiguration (C : LegacyRefinementBCConfiguration U) :
    LegacyRefinementBCConfiguration U where
  DOnePrime := C.pulled
  DOne := C.pullback
  DTwo := C.DTwo
  Base := C.Base
  sigmaOne := C.pullbackFst ≫ C.sigmaOne
  sigmaTwo := C.sigmaTwo
  refinement := C.pulledRefinement

/-- Authored positive-family geometry, without condition or regime evidence. -/
structure RefinementBCPositiveFamilyRaw (U : AtomCarrier.{u}) where
  /-- Family parameter type. -/
  Parameter : Type u
  /-- A named member prevents empty-family qualification. -/
  distinguished : Parameter
  /-- Raw configuration at each parameter. -/
  configuration : Parameter → LegacyRefinementBCConfiguration U

/--
The five qualifications for the unique fixed term.  Closure is stated for
identity refinements and literal composition; pulled-leg closure uses the
generated square.  All fields are theorem outputs, never raw fixture data.
-/
structure RefinementBCConditionQualification
    (term : RefinementBCConditionSyntax U) : Type (u + 1) where
  /-- Evaluation is invariant under the fixed componentwise configuration isomorphism. -/
  isomorphic_invariant : ∀ (first second : LegacyRefinementBCConfiguration U),
    LegacyRefinementBCConfigurationIso first second →
      (evalRefinementBCCondition term first ↔
        evalRefinementBCCondition term second)
  /-- The fixed condition contains every identity refinement. -/
  identity_mem : ∀ data : RefinementBCIdentityData U,
    evalRefinementBCCondition term data.configuration
  /-- The fixed condition is closed under the card-fixed composition rule. -/
  comp_mem : ∀ data : RefinementBCCompositionData U,
    evalRefinementBCCondition term data.outerConfiguration →
      InnerReflectingOnCompositeLocus data →
        evalRefinementBCCondition term data.compositeConfiguration
  /-- The fixed condition is closed under passage to the generated pulled leg. -/
  pulled_leg_mem : ∀ C : LegacyRefinementBCConfiguration U,
    evalRefinementBCCondition term C →
      evalRefinementBCCondition term (pulledLegConfiguration C)
  /-- Every exact-comparison-image configuration is included. -/
  comparison_image_mem : ∀ (C : LegacyRefinementBCConfiguration U),
    StrictRefinementImage C → evalRefinementBCCondition term C
  /-- Authored raw positive family. -/
  positiveFamily : RefinementBCPositiveFamilyRaw U
  /-- The fixed term fires on every raw positive-family member. -/
  positive_fires : ∀ parameter,
    evalRefinementBCCondition term
      (positiveFamily.configuration parameter)
  /-- The positive family contains a strict-image-external member. -/
  positive_strictly_outside : ∃ parameter,
    ¬ StrictRefinementImage (positiveFamily.configuration parameter)
  /-- The positive family contains a noninvertible pointed refinement. -/
  positive_noninvertible : ∃ parameter,
    NoninvertiblePointedRefinement
      (positiveFamily.configuration parameter)
  /-- The relevant package fibers are inhabited by concrete packages. -/
  positive_fibers_inhabited : ∀ parameter,
    Nonempty (CoreFiber
      (positiveFamily.configuration parameter).DOnePrime) ∧
    Nonempty (CoreFiber (positiveFamily.configuration parameter).DOne)

/-- Positive branch: every admissible raw configuration has a regime. -/
structure GlobalRefinementBaseChange (U : AtomCarrier.{u}) : Type (u + 2) where
  /-- Caller-free carrier-wide regime production. -/
  regime : ∀ C : LegacyRefinementBCConfiguration U, LegacyRefinementBCRegime C

/--
Negative branch: the unique fixed condition exactly characterizes regime
availability and one concrete configuration lies outside it.
-/
structure CharacterizedRefinementBaseChange (U : AtomCarrier.{u}) : Type (u + 2) where
  /-- Qualification of the mechanically fixed one-entry term. -/
  qualification :
    RefinementBCConditionQualification
      (pulledLocusExtractionReflectingTerm (U := U))
  /-- Sufficiency of compatible-locus extraction reflection. -/
  sufficient : ∀ C : LegacyRefinementBCConfiguration U,
    evalRefinementBCCondition pulledLocusExtractionReflectingTerm C →
      RegimeAvailable C
  /-- Independent necessity of compatible-locus extraction reflection. -/
  necessary : ∀ C : LegacyRefinementBCConfiguration U,
    RegimeAvailable C →
      evalRefinementBCCondition pulledLocusExtractionReflectingTerm C
  /-- Concrete non-regime configuration. -/
  counterexample : LegacyRefinementBCConfiguration U
  /-- The counterexample is outside the exact comparison image. -/
  counterexample_strictly_outside : ¬ StrictRefinementImage counterexample
  /-- The counterexample refinement is not invertible. -/
  counterexample_noninvertible : NoninvertiblePointedRefinement counterexample
  /-- The four fibers occurring in the two mate routes are concretely inhabited. -/
  counterexample_fibers_inhabited :
    Nonempty (CoreFiber counterexample.DOnePrime) ∧
    Nonempty (CoreFiber counterexample.DOne) ∧
    Nonempty (CoreFiber counterexample.pulled) ∧
    Nonempty (CoreFiber counterexample.pullback)
  /-- The generated pulled leg is itself genuinely non-exact. -/
  counterexample_pulled_strictly_outside :
    ¬ StrictRefinementImage (pulledLegConfiguration counterexample)
  /-- Concrete target package at which reverse transport is obstructed. -/
  counterexample_target : CoreFiber counterexample.DOne
  /-- No source package supports an upper lift over the authored refinement. -/
  counterexample_no_base_lift : ∀ source : CoreFiber counterexample.DOnePrime,
    ¬ Nonempty
      (RefinementOverHom counterexample.refinement source counterexample_target)

/-- The concrete lift obstruction rules out the complete regime. -/
theorem CharacterizedRefinementBaseChange.counterexample_not_available
    (branch : CharacterizedRefinementBaseChange U) :
    ¬ RegimeAvailable branch.counterexample := by
  rintro ⟨regime⟩
  exact branch.counterexample_no_base_lift
    (regime.baseCleavage.reverseObject branch.counterexample_target)
    ⟨(regime.baseCleavage.lift branch.counterexample_target).hom⟩

/-- The single G-114(b) two-branch artifact. -/
inductive RefinementBaseChangeDisjunction (U : AtomCarrier.{u}) : Type (u + 2)
  | global (proof : GlobalRefinementBaseChange U)
  | characterized (proof : CharacterizedRefinementBaseChange U)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
