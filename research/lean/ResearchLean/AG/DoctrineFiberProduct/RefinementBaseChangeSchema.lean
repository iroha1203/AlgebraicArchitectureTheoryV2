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
structure RefinementBCConfiguration (U : AtomCarrier.{u}) where
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

namespace RefinementBCConfiguration

/-- The generated exact pullback `P`. -/
def pullback (C : RefinementBCConfiguration U) : ExtractionInstance U :=
  pointedPullback C.sigmaOne C.sigmaTwo

/-- Sources of the generated mixed pullback `P'`. -/
abbrev PulledSource (C : RefinementBCConfiguration U) :=
  {pair : C.DOnePrime.doctrine.Source × C.DTwo.doctrine.Source //
    C.sigmaOne.doctrineHom.sourceMap
        (C.refinement.doctrineHom.sourceMap pair.1) =
      C.sigmaTwo.doctrineHom.sourceMap pair.2}

/-- The mixed pullback doctrine generated from forward refinement preservation. -/
def pulledDoctrine (C : RefinementBCConfiguration U) : ExtractionDoctrine U where
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
def pulledSource (C : RefinementBCConfiguration U) : C.PulledSource :=
  ⟨(C.DOnePrime.source, C.DTwo.source), by
    rw [C.refinement.source_eq, C.sigmaOne.source_eq, C.sigmaTwo.source_eq]⟩

/-- The generated pointed mixed pullback `P'`. -/
def pulled (C : RefinementBCConfiguration U) : ExtractionInstance U where
  doctrine := C.pulledDoctrine
  source := C.pulledSource

/-- The exact vertical projection `fst' : P' ⟶ D₁'`. -/
def pulledFst (C : RefinementBCConfiguration U) : C.pulled ⟶ C.DOnePrime where
  doctrineHom :=
    { sourceMap := fun source => source.val.1
      atomEquiv := Equiv.refl U.Atom
      normalize_eq := fun _ => rfl
      extraction_iff := fun _ _ => Iff.rfl }
  source_eq := rfl

/-- The exact vertical projection `fst : P ⟶ D₁`. -/
def pullbackFst (C : RefinementBCConfiguration U) : C.pullback ⟶ C.DOne :=
  pointedPullbackFst C.sigmaOne C.sigmaTwo

/-- The pulled horizontal refinement `f* : P' → P`. -/
def pulledRefinement (C : RefinementBCConfiguration U) :
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
theorem pulled_square_commutes (C : RefinementBCConfiguration U) :
    C.pulledRefinement.comp (PointedRefinementHom.ofExact C.pullbackFst) =
      (PointedRefinementHom.ofExact C.pulledFst).comp C.refinement := by
  apply PointedRefinementHom.ext
  apply RefinementDoctrineHom.ext
  · rfl
  · rfl

end RefinementBCConfiguration

/-! ## Configuration isomorphism head -/

/--
Componentwise configuration isomorphism, including both cospan squares and the
pointed refinement square.  The refinement endpoint uses the dedicated pointed
refinement isomorphism rather than silently requiring exactness.
-/
structure RefinementBCConfigurationIso
    (C C' : RefinementBCConfiguration U) where
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
def InPulledLocus (C : RefinementBCConfiguration U)
    (source : C.DOnePrime.doctrine.Source) : Prop :=
  ∃ second : C.DTwo.doctrine.Source,
    C.sigmaOne.doctrineHom.sourceMap
        (C.refinement.doctrineHom.sourceMap source) =
      C.sigmaTwo.doctrineHom.sourceMap second

/-- Extraction reflection restricted to the generated compatible locus. -/
def PulledLocusExtractionReflecting (C : RefinementBCConfiguration U) : Prop :=
  ∀ (source : C.DOnePrime.doctrine.Source), InPulledLocus C source →
    ∀ atom : U.Atom,
      C.DOne.doctrine.extracts
          (C.refinement.doctrineHom.sourceMap source)
          (C.refinement.doctrineHom.atomMap atom) →
        C.DOnePrime.doctrine.extracts source atom

/-- Evaluate the closed language without reading a regime, lift, mate, or certificate. -/
def evalRefinementBCCondition :
    RefinementBCConditionSyntax U → RefinementBCConfiguration U → Prop
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
    (C : RefinementBCConfiguration U) :
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
    (C : RefinementBCConfiguration U) :
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
refinement whenever the selected package families admit the required upper
change.
-/
structure RefinementOverHom
    {X Y : ExtractionInstance U} (f : PointedRefinementHom X Y)
    (source : CoreFiber X) (target : CoreFiber Y) where
  /-- Complete upper package change over the fixed lower refinement. -/
  upper : SignedExactCoreReadingHom source.1 target.1
  /-- The upper Atom equivalence is the one generated by the lower refinement. -/
  atomEquiv_eq : upper.atomEquiv = f.doctrineHom.atomEquiv

namespace RefinementOverHom

/-- Relative homs are determined by their complete upper package changes. -/
@[ext]
theorem ext
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {target : CoreFiber Y}
    {first second : RefinementOverHom f source target}
    (hupper : first.upper = second.upper) : first = second := by
  cases first
  cases second
  cases hupper
  rfl

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
structure RefinementCartesianLift
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
structure RefinementCartesianCleavage
    {X Y : ExtractionInstance U} (f : PointedRefinementHom X Y) where
  /-- The only choice: one universal lift at each target package. -/
  lift : ∀ target : CoreFiber Y, RefinementCartesianLift f target

namespace RefinementCartesianCleavage

/-- Reverse transport on objects, generated by the selected lift domains. -/
def reverseObject
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : RefinementCartesianCleavage f) (target : CoreFiber Y) : CoreFiber X :=
  (cleavage.lift target).domain

/-- Reverse transport on arrows, generated as the unique factor of postcomposition. -/
noncomputable def reverseMap
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : RefinementCartesianCleavage f)
    {first second : CoreFiber Y} (vertical : first ⟶ second) :
    cleavage.reverseObject first ⟶ cleavage.reverseObject second :=
  (cleavage.lift second).factor
    (RefinementOverHom.postcomp (cleavage.lift first).hom vertical)

/-- The generated reverse map has its defining cartesian factor triangle. -/
theorem reverseMap_fac
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : RefinementCartesianCleavage f)
    {first second : CoreFiber Y} (vertical : first ⟶ second) :
    RefinementOverHom.precomp (cleavage.reverseMap vertical)
        (cleavage.lift second).hom =
      RefinementOverHom.postcomp (cleavage.lift first).hom vertical :=
  (cleavage.lift second).factor_fac _

/-- Generated reverse transport preserves identities by universal uniqueness. -/
theorem reverseMap_id
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : RefinementCartesianCleavage f) (target : CoreFiber Y) :
    cleavage.reverseMap (𝟙 target) = 𝟙 (cleavage.reverseObject target) := by
  symm
  apply (cleavage.lift target).factor_unique
  rw [RefinementOverHom.precomp_id, RefinementOverHom.postcomp_id]

/-- Generated reverse transport preserves composition by universal uniqueness. -/
theorem reverseMap_comp
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : RefinementCartesianCleavage f)
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
    (cleavage : RefinementCartesianCleavage f) : CoreFiber Y ⥤ CoreFiber X where
  obj := cleavage.reverseObject
  map := cleavage.reverseMap
  map_id := cleavage.reverseMap_id
  map_comp := cleavage.reverseMap_comp

/-- Relative hom equivalence generated by the selected cartesian lift. -/
noncomputable def homEquiv
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : RefinementCartesianCleavage f)
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
    (cleavage : RefinementCartesianCleavage f)
    (source : CoreFiber X) (target : CoreFiber Y)
    (hom : RefinementOverHom f source target) :
    RefinementOverHom.precomp (cleavage.homEquiv source target hom)
        (cleavage.lift target).hom = hom :=
  (cleavage.lift target).factor_fac hom

/-- Source-variable naturality of the generated relative hom equivalence. -/
theorem homEquiv_natural_source
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    (cleavage : RefinementCartesianCleavage f)
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
    (cleavage : RefinementCartesianCleavage f)
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

end RefinementCartesianCleavage

/--
The G-114 regime signature.  Its only reverse-transport inputs are two
cartesian cleavages.  Reverse functors, their actions, and relative hom
equivalences are definitions generated from factorization uniqueness.
-/
structure RefinementBCRegime (C : RefinementBCConfiguration U) where
  /-- Universal refinement cleavage over the authored horizontal leg. -/
  baseCleavage : RefinementCartesianCleavage C.refinement
  /-- Universal refinement cleavage over the generated pulled leg. -/
  pulledCleavage : RefinementCartesianCleavage C.pulledRefinement
  /--
  The over-`f*` route generated by the exact selected lifts around the square.
  Its following equation, rather than a supplied comparison map, fixes the
  Beck--Chevalley route.
  -/
  mateRoute : ∀ target : CoreFiber C.DOne,
    RefinementOverHom C.pulledRefinement
      ((exact_bottom_semantic_global_reindex_functor C.pulledFst).obj
        (baseCleavage.reverseFunctor.obj target))
      ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).obj target)
  /-- The mate route is exactly the two exact-lift paths around the square. -/
  mateRoute_fac : ∀ target : CoreFiber C.DOne,
    (mateRoute target).upper.comp
        (exact_bottom_semantic_global_selected_lift C.pullbackFst target).hom.upper =
      (exact_bottom_semantic_global_selected_lift C.pulledFst
          (baseCleavage.reverseFunctor.obj target)).hom.upper.comp
        (baseCleavage.lift target).hom.upper
  /-- The exact-square factor equation uniquely determines the mate route. -/
  mateRoute_unique : ∀ (target : CoreFiber C.DOne)
    (candidate : RefinementOverHom C.pulledRefinement
      ((exact_bottom_semantic_global_reindex_functor C.pulledFst).obj
        (baseCleavage.reverseFunctor.obj target))
      ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).obj target)),
    candidate.upper.comp
        (exact_bottom_semantic_global_selected_lift C.pullbackFst target).hom.upper =
      (exact_bottom_semantic_global_selected_lift C.pulledFst
          (baseCleavage.reverseFunctor.obj target)).hom.upper.comp
        (baseCleavage.lift target).hom.upper →
      candidate = mateRoute target
  /-- Naturality of the universally generated component factors. -/
  mate_naturality : ∀ {source target : CoreFiber C.DOne}
    (vertical : source ⟶ target),
    (exact_bottom_semantic_global_reindex_functor C.pulledFst).map
          (baseCleavage.reverseFunctor.map vertical) ≫
        pulledCleavage.homEquiv _ _ (mateRoute target) =
      pulledCleavage.homEquiv _ _ (mateRoute source) ≫
        pulledCleavage.reverseFunctor.map
          ((exact_bottom_semantic_global_reindex_functor C.pullbackFst).map vertical)

/-- Reverse transport along the authored refinement, generated by its cleavage. -/
noncomputable def RefinementBCRegime.reverseBase
    {C : RefinementBCConfiguration U} (regime : RefinementBCRegime C) :
    CoreFiber C.DOne ⥤ CoreFiber C.DOnePrime :=
  regime.baseCleavage.reverseFunctor

/-- Reverse transport along the pulled refinement, generated by its cleavage. -/
noncomputable def RefinementBCRegime.reversePullback
    {C : RefinementBCConfiguration U} (regime : RefinementBCRegime C) :
    CoreFiber C.pullback ⥤ CoreFiber C.pulled :=
  regime.pulledCleavage.reverseFunctor

/-- The generated universal lift over the authored refinement. -/
def RefinementBCRegime.baseLift
    {C : RefinementBCConfiguration U} (regime : RefinementBCRegime C)
    (target : CoreFiber C.DOne) :=
  (regime.baseCleavage.lift target).hom

/-- The generated universal lift over the pulled refinement. -/
def RefinementBCRegime.pulledLift
    {C : RefinementBCConfiguration U} (regime : RefinementBCRegime C)
    (target : CoreFiber C.pullback) :=
  (regime.pulledCleavage.lift target).hom

/-- The relative hom equivalence generated by the base cleavage. -/
noncomputable def RefinementBCRegime.baseHomEquiv
    {C : RefinementBCConfiguration U} (regime : RefinementBCRegime C)
    (source : CoreFiber C.DOnePrime) (target : CoreFiber C.DOne) :=
  regime.baseCleavage.homEquiv source target

/-- The relative hom equivalence generated by the pulled cleavage. -/
noncomputable def RefinementBCRegime.pulledHomEquiv
    {C : RefinementBCConfiguration U} (regime : RefinementBCRegime C)
    (source : CoreFiber C.pulled) (target : CoreFiber C.pullback) :=
  regime.pulledCleavage.homEquiv source target

/--
The canonical mate generated by the pulled relative universal property.

Its component is not supplied as regime data: it is the unique factor of the
square route through `pulledLift`.  The regime stores only the route equation
and the naturality proof needed to assemble these generated factors.
-/
noncomputable def RefinementBCRegime.mate
    {C : RefinementBCConfiguration U} (regime : RefinementBCRegime C) :
    regime.reverseBase ⋙
        exact_bottom_semantic_global_reindex_functor C.pulledFst ⟶
      exact_bottom_semantic_global_reindex_functor C.pullbackFst ⋙
        regime.reversePullback where
  app target := regime.pulledHomEquiv _ _ (regime.mateRoute target)
  naturality _ _ vertical := regime.mate_naturality vertical

/-- Availability of the regime is existence of the fixed regime structure. -/
def RegimeAvailable (C : RefinementBCConfiguration U) : Prop :=
  Nonempty (RefinementBCRegime C)

/-! ## Qualification and branch heads -/

/-- A configuration whose refinement belongs to the exact comparison image. -/
def StrictRefinementImage (C : RefinementBCConfiguration U) : Prop :=
  ∃ exact : C.DOnePrime ⟶ C.DOne,
    PointedRefinementHom.ofExact exact = C.refinement

/-- The authored pointed refinement has no two-sided pointed refinement inverse. -/
def NoninvertiblePointedRefinement (C : RefinementBCConfiguration U) : Prop :=
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
    (data : RefinementBCIdentityData U) : RefinementBCConfiguration U where
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
    (data : RefinementBCCompositionData U) : RefinementBCConfiguration U where
  DOnePrime := data.DOnePrime
  DOne := data.DOne
  DTwo := data.DTwo
  Base := data.Base
  sigmaOne := data.sigmaOne
  sigmaTwo := data.sigmaTwo
  refinement := data.outer

/-- The configuration of the composite leg `f ∘ g`. -/
def RefinementBCCompositionData.compositeConfiguration
    (data : RefinementBCCompositionData U) : RefinementBCConfiguration U where
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
def pulledLegConfiguration (C : RefinementBCConfiguration U) :
    RefinementBCConfiguration U where
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
  configuration : Parameter → RefinementBCConfiguration U

/--
The five qualifications for the unique fixed term.  Closure is stated for
identity refinements and literal composition; pulled-leg closure uses the
generated square.  All fields are theorem outputs, never raw fixture data.
-/
structure RefinementBCConditionQualification
    (term : RefinementBCConditionSyntax U) : Type (u + 1) where
  /-- Evaluation is invariant under the fixed componentwise configuration isomorphism. -/
  isomorphic_invariant : ∀ (first second : RefinementBCConfiguration U),
    RefinementBCConfigurationIso first second →
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
  pulled_leg_mem : ∀ C : RefinementBCConfiguration U,
    evalRefinementBCCondition term C →
      evalRefinementBCCondition term (pulledLegConfiguration C)
  /-- Every exact-comparison-image configuration is included. -/
  comparison_image_mem : ∀ (C : RefinementBCConfiguration U),
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
  regime : ∀ C : RefinementBCConfiguration U, RefinementBCRegime C

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
  sufficient : ∀ C : RefinementBCConfiguration U,
    evalRefinementBCCondition pulledLocusExtractionReflectingTerm C →
      RegimeAvailable C
  /-- Independent necessity of compatible-locus extraction reflection. -/
  necessary : ∀ C : RefinementBCConfiguration U,
    RegimeAvailable C →
      evalRefinementBCCondition pulledLocusExtractionReflectingTerm C
  /-- Concrete non-regime configuration. -/
  counterexample : RefinementBCConfiguration U
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
  /-- The concrete nondegenerate configuration has no regime. -/
  counterexample_not_available : ¬ RegimeAvailable counterexample

/-- The single G-114(b) two-branch artifact. -/
inductive RefinementBaseChangeDisjunction (U : AtomCarrier.{u}) : Type (u + 2)
  | global (proof : GlobalRefinementBaseChange U)
  | characterized (proof : CharacterizedRefinementBaseChange U)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
