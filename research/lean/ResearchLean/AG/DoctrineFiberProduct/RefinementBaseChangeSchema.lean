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
definitions.  The regime records reverse functors, their relative hom
equivalences with factorization equations, and the comparison natural
transformation.  It contains neither a condition-membership field nor an
`IsIso` assertion about that comparison.  A callback-valued condition language
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

/-- The exact pointed base arrow of a total-package morphism between fiber objects. -/
noncomputable def pointedBaseOfFiberHom
    {X Y : ExtractionInstance U} (source : CoreFiber X) (target : CoreFiber Y)
    (hom : source.1 ⟶ target.1) : X ⟶ Y :=
  eqToHom source.2.symm ≫ hom.base ≫ eqToHom target.2

/-- Total-package morphisms whose pointed base is the specified refinement. -/
def RefinementOverHom
    {X Y : ExtractionInstance U} (f : PointedRefinementHom X Y)
    (source : CoreFiber X) (target : CoreFiber Y) :=
  {hom : source.1 ⟶ target.1 //
    PointedRefinementHom.ofExact
        (pointedBaseOfFiberHom source target hom) = f}

/--
The G-114 regime signature.  Reverse functors and relative hom equivalences are
paired with their universal factorization equations.  The mate is only a
natural transformation; no isomorphism assertion is present.
-/
structure RefinementBCRegime (C : RefinementBCConfiguration U) where
  /-- Reverse transport along the authored refinement `f`. -/
  reverseBase : Functor (CoreFiber C.DOne) (CoreFiber C.DOnePrime)
  /-- Reverse transport along the generated pulled refinement `f*`. -/
  reversePullback : Functor (CoreFiber C.pullback) (CoreFiber C.pulled)
  /-- Universal lift over `f` at every target-fiber package. -/
  baseLift : ∀ target : CoreFiber C.DOne,
    RefinementOverHom C.refinement (reverseBase.obj target) target
  /-- Relative hom equivalence generated by the lift over `f`. -/
  baseHomEquiv : ∀ (source : CoreFiber C.DOnePrime)
    (target : CoreFiber C.DOne),
    RefinementOverHom C.refinement source target ≃
      (source ⟶ reverseBase.obj target)
  /-- The forward direction satisfies the cartesian factorization equation. -/
  baseHomEquiv_fac : ∀ (source : CoreFiber C.DOnePrime)
    (target : CoreFiber C.DOne)
    (hom : RefinementOverHom C.refinement source target),
    hom.1 = (baseHomEquiv source target hom).1 ≫ (baseLift target).1
  /-- Universal lift over the generated pulled refinement. -/
  pulledLift : ∀ target : CoreFiber C.pullback,
    RefinementOverHom C.pulledRefinement
      (reversePullback.obj target) target
  /-- Relative hom equivalence generated by the lift over `f*`. -/
  pulledHomEquiv : ∀ (source : CoreFiber C.pulled)
    (target : CoreFiber C.pullback),
    RefinementOverHom C.pulledRefinement source target ≃
      (source ⟶ reversePullback.obj target)
  /-- The pulled forward direction satisfies its factorization equation. -/
  pulledHomEquiv_fac : ∀ (source : CoreFiber C.pulled)
    (target : CoreFiber C.pullback)
    (hom : RefinementOverHom C.pulledRefinement source target),
    hom.1 = (pulledHomEquiv source target hom).1 ≫ (pulledLift target).1
  /--
  Canonical comparison from exact reindexing after base reverse transport to
  pulled reverse transport after exact reindexing.
  -/
  mate :
    reverseBase ⋙
        exact_bottom_semantic_global_reindex_functor C.pulledFst ⟶
      exact_bottom_semantic_global_reindex_functor C.pullbackFst ⋙
        reversePullback

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
  /-- The positive family contains a genuinely nonidentity refinement. -/
  positive_nonidentity : ∃ parameter,
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
structure GlobalRefinementBaseChange (U : AtomCarrier.{u}) where
  /-- Caller-free carrier-wide regime production. -/
  regime : ∀ C : RefinementBCConfiguration U, RefinementBCRegime C

/--
Negative branch: the unique fixed condition exactly characterizes regime
availability and one concrete configuration lies outside it.
-/
structure CharacterizedRefinementBaseChange (U : AtomCarrier.{u}) : Type (u + 1) where
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
  /-- The concrete configuration has no regime. -/
  counterexample_not_available : ¬ RegimeAvailable counterexample

/-- The single G-114(b) two-branch artifact. -/
inductive RefinementBaseChangeDisjunction (U : AtomCarrier.{u}) : Type (u + 1)
  | global (proof : GlobalRefinementBaseChange U)
  | characterized (proof : CharacterizedRefinementBaseChange U)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
