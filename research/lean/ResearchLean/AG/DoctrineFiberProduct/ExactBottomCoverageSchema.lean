import ResearchLean.AG.DoctrineFiberProduct.CartesianBranchArtifact
import ResearchLean.AG.DoctrineFiberProduct.PointedDoctrinePullback

/-!
# Exact-bottom coverage schema

This module fixes the G-112 F0 type surface.  It contains the closed semantic
condition language, its evaluator and carrier rebase, the ordered first
predicate term, arrow-category coverage witnesses with shared object anchors,
and the two-branch/regime output types.  It constructs no coverage theorem and
chooses no branch.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

universe u v

local instance finiteExactBottomAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Closed condition language -/

/--
The five constructors fixed by G-112.  The carrier parameter is deliberately
phantom: a term contains no authored atom, number, set, callback, presentation,
realization function, or coverage witness.
-/
inductive ExactBottomConditionSyntax (U : AtomCarrier.{u})
  | sourceFinite
  | targetFinite
  | allSourceExtractionsFiniteOrCofinite
  | allTargetExtractionsFiniteOrCofinite
  | conjunction (left right : ExactBottomConditionSyntax U)

/-- The atoms extracted from one source cell, as a semantic set. -/
def extractedAtomSet {U : AtomCarrier.{u}}
    (object : ExtractionInstance U) (source : object.doctrine.Source) :
    Set U.Atom :=
  {atom | object.doctrine.extracts source atom}

/-- Every extraction set of one endpoint is finite or has finite complement. -/
def AllExtractionsFiniteOrCofinite {U : AtomCarrier.{u}}
    (object : ExtractionInstance U) : Prop :=
  ∀ source : object.doctrine.Source,
    (extractedAtomSet object source).Finite ∨
      (extractedAtomSet object source)ᶜ.Finite

/-- Evaluate the closed language directly on semantic exact-bottom arrows. -/
def evalExactBottomCondition {U : AtomCarrier.{u}} :
    ExactBottomConditionSyntax U → CartSemanticInput U → Prop
  | .sourceFinite, input => Finite input.source.doctrine.Source
  | .targetFinite, input => Finite input.target.doctrine.Source
  | .allSourceExtractionsFiniteOrCofinite, input =>
      AllExtractionsFiniteOrCofinite input.source
  | .allTargetExtractionsFiniteOrCofinite, input =>
      AllExtractionsFiniteOrCofinite input.target
  | .conjunction left right, input =>
      evalExactBottomCondition left input ∧ evalExactBottomCondition right input

/-- Canonically reinterpret a syntax term at another Atom carrier. -/
def rebaseExactBottomCondition
    {U : AtomCarrier.{u}} {V : AtomCarrier.{v}} :
    ExactBottomConditionSyntax U → ExactBottomConditionSyntax V
  | .sourceFinite => .sourceFinite
  | .targetFinite => .targetFinite
  | .allSourceExtractionsFiniteOrCofinite =>
      .allSourceExtractionsFiniteOrCofinite
  | .allTargetExtractionsFiniteOrCofinite =>
      .allTargetExtractionsFiniteOrCofinite
  | .conjunction left right =>
      .conjunction (rebaseExactBottomCondition left)
        (rebaseExactBottomCondition right)

/-- The authored first candidate fixed before K0. -/
def exactBottomFirstCandidate (U : AtomCarrier.{u}) :
    ExactBottomConditionSyntax U :=
  .conjunction .sourceFinite .targetFinite

/--
The F0 candidate sequence, fixed before K0.  It enumerates the fifteen
nonempty conjunction classes on the four atomic conditions without consulting
any coverage proof or counterexample.  The card-fixed endpoint-finite term is
first; later movement can therefore use only the next pre-existing entry.
-/
def exactBottomConditionCandidates :
    List (ExactBottomConditionSyntax FiniteModel.carrier) :=
  [ .conjunction .sourceFinite .targetFinite,
    .conjunction .sourceFinite .allSourceExtractionsFiniteOrCofinite,
    .conjunction .targetFinite .allTargetExtractionsFiniteOrCofinite,
    .conjunction .allSourceExtractionsFiniteOrCofinite
      .allTargetExtractionsFiniteOrCofinite,
    .conjunction .sourceFinite .allTargetExtractionsFiniteOrCofinite,
    .conjunction .targetFinite .allSourceExtractionsFiniteOrCofinite,
    .sourceFinite,
    .targetFinite,
    .allSourceExtractionsFiniteOrCofinite,
    .allTargetExtractionsFiniteOrCofinite,
    .conjunction (.conjunction .sourceFinite .targetFinite)
      .allSourceExtractionsFiniteOrCofinite,
    .conjunction (.conjunction .sourceFinite .targetFinite)
      .allTargetExtractionsFiniteOrCofinite,
    .conjunction
      (.conjunction .sourceFinite .allSourceExtractionsFiniteOrCofinite)
      .allTargetExtractionsFiniteOrCofinite,
    .conjunction
      (.conjunction .targetFinite .allSourceExtractionsFiniteOrCofinite)
      .allTargetExtractionsFiniteOrCofinite,
    .conjunction
      (.conjunction (.conjunction .sourceFinite .targetFinite)
        .allSourceExtractionsFiniteOrCofinite)
      .allTargetExtractionsFiniteOrCofinite ]

/-- The fixed head is the first candidate. -/
theorem exactBottomConditionCandidates_head :
    exactBottomConditionCandidates.head? =
      some (exactBottomFirstCandidate FiniteModel.carrier) :=
  rfl

/-- Every carrier receives exactly the canonical rebase of the authored head. -/
theorem rebase_exactBottomFirstCandidate
    (U : AtomCarrier.{u}) :
    rebaseExactBottomCondition
        (exactBottomFirstCandidate FiniteModel.carrier) =
      exactBottomFirstCandidate U :=
  rfl

/-! The following equivalences expose every evaluator dependency. -/

theorem eval_sourceFinite_iff {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) :
    evalExactBottomCondition (.sourceFinite) input ↔
      Finite input.source.doctrine.Source :=
  Iff.rfl

theorem eval_targetFinite_iff {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) :
    evalExactBottomCondition (.targetFinite) input ↔
      Finite input.target.doctrine.Source :=
  Iff.rfl

theorem eval_allSourceExtractionsFiniteOrCofinite_iff
    {U : AtomCarrier.{u}} (input : CartSemanticInput U) :
    evalExactBottomCondition
        (.allSourceExtractionsFiniteOrCofinite) input ↔
      AllExtractionsFiniteOrCofinite input.source :=
  Iff.rfl

theorem eval_allTargetExtractionsFiniteOrCofinite_iff
    {U : AtomCarrier.{u}} (input : CartSemanticInput U) :
    evalExactBottomCondition
        (.allTargetExtractionsFiniteOrCofinite) input ↔
      AllExtractionsFiniteOrCofinite input.target :=
  Iff.rfl

theorem eval_conjunction_iff {U : AtomCarrier.{u}}
    (left right : ExactBottomConditionSyntax U)
    (input : CartSemanticInput U) :
    evalExactBottomCondition (.conjunction left right) input ↔
      evalExactBottomCondition left input ∧
        evalExactBottomCondition right input :=
  Iff.rfl

/-! ## Anchored arrow-category coverage -/

/-- A finite code together with its semantic object isomorphism. -/
structure CoveredObjectWitness {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (object : ExtractionInstance U) where
  code : FiniteInstanceCode U
  iso : code.toSemantic ≅ object

/--
A code-level arrow whose decoded arrow is isomorphic to the semantic input,
with the square's endpoint isomorphisms fixed to the supplied object anchors.
-/
structure CoverageWitnessOver {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : CartSemanticInput U)
    (sourceAnchor : CoveredObjectWitness input.source)
    (targetAnchor : CoveredObjectWitness input.target) where
  presentation : CartPresentationBetween sourceAnchor.code targetAnchor.code
  square : CartSemanticInputIso
    (toSemanticCart presentation.toPresentation) input
  sourceIso_eq : square.sourceIso = sourceAnchor.iso
  targetIso_eq : square.targetIso = targetAnchor.iso

/-- The shared anchored coverage witness used by G-112(a), (b), and (d). -/
structure AnchoredCoverageWitness {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (input : CartSemanticInput U) where
  sourceAnchor : CoveredObjectWitness input.source
  targetAnchor : CoveredObjectWitness input.target
  arrow : CoverageWitnessOver input sourceAnchor targetAnchor

/-- Bundle one semantic exact-bottom arrow from its typed endpoints. -/
def cartSemanticInputOfHom {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (hom : source ⟶ target) :
    CartSemanticInput U :=
  ⟨source, target, hom⟩

/-- Two covered arrows whose middle object uses one shared anchor. -/
structure SharedAnchorComposablePair {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] where
  source : ExtractionInstance U
  middle : ExtractionInstance U
  target : ExtractionInstance U
  sourceAnchor : CoveredObjectWitness source
  middleAnchor : CoveredObjectWitness middle
  targetAnchor : CoveredObjectWitness target
  first : source ⟶ middle
  second : middle ⟶ target
  firstArrow : CoverageWitnessOver (cartSemanticInputOfHom first)
    sourceAnchor middleAnchor
  secondArrow : CoverageWitnessOver (cartSemanticInputOfHom second)
    middleAnchor targetAnchor

namespace SharedAnchorComposablePair

def firstInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pair : SharedAnchorComposablePair (U := U)) : CartSemanticInput U :=
  cartSemanticInputOfHom pair.first

def secondInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pair : SharedAnchorComposablePair (U := U)) : CartSemanticInput U :=
  cartSemanticInputOfHom pair.second

def compositeInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pair : SharedAnchorComposablePair (U := U)) : CartSemanticInput U :=
  cartSemanticInputOfHom (pair.first ≫ pair.second)

end SharedAnchorComposablePair

/-- A covered cospan whose two legs use one shared base anchor. -/
structure SharedBaseAnchorCospan {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] where
  left : ExtractionInstance U
  right : ExtractionInstance U
  base : ExtractionInstance U
  leftAnchor : CoveredObjectWitness left
  rightAnchor : CoveredObjectWitness right
  baseAnchor : CoveredObjectWitness base
  first : left ⟶ base
  second : right ⟶ base
  firstArrow : CoverageWitnessOver (cartSemanticInputOfHom first)
    leftAnchor baseAnchor
  secondArrow : CoverageWitnessOver (cartSemanticInputOfHom second)
    rightAnchor baseAnchor

namespace SharedBaseAnchorCospan

def firstInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (cospan : SharedBaseAnchorCospan (U := U)) : CartSemanticInput U :=
  cartSemanticInputOfHom cospan.first

def secondInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (cospan : SharedBaseAnchorCospan (U := U)) : CartSemanticInput U :=
  cartSemanticInputOfHom cospan.second

def pullbackFstInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (cospan : SharedBaseAnchorCospan (U := U)) : CartSemanticInput U :=
  cartSemanticInputOfHom
    (pointedPullbackFst cospan.first cospan.second)

def pullbackSndInput {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (cospan : SharedBaseAnchorCospan (U := U)) : CartSemanticInput U :=
  cartSemanticInputOfHom
    (pointedPullbackSnd cospan.first cospan.second)

end SharedBaseAnchorCospan

/--
The first-stage theorem type.  `Finite` records the mathematical hypotheses;
`DecidableEq U.Atom` is the finite-code interface instance and is not used by
the semantic condition evaluator.
-/
def FiniteEndpointCoverage : Prop :=
  ∀ (U : AtomCarrier.{u}) [Finite U.Atom] [DecidableEq U.Atom]
    (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source],
    Nonempty (AnchoredCoverageWitness input)

/-! ## Qualification and candidate selection -/

/-- Strict realization, without closing the image under semantic isomorphism. -/
def StrictCartRealizationImage {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : CartSemanticInput U) : Prop :=
  ∃ presentation : CartPresentation U,
    toSemanticCart presentation = input

/--
Authored positive-family geometry.  It stores only parameters, endpoints, and
arrows; firing, realization status, nonisomorphism, and noninvertibility are
theorem outputs below.
-/
structure ExactBottomPositiveFamilyRaw where
  Parameter : Type
  distinguished : Parameter
  source : Parameter → ExtractionInstance FiniteModel.carrier
  target : Parameter → ExtractionInstance FiniteModel.carrier
  hom : ∀ parameter, source parameter ⟶ target parameter

namespace ExactBottomPositiveFamilyRaw

def input (family : ExactBottomPositiveFamilyRaw)
    (parameter : family.Parameter) :
    CartSemanticInput FiniteModel.carrier :=
  cartSemanticInputOfHom (family.hom parameter)

end ExactBottomPositiveFamilyRaw

/--
All five qualifications attached to one authored base-carrier term.  Every
field is a theorem output about that same term; no qualification certificate
can be paired with a different candidate.
-/
structure ExactBottomConditionQualification
    (template : ExactBottomConditionSyntax FiniteModel.carrier) : Type (u + 1) where
  isomorphic_invariant : ∀ (U : AtomCarrier.{u})
    (first second : CartSemanticInput U),
    CartSemanticInputIso first second →
      (evalExactBottomCondition (rebaseExactBottomCondition template) first ↔
        evalExactBottomCondition (rebaseExactBottomCondition template) second)
  identity_mem : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (object : ExtractionInstance U) (_anchor : CoveredObjectWitness object),
    evalExactBottomCondition (rebaseExactBottomCondition template)
      (cartSemanticInputOfHom (𝟙 object))
  comp_mem : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (pair : SharedAnchorComposablePair (U := U)),
    evalExactBottomCondition (rebaseExactBottomCondition template)
        pair.firstInput →
      evalExactBottomCondition (rebaseExactBottomCondition template)
        pair.secondInput →
      evalExactBottomCondition (rebaseExactBottomCondition template)
        pair.compositeInput
  pullback_fst_mem : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (cospan : SharedBaseAnchorCospan (U := U)),
    evalExactBottomCondition (rebaseExactBottomCondition template)
        cospan.firstInput →
      evalExactBottomCondition (rebaseExactBottomCondition template)
        cospan.secondInput →
      evalExactBottomCondition (rebaseExactBottomCondition template)
        cospan.pullbackFstInput
  pullback_snd_mem : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (cospan : SharedBaseAnchorCospan (U := U)),
    evalExactBottomCondition (rebaseExactBottomCondition template)
        cospan.firstInput →
      evalExactBottomCondition (rebaseExactBottomCondition template)
        cospan.secondInput →
      evalExactBottomCondition (rebaseExactBottomCondition template)
        cospan.pullbackSndInput
  realization_image_mem : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (presentation : CartPresentation U),
    evalExactBottomCondition (rebaseExactBottomCondition template)
      (toSemanticCart presentation)
  positiveFamily : ExactBottomPositiveFamilyRaw
  positive_fires : ∀ parameter : positiveFamily.Parameter,
    evalExactBottomCondition template (positiveFamily.input parameter)
  positive_strictly_outside :
    ∃ parameter : positiveFamily.Parameter,
      ¬ StrictCartRealizationImage (positiveFamily.input parameter)
  positive_nonisomorphic_pair :
    ∃ first second : positiveFamily.Parameter, first ≠ second ∧
      ¬ Nonempty (CartSemanticInputIso
        (positiveFamily.input first) (positiveFamily.input second))
  positive_noninvertible :
    ∃ parameter : positiveFamily.Parameter,
      ¬ IsIso (positiveFamily.hom parameter)

/-- The term stored at one pre-registered candidate index. -/
def exactBottomCandidateTerm
    (index : Fin exactBottomConditionCandidates.length) :
    ExactBottomConditionSyntax FiniteModel.carrier :=
  exactBottomConditionCandidates.get index

/--
A reusable refutation fixes which of the two required candidate gates failed:
qualification itself, or semantic sufficiency at a concrete input.
-/
inductive ExactBottomCandidateRefutation
    (template : ExactBottomConditionSyntax FiniteModel.carrier) : Type (u + 1)
  | qualification
      (refutes : ¬ Nonempty (ExactBottomConditionQualification.{u} template))
  | insufficient {U : AtomCarrier.{u}} [DecidableEq U.Atom]
      (input : CartSemanticInput U)
      (fires : evalExactBottomCondition
        (rebaseExactBottomCondition template) input)
      (notCovered : ¬ Nonempty (AnchoredCoverageWitness input))

/--
The current candidate together with refutations of every earlier registered
candidate.  The current term is therefore selected only by its fixed list
index, never by a post-proof authored predicate.
-/
structure ExactBottomCandidateSelection : Type (u + 1) where
  index : Fin exactBottomConditionCandidates.length
  priorRefutations : ∀ prior : Fin index.val,
    ExactBottomCandidateRefutation.{u}
      (exactBottomCandidateTerm
        ⟨prior.val, Nat.lt_trans prior.isLt index.isLt⟩)

namespace ExactBottomCandidateSelection

/-- The selected authored term. -/
def template (selection : ExactBottomCandidateSelection.{u}) :
    ExactBottomConditionSyntax FiniteModel.carrier :=
  exactBottomCandidateTerm selection.index

/-- The unique initial state, selecting the card-fixed first candidate. -/
def initial : ExactBottomCandidateSelection.{u} where
  index := ⟨0, by decide⟩
  priorRefutations := fun prior => Fin.elim0 prior

/-- Move mechanically to the next registered term after fixing a refutation. -/
def next (selection : ExactBottomCandidateSelection.{u})
    (hasNext : selection.index.val + 1 < exactBottomConditionCandidates.length)
    (refutation : ExactBottomCandidateRefutation.{u} selection.template) :
    ExactBottomCandidateSelection.{u} where
  index := ⟨selection.index.val + 1, hasNext⟩
  priorRefutations := by
    intro prior
    by_cases hprior : prior.val < selection.index.val
    · exact selection.priorRefutations ⟨prior.val, hprior⟩
    · have heq : prior.val = selection.index.val :=
        Nat.eq_of_lt_succ_of_not_lt prior.isLt hprior
      have hfin :
          (⟨prior.val, Nat.lt_trans prior.isLt hasNext⟩ :
            Fin exactBottomConditionCandidates.length) = selection.index :=
        Fin.ext heq
      simpa [template, exactBottomCandidateTerm, hfin] using refutation

end ExactBottomCandidateSelection

/-! ## Branch and regime output types -/

/-- The positive branch: every semantic exact-bottom arrow is covered. -/
structure GlobalExactBottomCoverage : Type (u + 1) where
  cover : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (input : CartSemanticInput U),
    Nonempty (AnchoredCoverageWitness input)

/--
The negative branch payload at one universe level.  It records one authored
base term, its canonical carrier-wise rebase, a sufficient witness producer,
and a semantic arrow outside the covered locus.  Qualification proofs are
separate theorem fields so no presentation or raw fixture stores coverage.
-/
structure CharacterizedExactBottomCoverage : Type (u + 1) where
  selection : ExactBottomCandidateSelection.{u}
  qualification : ExactBottomConditionQualification.{u} selection.template
  sufficient : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (input : CartSemanticInput U),
    evalExactBottomCondition
        (rebaseExactBottomCondition selection.template) input →
      Nonempty (AnchoredCoverageWitness input)
  counterexampleCarrier : AtomCarrier.{u}
  counterexampleDecidableEq : DecidableEq counterexampleCarrier.Atom
  counterexample : CartSemanticInput counterexampleCarrier
  counterexample_not_covered :
    ¬ Nonempty (@AnchoredCoverageWitness _
      counterexampleDecidableEq counterexample)

/-- The single carrier-global disjunction required by G-112(b). -/
inductive ExactBottomCoverageDisjunction : Type (u + 1)
  | global (proof : GlobalExactBottomCoverage.{u})
  | characterized (proof : CharacterizedExactBottomCoverage.{u})

/--
A per-carrier view contains only the named branch artifact.  Its constructor
cannot accept a coverage producer independently of that artifact.
-/
structure ExactBottomCoverageRegime (U : AtomCarrier.{u})
    [DecidableEq U.Atom] where
  artifact : ExactBottomCoverageDisjunction.{u}

namespace ExactBottomCoverageRegime

/-- Membership is derived from the named branch artifact. -/
def Holds {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : ExactBottomCoverageRegime U)
    (input : CartSemanticInput U) : Prop :=
  match regime.artifact with
  | .global _ => True
  | .characterized proof =>
      evalExactBottomCondition
        (rebaseExactBottomCondition proof.selection.template) input

/-- Every regime uses the coverage producer stored in its named branch artifact. -/
theorem covers {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : ExactBottomCoverageRegime U)
    (input : CartSemanticInput U) (membership : regime.Holds input) :
    Nonempty (AnchoredCoverageWitness input) := by
  rcases regime with ⟨artifact⟩
  cases artifact with
  | global proof => exact proof.cover U input
  | characterized proof =>
      exact proof.sufficient U input (by simpa [Holds] using membership)

end ExactBottomCoverageRegime

/-- Produce the branch-independent regime by consuming the branch payload. -/
def exactBottomCoverageRegimeOfDisjunction
    (artifact : ExactBottomCoverageDisjunction.{u}) :
    ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom],
      ExactBottomCoverageRegime U :=
  fun _ _ => ⟨artifact⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
