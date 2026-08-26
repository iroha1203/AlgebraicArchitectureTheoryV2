import ResearchLean.AG.DoctrineFiberProduct.CartesianBranchArtifact

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

/-! ## Branch and regime output types -/

/--
A carrier-local regime is either global or governed by one closed syntax term.
There is no arbitrary `Prop` field: membership is derived below.
-/
inductive ExactBottomCoverageRegime (U : AtomCarrier.{u})
    [DecidableEq U.Atom]
  | global (cover : ∀ input : CartSemanticInput U,
      Nonempty (AnchoredCoverageWitness input))
  | characterized (term : ExactBottomConditionSyntax U)
      (cover : ∀ input : CartSemanticInput U,
        evalExactBottomCondition term input →
          Nonempty (AnchoredCoverageWitness input))

namespace ExactBottomCoverageRegime

/-- Membership is total in the global branch and syntax evaluation otherwise. -/
def Holds {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : ExactBottomCoverageRegime U)
    (input : CartSemanticInput U) : Prop :=
  match regime with
  | .global _ => True
  | .characterized term _ => evalExactBottomCondition term input

/-- Every regime produces coverage for each member. -/
theorem covers {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : ExactBottomCoverageRegime U)
    (input : CartSemanticInput U) (membership : regime.Holds input) :
    Nonempty (AnchoredCoverageWitness input) := by
  cases regime with
  | global cover => exact cover input
  | characterized _ cover => exact cover input membership

end ExactBottomCoverageRegime

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
  template : ExactBottomConditionSyntax FiniteModel.carrier
  template_is_fixed_head :
    template = exactBottomFirstCandidate FiniteModel.carrier
  sufficient : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (input : CartSemanticInput U),
    evalExactBottomCondition (rebaseExactBottomCondition template) input →
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

/-- Produce the branch-independent regime by consuming the branch payload. -/
def exactBottomCoverageRegimeOfDisjunction
    (artifact : ExactBottomCoverageDisjunction.{u}) :
    ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom],
      ExactBottomCoverageRegime U := by
  intro U _
  cases artifact with
  | global proof => exact .global (proof.cover U)
  | characterized proof =>
      exact .characterized (rebaseExactBottomCondition proof.template)
        (proof.sufficient U)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
