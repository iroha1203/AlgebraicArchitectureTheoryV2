import Formal.AG.Examples.FiniteModel
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchema

/-!
# Cartesian-regime signatures for G-110

This module fixes the first F0 type surface for the carrier-global
cartesian-lift disjunction.  Its domain is the already reviewed realization image:
`RealizableHom U` supplies both the semantic bottom arrow and its finite
presentation provenance, while an endpoint package is an object of the actual
core fiber over the semantic target.

The left-branch quantifier, qualified per-carrier right-regime data, genuine
positive-family interfaces, and the branch-independent per-carrier regime are
fixed here.  `CartesianBranch` constructs the carrier-global branch artifact
and its named producer.  The separate cross-universe modules record helper
constructions for finite package representations.

No value of either branch is constructed in this schema module.  Subsequent
modules construct the selected global lift, branch artifact, and regime
producer from these signatures.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Strong cartesian lifts on the realization image -/

/--
A strongly cartesian lift of one realized bottom arrow to a package over its
target.  The domain package and total morphism are output data; strong
cartesianness is a property of that generated morphism, not an input field of a
finite presentation.
-/
structure StrongCartesianLift {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) (targetPackage : CoreFiber input.target) where
  /-- Domain package of the lifted total morphism. -/
  domain : AATCorePackage U
  /-- Total morphism ending at the requested target package. -/
  hom : domain ⟶ targetPackage.1
  /-- The total morphism has the actual mathlib strong cartesian universal property. -/
  isStronglyCartesian :
    (packageProjection U).IsStronglyCartesian input.hom hom

namespace StrongCartesianLift

/-- The domain package lies over the source of the realized bottom arrow. -/
def domainObject {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    {targetPackage : CoreFiber input.target}
    (lift : StrongCartesianLift input targetPackage) : CoreFiber input.source := by
  letI := lift.isStronglyCartesian
  exact ⟨lift.domain,
    CategoryTheory.IsHomLift.domain_eq
      (packageProjection U) input.hom lift.hom⟩

end StrongCartesianLift

/-- Existence of a strong cartesian lift at one realized arrow and target package. -/
def HasStrongCartesianLift {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) (targetPackage : CoreFiber input.target) : Prop :=
  Nonempty (StrongCartesianLift input targetPackage)

/-- Strong cartesian lift existence for every realized arrow over one carrier. -/
def CarrierCartesianLift (U : AtomCarrier.{u}) [DecidableEq U.Atom] : Prop :=
  ∀ (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target),
    HasStrongCartesianLift input.semantic targetPackage

/--
The carrier-global left branch.  The branch is chosen outside the carrier
quantifier, so this is not the weaker statement `∀ U, left U ∨ right U`.
-/
def GlobalCartesianLift : Prop :=
  ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom], CarrierCartesianLift U

/-! ## Qualified right-branch conditions -/

/--
An isomorphism of semantic bottom-arrow inputs.  The commutative square fixes
the usual arrow-category notion without extending the theorem beyond the
realization image.
-/
structure CartSemanticInputIso {U : AtomCarrier.{u}}
    (first second : CartSemanticInput U) where
  /-- Isomorphism of source pointed instances. -/
  sourceIso : first.source ≅ second.source
  /-- Isomorphism of target pointed instances. -/
  targetIso : first.target ≅ second.target
  /-- Compatibility of the two bottom arrows with the endpoint isomorphisms. -/
  hom_comm : sourceIso.hom ≫ second.hom = first.hom ≫ targetIso.hom

namespace CartSemanticInputIso

/-- Every semantic bottom-arrow input is isomorphic to itself. -/
def refl {U : AtomCarrier.{u}} (input : CartSemanticInput U) :
    CartSemanticInputIso input input where
  sourceIso := Iso.refl _
  targetIso := Iso.refl _
  hom_comm := by simp

end CartSemanticInputIso

/-! ## Carrier-independent structural condition templates -/

/-- Reinterpret a fixed cartesian projection at another Atom carrier. -/
def rebaseCartProjection {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    {kind : CartFieldKind} : CartProjection U kind → CartProjection V kind
  | .sourceCard => .sourceCard
  | .targetCard => .targetCard
  | .sourcePoint => .sourcePoint
  | .targetPoint => .targetPoint
  | .sourceNormalize => .sourceNormalize
  | .targetNormalize => .targetNormalize
  | .sourceExtractionDefaults => .sourceExtractionDefaults
  | .targetExtractionDefaults => .targetExtractionDefaults
  | .sourceExtractionExceptions => .sourceExtractionExceptions
  | .targetExtractionExceptions => .targetExtractionExceptions
  | .sourceMap => .sourceMap
  | .atomSupport => .atomSupport
  | .atomMap => .atomMap

/-- Reinterpret one of the three fixed named constants at another Atom carrier. -/
def rebaseCartNamedConstant {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    {kind : CartFieldKind} :
    CartNamedConstant U kind → CartNamedConstant V kind
  | .identitySourceMap => .identitySourceMap
  | .identityAtomMap => .identityAtomMap
  | .emptyAtomSupport => .emptyAtomSupport

/-- Reinterpret a fixed field term at another Atom carrier. -/
def rebaseCartFieldTerm {U : AtomCarrier.{u}} {V : AtomCarrier.{v}}
    {kind : CartFieldKind} : CartFieldTerm U kind → CartFieldTerm V kind
  | .projection projection => .projection (rebaseCartProjection projection)
  | .constant constant => .constant (rebaseCartNamedConstant constant)

/--
Reinterpret a complete fixed-syntax condition at another Atom carrier.  The
map is possible precisely because the frozen language contains no authored
Atom, fixture value, external finite set, or result bit.
-/
def rebaseCartCondition {U : AtomCarrier.{u}} {V : AtomCarrier.{v}} :
    CartConditionSyntax U → CartConditionSyntax V
  | .fieldEq left right =>
      .fieldEq (rebaseCartFieldTerm left) (rebaseCartFieldTerm right)
  | .fieldMem field set => .fieldMem (rebaseCartFieldTerm field) set
  | .allCells equality => .allCells equality
  | .conjunction left right =>
      .conjunction (rebaseCartCondition left) (rebaseCartCondition right)

/--
A semantic `H_cart` together with every local qualification fixed by the GOAL.
The Boolean checker is derived from `term`; it is not stored independently.
The bridge therefore has the required direction from the fixed finite syntax to
a separately authored semantic predicate on `RealizableHom U`.
-/
structure QualifiedCartCondition (U : AtomCarrier.{u}) [DecidableEq U.Atom] where
  /-- One term of the completely enumerated cartesian condition language. -/
  term : CartConditionSyntax U
  /-- Semantic condition on realization witnesses. -/
  holds : RealizableHom U → Prop
  /-- Checker/semantic bridge whose eventual K1 proof must be non-definitional. -/
  bridge : ∀ presentation : CartPresentation U,
    evalCartCondition term presentation = true ↔
      holds (realizableHomOf presentation)
  /-- The checker cannot distinguish two presentations of the same semantic arrow. -/
  replacement_invariant : ∀ first second : CartPresentation U,
    toSemanticCart first = toSemanticCart second →
      evalCartCondition term first = evalCartCondition term second
  /-- The semantic condition is invariant under isomorphism of realized arrow data. -/
  isomorphic_invariant : ∀ first second : RealizableHom U,
    CartSemanticInputIso first.semantic second.semantic →
      (holds first ↔ holds second)
  /-- Every generated identity presentation belongs to the condition. -/
  identity_mem : ∀ instanceCode : FiniteInstanceCode U,
    holds (realizableHomOf (idPresentation instanceCode))
  /-- Membership is closed under the generated typed composition constructor. -/
  comp_mem : ∀ {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target),
    holds (realizableHomOf first.toPresentation) →
    holds (realizableHomOf second.toPresentation) →
    holds (realizableHomOf (compPresentation first second).toPresentation)
  /-- Base-changing the second cospan leg yields membership of the first projection. -/
  pullback_fst_mem : ∀ {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base),
    holds (realizableHomOf second.toPresentation) →
    holds (realizableHomOf
      (pullbackFstPresentation first second).toPresentation)
  /-- Base-changing the first cospan leg yields membership of the second projection. -/
  pullback_snd_mem : ∀ {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base),
    holds (realizableHomOf first.toPresentation) →
    holds (realizableHomOf
      (pullbackSndPresentation first second).toPresentation)

namespace QualifiedCartCondition

/-- The finite checker is exactly evaluation of the selected fixed-syntax term. -/
def checkCart {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (condition : QualifiedCartCondition U) (presentation : CartPresentation U) : Bool :=
  evalCartCondition condition.term presentation

/-- The derived checker has the separately stored semantic bridge. -/
theorem checkCart_eq_true_iff {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (condition : QualifiedCartCondition U) (presentation : CartPresentation U) :
    condition.checkCart presentation = true ↔
      condition.holds (realizableHomOf presentation) :=
  condition.bridge presentation

/-- Every realization witness is governed by the checker on its own presentation. -/
theorem checkCart_input_eq_true_iff {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (condition : QualifiedCartCondition U) (input : RealizableHom U) :
    condition.checkCart input.presentation = true ↔ condition.holds input := by
  rw [condition.checkCart_eq_true_iff]
  have heq : input = realizableHomOf input.presentation := by
    cases input with
    | mk semantic presentation realization_eq =>
        cases realization_eq
        rfl
  exact iff_of_eq (congrArg condition.holds heq).symm

end QualifiedCartCondition

/--
A genuinely parameterized positive family for a right branch.  The family has
at least two parameters, gives distinct semantic inputs, and every member joins
nonisomorphic endpoints by a noninvertible realized arrow on which `H_cart`
holds.  Each of those same members also carries an endpoint package and an
actual strong cartesian lift, so condition nonemptiness cannot be witnessed on
an empty target fiber or on a family unrelated to the lift portfolio.
-/
structure ParametricCartPositiveFamily {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (condition : QualifiedCartCondition U) where
  /-- Parameter type of the family. -/
  Parameter : Type u
  /-- First distinguished parameter. -/
  first : Parameter
  /-- Second distinguished parameter. -/
  second : Parameter
  /-- The family is not a disguised singleton fixture. -/
  first_ne_second : first ≠ second
  /-- Realized bottom arrow at every parameter. -/
  input : Parameter → RealizableHom U
  /-- Every member satisfies the qualified condition. -/
  holds : ∀ parameter, condition.holds (input parameter)
  /-- The two distinguished parameters produce different semantic inputs. -/
  distinguished_ne : (input first).semantic ≠ (input second).semantic
  /-- Distinct parameters represent distinct isomorphism classes of semantic arrows. -/
  pairwise_nonisomorphic : ∀ firstParameter secondParameter : Parameter,
    firstParameter ≠ secondParameter →
      ¬ Nonempty (CartSemanticInputIso
        (input firstParameter).semantic (input secondParameter).semantic)
  /-- Each member has nonisomorphic source and target instances. -/
  endpoints_nonisomorphic : ∀ parameter,
    ¬ Nonempty ((input parameter).semantic.source ≅
      (input parameter).semantic.target)
  /-- Each realized bottom arrow is genuinely noninvertible. -/
  hom_not_isIso : ∀ parameter, ¬ IsIso (input parameter).semantic.hom
  /-- Endpoint package selected for the explicit lift of this same positive member. -/
  targetPackage : ∀ parameter,
    CoreFiber (input parameter).semantic.target
  /-- Actual strong cartesian lift of this same `H_cart`-positive member. -/
  lift : ∀ parameter,
    StrongCartesianLift (input parameter).semantic (targetPackage parameter)

/--
A genuinely parameterized family of constructed strong lifts.  This portfolio
interface is independent of which global branch K1 eventually proves.  It
prevents an identity-only witness or duplicated representatives of one arrow
isomorphism class from discharging the positive-family obligation.
-/
structure ParametricCartLiftFamily (U : AtomCarrier.{u})
    [DecidableEq U.Atom] where
  /-- Parameter type of the family. -/
  Parameter : Type u
  /-- First distinguished parameter. -/
  first : Parameter
  /-- Second distinguished parameter. -/
  second : Parameter
  /-- The family contains at least two parameters. -/
  first_ne_second : first ≠ second
  /-- Realized bottom arrow at every parameter. -/
  input : Parameter → RealizableHom U
  /-- Distinct parameters represent distinct isomorphism classes of semantic arrows. -/
  pairwise_nonisomorphic : ∀ firstParameter secondParameter : Parameter,
    firstParameter ≠ secondParameter →
      ¬ Nonempty (CartSemanticInputIso
        (input firstParameter).semantic (input secondParameter).semantic)
  /-- Each member joins nonisomorphic endpoint instances. -/
  endpoints_nonisomorphic : ∀ parameter,
    ¬ Nonempty ((input parameter).semantic.source ≅
      (input parameter).semantic.target)
  /-- Each member is a genuinely noninvertible realized bottom arrow. -/
  hom_not_isIso : ∀ parameter, ¬ IsIso (input parameter).semantic.hom
  /-- Endpoint package selected for the explicit lift at every parameter. -/
  targetPackage : ∀ parameter,
    CoreFiber (input parameter).semantic.target
  /-- Actual strong cartesian lift constructed at every parameter. -/
  lift : ∀ parameter,
    StrongCartesianLift (input parameter).semantic (targetPackage parameter)

/-- One carrier's qualified right-branch data and uniform lift sufficiency. -/
structure RightCartesianRegime (U : AtomCarrier.{u}) [DecidableEq U.Atom] where
  /-- Qualified semantic condition selected by the right branch. -/
  condition : QualifiedCartCondition U
  /-- Membership supplies a lift for every package over the semantic endpoint. -/
  sufficient : ∀ (input : RealizableHom U), condition.holds input →
    ∀ targetPackage : CoreFiber input.semantic.target,
      HasStrongCartesianLift input.semantic targetPackage

/-! ## Finite counterexample endpoint types -/

/--
The canonical universe lift of the fixed finite carrier.  Every coordinate and
the Atom type itself are transported through `ULift`, preventing an implicit
specialization of the global branch to universe zero.
-/
def finiteModelLiftCarrier : AtomCarrier.{u} where
  AtomKind := ULift.{u} FiniteModel.FiniteAtom
  Axis := ULift.{u} FiniteModel.FiniteAtom
  Subject := ULift.{u} FiniteModel.FiniteAtom
  Predicate := ULift.{u} FiniteModel.FiniteAtom
  Payload := ULift.{u} FiniteModel.FiniteAtom
  Atom := ULift.{u} FiniteModel.FiniteAtom
  kind atom := ULift.up atom.down
  axis atom := ULift.up atom.down
  subject atom := ULift.up atom.down
  predicate atom := ULift.up atom.down
  payload atom := ULift.up atom.down

/-- Decidable Atom equality survives the canonical finite-carrier universe lift. -/
instance finiteModelLiftCarrierAtomDecidableEq :
    DecidableEq finiteModelLiftCarrier.{u}.Atom := by
  change DecidableEq (ULift.{u} FiniteModel.FiniteAtom)
  infer_instance

/-- Decidable Atom equality for the original universe-zero finite carrier. -/
local instance finiteModelRegimeCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- A realized finite input and endpoint package for which no strong lift exists. -/
structure CartesianLiftNonexistence (U : AtomCarrier.{u}) [DecidableEq U.Atom] where
  /-- Realized bottom arrow of the counterexample. -/
  input : RealizableHom U
  /-- Package over the semantic target at which lifting fails. -/
  targetPackage : CoreFiber input.semantic.target
  /-- Kernel-level nonexistence of a strongly cartesian lift. -/
  no_lift : ¬ HasStrongCartesianLift input.semantic targetPackage

/-- A no-lift witness which also lies outside the selected right-branch condition. -/
structure CartesianLiftCounterexample {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (condition : QualifiedCartCondition U) where
  /-- Underlying realized no-lift witness. -/
  nonexistence : CartesianLiftNonexistence U
  /-- The same input does not satisfy `H_cart`. -/
  condition_fails : ¬ condition.holds nonexistence.input

/-
The pre-revision F0c2 route investigated cross-universe reindexing of
`packageProjection` before a finite no-lift transport.  The branch-conditioned
contract uses a named package only in the right-branch theorem package; the
selected global branch makes that package inapplicable.
-/

/-! ## Branch-independent per-carrier regime -/

/--
Per-carrier data to be exported from the carrier-global branch chosen in F0c2.
An arbitrary value of this type does not discharge the global disjunction;
later theorems must use the named producer built from that artifact.
-/
inductive CartesianRegime (U : AtomCarrier.{u}) [DecidableEq U.Atom]
  /-- The selected global branch, instantiated at this carrier. -/
  | global (lift : CarrierCartesianLift U)
  /-- The selected conditional branch, instantiated at this carrier. -/
  | conditional (right : RightCartesianRegime U)

namespace CartesianRegime

/-- Membership predicate exported by a regime; the global branch admits every realized arrow. -/
def HCart {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : CartesianRegime U) (input : RealizableHom U) : Prop :=
  match regime with
  | .global _ => True
  | .conditional right => right.condition.holds input

/-- Every regime supplies a strong lift for each admitted realized arrow and endpoint package. -/
theorem hasStrongCartesianLift {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : CartesianRegime U) (input : RealizableHom U)
    (membership : regime.HCart input)
    (targetPackage : CoreFiber input.semantic.target) :
    HasStrongCartesianLift input.semantic targetPackage := by
  cases regime with
  | global lift => exact lift input targetPackage
  | conditional right => exact right.sufficient input membership targetPackage

/-- Every generated identity belongs to the regime's admissible class. -/
theorem identity_mem {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : CartesianRegime U) (instanceCode : FiniteInstanceCode U) :
    regime.HCart (realizableHomOf (idPresentation instanceCode)) := by
  cases regime with
  | global _ => trivial
  | conditional right => exact right.condition.identity_mem instanceCode

/-- The regime's admissible class is closed under generated typed composition. -/
theorem comp_mem {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : CartesianRegime U)
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target)
    (hfirst : regime.HCart (realizableHomOf first.toPresentation))
    (hsecond : regime.HCart (realizableHomOf second.toPresentation)) :
    regime.HCart
      (realizableHomOf (compPresentation first second).toPresentation) := by
  cases regime with
  | global _ => trivial
  | conditional right => exact right.condition.comp_mem first second hfirst hsecond

/-- Membership of the second cospan leg gives membership of the first pullback projection. -/
theorem pullback_fst_mem {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : CartesianRegime U)
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base)
    (hsecond : regime.HCart (realizableHomOf second.toPresentation)) :
    regime.HCart (realizableHomOf
      (pullbackFstPresentation first second).toPresentation) := by
  cases regime with
  | global _ => trivial
  | conditional right => exact right.condition.pullback_fst_mem first second hsecond

/-- Membership of the first cospan leg gives membership of the second pullback projection. -/
theorem pullback_snd_mem {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (regime : CartesianRegime U)
    {left right base : FiniteInstanceCode U}
    (first : CartPresentationBetween left base)
    (second : CartPresentationBetween right base)
    (hfirst : regime.HCart (realizableHomOf first.toPresentation)) :
    regime.HCart (realizableHomOf
      (pullbackSndPresentation first second).toPresentation) := by
  cases regime with
  | global _ => trivial
  | conditional right => exact right.condition.pullback_snd_mem first second hfirst

end CartesianRegime

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
