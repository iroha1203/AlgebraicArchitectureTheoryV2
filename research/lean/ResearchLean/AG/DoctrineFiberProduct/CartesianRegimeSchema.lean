import Formal.AG.Examples.FiniteModel
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchema

/-!
# Cartesian-regime signatures for G-110

This module fixes the F0 type surface for the carrier-global cartesian-lift
disjunction.  Its domain is the already reviewed realization image:
`RealizableHom U` supplies both the semantic bottom arrow and its finite
presentation provenance, while an endpoint package is an object of the actual
core fiber over the semantic target.

The left branch quantifies over every carrier at one universe before choosing a
branch.  The right branch carries one uniform family of qualified conditions,
not a per-carrier disjunction.  A `CartesianRegime U` is obtained only by the
named `cartesianRegimeOfDisjunction` producer in later theorem use; accepting an
unrelated regime as a hypothesis does not discharge G-110.

No value of either branch is constructed here.  In particular, this F0 module
does not choose `H_cart`, prove a checker bridge or sufficiency theorem, produce
a cartesian lift, or prove a finite nonexistence counterexample.  Those are K1
proof obligations.
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
holds.
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
  /-- Each member has nonisomorphic source and target instances. -/
  endpoints_nonisomorphic : ∀ parameter,
    ¬ Nonempty ((input parameter).semantic.source ≅
      (input parameter).semantic.target)
  /-- Each realized bottom arrow is genuinely noninvertible. -/
  hom_not_isIso : ∀ parameter, ¬ IsIso (input parameter).semantic.hom

/-- One carrier's qualified right-branch data and uniform lift sufficiency. -/
structure RightCartesianRegime (U : AtomCarrier.{u}) [DecidableEq U.Atom] where
  /-- Qualified semantic condition selected by the right branch. -/
  condition : QualifiedCartCondition U
  /-- Membership supplies a lift for every package over the semantic endpoint. -/
  sufficient : ∀ (input : RealizableHom U), condition.holds input →
    ∀ targetPackage : CoreFiber input.semantic.target,
      HasStrongCartesianLift input.semantic targetPackage

/-! ## Finite counterexample transport interface -/

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

/--
Interface for transporting the concrete universe-zero `FiniteModel` no-lift
witness to the canonical `ULift` carrier.  `strongLiftEquiv` is the exact
transport statement: nonexistence at the lifted input is derived from the base
proof rather than assumed as a second certificate.
-/
structure FiniteModelLift
    (baseCondition : QualifiedCartCondition FiniteModel.carrier)
    (liftedCondition : QualifiedCartCondition finiteModelLiftCarrier.{u}) where
  /-- Concrete condition-failing no-lift witness on the original finite carrier. -/
  base : CartesianLiftCounterexample baseCondition
  /-- Transported realized bottom arrow on the lifted carrier. -/
  liftedInput : RealizableHom finiteModelLiftCarrier.{u}
  /-- Transported endpoint package on the lifted carrier. -/
  liftedTargetPackage : CoreFiber liftedInput.semantic.target
  /-- Strong lift data are equivalent before and after the explicit universe transport. -/
  strongLiftEquiv :
    StrongCartesianLift base.nonexistence.input.semantic
        base.nonexistence.targetPackage ≃
      StrongCartesianLift liftedInput.semantic liftedTargetPackage
  /-- The semantic condition has the same truth value on the transported input. -/
  condition_preserved :
    liftedCondition.holds liftedInput ↔
      baseCondition.holds base.nonexistence.input

namespace FiniteModelLift

/-- Nonexistence transfers from the universe-zero finite witness. -/
theorem lifted_no_lift
    {baseCondition : QualifiedCartCondition FiniteModel.carrier}
    {liftedCondition : QualifiedCartCondition finiteModelLiftCarrier.{u}}
    (lift : FiniteModelLift baseCondition liftedCondition) :
    ¬ HasStrongCartesianLift lift.liftedInput.semantic
      lift.liftedTargetPackage := by
  intro hexists
  rcases hexists with ⟨lifted⟩
  exact lift.base.nonexistence.no_lift ⟨lift.strongLiftEquiv.symm lifted⟩

/-- Package the transported no-lift and condition-failure proofs together. -/
def counterexample
    {baseCondition : QualifiedCartCondition FiniteModel.carrier}
    {liftedCondition : QualifiedCartCondition finiteModelLiftCarrier.{u}}
    (lift : FiniteModelLift baseCondition liftedCondition) :
    CartesianLiftCounterexample liftedCondition where
  nonexistence :=
    { input := lift.liftedInput
      targetPackage := lift.liftedTargetPackage
      no_lift := lift.lifted_no_lift }
  condition_fails := by
    intro hholds
    exact lift.base.condition_fails (lift.condition_preserved.mp hholds)

end FiniteModelLift

/-! ## Global branch artifact and generated per-carrier regime -/

/--
The carrier-global right branch.  `regime` chooses one uniform qualified family
over all carriers at the fixed universe.  The positive family and original
counterexample use the exact universe-zero finite specialization; the
`FiniteModelLift` field relates that specialization to the structurally rebased
condition on the canonical lifted carrier.
-/
structure RightBranch where
  /-- Carrier-independent structural syntax selected before any fixture is inspected. -/
  template : CartConditionSyntax FiniteModel.carrier
  /-- Universe-zero specialization of the same qualified right-branch family. -/
  baseRegime : RightCartesianRegime FiniteModel.carrier
  /-- The base specialization uses exactly the selected structural template. -/
  base_term : baseRegime.condition.term = template
  /-- Uniform qualified condition and sufficiency theorem for every carrier. -/
  regime : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom], RightCartesianRegime U
  /-- Every carrier specialization is the structural rebasing of the same template. -/
  regime_term : ∀ (U : AtomCarrier.{u}) [DecidableEq U.Atom],
    (regime U).condition.term = rebaseCartCondition template
  /-- A non-singleton noninvertible positive family on the concrete finite carrier. -/
  positiveFamily : ParametricCartPositiveFamily
    baseRegime.condition
  /-- The finite no-lift counterexample transported to this universe. -/
  finiteModelLift : FiniteModelLift
    baseRegime.condition
    (regime finiteModelLiftCarrier.{u}).condition

namespace RightBranch

/-- The transported finite witness fails both the selected condition and lift existence. -/
def finiteCounterexample (right : RightBranch.{u}) :
    CartesianLiftCounterexample
      (right.regime finiteModelLiftCarrier.{u}).condition :=
  right.finiteModelLift.counterexample

/-- The transported finite counterexample refutes the carrier-global left branch. -/
theorem not_global (right : RightBranch.{u}) : ¬ GlobalCartesianLift.{u} := by
  intro global
  exact right.finiteModelLift.lifted_no_lift
    (global finiteModelLiftCarrier.{u}
      right.finiteModelLift.liftedInput
      right.finiteModelLift.liftedTargetPackage)

end RightBranch

/-- The single carrier-global disjunction artifact fixed by G-110. -/
inductive DisjunctionArtifact
  /-- The unconditional branch supplies lifts over every carrier. -/
  | global (proof : GlobalCartesianLift.{u})
  /-- The conditional branch supplies one uniform qualified right branch. -/
  | conditional (proof : RightBranch.{u})

/-- Per-carrier data exported from the already chosen global disjunction branch. -/
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

/--
Instantiate the already chosen global branch at every carrier.  This is the
only producer counted by G-110; later theorems must use its output rather than
accept an unrelated `CartesianRegime` as a discharge of the disjunction.
-/
def cartesianRegimeOfDisjunction
    (artifact : DisjunctionArtifact.{u})
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] : CartesianRegime U :=
  match artifact with
  | .global global => .global (global U)
  | .conditional right => .conditional (right.regime U)

/-- The producer specializes the global branch to its carrier-level lift supply. -/
@[simp]
theorem cartesianRegimeOfDisjunction_global
    (global : GlobalCartesianLift.{u})
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    cartesianRegimeOfDisjunction (.global global) U = .global (global U) :=
  rfl

/-- The producer specializes the uniform right branch to its carrier-level regime. -/
@[simp]
theorem cartesianRegimeOfDisjunction_conditional
    (right : RightBranch.{u})
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    cartesianRegimeOfDisjunction (.conditional right) U =
      .conditional (right.regime U) :=
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
