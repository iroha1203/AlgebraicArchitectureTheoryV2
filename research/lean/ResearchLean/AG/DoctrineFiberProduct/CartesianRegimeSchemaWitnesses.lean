import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchema

/-!
# Witnesses for the G-110 cartesian-regime type surface

These witnesses exercise the F0 signatures without selecting the theorem's K1
branch.  They construct an actual strong cartesian lift of an identity bottom
arrow, a qualified tautological condition using only the fixed finite syntax,
and both per-carrier regime eliminator paths under their mathematically honest
premises.  They do not provide `GlobalCartesianLift`, `RightBranch`, a finite
no-lift witness, or the final `DisjunctionArtifact`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## A genuine strong cartesian identity lift -/

/-- Semantic identity input at the point selected by one core package. -/
def packageIdentitySemanticInput {U : AtomCarrier.{u}}
    (package : AATCorePackage U) : CartSemanticInput U where
  source := packagePoint package
  target := packagePoint package
  hom := 𝟙 (packagePoint package)

/-- The package itself as an endpoint object over its selected point. -/
def packageIdentityTarget {U : AtomCarrier.{u}}
    (package : AATCorePackage U) :
    CoreFiber (packageIdentitySemanticInput package).target :=
  ⟨package, rfl⟩

/-- Identity in the package total category is a genuine strong cartesian lift. -/
def packageIdentityStrongCartesianLift {U : AtomCarrier.{u}}
    (package : AATCorePackage U) :
    StrongCartesianLift (packageIdentitySemanticInput package)
      (packageIdentityTarget package) where
  domain := package
  hom := 𝟙 package
  isStronglyCartesian := by
    letI : (packageProjection U).IsHomLift
        (𝟙 (packagePoint package)) (𝟙 package) :=
      CategoryTheory.IsHomLift.id rfl
    change (packageProjection U).IsStronglyCartesian
      (𝟙 (packagePoint package)) (𝟙 package)
    infer_instance

/-- The identity lift existence predicate fires on the concrete generated lift. -/
theorem packageIdentity_hasStrongCartesianLift {U : AtomCarrier.{u}}
    (package : AATCorePackage U) :
    HasStrongCartesianLift (packageIdentitySemanticInput package)
      (packageIdentityTarget package) :=
  ⟨packageIdentityStrongCartesianLift package⟩

/-- The generated lift's domain object is the original package in the source fiber. -/
theorem packageIdentity_domainObject_val {U : AtomCarrier.{u}}
    (package : AATCorePackage U) :
    (packageIdentityStrongCartesianLift package).domainObject.1 = package :=
  rfl

/-! ## A fixed-syntax qualified condition -/

/-- A tautology expressed solely by equality of the source-cardinality projection with itself. -/
def tautologicalCartConditionTerm (U : AtomCarrier.{u}) : CartConditionSyntax U :=
  .fieldEq (.projection .sourceCard) (.projection .sourceCard)

/--
A qualified wide condition used only to exercise the signature.  Its semantic
predicate is `True`, and its checker is the fixed projection equality above;
it is not the K1 right-branch `H_cart` because it cannot support a condition-
failing counterexample.
-/
def tautologicalQualifiedCartCondition (U : AtomCarrier.{u})
    [DecidableEq U.Atom] : QualifiedCartCondition U where
  term := tautologicalCartConditionTerm U
  holds := fun _ => True
  bridge := by
    intro presentation
    simp [tautologicalCartConditionTerm, evalCartCondition]
  replacement_invariant := by
    intro first second hsame
    simp [tautologicalCartConditionTerm, evalCartCondition]
  isomorphic_invariant := by
    intro first second hiso
    simp
  identity_mem := by
    intro instanceCode
    trivial
  comp_mem := by
    intro source middle target first second hfirst hsecond
    trivial
  pullback_fst_mem := by
    intro left right base first second hsecond
    trivial
  pullback_snd_mem := by
    intro left right base first second hfirst
    trivial

/-- The derived finite checker for the qualified tautology evaluates to true. -/
theorem tautologicalQualifiedCartCondition_check_true
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : CartPresentation U) :
    (tautologicalQualifiedCartCondition U).checkCart presentation = true := by
  simp [QualifiedCartCondition.checkCart, tautologicalQualifiedCartCondition,
    tautologicalCartConditionTerm, evalCartCondition]

/-- A carrier-wide lift supply turns the qualified tautology into local right-branch data. -/
def tautologicalRightCartesianRegime
    (U : AtomCarrier.{u}) [DecidableEq U.Atom]
    (lift : CarrierCartesianLift U) : RightCartesianRegime U where
  condition := tautologicalQualifiedCartCondition U
  sufficient := by
    intro input membership targetPackage
    exact lift input targetPackage

/-- The global regime constructor exposes the unconditional lift supply unchanged. -/
theorem globalRegime_hasStrongCartesianLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (lift : CarrierCartesianLift U) (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    HasStrongCartesianLift input.semantic targetPackage := by
  exact (CartesianRegime.global lift).hasStrongCartesianLift input trivial
    targetPackage

/-- The conditional regime path consumes the selected semantic membership proof. -/
theorem conditionalRegime_hasStrongCartesianLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (lift : CarrierCartesianLift U) (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    HasStrongCartesianLift input.semantic targetPackage := by
  let regime : CartesianRegime U :=
    .conditional (tautologicalRightCartesianRegime U lift)
  exact regime.hasStrongCartesianLift input trivial targetPackage

/-! ## Explicit universe-lifted finite carrier cells -/

/-- One Atom of the canonical finite carrier lifted to arbitrary universe. -/
def finiteModelLiftAtomA : finiteModelLiftCarrier.{u}.Atom :=
  ULift.up FiniteModel.FiniteAtom.componentA

/-- A second Atom of the canonical finite carrier lifted to arbitrary universe. -/
def finiteModelLiftAtomB : finiteModelLiftCarrier.{u}.Atom :=
  ULift.up FiniteModel.FiniteAtom.componentB

/-- The explicit universe transport does not collapse distinct finite Atoms. -/
theorem finiteModelLiftAtoms_ne :
    finiteModelLiftAtomA.{u} ≠ finiteModelLiftAtomB.{u} := by
  intro h
  have hdown := congrArg ULift.down h
  cases hdown

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
