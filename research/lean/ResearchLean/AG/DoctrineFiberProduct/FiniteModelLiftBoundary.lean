import ResearchLean.AG.DoctrineFiberProduct.CartesianTarget
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteCorePackageULift

/-!
# The ambient boundary of finite-model lift reflection

This module records the strongest comparison supplied by the existing
cartesian universal property.  Two strong lifts of the same semantic arrow to
the same target package have canonically isomorphic domains, the isomorphism
is vertical over the source, and both triangle equations hold.  In particular,
every strong lift is comparable inside its original package-total category to
the generated lift from `strongCartesianLiftOfTarget`.

The comparison remains entirely over one Atom carrier.  It neither lowers an
arbitrary lifted domain package to `FiniteModel.carrier` nor supplies a
cross-carrier package-total hom.  Those are separate data that the current
universal property does not produce.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

namespace StrongCartesianLift

/--
The canonical domain isomorphism between two strong lifts with the same base
arrow and target package.
-/
noncomputable def domainIso {U : AtomCarrier.{u}}
    {input : CartSemanticInput U} {targetPackage : CoreFiber input.target}
    (first second : StrongCartesianLift input targetPackage) :
    second.domain ≅ first.domain := by
  letI := first.isStronglyCartesian
  letI := second.isStronglyCartesian
  exact CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso
    (packageProjection U) input.hom first.hom second.hom

/-- The forward domain comparison followed by the first lift is the second lift. -/
theorem domainIso_hom_fac {U : AtomCarrier.{u}}
    {input : CartSemanticInput U} {targetPackage : CoreFiber input.target}
    (first second : StrongCartesianLift input targetPackage) :
    (domainIso first second).hom ≫ first.hom = second.hom := by
  letI := first.isStronglyCartesian
  letI := second.isStronglyCartesian
  exact CategoryTheory.Functor.IsCartesian.fac
    (packageProjection U) input.hom first.hom second.hom

/-- The inverse domain comparison followed by the second lift is the first lift. -/
theorem domainIso_inv_fac {U : AtomCarrier.{u}}
    {input : CartSemanticInput U} {targetPackage : CoreFiber input.target}
    (first second : StrongCartesianLift input targetPackage) :
    (domainIso first second).inv ≫ second.hom = first.hom := by
  rw [← domainIso_hom_fac first second]
  simp

/-- The forward domain comparison is vertical over the source identity. -/
theorem domainIso_hom_isHomLift {U : AtomCarrier.{u}}
    {input : CartSemanticInput U} {targetPackage : CoreFiber input.target}
    (first second : StrongCartesianLift input targetPackage) :
    (packageProjection U).IsHomLift (𝟙 input.source)
      (domainIso first second).hom := by
  letI := first.isStronglyCartesian
  letI := second.isStronglyCartesian
  change (packageProjection U).IsHomLift (𝟙 input.source)
    (CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso
      (packageProjection U) input.hom first.hom second.hom).hom
  infer_instance

/-- The inverse domain comparison is vertical over the source identity. -/
theorem domainIso_inv_isHomLift {U : AtomCarrier.{u}}
    {input : CartSemanticInput U} {targetPackage : CoreFiber input.target}
    (first second : StrongCartesianLift input targetPackage) :
    (packageProjection U).IsHomLift (𝟙 input.source)
      (domainIso first second).inv := by
  letI := first.isStronglyCartesian
  letI := second.isStronglyCartesian
  change (packageProjection U).IsHomLift (𝟙 input.source)
    (CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso
      (packageProjection U) input.hom first.hom second.hom).inv
  infer_instance

/-- Compare an arbitrary strong lift to the generated lift over the same endpoints. -/
noncomputable def canonicalDomainIso {U : AtomCarrier.{u}}
    {input : CartSemanticInput U} {targetPackage : CoreFiber input.target}
    (lift : StrongCartesianLift input targetPackage) :
    lift.domain ≅ (strongCartesianLiftOfTarget input targetPackage).domain :=
  domainIso (strongCartesianLiftOfTarget input targetPackage) lift

/-- The canonical comparison triangle uses the supplied lift as its right edge. -/
theorem canonicalDomainIso_hom_fac {U : AtomCarrier.{u}}
    {input : CartSemanticInput U} {targetPackage : CoreFiber input.target}
    (lift : StrongCartesianLift input targetPackage) :
    (canonicalDomainIso lift).hom ≫
        (strongCartesianLiftOfTarget input targetPackage).hom =
      lift.hom :=
  domainIso_hom_fac _ _

end StrongCartesianLift

/-! ## Concrete lifted finite-package boundary witness -/

/--
At the lifted finite package, the generated identity-arrow lift has a domain
canonically isomorphic to the literal identity lift domain.
-/
noncomputable def finiteModelLiftIdentityDomainIso :
    (strongCartesianLiftOfTarget
      (packageIdentitySemanticInput finiteModelLiftCorePackage.{u})
      (packageIdentityTarget finiteModelLiftCorePackage.{u})).domain ≅
      finiteModelLiftCorePackage.{u} :=
  StrongCartesianLift.domainIso
    (packageIdentityStrongCartesianLift finiteModelLiftCorePackage.{u})
    (strongCartesianLiftOfTarget
      (packageIdentitySemanticInput finiteModelLiftCorePackage.{u})
      (packageIdentityTarget finiteModelLiftCorePackage.{u}))

/-- The concrete lifted finite-package domain isomorphism satisfies its triangle law. -/
theorem finiteModelLiftIdentityDomainIso_hom_fac :
    finiteModelLiftIdentityDomainIso.{u}.hom ≫
      (packageIdentityStrongCartesianLift
        finiteModelLiftCorePackage.{u}).hom =
    (strongCartesianLiftOfTarget
      (packageIdentitySemanticInput finiteModelLiftCorePackage.{u})
      (packageIdentityTarget finiteModelLiftCorePackage.{u})).hom :=
  StrongCartesianLift.domainIso_hom_fac _ _

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
