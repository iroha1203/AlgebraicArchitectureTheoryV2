import ResearchLean.AG.DoctrineFiberProduct.FiniteModelRealizationULift

/-!
# Strong-cartesian lift transport along semantic-input isomorphisms

This module turns canonical core transport over an isomorphism into an
isomorphism in the total package category.  It then uses the inverse source and
target bridges to pull an already supplied strong-cartesian lift across an
isomorphism of semantic inputs.

The strong-cartesian certificate of the supplied lift is used in the composite
universal property.  No package, lift, or certificate is manufactured from a
global existence premise.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Total isomorphism carried by canonical core transport -/

/--
Canonical core transport over a base isomorphism is an isomorphism in the
total package category.
-/
noncomputable def coreFiberLiftIsoOfIso {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (iso : X ≅ Y) (package : CoreFiber X) :
    package.1 ≅ (coreFiberTransportObj iso.hom package).1 := by
  letI : (packageProjection U).IsStronglyCocartesian iso.hom
      (coreFiberLift iso.hom package) :=
    coreFiberLift_isStronglyCocartesian iso.hom package
  letI : IsIso (coreFiberLift iso.hom package) :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (packageProjection U) iso.hom (coreFiberLift iso.hom package)
  exact asIso (coreFiberLift iso.hom package)

/-- The forward map is exactly the canonical core lift. -/
@[simp]
theorem coreFiberLiftIsoOfIso_hom {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (iso : X ≅ Y) (package : CoreFiber X) :
    (coreFiberLiftIsoOfIso iso package).hom =
      coreFiberLift iso.hom package :=
  rfl

/-- The forward map lies over the authored base isomorphism. -/
theorem coreFiberLiftIsoOfIso_hom_isHomLift {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (iso : X ≅ Y) (package : CoreFiber X) :
    (packageProjection U).IsHomLift iso.hom
      (coreFiberLiftIsoOfIso iso package).hom := by
  simpa using coreFiberLift_isHomLift iso.hom package

/-- The inverse total map lies over the inverse base isomorphism. -/
theorem coreFiberLiftIsoOfIso_inv_isHomLift {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (iso : X ≅ Y) (package : CoreFiber X) :
    (packageProjection U).IsHomLift iso.inv
      (coreFiberLiftIsoOfIso iso package).inv := by
  letI : (packageProjection U).IsHomLift iso.hom
      (coreFiberLiftIsoOfIso iso package).hom :=
    coreFiberLiftIsoOfIso_hom_isHomLift iso package
  exact CategoryTheory.IsHomLift.inv_lift_inv
    (packageProjection U) iso (coreFiberLiftIsoOfIso iso package)

/-! ## Pullback of supplied strong-cartesian lifts -/

namespace CartSemanticInputIso

/-- Transport a target package along the target component of an input iso. -/
noncomputable def transportTarget {U : AtomCarrier.{u}}
    {first second : CartSemanticInput U}
    (iso : CartSemanticInputIso first second)
    (targetPackage : CoreFiber first.target) : CoreFiber second.target :=
  coreFiberTransportObj iso.targetIso.hom targetPackage

/--
Pull a supplied strong-cartesian lift on the second semantic input back to the
first input by conjugating it with the canonical source and target bridges.
-/
noncomputable def pullStrongCartesianLift {U : AtomCarrier.{u}}
    {first second : CartSemanticInput U}
    (iso : CartSemanticInputIso first second)
    (targetPackage : CoreFiber first.target)
    (lift : StrongCartesianLift second (iso.transportTarget targetPackage)) :
    StrongCartesianLift first targetPackage := by
  let sourceBridge :=
    coreFiberLiftIsoOfIso iso.sourceIso.symm lift.domainObject
  let targetBridge := coreFiberLiftIsoOfIso iso.targetIso targetPackage
  letI sourceInverseLift : (packageProjection U).IsHomLift
      iso.sourceIso.hom sourceBridge.inv := by
    simpa [sourceBridge] using
      coreFiberLiftIsoOfIso_inv_isHomLift
        iso.sourceIso.symm lift.domainObject
  letI targetInverseLift : (packageProjection U).IsHomLift
      iso.targetIso.inv targetBridge.inv := by
    simpa [targetBridge] using
      coreFiberLiftIsoOfIso_inv_isHomLift iso.targetIso targetPackage
  letI sourceInverseStrong : (packageProjection U).IsStronglyCartesian
      iso.sourceIso.hom sourceBridge.inv := by
    exact CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (packageProjection U) iso.sourceIso.hom sourceBridge.inv
  letI targetInverseStrong : (packageProjection U).IsStronglyCartesian
      iso.targetIso.inv targetBridge.inv := by
    exact CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (packageProjection U) iso.targetIso.inv targetBridge.inv
  letI suppliedStrong : (packageProjection U).IsStronglyCartesian
      second.hom lift.hom := lift.isStronglyCartesian
  letI suffixStrong : (packageProjection U).IsStronglyCartesian
      (second.hom ≫ iso.targetIso.inv)
      (lift.hom ≫ targetBridge.inv) :=
    CategoryTheory.Functor.IsStronglyCartesian.comp (packageProjection U)
  letI compositeStrong : (packageProjection U).IsStronglyCartesian
      (iso.sourceIso.hom ≫ (second.hom ≫ iso.targetIso.inv))
      (sourceBridge.inv ≫ (lift.hom ≫ targetBridge.inv)) :=
    CategoryTheory.Functor.IsStronglyCartesian.comp (packageProjection U)
  have base_eq :
      iso.sourceIso.hom ≫ (second.hom ≫ iso.targetIso.inv) =
        first.hom := by
    calc
      iso.sourceIso.hom ≫ (second.hom ≫ iso.targetIso.inv) =
          (iso.sourceIso.hom ≫ second.hom) ≫ iso.targetIso.inv :=
        (Category.assoc _ _ _).symm
      _ = (first.hom ≫ iso.targetIso.hom) ≫ iso.targetIso.inv := by
        rw [iso.hom_comm]
      _ = first.hom := by simp
  refine
    { domain :=
        (coreFiberTransportObj iso.sourceIso.inv lift.domainObject).1
      hom := sourceBridge.inv ≫ lift.hom ≫ targetBridge.inv
      isStronglyCartesian := ?_ }
  simpa only [base_eq] using
    (inferInstanceAs ((packageProjection U).IsStronglyCartesian
      (iso.sourceIso.hom ≫ (second.hom ≫ iso.targetIso.inv))
      (sourceBridge.inv ≫ (lift.hom ≫ targetBridge.inv))))

/-- The pulled lift has the canonically transported source-domain package. -/
@[simp]
theorem pullStrongCartesianLift_domain {U : AtomCarrier.{u}}
    {first second : CartSemanticInput U}
    (iso : CartSemanticInputIso first second)
    (targetPackage : CoreFiber first.target)
    (lift : StrongCartesianLift second (iso.transportTarget targetPackage)) :
    (iso.pullStrongCartesianLift targetPackage lift).domain =
      (coreFiberTransportObj iso.sourceIso.inv lift.domainObject).1 :=
  rfl

/-- The pulled map is the required inverse-bridge conjugate. -/
@[simp]
theorem pullStrongCartesianLift_hom {U : AtomCarrier.{u}}
    {first second : CartSemanticInput U}
    (iso : CartSemanticInputIso first second)
    (targetPackage : CoreFiber first.target)
    (lift : StrongCartesianLift second (iso.transportTarget targetPackage)) :
    (iso.pullStrongCartesianLift targetPackage lift).hom =
      (coreFiberLiftIsoOfIso iso.sourceIso.symm lift.domainObject).inv ≫
        lift.hom ≫
          (coreFiberLiftIsoOfIso iso.targetIso targetPackage).inv :=
  rfl

/-- Conjugating the pulled map forward recovers the supplied lift map. -/
theorem pullStrongCartesianLift_conjugation_triangle {U : AtomCarrier.{u}}
    {first second : CartSemanticInput U}
    (iso : CartSemanticInputIso first second)
    (targetPackage : CoreFiber first.target)
    (lift : StrongCartesianLift second (iso.transportTarget targetPackage)) :
    (coreFiberLiftIsoOfIso iso.sourceIso.symm lift.domainObject).hom ≫
          (iso.pullStrongCartesianLift targetPackage lift).hom ≫
        (coreFiberLiftIsoOfIso iso.targetIso targetPackage).hom =
      lift.hom := by
  let sourceBridge :=
    coreFiberLiftIsoOfIso iso.sourceIso.symm lift.domainObject
  let targetBridge := coreFiberLiftIsoOfIso iso.targetIso targetPackage
  change sourceBridge.hom ≫
      ((sourceBridge.inv ≫ (lift.hom ≫ targetBridge.inv)) ≫
        targetBridge.hom) = lift.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

end CartSemanticInputIso

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
