import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportWholeCompositionDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedPackageTotalHomAssembly
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperCompositionOperationSignatureDescent

/-!
# Generated package-total triangle and ambient factor

This module completes the specialized low triangle reflected from the actual
normalized high factorization.  It first assembles equality of all seven
computational fields of the signed upper, then combines that equality with the
actual-derived lower field of the reflected package-total hom.

An arbitrary ambient competitor is factored through the reflected generated
prefix by composing its existing vertical outer factor with this new total
hom.  Existence, its hom-lift property, and its factorization equality are
proved here; no ambient uniqueness or full cartesianness reflection is
claimed.

No known low prefix factor, canonical-factor equality, low cartesianness proof,
global lift, or caller-supplied comparison is used.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Whole upper and total triangle -/

/--
All computational fields of the reflected generated upper followed by the
inner generated upper agree with the outer generated upper.
-/
theorem finiteGeneratedReflectedUpper_comp
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
        input.lowGeneratedLift.hom.upper =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom.upper := by
  apply SignedExactCoreReadingHom.ext
  · exact finiteGeneratedReflectedUpper_comp_atomEquiv input lift base
  · exact finiteGeneratedReflectedUpper_comp_objectMap input lift base
  · exact finiteGeneratedReflectedUpper_comp_equationTransport input lift base
  · exact finiteGeneratedReflectedUpper_comp_operationMap input lift base
  · exact heq_of_eq
      (finiteGeneratedReflectedUpper_comp_invariantMap input lift base)
  · exact heq_of_eq
      (finiteGeneratedReflectedUpper_comp_axisMap input lift base)
  · exact finiteGeneratedReflectedUpper_comp_coordinateEquiv input lift base

/--
The reflected package-total prefix followed by the inner generated hom is the
outer generated hom.  The upper equality descends all seven fields of the
actual high triangle; the lower equality uses the actual-derived base
reflection.
-/
theorem finiteGeneratedReflectedPackageTotalHom_fac
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteGeneratedReflectedPackageTotalHom input lift base ≫
        input.lowGeneratedLift.hom =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom := by
  let outer := finiteGeneratedOuterInput input base
  apply PackageTotalHom.ext
  · change
      (finiteGeneratedReflectedPackageTotalHom input lift base).base.comp
          input.lowGeneratedLift.hom.base =
        outer.lowGeneratedLift.hom.base
    rw [finiteGeneratedReflectedPackageTotalHom_base_eq,
      input.lowGeneratedLift_base, outer.lowGeneratedLift_base]
    rfl
  · change
      (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).comp
          input.lowGeneratedLift.hom.upper =
        outer.lowGeneratedLift.hom.upper
    exact finiteGeneratedReflectedUpper_comp input lift base

/-! ## Arbitrary ambient factor -/

/--
Factor an arbitrary ambient low competitor through the reflected generated
prefix.  The first leg is its vertical factor to the outer inverse package;
the second leg is the actual-high-derived reflected package-total hom.
-/
noncomputable def finiteGeneratedReflectedAmbientFactor
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom] :
    package ⟶ input.lowGeneratedLift.domain :=
  finiteGeneratedAmbientToOuter input base hom ≫
    finiteGeneratedReflectedPackageTotalHom input lift base

/-- The reflected ambient factor lies over the supplied prefix base. -/
theorem finiteGeneratedReflectedAmbientFactor_isHomLift
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom] :
    (packageProjection FiniteModel.carrier).IsHomLift base
      (finiteGeneratedReflectedAmbientFactor input lift base hom) := by
  letI : (packageProjection FiniteModel.carrier).IsHomLift
      (𝟙 (packagePoint package))
      (finiteGeneratedAmbientToOuter input base hom) :=
    finiteGeneratedAmbientToOuter_isHomLift input base hom
  letI : (packageProjection FiniteModel.carrier).IsHomLift base
      (finiteGeneratedReflectedPackageTotalHom input lift base) :=
    finiteGeneratedReflectedPackageTotalHom_isHomLift input lift base
  change (packageProjection FiniteModel.carrier).IsHomLift base
    (finiteGeneratedAmbientToOuter input base hom ≫
      finiteGeneratedReflectedPackageTotalHom input lift base)
  simpa using
    (inferInstance :
      (packageProjection FiniteModel.carrier).IsHomLift
        ((𝟙 (packagePoint package)) ≫ base)
        (finiteGeneratedAmbientToOuter input base hom ≫
          finiteGeneratedReflectedPackageTotalHom input lift base))

/-- The reflected ambient factor followed by the generated hom is the competitor. -/
theorem finiteGeneratedReflectedAmbientFactor_fac
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom] :
    finiteGeneratedReflectedAmbientFactor input lift base hom ≫
        input.lowGeneratedLift.hom =
      hom := by
  change
    (finiteGeneratedAmbientToOuter input base hom ≫
        finiteGeneratedReflectedPackageTotalHom input lift base) ≫
      input.lowGeneratedLift.hom = hom
  rw [Category.assoc, finiteGeneratedReflectedPackageTotalHom_fac,
    finiteGeneratedAmbientToOuter_fac]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
