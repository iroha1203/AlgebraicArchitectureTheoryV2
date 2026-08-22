import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedPackageTotalHomTriangle

/-!
# Reflected generated ambient universal property

This module closes the exact Cycle 16 reflection surface.  Every ambient factor
is the Cycle 25 factor whose second computational leg is descended from the
supplied high strong-cartesian lift.  Its lift and factorization laws therefore
retain that same dependency.

Uniqueness is proved separately by the intrinsic two-sided inverse of the
generated inverse package: an arbitrary candidate and the generated factor are
both reduced to the same explicit inverse-package normal form.  This does not
reuse the existing low strong-cartesian certificate, and it does not claim to
reflect an arbitrary high factor or high uniqueness proof.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Ambient uniqueness -/

/--
The actual-high-derived ambient factor is the unique factor over the requested
base.  Both the arbitrary candidate and the generated factor are compared with
the same explicit inverse-package factor; the latter comparison consumes the
generated factor's high-derived factorization law.
-/
theorem finiteGeneratedReflectedAmbientFactor_unique
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom]
    (candidate : package ⟶ input.lowGeneratedLift.domain)
    [(packageProjection FiniteModel.carrier).IsHomLift base candidate]
    (hfac : candidate ≫ input.lowGeneratedLift.hom = hom) :
    candidate = finiteGeneratedReflectedAmbientFactor input lift base hom := by
  let hbase : hom.base = base ≫ input.hom := by
    simpa only [finiteGeneratedOuterInput_hom,
      FiniteGeneratedLiftInput.lowInput_hom] using
        (finiteGeneratedCompetitor_base input base hom)
  have hcandidate :
      candidate =
        inverseCorePackageFactor FiniteModel.corePackage input.hom
          base hom hbase := by
    exact inverseCorePackageFactor_unique FiniteModel.corePackage input.hom
      base hom hbase candidate hfac
  letI : (packageProjection FiniteModel.carrier).IsHomLift base
      (finiteGeneratedReflectedAmbientFactor input lift base hom) :=
    finiteGeneratedReflectedAmbientFactor_isHomLift input lift base hom
  have hgenerated :
      finiteGeneratedReflectedAmbientFactor input lift base hom =
        inverseCorePackageFactor FiniteModel.corePackage input.hom
          base hom hbase := by
    exact inverseCorePackageFactor_unique FiniteModel.corePackage input.hom
      base hom hbase
      (finiteGeneratedReflectedAmbientFactor input lift base hom)
      (finiteGeneratedReflectedAmbientFactor_fac input lift base hom)
  exact hcandidate.trans hgenerated.symm

/-! ## Exact reflected theorem-output surface -/

/--
The reflected normalized hom has the fixed generated low source and target.
Its arrow is extensionally the canonical generated low hom; the new content is
the supplied-high-derived ambient universal property below.
-/
noncomputable def reflectNormalizedHighHom
    (input : FiniteGeneratedLiftInput)
    (_lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    input.lowGeneratedLift.domain ⟶ FiniteModel.corePackage :=
  input.lowGeneratedLift.hom

/-- The reflected hom lies over the original finite-model bottom arrow. -/
@[simp]
theorem reflectNormalizedHighHom_base
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    (reflectNormalizedHighHom input lift).base = input.hom := by
  exact input.lowGeneratedLift_base

/--
The complete generated component graph is produced internally for the
reflected hom and the supplied high lift.
-/
theorem reflectNormalizedHighHom_components
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    ReflectedGeneratedComponentGraph.{u} input lift
      (reflectNormalizedHighHom input lift) := by
  exact canonicalLowGeneratedComponentComparison input lift

/--
Generate the exact ambient reflected universal-property packet.  No factor,
factorization, uniqueness proof, or component packet is supplied by the caller.
-/
noncomputable def reflectNormalizedUniversalProperty
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    ReflectedGeneratedUniversalProperty.{u, u, u, u, u, u, u, u, u}
      input lift
      (reflectNormalizedHighHom input lift) where
  components := reflectNormalizedHighHom_components input lift
  factor := fun base hom =>
    finiteGeneratedReflectedAmbientFactor input lift base hom
  factor_isHomLift := fun base hom =>
    finiteGeneratedReflectedAmbientFactor_isHomLift input lift base hom
  factor_fac := fun base hom =>
    finiteGeneratedReflectedAmbientFactor_fac input lift base hom
  factor_unique := by
    intro package base hom homLift candidate candidateLift hfac
    exact finiteGeneratedReflectedAmbientFactor_unique input lift base hom
      candidate hfac

/-- The packet's factor is definitionally the actual-high-derived ambient factor. -/
@[simp]
theorem reflectNormalizedUniversalProperty_factor
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom] :
    (reflectNormalizedUniversalProperty input lift).factor base hom =
      finiteGeneratedReflectedAmbientFactor input lift base hom :=
  rfl

/-- Reflection retracts to the named generated low hom. -/
@[simp]
theorem reflectNormalizedHighHom_retraction
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    reflectNormalizedHighHom input lift = input.lowGeneratedLift.hom :=
  rfl

/-! ## Strong cartesianness and the reflected lift -/

/--
The reflected hom is strongly cartesian.  Its Mathlib universal property is
assembled only from the generated packet above; the existing low
strong-cartesian proof is not used.
-/
theorem reflectNormalizedHighHom_isStronglyCartesian
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    (packageProjection FiniteModel.carrier).IsStronglyCartesian
      input.lowInput.hom (reflectNormalizedHighHom input lift) := by
  letI : (packageProjection FiniteModel.carrier).IsHomLift
      input.lowInput.hom (reflectNormalizedHighHom input lift) := by
    change (packageProjection FiniteModel.carrier).IsHomLift
      ((packageProjection FiniteModel.carrier).map
        (reflectNormalizedHighHom input lift))
      (reflectNormalizedHighHom input lift)
    infer_instance
  apply CategoryTheory.Functor.IsStronglyCartesian.mk
  intro package base hom homLift
  refine ⟨(reflectNormalizedUniversalProperty.{u} input lift).factor base hom,
    ?_, ?_⟩
  · exact ⟨
      (reflectNormalizedUniversalProperty.{u} input lift).factor_isHomLift
        base hom,
      (reflectNormalizedUniversalProperty.{u} input lift).factor_fac base hom⟩
  · intro candidate hcandidate
    letI : (packageProjection FiniteModel.carrier).IsHomLift base candidate :=
      hcandidate.1
    exact (reflectNormalizedUniversalProperty.{u} input lift).factor_unique
      base hom candidate hcandidate.2

/--
Package the reflected hom with the newly proved strong-cartesian certificate.
The domain and hom are generated output data, while the certificate is the
ambient universal property proved in this module.
-/
noncomputable def reflectNormalizedStrongCartesianLift
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    StrongCartesianLift input.lowInput input.lowTarget where
  domain := input.lowGeneratedLift.domain
  hom := reflectNormalizedHighHom input lift
  isStronglyCartesian := reflectNormalizedHighHom_isStronglyCartesian input lift

/-- The reflected strong lift uses the generated low domain. -/
@[simp]
theorem reflectNormalizedStrongCartesianLift_domain
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    (reflectNormalizedStrongCartesianLift input lift).domain =
      input.lowGeneratedLift.domain :=
  rfl

/-- The reflected strong lift uses the reflected normalized hom. -/
@[simp]
theorem reflectNormalizedStrongCartesianLift_hom
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    (reflectNormalizedStrongCartesianLift input lift).hom =
      reflectNormalizedHighHom input lift :=
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
