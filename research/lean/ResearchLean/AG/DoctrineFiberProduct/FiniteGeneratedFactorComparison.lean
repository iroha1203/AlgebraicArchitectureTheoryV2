import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedLiftNaturality

/-!
# Generated high factors and low inverse-upper factors

This module isolates the generated-factor data required by a future reflection
construction for the selected finite package.  An ambient low competitor
determines a second finite generated input.  Its generated high lift factors
through a supplied high strong-cartesian lift by the Mathlib universal property,
and the resulting factor is normalized to the theorem-generated high domain.

On the low carrier, the corresponding whole-upper factor is constructed
directly from the two inverse-package upper equivalences.  Its factorization
law uses the proved inverse-upper round trip, without invoking a low
strong-cartesian instance.  The comparison theorem records that this low factor
is independent of the supplied high lift; no ambient high-to-low
strong-cartesianness reflection is claimed in this module.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Explicit factors for inverse-generated packages -/

/--
Factor an ambient total hom through the inverse-generated package of its target.
The construction uses the generated backward upper equivalence and the supplied
base factorization equality; it does not invoke a cartesian instance.
-/
noncomputable def inverseCorePackageFactor {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q)
    {package : AATCorePackage U}
    (base : packagePoint package ⟶ X)
    (hom : package ⟶ Q)
    (hbase : hom.base = base ≫ f) :
    package ⟶ inverseCorePackage Q f where
  base := base
  upper := hom.upper.comp (inverseCorePackageBackwardUpper Q f)
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    change (inverseCorePackageBackwardUpper Q f).atomEquiv
        (hom.upper.atomEquiv atom) = base.doctrineHom.atomEquiv atom
    rw [hom.atomEquiv_eq]
    have hbaseAtom := congrArg
      (fun lower => lower.doctrineHom.atomEquiv atom) hbase
    change hom.base.doctrineHom.atomEquiv atom =
      f.doctrineHom.atomEquiv (base.doctrineHom.atomEquiv atom) at hbaseAtom
    rw [hbaseAtom]
    simp [inverseCorePackageBackwardUpper]

/-- The explicit inverse-package factor lies over the requested base arrow. -/
theorem inverseCorePackageFactor_isHomLift {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q)
    {package : AATCorePackage U}
    (base : packagePoint package ⟶ X)
    (hom : package ⟶ Q)
    (hbase : hom.base = base ≫ f) :
    (packageProjection U).IsHomLift base
      (inverseCorePackageFactor Q f base hom hbase) := by
  change (packageProjection U).IsHomLift
    ((packageProjection U).map (inverseCorePackageFactor Q f base hom hbase))
      (inverseCorePackageFactor Q f base hom hbase)
  infer_instance

/-- The explicit inverse-package factor followed by the generated hom is the ambient hom. -/
theorem inverseCorePackageFactor_fac {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q)
    {package : AATCorePackage U}
    (base : packagePoint package ⟶ X)
    (hom : package ⟶ Q)
    (hbase : hom.base = base ≫ f) :
    inverseCorePackageFactor Q f base hom hbase ≫
        inverseCorePackageHom Q f = hom := by
  apply PackageTotalHom.ext
  · exact hbase.symm
  · change
      (hom.upper.comp (inverseCorePackageBackwardUpper Q f)).comp
          (inverseCorePackageForwardUpper Q f) = hom.upper
    rw [PackageTotalHom.upper_comp_assoc,
      inverseCorePackageBackward_comp_forward,
      PackageTotalHom.upper_comp_id]

/--
The explicit inverse-package factor is unique among factors over the same base
arrow.  Uniqueness is proved by cancellation with the generated backward upper
map, not by importing a low cartesian universal property.
-/
theorem inverseCorePackageFactor_unique {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (Q : AATCorePackage U)
    (f : X ⟶ packagePoint Q)
    {package : AATCorePackage U}
    (base : packagePoint package ⟶ X)
    (hom : package ⟶ Q)
    (hbase : hom.base = base ≫ f)
    (candidate : package ⟶ inverseCorePackage Q f)
    [(packageProjection U).IsHomLift base candidate]
    (hfac : candidate ≫ inverseCorePackageHom Q f = hom) :
    candidate = inverseCorePackageFactor Q f base hom hbase := by
  apply PackageTotalHom.ext
  · change candidate.base = base
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (p := packageProjection U) (a := package)
      (b := inverseCorePackage Q f) base candidate).symm
  · have hupper :
        candidate.upper.comp (inverseCorePackageForwardUpper Q f) =
          hom.upper := by
      simpa [inverseCorePackageHom, PackageTotalHom.comp] using
        congrArg PackageTotalHom.upper hfac
    change candidate.upper =
      hom.upper.comp (inverseCorePackageBackwardUpper Q f)
    calc
      candidate.upper = candidate.upper.comp
          (SignedExactCoreReadingHom.refl (inverseCorePackage Q f)) :=
        (PackageTotalHom.upper_comp_id candidate.upper).symm
      _ = candidate.upper.comp
          ((inverseCorePackageForwardUpper Q f).comp
            (inverseCorePackageBackwardUpper Q f)) := by
              rw [inverseCorePackageForward_comp_backward]
      _ = (candidate.upper.comp (inverseCorePackageForwardUpper Q f)).comp
          (inverseCorePackageBackwardUpper Q f) := by
            rw [PackageTotalHom.upper_comp_assoc]
      _ = hom.upper.comp (inverseCorePackageBackwardUpper Q f) := by
            rw [hupper]

/-! ## The outer generated input -/

/--
Extend one selected finite input by an ambient prefix base arrow.  The resulting
input records the exact composite bottom arrow and supplies no package or graph
certificate.
-/
noncomputable def finiteGeneratedOuterInput
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    FiniteGeneratedLiftInput where
  source := packagePoint package
  hom := base ≫ input.lowInput.hom

/-- The outer low bottom arrow is the ambient prefix followed by the selected input. -/
@[simp]
theorem finiteGeneratedOuterInput_hom
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    (finiteGeneratedOuterInput input base).hom =
      base ≫ input.lowInput.hom :=
  rfl

/--
The outer high bottom arrow is the lifted prefix followed by the original high
bottom arrow.  This is the composition law used by the high factor.
-/
theorem finiteGeneratedOuterInput_high_hom
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (FiniteGeneratedLiftInput.highInput.{u}
      (finiteGeneratedOuterInput input base)).hom =
      ExtInstHom.comp (finiteModelLiftExtInstHom.{u} base)
        (finiteModelLiftExtInstHom.{u} input.hom) := by
  change finiteModelLiftExtInstHom.{u} (base.comp input.hom) =
    ExtInstHom.comp (finiteModelLiftExtInstHom.{u} base)
      (finiteModelLiftExtInstHom.{u} input.hom)
  exact finiteModelLiftExtInstHom_comp base input.hom

/--
An ambient low competitor has the composite base encoded by the outer input.
The equality is derived from its `IsHomLift` instance.
-/
theorem finiteGeneratedCompetitor_base
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom] :
    hom.base = (finiteGeneratedOuterInput input base).hom := by
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (packageProjection FiniteModel.carrier)
      (base ≫ input.lowInput.hom) hom).symm

/-! ## High factor through the supplied lift -/

/--
Factor the generated outer high lift through the supplied ambient high
strong-cartesian lift.  The factor is produced by Mathlib's universal property;
it is not accepted from the caller.
-/
noncomputable def finiteGeneratedHighFactor
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    (FiniteGeneratedLiftInput.highGeneratedLift.{u}
      (finiteGeneratedOuterInput input base)).domain ⟶
      lift.domain := by
  let outer := finiteGeneratedOuterInput input base
  letI := lift.isStronglyCartesian
  letI := outer.highGeneratedLift.isStronglyCartesian
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (p := packageProjection finiteModelLiftCarrier.{u})
      (R := input.highInput.source) (S := input.highInput.target)
      (a := lift.domain) (b := input.highTarget.1)
      (R' := outer.highInput.source)
      (a' := outer.highGeneratedLift.domain)
      input.highInput.hom lift.hom
      (g := finiteModelLiftExtInstHom.{u} base)
      (f' := outer.highInput.hom)
      (finiteGeneratedOuterInput_high_hom input base)
      outer.highGeneratedLift.hom

/-- The generated high factor lies over the canonical lift of the low prefix. -/
theorem finiteGeneratedHighFactor_isHomLift
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
      (finiteModelLiftExtInstHom.{u} base)
      (finiteGeneratedHighFactor input lift base) := by
  let outer := finiteGeneratedOuterInput input base
  letI := lift.isStronglyCartesian
  letI := outer.highGeneratedLift.isStronglyCartesian
  unfold finiteGeneratedHighFactor
  infer_instance

/-- The generated high factor followed by the supplied lift is the outer generated hom. -/
theorem finiteGeneratedHighFactor_fac
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    finiteGeneratedHighFactor input lift base ≫ lift.hom =
      (FiniteGeneratedLiftInput.highGeneratedLift.{u}
        (finiteGeneratedOuterInput input base)).hom := by
  let outer := finiteGeneratedOuterInput input base
  letI := lift.isStronglyCartesian
  letI := outer.highGeneratedLift.isStronglyCartesian
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (p := packageProjection _)
      (R := input.highInput.source) (S := input.highInput.target)
      (a := lift.domain) (b := input.highTarget.1)
      (R' := outer.highInput.source)
      (a' := outer.highGeneratedLift.domain)
      input.highInput.hom lift.hom
      (g := finiteModelLiftExtInstHom.{u} base)
      (f' := outer.highInput.hom)
      (finiteGeneratedOuterInput_high_hom input base)
      outer.highGeneratedLift.hom

/--
Normalize the generated high factor to the theorem-generated high domain by
following it with the canonical comparison from the supplied lift.
-/
noncomputable def finiteGeneratedNormalizedHighFactor
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    (FiniteGeneratedLiftInput.highGeneratedLift.{u}
      (finiteGeneratedOuterInput input base)).domain ⟶
      (FiniteGeneratedLiftInput.highGeneratedLift.{u} input).domain :=
  finiteGeneratedHighFactor input lift base ≫
    (StrongCartesianLift.canonicalDomainIso lift).hom

/--
The normalized high factor followed by the generated high hom is the outer
generated high hom.  The proof uses both the supplied lift factor and its
canonical inverse triangle.
-/
theorem finiteGeneratedNormalizedHighFactor_fac
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    finiteGeneratedNormalizedHighFactor input lift base ≫
        (FiniteGeneratedLiftInput.highGeneratedLift.{u} input).hom =
      (FiniteGeneratedLiftInput.highGeneratedLift.{u}
        (finiteGeneratedOuterInput input base)).hom := by
  change (finiteGeneratedHighFactor input lift base ≫
      (StrongCartesianLift.canonicalDomainIso lift).hom) ≫
        input.highGeneratedLift.hom = _
  rw [Category.assoc]
  change finiteGeneratedHighFactor input lift base ≫
      ((StrongCartesianLift.canonicalDomainIso lift).hom ≫
        (strongCartesianLiftOfTarget input.highInput input.highTarget).hom) = _
  rw [StrongCartesianLift.canonicalDomainIso_hom_fac]
  exact finiteGeneratedHighFactor_fac input lift base

/-! ## The named generated high factor -/

/--
The base of the outer named high hom is the lifted prefix followed by the
inner named high base.  The equation is generated from pointed-morphism
composition; no comparison equality is supplied by a caller.
-/
theorem finiteGeneratedCanonicalHighFactor_base_eq
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (FiniteGeneratedLiftInput.highPackageHomFromLowData.{u}
      (finiteGeneratedOuterInput input base)).base =
      ExtInstHom.comp (finiteModelLiftExtInstHom.{u} base)
        input.highAlignedBaseFromLowData := by
  let outer := finiteGeneratedOuterInput input base
  calc
    outer.highPackageHomFromLowData.base =
        finiteModelLiftExtInstHom.{u} outer.hom :=
      outer.highPackageHomFromLowData_base
    _ = finiteModelLiftExtInstHom.{u} (base.comp input.hom) := rfl
    _ = ExtInstHom.comp (finiteModelLiftExtInstHom.{u} base)
        (finiteModelLiftExtInstHom.{u} input.hom) :=
      finiteModelLiftExtInstHom_comp base input.hom
    _ = ExtInstHom.comp (finiteModelLiftExtInstHom.{u} base)
        input.highAlignedBaseFromLowData := by
      rw [input.highAlignedBaseFromLowData_eq]

/--
The canonical high prefix factor is generated directly by the two high
inverse-package upper equivalences.
-/
noncomputable def finiteGeneratedCanonicalHighFactor
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (FiniteGeneratedLiftInput.highGeneratedLift.{u}
      (finiteGeneratedOuterInput input base)).domain ⟶
      (FiniteGeneratedLiftInput.highGeneratedLift.{u} input).domain := by
  let outer := finiteGeneratedOuterInput input base
  change outer.highPackageFromLowData ⟶ input.highPackageFromLowData
  exact inverseCorePackageFactor finiteModelLiftCorePackage.{u}
    input.highAlignedBaseFromLowData
    (finiteModelLiftExtInstHom.{u} base)
    outer.highPackageHomFromLowData
    (finiteGeneratedCanonicalHighFactor_base_eq input base)

/-- The named high prefix factor lies over the lifted low prefix. -/
theorem finiteGeneratedCanonicalHighFactor_isHomLift
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
    (finiteModelLiftExtInstHom.{u} base)
    (finiteGeneratedCanonicalHighFactor.{u} input base) := by
  let outer := finiteGeneratedOuterInput input base
  change (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
    (finiteModelLiftExtInstHom.{u} base)
    (inverseCorePackageFactor finiteModelLiftCorePackage.{u}
      (package := outer.highPackageFromLowData)
      input.highAlignedBaseFromLowData
      (finiteModelLiftExtInstHom.{u} base)
      outer.highPackageHomFromLowData
      (finiteGeneratedCanonicalHighFactor_base_eq input base))
  exact inverseCorePackageFactor_isHomLift _ _ _ _ _

/-- The named high prefix factor satisfies the generated high triangle. -/
theorem finiteGeneratedCanonicalHighFactor_fac
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteGeneratedCanonicalHighFactor.{u} input base ≫
        (FiniteGeneratedLiftInput.highGeneratedLift.{u} input).hom =
      (FiniteGeneratedLiftInput.highGeneratedLift.{u}
        (finiteGeneratedOuterInput input base)).hom := by
  let outer := finiteGeneratedOuterInput input base
  change inverseCorePackageFactor finiteModelLiftCorePackage.{u}
      (package := outer.highPackageFromLowData)
      input.highAlignedBaseFromLowData
      (finiteModelLiftExtInstHom.{u} base)
      outer.highPackageHomFromLowData
      (finiteGeneratedCanonicalHighFactor_base_eq input base) ≫
        input.highPackageHomFromLowData =
      outer.highPackageHomFromLowData
  exact inverseCorePackageFactor_fac _ _ _ _ _

/-- The normalized supplied factor lies over the lifted low prefix. -/
theorem finiteGeneratedNormalizedHighFactor_isHomLift
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
      (finiteModelLiftExtInstHom.{u} base)
      (finiteGeneratedNormalizedHighFactor input lift base) := by
  letI : (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
      (finiteModelLiftExtInstHom.{u} base)
      (finiteGeneratedHighFactor input lift base) :=
    finiteGeneratedHighFactor_isHomLift input lift base
  letI : (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
      (𝟙 (FiniteGeneratedLiftInput.highInput.{u} input).source)
      (StrongCartesianLift.canonicalDomainIso lift).hom := by
    change (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
      (𝟙 (FiniteGeneratedLiftInput.highInput.{u} input).source)
      (StrongCartesianLift.domainIso
        (FiniteGeneratedLiftInput.highGeneratedLift.{u} input) lift).hom
    exact StrongCartesianLift.domainIso_hom_isHomLift _ _
  simpa [finiteGeneratedNormalizedHighFactor] using
    CategoryTheory.IsHomLift.comp
      (packageProjection finiteModelLiftCarrier.{u})
      (finiteModelLiftExtInstHom.{u} base)
      (𝟙 (FiniteGeneratedLiftInput.highInput.{u} input).source)
      (finiteGeneratedHighFactor input lift base)
      (StrongCartesianLift.canonicalDomainIso lift).hom

/--
The factor obtained from the supplied high universal property, after canonical
normalization, is exactly the named generated high prefix factor.
-/
theorem finiteGeneratedNormalizedHighFactor_eq_canonical
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteGeneratedNormalizedHighFactor input lift base =
      finiteGeneratedCanonicalHighFactor.{u} input base := by
  letI : (packageProjection finiteModelLiftCarrier.{u}).IsHomLift
      (finiteModelLiftExtInstHom.{u} base)
      (finiteGeneratedNormalizedHighFactor input lift base) :=
    finiteGeneratedNormalizedHighFactor_isHomLift input lift base
  let outer := finiteGeneratedOuterInput input base
  change finiteGeneratedNormalizedHighFactor input lift base =
    inverseCorePackageFactor finiteModelLiftCorePackage.{u}
      (package := outer.highPackageFromLowData)
      input.highAlignedBaseFromLowData
      (finiteModelLiftExtInstHom.{u} base)
      outer.highPackageHomFromLowData
      (finiteGeneratedCanonicalHighFactor_base_eq input base)
  apply inverseCorePackageFactor_unique
  exact finiteGeneratedNormalizedHighFactor_fac input lift base

/-! ## Low whole-upper factor without low cartesianness -/

/--
The low whole-upper factor between the outer and inner inverse-generated
packages.  It first maps the outer inverse package forward to the selected
target and then applies the generated backward upper map for the inner input.
-/
noncomputable def finiteGeneratedLowFactorUpper
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    SignedExactCoreReadingHom
      (inverseCorePackage FiniteModel.corePackage
        (finiteGeneratedOuterInput input base).hom)
      (inverseCorePackage FiniteModel.corePackage input.hom) :=
  (inverseCorePackageForwardUpper FiniteModel.corePackage
      (finiteGeneratedOuterInput input base).hom).comp
    (inverseCorePackageBackwardUpper FiniteModel.corePackage input.hom)

/--
The low whole-upper factor followed by the inner generated upper hom is the
outer generated upper hom.
-/
theorem finiteGeneratedLowFactorUpper_fac
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source) :
    (finiteGeneratedLowFactorUpper input base).comp
        (inverseCorePackageForwardUpper FiniteModel.corePackage input.hom) =
      inverseCorePackageForwardUpper FiniteModel.corePackage
        (finiteGeneratedOuterInput input base).hom := by
  rw [finiteGeneratedLowFactorUpper,
    PackageTotalHom.upper_comp_assoc,
    inverseCorePackageBackward_comp_forward,
    PackageTotalHom.upper_comp_id]

/-- The low whole-upper factor has the ambient prefix Atom map. -/
@[simp]
theorem finiteGeneratedLowFactorUpper_atom_graph
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source)
    (atom : FiniteModel.carrier.Atom) :
    (finiteGeneratedLowFactorUpper input base).atomEquiv atom =
      base.doctrineHom.atomEquiv atom := by
  change input.hom.doctrineHom.atomEquiv.symm
      (input.hom.doctrineHom.atomEquiv
        (base.doctrineHom.atomEquiv atom)) = _
  exact input.hom.doctrineHom.atomEquiv.symm_apply_apply _

/--
The low generated prefix factor as a total package hom.  It is the explicit
inverse-package factor, not a factor selected from low cartesianness.
-/
noncomputable def finiteGeneratedLowFactor
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain ⟶
      input.lowGeneratedLift.domain := by
  let outer := finiteGeneratedOuterInput input base
  change inverseCorePackage FiniteModel.corePackage outer.hom ⟶
    inverseCorePackage FiniteModel.corePackage input.hom
  exact inverseCorePackageFactor FiniteModel.corePackage input.hom
    (package := inverseCorePackage FiniteModel.corePackage outer.hom)
    base (inverseCorePackageHom FiniteModel.corePackage outer.hom) rfl

/-- The low generated prefix factor lies over the ambient prefix. -/
theorem finiteGeneratedLowFactor_isHomLift
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (packageProjection FiniteModel.carrier).IsHomLift base
      (finiteGeneratedLowFactor input base) := by
  let outer := finiteGeneratedOuterInput input base
  change (packageProjection FiniteModel.carrier).IsHomLift base
    (inverseCorePackageFactor FiniteModel.corePackage input.hom
      (package := inverseCorePackage FiniteModel.corePackage outer.hom)
      base (inverseCorePackageHom FiniteModel.corePackage outer.hom) rfl)
  exact inverseCorePackageFactor_isHomLift _ _ _ _ _

/-- The low generated prefix factor satisfies the inverse-package triangle. -/
theorem finiteGeneratedLowFactor_fac
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteGeneratedLowFactor input base ≫ input.lowGeneratedLift.hom =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom := by
  let outer := finiteGeneratedOuterInput input base
  change inverseCorePackageFactor FiniteModel.corePackage input.hom
      (package := inverseCorePackage FiniteModel.corePackage outer.hom)
      base (inverseCorePackageHom FiniteModel.corePackage outer.hom) rfl ≫
        inverseCorePackageHom FiniteModel.corePackage input.hom =
      inverseCorePackageHom FiniteModel.corePackage outer.hom
  exact inverseCorePackageFactor_fac _ _ _ _ _

/-- The upper component of the low generated prefix factor is the named one. -/
theorem finiteGeneratedLowFactor_upper
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedLowFactor input base).upper =
      finiteGeneratedLowFactorUpper input base := by
  rfl

/-! ## Caller-free generated-factor comparison -/

/--
A generated factor comparison indexed by the actual normalized supplied-high
factor.  The low factor and all displayed laws are theorem outputs.  This
checkpoint records the whole-hom high equality and the first cross-carrier
upper graph.  It does not claim that the low factor is constructed by
reflecting the high factor, or that ambient cartesianness has been reflected.
-/
structure GeneratedPrefixFactorComparison
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) : Type (u + 1) where
  /-- Generated low prefix factor paired with the supplied-high factor. -/
  lowFactor :
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain ⟶
      input.lowGeneratedLift.domain
  /-- The paired low factor lies over the original prefix. -/
  lowFactor_isHomLift :
    (packageProjection FiniteModel.carrier).IsHomLift base lowFactor
  /-- The paired low factor satisfies the generated low triangle. -/
  lowFactor_fac :
    lowFactor ≫ input.lowGeneratedLift.hom =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.hom
  /-- Its upper component is the named inverse-upper composite. -/
  lowFactor_upper :
    lowFactor.upper = finiteGeneratedLowFactorUpper input base
  /-- The actual supplied-high factor normalizes to the named high factor. -/
  normalized_high :
    finiteGeneratedNormalizedHighFactor input lift base =
      finiteGeneratedCanonicalHighFactor.{u} input base
  /-- The actual normalized high Atom map is the lifted low factor Atom map. -/
  atom_graph : ∀ atom : FiniteModel.carrier.Atom,
    (finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom (lowFactor.upper.atomEquiv atom)

/--
Generate the prefix-factor comparison packet from the supplied high lift.
No factor, image membership proof, or component graph is caller supplied.  The
low factor is the independent inverse-upper construction; the theorem below
makes its independence from the supplied high lift explicit.
-/
noncomputable def generatedPrefixFactorComparison
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    GeneratedPrefixFactorComparison.{u} input lift base where
  lowFactor := finiteGeneratedLowFactor input base
  lowFactor_isHomLift := finiteGeneratedLowFactor_isHomLift input base
  lowFactor_fac := finiteGeneratedLowFactor_fac input base
  lowFactor_upper := finiteGeneratedLowFactor_upper input base
  normalized_high :=
    finiteGeneratedNormalizedHighFactor_eq_canonical input lift base
  atom_graph := by
    intro atom
    rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
    rw [(finiteGeneratedCanonicalHighFactor.{u} input base).atomEquiv_eq]
    rw [(finiteGeneratedLowFactor input base).atomEquiv_eq]
    exact finiteModelLiftExtInstHom_atomEquiv base atom

/--
The low projection of the comparison packet is independent of the supplied
high lift.  This theorem records the exact proof-use limitation: the packet is
a comparison checkpoint, not a strong-cartesianness reflection producer.
-/
theorem generatedPrefixFactorComparison_lowFactor_independent
    (input : FiniteGeneratedLiftInput)
    (first second : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (generatedPrefixFactorComparison.{u} input first base).lowFactor =
      (generatedPrefixFactorComparison.{u} input second base).lowFactor :=
  rfl

/-! ## Ambient competitor factorization through the generated pair -/

/--
Factor an arbitrary ambient low competitor vertically into the outer generated
inverse package.  The construction retains the competitor's complete upper
hom and uses no cartesian instance.
-/
noncomputable def finiteGeneratedAmbientToOuter
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom] :
    package ⟶ (finiteGeneratedOuterInput input base).lowGeneratedLift.domain := by
  let outer := finiteGeneratedOuterInput input base
  change package ⟶ inverseCorePackage FiniteModel.corePackage outer.hom
  apply inverseCorePackageFactor FiniteModel.corePackage outer.hom
    (𝟙 (packagePoint package)) hom
  simpa [outer] using finiteGeneratedCompetitor_base input base hom

/-- The vertical ambient-to-outer map lies over the source identity. -/
theorem finiteGeneratedAmbientToOuter_isHomLift
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom] :
    (packageProjection FiniteModel.carrier).IsHomLift
      (𝟙 (packagePoint package))
      (finiteGeneratedAmbientToOuter input base hom) := by
  let outer := finiteGeneratedOuterInput input base
  let hbase : hom.base = (𝟙 (packagePoint package)) ≫ outer.hom := by
    simpa [outer] using finiteGeneratedCompetitor_base input base hom
  change (packageProjection FiniteModel.carrier).IsHomLift
    (𝟙 (packagePoint package))
    (inverseCorePackageFactor FiniteModel.corePackage outer.hom
      (𝟙 (packagePoint package)) hom hbase)
  exact inverseCorePackageFactor_isHomLift _ _ _ _ _

/-- The vertical map followed by the outer generated hom recovers the competitor. -/
theorem finiteGeneratedAmbientToOuter_fac
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom] :
    finiteGeneratedAmbientToOuter input base hom ≫
        (finiteGeneratedOuterInput input base).lowGeneratedLift.hom = hom := by
  let outer := finiteGeneratedOuterInput input base
  let hbase : hom.base = (𝟙 (packagePoint package)) ≫ outer.hom := by
    simpa [outer] using finiteGeneratedCompetitor_base input base hom
  change inverseCorePackageFactor FiniteModel.corePackage outer.hom
      (𝟙 (packagePoint package)) hom hbase ≫
        inverseCorePackageHom FiniteModel.corePackage outer.hom = hom
  exact inverseCorePackageFactor_fac _ _ _ _ _

/-! ## Component comparison for the canonical low hom -/

/--
Two exact upper homs with the same Atom equivalence induce operation
configuration maps with the same Atom map.  Naturality and surjectivity of the
common Atom equivalence determine the target operation map pointwise.
-/
theorem operationConfigurationMap_atomMap_eq_of_atomEquiv_eq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (first second : SignedExactCoreReadingHom P Q)
    (hatom : first.atomEquiv = second.atomEquiv)
    {source target : ArchitectureObject U}
    (operation : P.reading.operationReading.Op source target) :
    (Q.reading.operationReading.configurationMap
      (first.operationMap operation)).atomMap =
      (Q.reading.operationReading.configurationMap
        (second.operationMap operation)).atomMap := by
  funext atom
  let preimage := first.atomEquiv.symm atom
  have hfirst := congrArg
    (fun hom => hom.atomMap preimage)
    (first.operation_naturality operation)
  have hsecond := congrArg
    (fun hom => hom.atomMap preimage)
    (second.operation_naturality operation)
  have hfirst' :
      (Q.reading.operationReading.configurationMap
        (first.operationMap operation)).atomMap
          (first.atomEquiv preimage) =
        first.atomEquiv
          ((P.reading.operationReading.configurationMap operation).atomMap
            preimage) := by
    simpa [ConfigurationHom.comp, first.configurationMap_atomMap] using hfirst
  have hsecond' :
      (Q.reading.operationReading.configurationMap
        (second.operationMap operation)).atomMap
          (second.atomEquiv preimage) =
        second.atomEquiv
          ((P.reading.operationReading.configurationMap operation).atomMap
            preimage) := by
    simpa [ConfigurationHom.comp, second.configurationMap_atomMap] using hsecond
  calc
    (Q.reading.operationReading.configurationMap
      (first.operationMap operation)).atomMap atom =
        (Q.reading.operationReading.configurationMap
          (first.operationMap operation)).atomMap
            (first.atomEquiv preimage) := by
      simp [preimage]
    _ = first.atomEquiv
        ((P.reading.operationReading.configurationMap operation).atomMap
          preimage) := hfirst'
    _ = second.atomEquiv
        ((P.reading.operationReading.configurationMap operation).atomMap
          preimage) := by rw [hatom]
    _ = (Q.reading.operationReading.configurationMap
          (second.operationMap operation)).atomMap
            (second.atomEquiv preimage) := hsecond'.symm
    _ = (Q.reading.operationReading.configurationMap
          (second.operationMap operation)).atomMap atom := by
      simp [preimage, ← hatom]

/--
Compare the canonical low generated hom with the normalized supplied-high hom
through the complete Cycle 16 component relation.  This theorem fills the
relation for an already generated low hom; it does not construct that hom by
reflection and does not discharge the ambient universal-property obligation.
-/
theorem canonicalLowGeneratedComponentComparison
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input)) :
    ReflectedGeneratedComponentGraph.{u} input lift
      input.lowGeneratedLift.hom where
  normalized := input.normalizedHighHom_eq_highPackageHomFromLowData lift
  generated_naturality := generatedPackageHomULiftNaturality input
  reflected_base := input.lowGeneratedLift_base
  normalized_base := by
    rw [input.normalizedHighHom_base lift, input.lowGeneratedLift_base]
  low_domain_point := input.lowGeneratedLift_domain_point
  high_domain_point := input.highGeneratedLift_domain_point
  target_point := FiniteGeneratedLiftInput.lift_packagePoint
  normalized_projection := input.normalizedHighHom_projection lift
  upper_atom := by
    intro atom
    rw [input.normalizedHighHom_eq_highPackageHomFromLowData lift,
      input.highPackageHomFromLowData_upper_atom_graph,
      input.lowGeneratedLift_upper_atomEquiv]
  upper_object := by
    intro object
    rw [input.normalizedHighHom_eq_highPackageHomFromLowData lift]
    exact input.highPackageHomFromLowData_upper_objectMap_lift object
  upper_configurationMap := by
    intro object
    apply ConfigurationHom.ext
    rw [castConfigurationHom_atomMap,
      finiteModelLiftConfigurationHom_atomMap,
      (input.normalizedHighHom lift).upper.configurationMap_atomMap,
      input.lowGeneratedLift.hom.upper.configurationMap_atomMap,
      input.normalizedHighHom_eq_highPackageHomFromLowData lift,
      input.highPackageHomFromLowData_upper_atomEquiv,
      input.lowGeneratedLift_upper_atomEquiv]
    rfl
  upper_equationMap := by
    intro index
    rw [input.normalizedHighHom_eq_highPackageHomFromLowData lift]
    exact input.generatedUpper_equationMap_graph index
  domain_detectorCode := input.inverseGeneratedDomain_detectorCode_graph
  domain_equationHolds := input.inverseGeneratedDomain_equationHolds_iff
  upper_operation := by
    intro source target operation
    apply ConfigurationHom.ext
    have hatom :
        (input.normalizedHighHom lift).upper.atomEquiv =
          input.highPackageHomFromLowData.upper.atomEquiv := by
      exact congrArg (fun hom => hom.upper.atomEquiv)
        (input.normalizedHighHom_eq_highPackageHomFromLowData lift)
    calc
      (finiteModelLiftCorePackage.{u}.reading.operationReading.configurationMap
        ((input.normalizedHighHom lift).upper.operationMap
          (input.generatedDomainOperationLift operation))).atomMap =
          (finiteModelLiftCorePackage.{u}.reading.operationReading.configurationMap
            (input.highPackageHomFromLowData.upper.operationMap
              (input.generatedDomainOperationLift operation))).atomMap :=
        operationConfigurationMap_atomMap_eq_of_atomEquiv_eq
          (input.normalizedHighHom lift).upper
          input.highPackageHomFromLowData.upper hatom
          (input.generatedDomainOperationLift operation)
      _ = (castConfigurationHom
          (input.highPackageHomFromLowData_upper_configurationMap_target source).symm
          (input.highPackageHomFromLowData_upper_configurationMap_target target).symm
          (finiteModelLiftConfigurationHom.{u}
            (FiniteModel.corePackage.reading.operationReading.configurationMap
              (input.lowGeneratedLift.hom.upper.operationMap operation)))).atomMap := by
        exact congrArg ConfigurationHom.atomMap
          (input.generatedUpper_operation_configurationMap_graph operation)
      _ = _ := by
        rw [castConfigurationHom_atomMap, castConfigurationHom_atomMap]
  upper_invariantMap := by
    intro index
    rw [input.normalizedHighHom_eq_highPackageHomFromLowData lift]
    exact input.generatedUpper_invariantMap_graph index
  domain_invariant :=
    FiniteGeneratedLiftInput.inverseGeneratedDomain_invariant_holds_iff.{u} input
  upper_axisMap := by
    intro axis
    rw [input.normalizedHighHom_eq_highPackageHomFromLowData lift]
    exact input.generatedUpper_axisMap_graph axis
  domain_axis_selected :=
    FiniteGeneratedLiftInput.inverseGeneratedDomain_axis_selected_iff.{u} input
  upper_coordinateEquiv := by
    intro axis coordinate
    rw [input.normalizedHighHom_eq_highPackageHomFromLowData lift]
    exact input.generatedUpper_coordinateEquiv_graph axis coordinate
  domain_coordinate := input.inverseGeneratedDomain_coordinate_graph

/-! ## Concrete firing witness -/

/--
The noninvertible two-source chain fires the supplied-high factor comparison at
every target universe.  Its supplied high lift and every compared hom are
generated internally; the chain's first arrow is proved noninvertible by
`finiteSelectiveTwoGeneratedChain_first_not_isIso`.
-/
noncomputable def finiteSelectiveTwoGeneratedPrefixFactorComparison :
    GeneratedPrefixFactorComparison.{u}
      (package := inverseCorePackage FiniteModel.corePackage
        (finiteSelectiveTwoGeneratedChain.first ≫
          finiteSelectiveTwoGeneratedChain.second))
      finiteSelectiveTwoGeneratedChain.tailGeneratedInput
      (FiniteGeneratedLiftInput.highGeneratedLift.{u}
        finiteSelectiveTwoGeneratedChain.tailGeneratedInput)
      finiteSelectiveTwoGeneratedChain.first :=
  generatedPrefixFactorComparison
    (package := inverseCorePackage FiniteModel.corePackage
      (finiteSelectiveTwoGeneratedChain.first ≫
        finiteSelectiveTwoGeneratedChain.second))
    finiteSelectiveTwoGeneratedChain.tailGeneratedInput
    (FiniteGeneratedLiftInput.highGeneratedLift.{u}
      finiteSelectiveTwoGeneratedChain.tailGeneratedInput)
    finiteSelectiveTwoGeneratedChain.first

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
