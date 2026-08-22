import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMateCleavageIndependence

/-!
# Package-specific Beck--Chevalley exactness

The mates correspondence does not preserve isomorphisms in general.  This
module proves the missing support for `packageProjection` itself.  Canonical
upper transport has a generated two-sided inverse, and the explicit
arbitrary-target cartesian lift has the same property.  Cartesian and
cocartesian universal properties therefore make every generated
transport/reindexing unit and counit invertible.  The canonical
Beck--Chevalley mate is then componentwise a composite of the generated unit,
the generated square isomorphism, and the generated counit.

No pullback, exactness, adjoint-equivalence, unit, counit, mate, or inverse
certificate is accepted from a caller.  The public exactness theorem remains
on the validated `BCPresentation` surface, whose pointed pullback is generated
internally by `bcPresentation_isPullback_from_producer`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u u₁ u₂ v₁ v₂

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## Package-specific cocartesianness from upper exactness -/

/--
A package-total hom with a generated two-sided inverse on its complete upper
map is strongly cocartesian.  The lower base arrow need not be invertible.
-/
theorem packageTotalHom_isStronglyCocartesian_of_upper_inverse
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (hom : PackageTotalHom P Q)
    (upperInverse : SignedExactCoreReadingHom Q P)
    (hom_inverse : hom.upper.comp upperInverse =
      SignedExactCoreReadingHom.refl P)
    (inverse_hom : upperInverse.comp hom.upper =
      SignedExactCoreReadingHom.refl Q) :
    (packageProjection U).IsStronglyCocartesian hom.base hom := by
  letI : (packageProjection U).IsHomLift hom.base hom := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map hom) hom
    infer_instance
  apply CategoryTheory.Functor.IsStronglyCocartesian.mk
  intro R base targetHom targetLift
  have targetBase : targetHom.base = hom.base.comp base := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (packageProjection U) (hom.base.comp base) targetHom).symm
  let factor : PackageTotalHom Q R := {
    base := base
    upper := upperInverse.comp targetHom.upper
    atomEquiv_eq := by
      apply Equiv.ext
      intro atom
      have targetBaseAtom := congrArg
        (fun lower => lower.doctrineHom.atomEquiv
          (upperInverse.atomEquiv atom)) targetBase
      change targetHom.base.doctrineHom.atomEquiv
          (upperInverse.atomEquiv atom) =
        base.doctrineHom.atomEquiv
          (hom.base.doctrineHom.atomEquiv
            (upperInverse.atomEquiv atom)) at targetBaseAtom
      change targetHom.upper.atomEquiv (upperInverse.atomEquiv atom) =
        base.doctrineHom.atomEquiv atom
      rw [targetHom.atomEquiv_eq, targetBaseAtom, ← hom.atomEquiv_eq]
      have cancel := congrArg
        (fun upper => upper.atomEquiv atom) inverse_hom
      simpa [SignedExactCoreReadingHom.comp,
        SignedExactCoreReadingHom.refl] using
        congrArg base.doctrineHom.atomEquiv cancel
  }
  have factor_fac : hom.comp factor = targetHom := by
    apply PackageTotalHom.ext
    · exact targetBase.symm
    · change hom.upper.comp
          (upperInverse.comp targetHom.upper) = targetHom.upper
      rw [← PackageTotalHom.upper_comp_assoc, hom_inverse,
        PackageTotalHom.upper_id_comp]
  refine ⟨factor, ?_, ?_⟩
  · constructor
    · change (packageProjection U).IsHomLift base factor
      change (packageProjection U).IsHomLift
        ((packageProjection U).map factor) factor
      infer_instance
    · exact factor_fac
  · intro other other_spec
    apply PackageTotalHom.ext
    · letI : (packageProjection U).IsHomLift base other := other_spec.1
      exact (CategoryTheory.IsHomLift.eq_of_isHomLift
        (packageProjection U) base other).symm
    · have other_upper : hom.upper.comp other.upper = targetHom.upper := by
        simpa [PackageTotalHom.comp] using
          congrArg PackageTotalHom.upper other_spec.2
      change other.upper = upperInverse.comp targetHom.upper
      calc
        other.upper =
            (SignedExactCoreReadingHom.refl Q).comp other.upper :=
          (PackageTotalHom.upper_id_comp other.upper).symm
        _ = (upperInverse.comp hom.upper).comp other.upper := by
          rw [inverse_hom]
        _ = upperInverse.comp (hom.upper.comp other.upper) := by
          rw [PackageTotalHom.upper_comp_assoc]
        _ = upperInverse.comp targetHom.upper := by rw [other_upper]

/-- The upper-inverse cocartesian criterion after retagging endpoint equalities. -/
theorem packageTotalHom_isStronglyCocartesian_of_upper_inverse_lift
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} {P Q : AATCorePackage U}
    (base : X ⟶ Y) (hom : PackageTotalHom P Q)
    [homLift : (packageProjection U).IsHomLift base hom]
    (upperInverse : SignedExactCoreReadingHom Q P)
    (hom_inverse : hom.upper.comp upperInverse =
      SignedExactCoreReadingHom.refl P)
    (inverse_hom : upperInverse.comp hom.upper =
      SignedExactCoreReadingHom.refl Q) :
    (packageProjection U).IsStronglyCocartesian base hom := by
  subst_hom_lift (packageProjection U) base hom
  exact packageTotalHom_isStronglyCocartesian_of_upper_inverse hom
    upperInverse hom_inverse inverse_hom

/-- The explicit arbitrary-target cartesian lift is also strongly cocartesian. -/
theorem strongCartesianLiftOfTarget_isStronglyCocartesian
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (targetPackage : CoreFiber input.target) :
    (packageProjection U).IsStronglyCocartesian input.hom
      (strongCartesianLiftOfTarget input targetPackage).hom := by
  rcases targetPackage with ⟨targetPackage, targetPoint⟩
  let aligned : input.source ⟶ packagePoint targetPackage :=
    input.hom ≫ eqToHom targetPoint.symm
  let hom := inverseCorePackageHom targetPackage aligned
  letI : (packageProjection U).IsHomLift input.hom hom := by
    apply CategoryTheory.IsHomLift.of_fac'
      (packageProjection U) input.hom hom
      (inverseCorePackage_point targetPackage aligned) targetPoint
    simp [hom, aligned, inverseCorePackageHom]
  change (packageProjection U).IsStronglyCocartesian input.hom hom
  exact packageTotalHom_isStronglyCocartesian_of_upper_inverse_lift
    input.hom hom (inverseCorePackageBackwardUpper targetPackage aligned)
    (inverseCorePackageForward_comp_backward targetPackage aligned)
    (inverseCorePackageBackward_comp_forward targetPackage aligned)

/-! ## The selected lift is ambidextrous -/

/--
The selected cartesian lift is strongly cocartesian by comparison with the
explicit arbitrary-target lift, whose upper inverse was generated above.
-/
theorem selectedCoreFiberCartesianLift_isStronglyCocartesian
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    (packageProjection U).IsStronglyCocartesian input.semantic.hom
      (selectedCoreFiberCartesianLift input targetPackage).hom := by
  let explicit := strongCartesianLiftOfTarget input.semantic targetPackage
  let selected := selectedCoreFiberCartesianLift input targetPackage
  letI : (packageProjection U).IsStronglyCartesian input.semantic.hom
      explicit.hom := explicit.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCartesian input.semantic.hom
      selected.hom := selected.isStronglyCartesian
  have base_fac : input.semantic.hom =
      (Iso.refl input.semantic.source).hom ≫ input.semantic.hom := by simp
  let comparison : selected.domain ≅ explicit.domain :=
    CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := packageProjection U)
      (g := Iso.refl input.semantic.source)
      (f := input.semantic.hom) (f' := input.semantic.hom)
      base_fac explicit.hom selected.hom
  have comparison_fac : comparison.hom ≫ explicit.hom = selected.hom := by
    exact CategoryTheory.Functor.IsStronglyCartesian.fac
      (packageProjection U) input.semantic.hom explicit.hom base_fac
      selected.hom
  letI : (packageProjection U).IsHomLift
      (𝟙 input.semantic.source) comparison.hom := by
    change (packageProjection U).IsHomLift
      (Iso.refl input.semantic.source).hom comparison.hom
    infer_instance
  letI : (packageProjection U).IsStronglyCocartesian
      (𝟙 input.semantic.source) comparison.hom :=
    CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (packageProjection U) (𝟙 input.semantic.source) comparison
  letI : (packageProjection U).IsStronglyCocartesian input.semantic.hom
      explicit.hom := strongCartesianLiftOfTarget_isStronglyCocartesian
        input.semantic targetPackage
  have composed : (packageProjection U).IsStronglyCocartesian
      ((𝟙 input.semantic.source) ≫ input.semantic.hom)
      (comparison.hom ≫ explicit.hom) :=
    CategoryTheory.Functor.IsStronglyCocartesian.comp (packageProjection U)
  simpa only [Category.id_comp, comparison_fac] using composed

/-! ## Invertible generated unit and counit -/

/-- A fiber morphism is invertible when its underlying total morphism is. -/
theorem coreFiberHom_isIso_of_total_isIso
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {source target : CoreFiber X} (hom : source ⟶ target)
    [IsIso hom.1] : IsIso hom := by
  letI : (packageProjection U).IsHomLift (𝟙 X) hom.1 := hom.2
  let inverse : target ⟶ source :=
    ⟨inv hom.1, CategoryTheory.IsHomLift.lift_id_inv_isIso
      (packageProjection U) X hom.1⟩
  exact ⟨⟨inverse, by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact IsIso.hom_inv_id hom.1, by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact IsIso.inv_hom_id hom.1⟩⟩

/-- The canonical core lift is also strongly cartesian after fiber retagging. -/
theorem stronglyCartesian_of_isHomLift_support
    {Base : Type u₁} {Total : Type u₂}
    [Category.{v₁} Base] [Category.{v₂} Total]
    (projection : Total ⥤ Base) {source target : Base}
    {domain codomain : Total} (base : source ⟶ target)
    (hom : domain ⟶ codomain)
    [projection.IsStronglyCartesian (projection.map hom) hom]
    [projection.IsHomLift base hom] :
    projection.IsStronglyCartesian base hom := by
  subst_hom_lift projection base hom
  infer_instance

/-- The canonical core lift is also strongly cartesian after fiber retagging. -/
theorem coreFiberLift_isStronglyCartesian_support
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (base : X ⟶ Y) (sourcePackage : CoreFiber X) :
    (packageProjection U).IsStronglyCartesian base
      (coreFiberLift base sourcePackage) := by
  letI : (packageProjection U).IsStronglyCartesian
      ((packageProjection U).map (coreFiberLift base sourcePackage))
      (coreFiberLift base sourcePackage) := by
    simpa only [coreFiberLift, packageProjection_map] using
      transportAlongHom_isStronglyCartesian sourcePackage.1
        (coreFiberBaseHom base sourcePackage).doctrineHom
  letI : (packageProjection U).IsHomLift base
      (coreFiberLift base sourcePackage) :=
    coreFiberLift_isHomLift base sourcePackage
  exact stronglyCartesian_of_isHomLift_support
    (packageProjection U) base (coreFiberLift base sourcePackage)

/-- Every generated unit component is invertible from cartesian uniqueness. -/
theorem coreTransportReindexUnit_app_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source) :
    IsIso ((coreTransportReindexUnit input).app sourcePackage) := by
  let unit := (coreTransportReindexUnit input).app sourcePackage
  let selectedLift := selectedCoreFiberCartesianLift input
    ((coreFiberTransportFunctor input.semantic.hom).obj sourcePackage)
  let canonicalLift := coreFiberLift input.semantic.hom sourcePackage
  letI : (packageProjection U).IsStronglyCartesian input.semantic.hom
      selectedLift.hom := selectedLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCartesian input.semantic.hom
      canonicalLift := coreFiberLift_isStronglyCartesian_support
        input.semantic.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.semantic.source) unit.1 := unit.2
  have composed : (packageProjection U).IsStronglyCartesian
      ((𝟙 input.semantic.source) ≫ input.semantic.hom)
      (unit.1 ≫ selectedLift.hom) := by
    rw [Category.id_comp, coreTransportReindexUnit_app_fac]
    infer_instance
  letI : (packageProjection U).IsStronglyCartesian
      ((𝟙 input.semantic.source) ≫ input.semantic.hom)
      (unit.1 ≫ selectedLift.hom) := composed
  letI : (packageProjection U).IsStronglyCartesian
      (𝟙 input.semantic.source) unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.of_comp
      (p := packageProjection U)
      (f := 𝟙 input.semantic.source) (g := input.semantic.hom)
      (φ := unit.1) (ψ := selectedLift.hom)
  letI : IsIso unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
      (packageProjection U) (𝟙 input.semantic.source) unit.1
  exact coreFiberHom_isIso_of_total_isIso unit

/-- Every generated counit component is invertible from cocartesian uniqueness. -/
theorem coreTransportReindexCounit_app_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    IsIso ((coreTransportReindexCounit input).app targetPackage) := by
  let counit := (coreTransportReindexCounit input).app targetPackage
  let sourcePackage :=
    (selectedCoreFiberReindexFunctor input).obj targetPackage
  let canonicalLift := coreFiberLift input.semantic.hom sourcePackage
  let selectedLift := selectedCoreFiberCartesianLift input targetPackage
  letI : (packageProjection U).IsStronglyCocartesian input.semantic.hom
      canonicalLift := coreFiberLift_isStronglyCocartesian
        input.semantic.hom sourcePackage
  letI : (packageProjection U).IsStronglyCocartesian input.semantic.hom
      selectedLift.hom :=
    selectedCoreFiberCartesianLift_isStronglyCocartesian input targetPackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.semantic.target) counit.1 := counit.2
  have composed : (packageProjection U).IsStronglyCocartesian
      (input.semantic.hom ≫ 𝟙 input.semantic.target)
      (canonicalLift ≫ counit.1) := by
    rw [Category.comp_id, coreTransportReindexCounit_app_fac]
    infer_instance
  letI : (packageProjection U).IsStronglyCocartesian
      (input.semantic.hom ≫ 𝟙 input.semantic.target)
      (canonicalLift ≫ counit.1) := composed
  letI : (packageProjection U).IsStronglyCocartesian
      (𝟙 input.semantic.target) counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.of_comp
      (p := packageProjection U)
      (f := input.semantic.hom) (g := 𝟙 input.semantic.target)
      (φ := canonicalLift) (ψ := counit.1)
  letI : IsIso counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (packageProjection U) (𝟙 input.semantic.target) counit.1
  exact coreFiberHom_isIso_of_total_isIso counit

/-- The generated unit natural transformation is an isomorphism. -/
theorem coreTransportReindexUnit_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) : IsIso (coreTransportReindexUnit input) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact coreTransportReindexUnit_app_isIso input

/-- The generated counit natural transformation is an isomorphism. -/
theorem coreTransportReindexCounit_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) : IsIso (coreTransportReindexCounit input) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact coreTransportReindexCounit_app_isIso input

/-! ## Beck--Chevalley exactness -/

/-- Every canonical mate component is invertible by package-specific support. -/
theorem coreBeckChevalleyMate_app_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (sourcePackage : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    IsIso ((coreBeckChevalleyMate presentation).app sourcePackage) := by
  let topSource :=
    (coreFiberTransportFunctor
      (typedPresentationToSemantic (bcTopPresentation presentation))).obj
      ((selectedCoreFiberReindexFunctor
        (bcLeftInput presentation)).obj sourcePackage)
  let unitApp := (bcRightAdjunction presentation).unit.app topSource
  let squareApp := (bcCoreTransportSquareIso presentation).hom.app
    ((selectedCoreFiberReindexFunctor
      (bcLeftInput presentation)).obj sourcePackage)
  let counitApp := (bcLeftAdjunction presentation).counit.app sourcePackage
  let mappedSquare :=
    (selectedCoreFiberReindexFunctor
      (bcRightInput presentation)).map squareApp
  let mappedCounit :=
    (selectedCoreFiberReindexFunctor
      (bcRightInput presentation)).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map counitApp)
  letI : IsIso unitApp := by
    change IsIso
      ((coreTransportReindexUnit (bcRightInput presentation)).app topSource)
    exact coreTransportReindexUnit_app_isIso
      (bcRightInput presentation) topSource
  letI : IsIso squareApp := by
    dsimp [squareApp]
    infer_instance
  letI : IsIso counitApp := by
    change IsIso
      ((coreTransportReindexCounit (bcLeftInput presentation)).app sourcePackage)
    exact coreTransportReindexCounit_app_isIso
      (bcLeftInput presentation) sourcePackage
  letI : IsIso mappedSquare := by
    dsimp [mappedSquare]
    infer_instance
  letI : IsIso mappedCounit := by
    dsimp [mappedCounit]
    infer_instance
  rw [coreBeckChevalleyMate_app]
  change IsIso (unitApp ≫ mappedSquare ≫ mappedCounit)
  infer_instance

/--
The package-projection Beck--Chevalley support: every generated canonical mate
on a validated finite pointed pullback presentation is an isomorphism.
-/
theorem coreBeckChevalleyMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    IsIso (coreBeckChevalleyMate presentation) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact coreBeckChevalleyMate_app_isIso presentation

/-- Exactness is independent of both arbitrary cleavage choices. -/
theorem coreBeckChevalleyCleavageMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (leftCleavage : CoreFiberCartesianCleavage
      (bcLeftInput presentation).semantic)
    (rightCleavage : CoreFiberCartesianCleavage
      (bcRightInput presentation).semantic) :
    IsIso (coreBeckChevalleyCleavageMate presentation
      leftCleavage rightCleavage) := by
  letI : IsIso (coreBeckChevalleyMate presentation) :=
    coreBeckChevalleyMate_isIso presentation
  have comparison := coreBeckChevalleyCleavageMate_selectedComparison
    presentation leftCleavage rightCleavage
  exact IsIso.of_isIso_fac_right comparison.symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
