import ResearchLean.AG.AtomFoundation.Categories
import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFold
import ResearchLean.AG.DoctrineFiberProduct.CartesianTransport
import ResearchLean.AG.DoctrineFiberProduct.CartesianTarget
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexing
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelLiftComparison
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredDiagnosticObjectCollapseProducer
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredSupportCanonicalMate
import ResearchLean.AG.DoctrineFiberProduct.SignedExactCoreReadingHomObjectMapAPI
import ResearchLean.AG.DoctrineFiberProduct.CoreFiberLiftAxisAPI

/-!
# G-116 observable exactness of the transported projector

This module proves the literal equation-residual and signature-coordinate
equalities required by G-116(f).  The intermediate lemmas expose how canonical
cocartesian transport and selected cartesian reindexing preserve a literally
fixed signature axis on a vertical endomorphism.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- A two-sided inverse for the upper part of an exact package morphism. -/
structure SignedUpperInverseData
    {U : AtomCarrier.{u}} {source target : AATCorePackage U}
    (hom : SignedExactCoreReadingHom source target) where
  inverse : SignedExactCoreReadingHom target source
  hom_inverse : hom.comp inverse = SignedExactCoreReadingHom.refl source
  inverse_hom : inverse.comp hom = SignedExactCoreReadingHom.refl target

namespace SignedUpperInverseData

/-- Reverse a two-sided upper equivalence. -/
def symm
    {U : AtomCarrier.{u}} {source target : AATCorePackage U}
    {hom : SignedExactCoreReadingHom source target}
    (data : SignedUpperInverseData hom) : SignedUpperInverseData data.inverse where
  inverse := hom
  hom_inverse := data.inverse_hom
  inverse_hom := data.hom_inverse

end SignedUpperInverseData

/-- The generated arbitrary-target cartesian lift is literally the identity on
signature axes. -/
theorem strongCartesianLiftOfTarget_axisMap
    {U : AtomCarrier.{u}} (input : CartSemanticInput U)
    (targetPackage : CoreFiber input.target)
    (axis : (strongCartesianLiftOfTarget input targetPackage).domain.reading.signatureReading.Axis) :
    (strongCartesianLiftOfTarget input targetPackage).hom.upper.axisMap axis = axis := by
  rcases targetPackage with ⟨targetPackage, targetPoint⟩
  rfl

/-- Every selected cartesian lift is injective on signature axes.  The proof
compares it with the generated arbitrary-target lift and uses the actual domain
isomorphism, rather than assuming a property of the selected cleavage. -/
theorem selectedCoreFiberCartesianLift_axisMap_injective
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    Function.Injective
      (selectedCoreFiberCartesianLift input targetPackage).hom.upper.axisMap := by
  let canonical := strongCartesianLiftOfTarget input.semantic targetPackage
  let selected := selectedCoreFiberCartesianLift input targetPackage
  let comparison := StrongCartesianLift.domainIso canonical selected
  have comparison_injective :
      Function.Injective comparison.hom.upper.axisMap :=
    PackageFiberAut.packageTotalHom_axisMap_injective_of_isIso comparison.hom
  intro first second equality
  apply comparison_injective
  have factor := StrongCartesianLift.domainIso_hom_fac canonical selected
  have factor_first := congrArg
    (fun hom : selected.domain ⟶ targetPackage.1 => hom.upper.axisMap first)
    factor
  have factor_second := congrArg
    (fun hom : selected.domain ⟶ targetPackage.1 => hom.upper.axisMap second)
    factor
  change canonical.hom.upper.axisMap
      (comparison.hom.upper.axisMap first) =
        selected.hom.upper.axisMap first at factor_first
  change canonical.hom.upper.axisMap
      (comparison.hom.upper.axisMap second) =
        selected.hom.upper.axisMap second at factor_second
  rw [strongCartesianLiftOfTarget_axisMap] at factor_first factor_second
  exact factor_first.trans (equality.trans factor_second.symm)

/-- The selected cartesian lift has the canonical two-sided upper inverse. -/
noncomputable def selectedCoreFiberCartesianLift_upperInverseData
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    SignedUpperInverseData
      (selectedCoreFiberCartesianLift input targetPackage).hom.upper := by
  rcases targetPackage with ⟨targetPackage, targetPoint⟩
  let aligned : input.semantic.source ⟶ packagePoint targetPackage :=
    input.semantic.hom ≫ eqToHom targetPoint.symm
  let canonical := strongCartesianLiftOfTarget input.semantic
    ⟨targetPackage, targetPoint⟩
  let selected := selectedCoreFiberCartesianLift input
    ⟨targetPackage, targetPoint⟩
  let comparison := StrongCartesianLift.domainIso canonical selected
  let canonicalInverse := inverseCorePackageBackwardUpper targetPackage aligned
  have comparison_factor := congrArg PackageTotalHom.upper
    (StrongCartesianLift.domainIso_hom_fac canonical selected)
  change comparison.hom.upper.comp canonical.hom.upper =
    selected.hom.upper at comparison_factor
  have canonical_hom_inverse : canonical.hom.upper.comp canonicalInverse =
      SignedExactCoreReadingHom.refl canonical.domain :=
    inverseCorePackageForward_comp_backward targetPackage aligned
  have canonical_inverse_hom : canonicalInverse.comp canonical.hom.upper =
      SignedExactCoreReadingHom.refl targetPackage :=
    inverseCorePackageBackward_comp_forward targetPackage aligned
  have comparison_hom_inverse := congrArg PackageTotalHom.upper comparison.hom_inv_id
  have comparison_inverse_hom := congrArg PackageTotalHom.upper comparison.inv_hom_id
  change comparison.hom.upper.comp comparison.inv.upper =
    SignedExactCoreReadingHom.refl selected.domain at comparison_hom_inverse
  change comparison.inv.upper.comp comparison.hom.upper =
    SignedExactCoreReadingHom.refl canonical.domain at comparison_inverse_hom
  refine {
    inverse := canonicalInverse.comp comparison.inv.upper
    hom_inverse := ?_
    inverse_hom := ?_
  }
  · calc
      selected.hom.upper.comp (canonicalInverse.comp comparison.inv.upper) =
          (comparison.hom.upper.comp canonical.hom.upper).comp
            (canonicalInverse.comp comparison.inv.upper) := by
              rw [comparison_factor]
      _ = comparison.hom.upper.comp
          ((canonical.hom.upper.comp canonicalInverse).comp comparison.inv.upper) := by
            simp only [PackageTotalHom.upper_comp_assoc]
      _ = comparison.hom.upper.comp comparison.inv.upper := by
            rw [canonical_hom_inverse, PackageTotalHom.upper_id_comp]
      _ = SignedExactCoreReadingHom.refl selected.domain := comparison_hom_inverse
  · calc
      (canonicalInverse.comp comparison.inv.upper).comp selected.hom.upper =
          (canonicalInverse.comp comparison.inv.upper).comp
            (comparison.hom.upper.comp canonical.hom.upper) := by
              rw [comparison_factor]
      _ = canonicalInverse.comp
          ((comparison.inv.upper.comp comparison.hom.upper).comp
            canonical.hom.upper) := by
              simp only [PackageTotalHom.upper_comp_assoc]
      _ = canonicalInverse.comp canonical.hom.upper := by
            rw [comparison_inverse_hom, PackageTotalHom.upper_id_comp]
      _ = SignedExactCoreReadingHom.refl targetPackage := canonical_inverse_hom

/-- Literal residual invariance is preserved by conjugating an endomorphism
through a two-sided exact upper equivalence. -/
theorem equationResidual_eq_of_upper_conjugation
    {U : AtomCarrier.{u}} {source target : AATCorePackage U}
    (forward : SignedExactCoreReadingHom source target)
    (inverseData : SignedUpperInverseData forward)
    (middle : SignedExactCoreReadingHom target target)
    (middleResidual : ∀ W object index atom,
      target.algebra.equationSystem.equationResidual W
          (middle.objectMap object) index atom =
        target.algebra.equationSystem.equationResidual W object index atom)
    (W : Site.ContextCategoryObject source.algebra.contextPreorder)
    (object : ArchitectureObject U)
    (index : source.algebra.equationSystem.Index)
    (atom : U.Atom) :
    source.algebra.equationSystem.equationResidual W
        (((forward.comp middle).comp inverseData.inverse).objectMap object)
        index atom =
      source.algebra.equationSystem.equationResidual W object index atom := by
  apply (forward.equationTransport.observableEquiv W).injective
  rw [forward.equationTransport.equationResidual_eq,
    forward.equationTransport.equationResidual_eq]
  have object_cancel (current : ArchitectureObject U) :
      forward.objectMap (inverseData.inverse.objectMap current) = current := by
    have applied := congrArg
      (fun hom : SignedExactCoreReadingHom target target =>
        hom.objectMap current) inverseData.inverse_hom
    simpa only [signedExactCoreReadingHom_comp_objectMap_apply,
      signedExactCoreReadingHom_refl_objectMap_apply] using applied
  change target.algebra.equationSystem.equationResidual
      (forward.equationTransport.contextForward W)
      (forward.objectMap
        (inverseData.inverse.objectMap
          (middle.objectMap (forward.objectMap object))))
      (forward.equationMap index) (forward.atomEquiv atom) = _
  rw [object_cancel]
  exact middleResidual _ _ _ _

/-- Literal coordinate invariance is preserved by conjugating an endomorphism
through a two-sided exact upper equivalence. -/
theorem coordinate_eq_of_upper_conjugation
    {U : AtomCarrier.{u}} {source target : AATCorePackage U}
    (forward : SignedExactCoreReadingHom source target)
    (inverseData : SignedUpperInverseData forward)
    (middle : SignedExactCoreReadingHom target target)
    (middleCoordinate : ∀ object axis,
      target.reading.signatureReading.coordinate
          (middle.objectMap object) axis =
        target.reading.signatureReading.coordinate object axis)
    (object : ArchitectureObject U)
    (axis : source.reading.signatureReading.Axis) :
    source.reading.signatureReading.coordinate
        (((forward.comp middle).comp inverseData.inverse).objectMap object) axis =
      source.reading.signatureReading.coordinate object axis := by
  apply (forward.coordinateEquiv axis).injective
  rw [forward.coordinate_eq, forward.coordinate_eq]
  have object_cancel (current : ArchitectureObject U) :
      forward.objectMap (inverseData.inverse.objectMap current) = current := by
    have applied := congrArg
      (fun hom : SignedExactCoreReadingHom target target =>
        hom.objectMap current) inverseData.inverse_hom
    simpa only [signedExactCoreReadingHom_comp_objectMap_apply,
      signedExactCoreReadingHom_refl_objectMap_apply] using applied
  change target.reading.signatureReading.coordinate
      (forward.objectMap
        (inverseData.inverse.objectMap
          (middle.objectMap (forward.objectMap object))))
      (forward.axisMap axis) = _
  rw [object_cancel]
  exact middleCoordinate _ _

/-- The canonical cocartesian core lift exposes its generated upper inverse. -/
noncomputable def coreFiberLift_upperInverseData
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (base : X ⟶ Y) (package : CoreFiber X) :
    SignedUpperInverseData (coreFiberLift base package).upper where
  inverse := transportAlongUpperInverse package.1
    (coreFiberBaseHom base package).doctrineHom
  hom_inverse := transportAlongUpper_comp_inverse package.1
    (coreFiberBaseHom base package).doctrineHom
  inverse_hom := transportAlongUpperInverse_comp package.1
    (coreFiberBaseHom base package).doctrineHom

/-- The upper map of canonical covariant transport is the literal conjugate by
the generated lift and its inverse. -/
theorem coreFiberTransportMap_upper_eq_conjugation
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (base : X ⟶ Y) (package : CoreFiber X)
    (endomorphism : package ⟶ package) :
    (coreFiberTransportMap base endomorphism).1.upper =
      ((coreFiberLift_upperInverseData base package).inverse.comp
        endomorphism.1.upper).comp (coreFiberLift base package).upper := by
  let lift := (coreFiberLift base package).upper
  let inverseData := coreFiberLift_upperInverseData base package
  have factor := congrArg PackageTotalHom.upper
    (coreFiberTransportMap_fac base endomorphism)
  change lift.comp (coreFiberTransportMap base endomorphism).1.upper =
    endomorphism.1.upper.comp lift at factor
  calc
    (coreFiberTransportMap base endomorphism).1.upper =
        (SignedExactCoreReadingHom.refl _).comp
          (coreFiberTransportMap base endomorphism).1.upper :=
      (PackageTotalHom.upper_id_comp _).symm
    _ = (inverseData.inverse.comp lift).comp
          (coreFiberTransportMap base endomorphism).1.upper := by
      rw [inverseData.inverse_hom]
    _ = inverseData.inverse.comp
          (lift.comp (coreFiberTransportMap base endomorphism).1.upper) := by
      rw [PackageTotalHom.upper_comp_assoc]
    _ = inverseData.inverse.comp (endomorphism.1.upper.comp lift) := by
      rw [factor]
    _ = (inverseData.inverse.comp endomorphism.1.upper).comp lift := by
      rw [PackageTotalHom.upper_comp_assoc]

/-- The upper map of selected contravariant reindexing is the literal
conjugate by the selected lift and its generated inverse. -/
theorem selectedCoreFiberReindexMap_upper_eq_conjugation
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (package : CoreFiber input.semantic.target)
    (endomorphism : package ⟶ package) :
    ((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper =
      (((selectedCoreFiberCartesianLift input package).hom.upper.comp
        endomorphism.1.upper).comp
          (selectedCoreFiberCartesianLift_upperInverseData
            input package).inverse) := by
  let lift := (selectedCoreFiberCartesianLift input package).hom.upper
  let inverseData := selectedCoreFiberCartesianLift_upperInverseData input package
  have hom_inverse_actual :
      lift.comp inverseData.inverse =
        SignedExactCoreReadingHom.refl
          ((selectedCoreFiberReindexFunctor input).obj package).1 := by
    simpa only [selectedCoreFiberReindexFunctor_obj] using
      inverseData.hom_inverse
  have factor := congrArg PackageTotalHom.upper
    (selectedCoreFiberReindexFunctor_map_fac input endomorphism)
  change ((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper.comp
      lift = lift.comp endomorphism.1.upper at factor
  calc
    ((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper =
        ((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper.comp
          (SignedExactCoreReadingHom.refl _) :=
      (PackageTotalHom.upper_comp_id _).symm
    _ = ((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper.comp
          (lift.comp inverseData.inverse) := by
      rw [hom_inverse_actual]
    _ = (((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper.comp
          lift).comp inverseData.inverse := by
      rw [PackageTotalHom.upper_comp_assoc]
    _ = (lift.comp endomorphism.1.upper).comp inverseData.inverse := by
      rw [factor]

/-- Canonical covariant transport preserves literal residual invariance of a
vertical endomorphism. -/
theorem coreFiberTransportMap_equationResidual
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (base : X ⟶ Y) (package : CoreFiber X)
    (endomorphism : package ⟶ package)
    (residual : ∀ W object index atom,
      package.1.algebra.equationSystem.equationResidual W
          (endomorphism.1.upper.objectMap object) index atom =
        package.1.algebra.equationSystem.equationResidual W object index atom)
    (W : Site.ContextCategoryObject
      (coreFiberTransportObj base package).1.algebra.contextPreorder)
    (object : ArchitectureObject U)
    (index : (coreFiberTransportObj base package).1.algebra.equationSystem.Index)
    (atom : U.Atom) :
    (coreFiberTransportObj base package).1.algebra.equationSystem.equationResidual W
        ((coreFiberTransportMap base endomorphism).1.upper.objectMap object)
        index atom =
      (coreFiberTransportObj base package).1.algebra.equationSystem.equationResidual W
        object index atom := by
  rw [coreFiberTransportMap_upper_eq_conjugation]
  exact equationResidual_eq_of_upper_conjugation
    (coreFiberLift_upperInverseData base package).inverse
    (coreFiberLift_upperInverseData base package).symm
    endomorphism.1.upper residual W object index atom

/-- Canonical covariant transport preserves literal coordinate invariance of a
vertical endomorphism. -/
theorem coreFiberTransportMap_coordinate
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (base : X ⟶ Y) (package : CoreFiber X)
    (endomorphism : package ⟶ package)
    (coordinate : ∀ object axis,
      package.1.reading.signatureReading.coordinate
          (endomorphism.1.upper.objectMap object) axis =
        package.1.reading.signatureReading.coordinate object axis)
    (object : ArchitectureObject U)
    (axis : (coreFiberTransportObj base package).1.reading.signatureReading.Axis) :
    (coreFiberTransportObj base package).1.reading.signatureReading.coordinate
        ((coreFiberTransportMap base endomorphism).1.upper.objectMap object) axis =
      (coreFiberTransportObj base package).1.reading.signatureReading.coordinate
        object axis := by
  rw [coreFiberTransportMap_upper_eq_conjugation]
  exact coordinate_eq_of_upper_conjugation
    (coreFiberLift_upperInverseData base package).inverse
    (coreFiberLift_upperInverseData base package).symm
    endomorphism.1.upper coordinate object axis

/-- Selected contravariant reindexing preserves literal residual invariance of
a vertical endomorphism. -/
theorem selectedCoreFiberReindexMap_equationResidual
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (package : CoreFiber input.semantic.target)
    (endomorphism : package ⟶ package)
    (residual : ∀ W object index atom,
      package.1.algebra.equationSystem.equationResidual W
          (endomorphism.1.upper.objectMap object) index atom =
        package.1.algebra.equationSystem.equationResidual W object index atom)
    (W : Site.ContextCategoryObject
      ((selectedCoreFiberReindexFunctor input).obj package).1.algebra.contextPreorder)
    (object : ArchitectureObject U)
    (index : ((selectedCoreFiberReindexFunctor input).obj package).1.algebra.equationSystem.Index)
    (atom : U.Atom) :
    ((selectedCoreFiberReindexFunctor input).obj package).1.algebra.equationSystem.equationResidual W
        (((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper.objectMap object)
        index atom =
      ((selectedCoreFiberReindexFunctor input).obj package).1.algebra.equationSystem.equationResidual W
        object index atom := by
  rw [selectedCoreFiberReindexMap_upper_eq_conjugation]
  exact equationResidual_eq_of_upper_conjugation
    (selectedCoreFiberCartesianLift input package).hom.upper
    (selectedCoreFiberCartesianLift_upperInverseData input package)
    endomorphism.1.upper residual W object index atom

/-- Selected contravariant reindexing preserves literal coordinate invariance
of a vertical endomorphism. -/
theorem selectedCoreFiberReindexMap_coordinate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (package : CoreFiber input.semantic.target)
    (endomorphism : package ⟶ package)
    (coordinate : ∀ object axis,
      package.1.reading.signatureReading.coordinate
          (endomorphism.1.upper.objectMap object) axis =
        package.1.reading.signatureReading.coordinate object axis)
    (object : ArchitectureObject U)
    (axis : ((selectedCoreFiberReindexFunctor input).obj package).1.reading.signatureReading.Axis) :
    ((selectedCoreFiberReindexFunctor input).obj package).1.reading.signatureReading.coordinate
        (((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper.objectMap object) axis =
      ((selectedCoreFiberReindexFunctor input).obj package).1.reading.signatureReading.coordinate
        object axis := by
  rw [selectedCoreFiberReindexMap_upper_eq_conjugation]
  exact coordinate_eq_of_upper_conjugation
    (selectedCoreFiberCartesianLift input package).hom.upper
    (selectedCoreFiberCartesianLift_upperInverseData input package)
    endomorphism.1.upper coordinate object axis

/-- Canonical covariant package transport preserves a literally fixed axis of
a vertical endomorphism. -/
theorem coreFiberTransportMap_axisMap_of_eq
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (base : X ⟶ Y) (package : CoreFiber X)
    (endomorphism : package ⟶ package)
    (axis_fixed : ∀ axis, endomorphism.1.upper.axisMap axis = axis)
    (axis : (coreFiberTransportObj base package).1.reading.signatureReading.Axis) :
    (coreFiberTransportMap base endomorphism).1.upper.axisMap axis = axis := by
  have factor := congrArg
    (fun hom : package.1 ⟶ (coreFiberTransportObj base package).1 =>
      hom.upper.axisMap axis)
    (coreFiberTransportMap_fac base endomorphism)
  change
    (coreFiberTransportMap base endomorphism).1.upper.axisMap axis =
      (coreFiberLift base package).upper.axisMap
        (endomorphism.1.upper.axisMap axis) at factor
  simpa only [coreFiberLift_axisMap, axis_fixed axis] using factor

/-- Selected contravariant reindexing preserves a literally fixed axis of a
vertical endomorphism. -/
theorem selectedCoreFiberReindexMap_axisMap_of_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (package : CoreFiber input.semantic.target)
    (endomorphism : package ⟶ package)
    (axis_fixed : ∀ axis, endomorphism.1.upper.axisMap axis = axis)
    (axis : ((selectedCoreFiberReindexFunctor input).obj package).1.reading.signatureReading.Axis) :
    ((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper.axisMap axis = axis := by
  let lift := selectedCoreFiberCartesianLift input package
  apply selectedCoreFiberCartesianLift_axisMap_injective input package
  have factor := congrArg
    (fun hom : ((selectedCoreFiberReindexFunctor input).obj package).1 ⟶ package.1 =>
      hom.upper.axisMap axis)
    (selectedCoreFiberReindexFunctor_map_fac input endomorphism)
  change lift.hom.upper.axisMap
      (((selectedCoreFiberReindexFunctor input).map endomorphism).1.upper.axisMap axis) =
    endomorphism.1.upper.axisMap (lift.hom.upper.axisMap axis) at factor
  simpa [lift, axis_fixed] using factor

/-- On an admissible firing component, the transported projector fixes every
signature axis literally. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_axisMap
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (axis : ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.Axis) :
    (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
      input cochain cell).1.upper.axisMap axis = axis := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  apply selectedCoreFiberReindexMap_axisMap_of_eq
  intro transportedAxis
  apply coreFiberTransportMap_axisMap_of_eq
  intro supportAxis
  rw [authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
    _ cochain cell.as fires admissible]
  rfl

/-- Casting a dependent value along its index equality lands at the value with
the rewritten index. -/
private theorem coordinate_cast_apply
    {Axis : Type*} (Coordinate : Axis → Type*)
    (value : ∀ axis, Coordinate axis) {first second : Axis}
    (index_eq : first = second) :
    Equiv.cast (congrArg Coordinate index_eq) (value first) = value second := by
  cases index_eq
  rfl

/-- An idempotent exact endomorphism which fixes its signature axes preserves
the literal coordinate of every architecture object. -/
theorem signedExactCoreReadingHom_coordinate_eq_of_comp
    {U : AtomCarrier.{u}} {package : AATCorePackage U}
    (endomorphism : SignedExactCoreReadingHom package package)
    (idempotent : endomorphism.comp endomorphism = endomorphism)
    (axis_fixed : ∀ axis, endomorphism.axisMap axis = axis)
    (object : ArchitectureObject U)
    (axis : package.reading.signatureReading.Axis)
    : package.reading.signatureReading.coordinate
        (endomorphism.objectMap object) axis =
      package.reading.signatureReading.coordinate object axis := by
  let landed : package.reading.signatureReading.Coordinate axis ≃
      package.reading.signatureReading.Coordinate axis :=
    (endomorphism.coordinateEquiv axis).trans
      (Equiv.cast (congrArg package.reading.signatureReading.Coordinate
        (axis_fixed axis)))
  have landed_coordinate (current : ArchitectureObject U) :
      landed (package.reading.signatureReading.coordinate current axis) =
        package.reading.signatureReading.coordinate
          (endomorphism.objectMap current) axis := by
    change Equiv.cast (congrArg package.reading.signatureReading.Coordinate
        (axis_fixed axis))
      (endomorphism.coordinateEquiv axis
        (package.reading.signatureReading.coordinate current axis)) = _
    rw [endomorphism.coordinate_eq]
    exact coordinate_cast_apply
      package.reading.signatureReading.Coordinate
      (package.reading.signatureReading.coordinate
        (endomorphism.objectMap current)) (axis_fixed axis)
  have object_idempotent (current : ArchitectureObject U) :
      endomorphism.objectMap (endomorphism.objectMap current) =
        endomorphism.objectMap current := by
    have applied := congrArg
      (fun hom : SignedExactCoreReadingHom package package =>
        hom.objectMap current) idempotent
    simpa only [signedExactCoreReadingHom_comp_objectMap_apply] using applied
  have landed_fixed :
      landed (package.reading.signatureReading.coordinate object axis) =
        package.reading.signatureReading.coordinate object axis := by
    apply landed.injective
    rw [landed_coordinate, landed_coordinate, object_idempotent]
  exact (landed_coordinate object).symm.trans landed_fixed

/-- G-116(f), coordinate part: on an admissible firing component, the
transported projector preserves the literal coordinate at the same axis. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (object : ArchitectureObject U)
    (axis : ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.Axis) :
    ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.coordinate
        ((authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell).1.upper.objectMap object) axis =
      ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.coordinate
        object axis := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  apply selectedCoreFiberReindexMap_coordinate
  intro transportedObject transportedAxis
  apply coreFiberTransportMap_coordinate
  intro supportObject supportAxis
  rw [authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
    _ cochain cell.as fires admissible]
  exact (admissible.coordinate_eq supportObject supportAxis).symm

/-- G-116(f), equation part: on an admissible firing component, the transported
projector preserves the literal equation residual at the same context, index,
and Atom. -/
theorem authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (W : Site.ContextCategoryObject
      ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.contextPreorder)
    (object : ArchitectureObject U)
    (index : ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.Index)
    (atom : U.Atom) :
    ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.equationResidual W
        ((authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
          input cochain cell).1.upper.objectMap object) index atom =
      ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.equationResidual W
        object index atom := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  apply selectedCoreFiberReindexMap_equationResidual
  intro transportedW transportedObject transportedIndex transportedAtom
  apply coreFiberTransportMap_equationResidual
  intro supportW supportObject supportIndex supportAtom
  rw [authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
    _ cochain cell.as fires admissible]
  exact (admissible.equationResidual_eq
    supportW supportObject supportIndex supportAtom).symm

/-- G-116(f): the diagnostic comparison and canonical mate have the same
literal coordinate after applying their upper object maps. -/
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_coordinate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (object : ArchitectureObject U)
    (axis : ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.Axis) :
    ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.coordinate
        (((authoredDiagnosticObjectCollapseComparisonAtCochain
          input cochain).app cell).1.upper.objectMap object) axis =
      ((authoredSupportViaBaseRoute input.context).obj cell).1.reading.signatureReading.coordinate
        (((authoredSupportCanonicalMate input.context).app cell).1.upper.objectMap
          object) axis := by
  rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
  exact authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate
    input cochain cell fires admissible
      (((authoredSupportCanonicalMate input.context).app cell).1.upper.objectMap
        object) axis

/-- G-116(f): the diagnostic comparison and canonical mate have the same
literal equation residual at the same context, equation index, and Atom after
applying their upper object maps. -/
theorem authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (fires : cochain cell.as ≠ 1)
    (admissible : CanonicalObjectNormalizationAdmissible
      (input.context.supportPackage cell.as))
    (W : Site.ContextCategoryObject
      ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.contextPreorder)
    (object : ArchitectureObject U)
    (index : ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.Index)
    (atom : U.Atom) :
    ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.equationResidual W
        (((authoredDiagnosticObjectCollapseComparisonAtCochain
          input cochain).app cell).1.upper.objectMap object) index atom =
      ((authoredSupportViaBaseRoute input.context).obj cell).1.algebra.equationSystem.equationResidual W
        (((authoredSupportCanonicalMate input.context).app cell).1.upper.objectMap
          object) index atom := by
  rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
  exact authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual
    input cochain cell fires admissible W
      (((authoredSupportCanonicalMate input.context).app cell).1.upper.objectMap
        object) index atom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
