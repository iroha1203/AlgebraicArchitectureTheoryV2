import ResearchLean.AG.FullGeometryNormalization.ExactGeometryPushCartesian
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryTransportAdjunction

/-!
# Invertibility of the exact complete-geometry transport unit

The canonical push lift and the generated exact pull lift are both genuinely
Cartesian.  Their defining unit triangle therefore makes the vertical unit
Cartesian over an identity base arrow, hence invertible.  No isomorphism or
universal-property certificate is accepted from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- A vertical complete-geometry fiber morphism is invertible whenever its
underlying total geometry morphism is invertible. -/
theorem geomFiberHom_isIso_of_total_isIso
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {source target : GeomFiber.{u, v} X} (hom : source ⟶ target)
    [IsIso hom.1] : IsIso hom := by
  letI : (crossStageProjection.{u, v} U).IsHomLift (𝟙 X) hom.1 := hom.2
  let inverse : target ⟶ source :=
    ⟨inv hom.1, CategoryTheory.IsHomLift.lift_id_inv_isIso
      (crossStageProjection.{u, v} U) X hom.1⟩
  exact ⟨⟨inverse, by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact IsIso.hom_inv_id hom.1, by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact IsIso.inv_hom_id hom.1⟩⟩

/-- Every generated exact complete-geometry adjunction unit component is
invertible by Cartesian cancellation over the identity base arrow. -/
theorem exactGeometryTransportPullUnit_app_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (source : GeomFiber.{u, v} input.semantic.source) :
    IsIso ((exactGeometryTransportPullUnit input).app source) := by
  let unit := (exactGeometryTransportPullUnit input).app source
  let pullLift := exactGeometryPullLift input
    ((geomFiberTransportFunctor input.semantic.hom).obj source)
  let pushLift := geomFiberLift input.semantic.hom source
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input.semantic.hom pullLift :=
    exactGeometryPullLift_crossStageStronglyCartesian input _
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input.semantic.hom pushLift :=
    geomFiberLift_crossStageStronglyCartesian input.semantic.hom source
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 input.semantic.source) unit.1 := unit.2
  have composed : (crossStageProjection.{u, v} U).IsStronglyCartesian
      ((𝟙 input.semantic.source) ≫ input.semantic.hom)
      (unit.1 ≫ pullLift) := by
    rw [Category.id_comp, exactGeometryTransportPullUnit_app_fac]
    exact geomFiberLift_crossStageStronglyCartesian input.semantic.hom source
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      ((𝟙 input.semantic.source) ≫ input.semantic.hom)
      (unit.1 ≫ pullLift) := composed
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      (𝟙 input.semantic.source) unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.of_comp
      (p := crossStageProjection.{u, v} U)
      (f := 𝟙 input.semantic.source) (g := input.semantic.hom)
      (φ := unit.1) (ψ := pullLift)
  letI : IsIso unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
      (crossStageProjection.{u, v} U) (𝟙 input.semantic.source) unit.1
  exact geomFiberHom_isIso_of_total_isIso unit

/-- The generated unit does not change the fixed coefficient ring. -/
theorem exactGeometryTransportPullUnit_app_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (source : GeomFiber.{u, v} input.semantic.source) :
    ((exactGeometryTransportPullUnit input).app source).1.geometry.coefficientHom =
      RingHom.id source.1.Coefficient := by
  have h := congrArg
    (fun hom : GeometryTotalHom _ _ => hom.geometry.coefficientHom)
    (exactGeometryTransportPullUnit_app_fac input source)
  simpa [GeometryTotalHom.comp, GeomReadHom.comp, geomFiberLift,
    geomTransportAlongHom, geomTransportAlongGeometryHom] using h

/-- Canonical complete-geometry push preserves the coefficient map of every
vertical fiber morphism. -/
theorem geomFiberTransportMap_coefficientHom
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (sigma : X ⟶ Y)
    {first second : GeomFiber.{u, v} X} (hom : first ⟶ second) :
    (geomFiberTransportMap sigma hom).1.geometry.coefficientHom =
      hom.1.geometry.coefficientHom := by
  have factorization := congrArg
    (fun totalHom => totalHom.geometry.coefficientHom)
    (geomFiberTransportMap_fac sigma hom)
  change
    (geomFiberTransportMap sigma hom).1.geometry.coefficientHom.comp
        (geomFiberLift sigma first).geometry.coefficientHom =
      (geomFiberLift sigma second).geometry.coefficientHom.comp
        hom.1.geometry.coefficientHom at factorization
  simpa [geomFiberLift, geomTransportAlongHom,
    geomTransportAlongGeometryHom] using factorization

/-- The generated exact complete-geometry adjunction unit is a natural
isomorphism. -/
theorem exactGeometryTransportPullUnit_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    IsIso (exactGeometryTransportPullUnit input) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro source
  exact exactGeometryTransportPullUnit_app_isIso input source

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
