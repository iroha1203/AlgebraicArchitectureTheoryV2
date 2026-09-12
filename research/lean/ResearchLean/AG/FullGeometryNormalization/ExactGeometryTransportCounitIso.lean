import ResearchLean.AG.FullGeometryNormalization.ExactGeometryPullCocartesian
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryTransportUnitIso

/-!
# Invertibility of the exact complete-geometry transport counit

The canonical push lift and exact pull lift are both genuinely cocartesian.
Their defining counit triangle makes the vertical counit cocartesian over an
identity base arrow, hence invertible.  The coefficient component is then
computed from the same triangle and the identity coefficient maps of both
lifts.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- Every generated exact complete-geometry adjunction counit component is
invertible by cocartesian cancellation over the identity base arrow. -/
theorem exactGeometryTransportPullCounit_app_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target) :
    IsIso ((exactGeometryTransportPullCounit input).app target) := by
  let counit := (exactGeometryTransportPullCounit input).app target
  let source := (exactGeometryPullFunctor input).obj target
  let pushLift := geomFiberLift input.semantic.hom source
  let pullLift := exactGeometryPullLift input target
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input.semantic.hom pushLift :=
    geomFiberLift_isStronglyCocartesian input.semantic.hom source
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input.semantic.hom pullLift :=
    exactGeometryPullLift_crossStageStronglyCocartesian input target
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 input.semantic.target) counit.1 := counit.2
  have composed : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (input.semantic.hom ≫ 𝟙 input.semantic.target)
      (pushLift ≫ counit.1) := by
    rw [Category.comp_id, exactGeometryTransportPullCounit_app_fac]
    exact exactGeometryPullLift_crossStageStronglyCocartesian input target
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (input.semantic.hom ≫ 𝟙 input.semantic.target)
      (pushLift ≫ counit.1) := composed
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (𝟙 input.semantic.target) counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.of_comp
      (p := crossStageProjection.{u, v} U)
      (f := input.semantic.hom) (g := 𝟙 input.semantic.target)
      (φ := pushLift) (ψ := counit.1)
  letI : IsIso counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (crossStageProjection.{u, v} U) (𝟙 input.semantic.target) counit.1
  exact geomFiberHom_isIso_of_total_isIso counit

/-- The generated counit does not change the fixed coefficient ring. -/
theorem exactGeometryTransportPullCounit_app_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target) :
    ((exactGeometryTransportPullCounit input).app target).1.geometry.coefficientHom =
      RingHom.id target.1.Coefficient := by
  have h := congrArg
    (fun hom : GeometryTotalHom _ _ => hom.geometry.coefficientHom)
    (exactGeometryTransportPullCounit_app_fac input target)
  simpa [GeometryTotalHom.comp, GeomReadHom.comp, geomFiberLift,
    geomTransportAlongHom, geomTransportAlongGeometryHom] using h

/-- The generated exact complete-geometry adjunction counit is a natural
isomorphism. -/
theorem exactGeometryTransportPullCounit_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    IsIso (exactGeometryTransportPullCounit input) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro target
  exact exactGeometryTransportPullCounit_app_isIso input target

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
