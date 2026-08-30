import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateIso

/-!
# Explicit backward realization for the generated upper mate

The pulled-first route is assembled from a realized-refinement inverse lift
and an exact inverse lift.  This module composes their generated backward upper
maps, proves both cancellation laws against the literal pulled route, and
identifies the generated core mate's upper map with the base-route forward map
followed by that backward realization.  These are G-115-local inputs for the
Support / Axis / Observable geometry comparison; no predecessor is changed.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

set_option maxHeartbeats 2000000

private theorem signed_comp_assoc {P Q R S : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R)
    (h : SignedExactCoreReadingHom R S) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply SignedExactCoreReadingHom.ext <;> rfl

private theorem signed_refl_comp {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    (SignedExactCoreReadingHom.refl P).comp f = f := by
  apply SignedExactCoreReadingHom.ext <;> rfl

private theorem signed_comp_refl {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    f.comp (SignedExactCoreReadingHom.refl Q) = f := by
  apply SignedExactCoreReadingHom.ext <;> rfl

noncomputable def pulledRouteTransportData
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  selectedTransportDataOfRealizedReflection
    (ctx.configuration.pulledRefinementAt ctx.source)
    (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
    ⟨(pullbackTargetGeometry ctx target).core,
      pullbackTargetGeometry_packagePoint_eq ctx target⟩

noncomputable def pulledRouteBackwardUpper
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    SignedExactCoreReadingHom target.geometry.core
      (pulledRouteGeometry ctx target).core :=
  (inverseCorePackageBackwardUpper target.geometry.core
    (pullbackTargetExactArrow ctx target)).comp
      (SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target))

theorem pulledRouteGeometryHom_upper_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteGeometryHom ctx target).base.upper =
      (SelectedRefinementTransport.inverseCorePackageForwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).comp
      (inverseCorePackageForwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)) := by
  rfl

theorem pulledRouteBackwardUpper_comp_forward
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteBackwardUpper ctx target).comp
        (pulledRouteGeometryHom ctx target).base.upper =
      SignedExactCoreReadingHom.refl target.geometry.core := by
  rw [pulledRouteGeometryHom_upper_eq]
  unfold pulledRouteBackwardUpper
  let exactBackward := inverseCorePackageBackwardUpper target.geometry.core
    (pullbackTargetExactArrow ctx target)
  let exactForward := inverseCorePackageForwardUpper target.geometry.core
    (pullbackTargetExactArrow ctx target)
  let refinementBackward :=
    SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)
  let refinementForward :=
    SelectedRefinementTransport.inverseCorePackageForwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)
  rw [signed_comp_assoc exactBackward refinementBackward
    (refinementForward.comp exactForward)]
  rw [← signed_comp_assoc refinementBackward refinementForward exactForward]
  rw [SelectedRefinementTransport.inverseCorePackageBackward_comp_forward]
  rw [signed_refl_comp]
  exact inverseCorePackageBackward_comp_forward target.geometry.core
    (pullbackTargetExactArrow ctx target)

theorem pulledRouteForward_comp_backwardUpper
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteGeometryHom ctx target).base.upper.comp
        (pulledRouteBackwardUpper ctx target) =
      SignedExactCoreReadingHom.refl
        (pulledRouteGeometry ctx target).core := by
  rw [pulledRouteGeometryHom_upper_eq]
  unfold pulledRouteBackwardUpper
  let exactBackward := inverseCorePackageBackwardUpper target.geometry.core
    (pullbackTargetExactArrow ctx target)
  let exactForward := inverseCorePackageForwardUpper target.geometry.core
    (pullbackTargetExactArrow ctx target)
  let refinementBackward :=
    SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)
  let refinementForward :=
    SelectedRefinementTransport.inverseCorePackageForwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)
  rw [signed_comp_assoc refinementForward exactForward
    (exactBackward.comp refinementBackward)]
  rw [← signed_comp_assoc exactForward exactBackward refinementBackward]
  rw [inverseCorePackageForward_comp_backward]
  rw [signed_refl_comp]
  exact SelectedRefinementTransport.inverseCorePackageForward_comp_backward
    (pullbackTargetGeometry ctx target).core
    (pulledRouteTransportData ctx target)

theorem generatedRouteCoreMate_upper_eq_explicit
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (generatedRouteCoreMate ctx target).1.upper =
      (baseRouteGeometryHom ctx target).base.upper.comp
        (pulledRouteBackwardUpper ctx target) := by
  have htriangle := congrArg RefinementPackageHom.upper
    (generatedRouteRefinementMate_fac ctx target)
  change (generatedRouteRefinementMate ctx target).upper.comp
      (pulledRouteGeometryHom ctx target).base.upper =
    (baseRouteGeometryHom ctx target).base.upper at htriangle
  calc
    (generatedRouteCoreMate ctx target).1.upper =
        (generatedRouteRefinementMate ctx target).upper := rfl
    _ = (generatedRouteRefinementMate ctx target).upper.comp
        (SignedExactCoreReadingHom.refl
          (pulledRouteGeometry ctx target).core) :=
      (signed_comp_refl _).symm
    _ = (generatedRouteRefinementMate ctx target).upper.comp
        ((pulledRouteGeometryHom ctx target).base.upper.comp
          (pulledRouteBackwardUpper ctx target)) := by
      rw [pulledRouteForward_comp_backwardUpper]
    _ = ((generatedRouteRefinementMate ctx target).upper.comp
          (pulledRouteGeometryHom ctx target).base.upper).comp
        (pulledRouteBackwardUpper ctx target) :=
      (signed_comp_assoc _ _ _).symm
    _ = (baseRouteGeometryHom ctx target).base.upper.comp
        (pulledRouteBackwardUpper ctx target) := by
      rw [htriangle]

end UpperGeometryCleavage
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
