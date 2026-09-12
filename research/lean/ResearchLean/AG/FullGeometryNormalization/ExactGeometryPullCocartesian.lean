import ResearchLean.AG.FullGeometryNormalization.ExactGeometryPushCartesian
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateComponents
import ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactness
import ResearchLean.AG.CrossStageCoherence.ObstructionGroups

/-!
# Cocartesianity of exact complete-geometry pull lifts

For a realizable exact arrow, the generated exact pull lift has a second,
outgoing universal property.  The factor is constructed directly: the lower
package factor comes from the generated upper inverse, while support, axis,
and observable data are transported by the independently generated backward
realization supply and the forward/backward cancellation laws.

No geometry morphism, factor, isomorphism, or universal-property certificate
is accepted from the caller.  In particular this proof does not cancel a
composite Cartesian certificate through an adjunction counit.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

private theorem contextObject_eq_of_ctx_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {W V : Site.ContextCategoryObject C} (h : W.ctx = V.ctx) : W = V := by
  cases W
  cases V
  cases h
  rfl

/-- The backward upper context used by the direct outgoing factor is the
inverse context of the generated exact forward leg. -/
theorem exactPullBackwardContext_eq
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) :
    (inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
      W = contextBackward (UpperGeometryCleavage.exactBaseHom G f) W := by
  apply contextObject_eq_of_ctx_eq
  exact
    UpperGeometryCleavage.inverseCorePackageBackward_contextForward_eq_forward_contextBackward
      G.core f W

/-- After the backward exact context is fed to a composite outgoing base, its
target context is the target context of the lower factor. -/
theorem exactPullOutgoingFactorContext_eq
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (W : G.site.category) :
    contextForward
        (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)
        (contextBackward (UpperGeometryCleavage.exactBaseHom G f) W) =
      contextForward tail W := by
  rw [contextForward_comp]
  apply congrArg (contextForward tail)
  apply contextObject_eq_of_ctx_eq
  exact UpperGeometryCleavage.generatedExactContextForward_backward_ctx G f W

/-- The independently generated backward and forward exact upper maps cancel
on atoms in the orientation used by the outgoing factor. -/
theorem exactPullBackwardForwardAtom
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (atom : U.Atom) :
    (inverseCorePackageForwardUpper G.core f).atomEquiv
        ((inverseCorePackageBackwardUpper G.core f).atomEquiv atom) = atom := by
  have hcancel := congrArg (fun upper => upper.atomEquiv atom)
    (inverseCorePackageBackward_comp_forward G.core f)
  simpa [SignedExactCoreReadingHom.comp, SignedExactCoreReadingHom.refl] using
    hcancel

/-- Backward followed by forward exact upper transport cancels on signature
axes. -/
theorem exactPullBackwardForwardAxis
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (axis : G.core.algebra.signatureReading.Axis) :
    (inverseCorePackageForwardUpper G.core f).axisMap
        ((inverseCorePackageBackwardUpper G.core f).axisMap axis) = axis := by
  have hcancel := congrArg (fun upper => upper.axisMap axis)
    (inverseCorePackageBackward_comp_forward G.core f)
  simpa [SignedExactCoreReadingHom.comp, SignedExactCoreReadingHom.refl] using
    hcancel

/-- Backward followed by forward exact upper transport cancels on equation
indices. -/
theorem exactPullBackwardForwardEquation
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (equation : G.core.equationSystem.Index) :
    (inverseCorePackageForwardUpper G.core f).equationMap
        ((inverseCorePackageBackwardUpper G.core f).equationMap equation) =
      equation := by
  have hcancel := congrArg (fun upper => upper.equationMap equation)
    (inverseCorePackageBackward_comp_forward G.core f)
  simpa [SignedExactCoreReadingHom.comp, SignedExactCoreReadingHom.refl] using
    hcancel

/-- Backward followed by forward exact upper transport cancels on full
equation indices. -/
theorem exactPullBackwardForwardEquationEquiv
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (equation : G.core.equationSystem.Index) :
    (inverseCorePackageForwardUpper G.core f).equationEquiv
        ((inverseCorePackageBackwardUpper G.core f).equationEquiv equation) =
      equation := by
  have hcancel := congrArg (fun upper => upper.equationEquiv equation)
    (inverseCorePackageBackward_comp_forward G.core f)
  simpa [SignedExactCoreReadingHom.comp, SignedExactCoreReadingHom.refl] using
    hcancel

/-- Cancellation on the required equation/atom coordinate used by coverage. -/
theorem exactPullBackwardForwardRequiredCoordinate
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (coordinate : G.site.equationSystem.RequiredCoordinate) :
    (⟨⟨(inverseCorePackageForwardUpper G.core f).equationMap
          ((inverseCorePackageBackwardUpper G.core f).equationMap coordinate.1.1),
        (inverseCorePackageForwardUpper G.core f).required_iff _ |>.mp
          ((inverseCorePackageBackwardUpper G.core f).required_iff _ |>.mp
            coordinate.1.2)⟩,
      (inverseCorePackageForwardUpper G.core f).atomEquiv
        ((inverseCorePackageBackwardUpper G.core f).atomEquiv coordinate.2)⟩ :
      G.site.equationSystem.RequiredCoordinate) = coordinate := by
  apply Prod.ext
  · apply Subtype.ext
    exact exactPullBackwardForwardEquation G f coordinate.1.1
  · exact exactPullBackwardForwardAtom G f coordinate.2

/-- Cancellation on the full equation/atom coordinate used by coverage. -/
theorem exactPullBackwardForwardCoordinate
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (coordinate : G.site.equationSystem.Coordinate) :
    ((inverseCorePackageForwardUpper G.core f).equationEquiv
        ((inverseCorePackageBackwardUpper G.core f).equationEquiv coordinate.1),
      (inverseCorePackageForwardUpper G.core f).atomEquiv
        ((inverseCorePackageBackwardUpper G.core f).atomEquiv coordinate.2)) =
      coordinate := by
  apply Prod.ext
  · exact exactPullBackwardForwardEquationEquiv G f coordinate.1
  · exact exactPullBackwardForwardAtom G f coordinate.2

/-- Required supports are carried backward into the generated exact source
and then forward through an arbitrary compatible outgoing hom. -/
theorem exactPullOutgoingFactor_requiredSupport
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (atom : U.Atom) :
    G.geometry.requirements.requiredSupport atom →
      K.geometry.requirements.requiredSupport (tail.upper.atomEquiv atom) := by
  intro hreq
  let backward := inverseCorePackageBackwardUpper G.core f
  have sourceReq :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.requiredSupport
        (backward.atomEquiv atom) := by
    change G.geometry.requirements.requiredSupport
      ((inverseCorePackageForwardUpper G.core f).atomEquiv
        (backward.atomEquiv atom))
    rw [exactPullBackwardForwardAtom G f atom]
    exact hreq
  have mapped := H.coverage.requiredSupport (backward.atomEquiv atom) sourceReq
  change K.geometry.requirements.requiredSupport
    (tail.upper.atomEquiv
      ((inverseCorePackageForwardUpper G.core f).atomEquiv
        (backward.atomEquiv atom))) at mapped
  rw [exactPullBackwardForwardAtom G f atom] at mapped
  exact mapped

/-- Required equation coordinates are transported through the backward exact
upper map before applying the outgoing hom. -/
theorem exactPullOutgoingFactor_requiredEquationCoordinate
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (coordinate : G.site.equationSystem.RequiredCoordinate) :
    G.geometry.requirements.requiredEquationCoordinate coordinate →
      K.geometry.requirements.requiredEquationCoordinate
        (requiredCoordinateMap tail coordinate) := by
  intro hreq
  let backward := inverseCorePackageBackwardUpper G.core f
  let sourceCoordinate :
      (UpperGeometryCleavage.exactSourceGeometry G f).site.equationSystem.RequiredCoordinate :=
    (⟨backward.equationMap coordinate.1.1,
        (backward.required_iff coordinate.1.1).mp coordinate.1.2⟩,
      backward.atomEquiv coordinate.2)
  have sourceReq :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.requiredEquationCoordinate
        sourceCoordinate := by
    change G.geometry.requirements.requiredEquationCoordinate
      (⟨⟨(inverseCorePackageForwardUpper G.core f).equationMap
          (backward.equationMap coordinate.1.1), _⟩,
        (inverseCorePackageForwardUpper G.core f).atomEquiv
          (backward.atomEquiv coordinate.2)⟩)
    rw [exactPullBackwardForwardRequiredCoordinate G f coordinate]
    exact hreq
  have mapped := H.coverage.requiredEquationCoordinate sourceCoordinate sourceReq
  let forwardedCoordinate : G.site.equationSystem.RequiredCoordinate :=
    (⟨⟨(inverseCorePackageForwardUpper G.core f).equationMap
          (backward.equationMap coordinate.1.1),
        ((inverseCorePackageForwardUpper G.core f).required_iff _).mp
          ((backward.required_iff _).mp coordinate.1.2)⟩,
      (inverseCorePackageForwardUpper G.core f).atomEquiv
        (backward.atomEquiv coordinate.2)⟩)
  change K.geometry.requirements.requiredEquationCoordinate
    (requiredCoordinateMap tail forwardedCoordinate) at mapped
  have hforwarded : forwardedCoordinate = coordinate :=
    exactPullBackwardForwardRequiredCoordinate G f coordinate
  rw [hforwarded] at mapped
  exact mapped

/-- Selected violation coordinates are transported through the backward exact
upper map before applying the outgoing hom. -/
theorem exactPullOutgoingFactor_selectedViolationWitness
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (coordinate : G.site.equationSystem.Coordinate) :
    G.geometry.requirements.selectedViolationWitness coordinate →
      K.geometry.requirements.selectedViolationWitness
        (equationCoordinateMap tail coordinate) := by
  intro hreq
  let backward := inverseCorePackageBackwardUpper G.core f
  let sourceCoordinate :
      (UpperGeometryCleavage.exactSourceGeometry G f).site.equationSystem.Coordinate :=
    (backward.equationEquiv coordinate.1, backward.atomEquiv coordinate.2)
  have sourceReq :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.selectedViolationWitness
        sourceCoordinate := by
    change G.geometry.requirements.selectedViolationWitness
      ((inverseCorePackageForwardUpper G.core f).equationEquiv
          (backward.equationEquiv coordinate.1),
        (inverseCorePackageForwardUpper G.core f).atomEquiv
          (backward.atomEquiv coordinate.2))
    rw [exactPullBackwardForwardCoordinate G f coordinate]
    exact hreq
  have mapped := H.coverage.selectedViolationWitness sourceCoordinate sourceReq
  change K.geometry.requirements.selectedViolationWitness
    (equationCoordinateMap tail
      ((inverseCorePackageForwardUpper G.core f).equationEquiv
          (backward.equationEquiv coordinate.1),
        (inverseCorePackageForwardUpper G.core f).atomEquiv
          (backward.atomEquiv coordinate.2))) at mapped
  rw [exactPullBackwardForwardCoordinate G f coordinate] at mapped
  exact mapped

/-- Required axes are carried backward into the generated exact source and
then through the compatible outgoing hom. -/
theorem exactPullOutgoingFactor_requiredAxis
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (axis : G.core.algebra.signatureReading.Axis) :
    G.geometry.requirements.requiredAxis axis →
      K.geometry.requirements.requiredAxis (tail.upper.axisMap axis) := by
  intro hreq
  let backward := inverseCorePackageBackwardUpper G.core f
  have sourceReq :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.requiredAxis
        (backward.axisMap axis) := by
    change G.geometry.requirements.requiredAxis
      ((inverseCorePackageForwardUpper G.core f).axisMap
        (backward.axisMap axis))
    rw [exactPullBackwardForwardAxis G f axis]
    exact hreq
  have mapped := H.coverage.requiredAxis (backward.axisMap axis) sourceReq
  change K.geometry.requirements.requiredAxis
    (tail.upper.axisMap
      ((inverseCorePackageForwardUpper G.core f).axisMap
        (backward.axisMap axis))) at mapped
  rw [exactPullBackwardForwardAxis G f axis] at mapped
  exact mapped

/-- Support visibility is transported through the backward exact context and
then normalized by forward/backward context cancellation. -/
theorem exactPullOutgoingFactor_supportVisibleOn
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : Site.ArchCtx G.core.object) (atom : U.Atom) :
    G.geometry.requirements.supportVisibleOn W atom →
      K.geometry.requirements.supportVisibleOn
        (contextMap tail W) (tail.upper.atomEquiv atom) := by
  intro hvisible
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let backward := inverseCorePackageBackwardUpper G.core f
  let sourceW := contextBackward canonical (⟨W⟩ : G.site.category)
  have sourceVisible :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.supportVisibleOn
        sourceW.ctx (backward.atomEquiv atom) := by
    change G.geometry.requirements.supportVisibleOn
      (contextMap canonical sourceW.ctx)
      ((inverseCorePackageForwardUpper G.core f).atomEquiv
        (backward.atomEquiv atom))
    change G.geometry.requirements.supportVisibleOn
      (contextForward canonical sourceW).ctx _
    rw [UpperGeometryCleavage.generatedExactContextForward_backward_ctx,
      exactPullBackwardForwardAtom]
    exact hvisible
  have mapped := H.coverage.supportVisibleOn sourceW.ctx
    (backward.atomEquiv atom) sourceVisible
  change K.geometry.requirements.supportVisibleOn
    (contextMap tail W) (tail.upper.atomEquiv atom)
  change K.geometry.requirements.supportVisibleOn
    (contextForward tail ⟨W⟩).ctx (tail.upper.atomEquiv atom)
  change K.geometry.requirements.supportVisibleOn
    (contextForward
      (PackageTotalHom.comp canonical tail) sourceW).ctx
    (tail.upper.atomEquiv
      ((inverseCorePackageForwardUpper G.core f).atomEquiv
        (backward.atomEquiv atom))) at mapped
  rw [exactPullOutgoingFactorContext_eq G K f tail ⟨W⟩,
    exactPullBackwardForwardAtom G f atom] at mapped
  exact mapped

/-- Axis readability is transported through the backward exact context. -/
theorem exactPullOutgoingFactor_axisReadableOn
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : Site.ArchCtx G.core.object)
    (axis : G.core.algebra.signatureReading.Axis) :
    G.geometry.requirements.axisReadableOn W axis →
      K.geometry.requirements.axisReadableOn
        (contextMap tail W) (tail.upper.axisMap axis) := by
  intro hreadable
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let backward := inverseCorePackageBackwardUpper G.core f
  let sourceW := contextBackward canonical (⟨W⟩ : G.site.category)
  have sourceReadable :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.axisReadableOn
        sourceW.ctx (backward.axisMap axis) := by
    change G.geometry.requirements.axisReadableOn
      (contextForward canonical sourceW).ctx
      ((inverseCorePackageForwardUpper G.core f).axisMap
        (backward.axisMap axis))
    rw [UpperGeometryCleavage.generatedExactContextForward_backward_ctx,
      exactPullBackwardForwardAxis]
    exact hreadable
  have mapped := H.coverage.axisReadableOn sourceW.ctx
    (backward.axisMap axis) sourceReadable
  change K.geometry.requirements.axisReadableOn
    (contextForward (PackageTotalHom.comp canonical tail) sourceW).ctx
    (tail.upper.axisMap
      ((inverseCorePackageForwardUpper G.core f).axisMap
        (backward.axisMap axis))) at mapped
  change K.geometry.requirements.axisReadableOn
    (contextForward tail ⟨W⟩).ctx (tail.upper.axisMap axis)
  rw [exactPullOutgoingFactorContext_eq G K f tail ⟨W⟩,
    exactPullBackwardForwardAxis G f axis] at mapped
  exact mapped

/-- Boundary visibility is transported through both backward exact endpoint
contexts. -/
theorem exactPullOutgoingFactor_boundaryVisibleOn
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W V : Site.ArchCtx G.core.object) :
    G.geometry.requirements.boundaryVisibleOn W V →
      K.geometry.requirements.boundaryVisibleOn
        (contextMap tail W) (contextMap tail V) := by
  intro hvisible
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let sourceW := contextBackward canonical (⟨W⟩ : G.site.category)
  let sourceV := contextBackward canonical (⟨V⟩ : G.site.category)
  have sourceVisible :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.boundaryVisibleOn
        sourceW.ctx sourceV.ctx := by
    change G.geometry.requirements.boundaryVisibleOn
      (contextForward canonical sourceW).ctx
      (contextForward canonical sourceV).ctx
    rw [UpperGeometryCleavage.generatedExactContextForward_backward_ctx,
      UpperGeometryCleavage.generatedExactContextForward_backward_ctx]
    exact hvisible
  have mapped := H.coverage.boundaryVisibleOn sourceW.ctx sourceV.ctx sourceVisible
  change K.geometry.requirements.boundaryVisibleOn
    (contextForward (PackageTotalHom.comp canonical tail) sourceW).ctx
    (contextForward (PackageTotalHom.comp canonical tail) sourceV).ctx at mapped
  change K.geometry.requirements.boundaryVisibleOn
    (contextForward tail ⟨W⟩).ctx (contextForward tail ⟨V⟩).ctx
  rw [exactPullOutgoingFactorContext_eq G K f tail ⟨W⟩,
    exactPullOutgoingFactorContext_eq G K f tail ⟨V⟩] at mapped
  exact mapped

/-- Required-coordinate visibility is transported through the backward exact
context and coordinate maps. -/
theorem exactPullOutgoingFactor_equationCoordinateVisibleOn
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : Site.ArchCtx G.core.object)
    (coordinate : G.site.equationSystem.RequiredCoordinate) :
    G.geometry.requirements.equationCoordinateVisibleOn W coordinate →
      K.geometry.requirements.equationCoordinateVisibleOn
        (contextMap tail W) (requiredCoordinateMap tail coordinate) := by
  intro hvisible
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let backward := inverseCorePackageBackwardUpper G.core f
  let sourceW := contextBackward canonical (⟨W⟩ : G.site.category)
  let sourceCoordinate :
      (UpperGeometryCleavage.exactSourceGeometry G f).site.equationSystem.RequiredCoordinate :=
    (⟨backward.equationMap coordinate.1.1,
        (backward.required_iff coordinate.1.1).mp coordinate.1.2⟩,
      backward.atomEquiv coordinate.2)
  have sourceVisible :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.equationCoordinateVisibleOn
        sourceW.ctx sourceCoordinate := by
    change G.geometry.requirements.equationCoordinateVisibleOn
      (contextForward canonical sourceW).ctx
      (⟨⟨(inverseCorePackageForwardUpper G.core f).equationMap
          (backward.equationMap coordinate.1.1), _⟩,
        (inverseCorePackageForwardUpper G.core f).atomEquiv
          (backward.atomEquiv coordinate.2)⟩)
    rw [UpperGeometryCleavage.generatedExactContextForward_backward_ctx,
      exactPullBackwardForwardRequiredCoordinate]
    exact hvisible
  have mapped := H.coverage.equationCoordinateVisibleOn sourceW.ctx
    sourceCoordinate sourceVisible
  let forwardedCoordinate : G.site.equationSystem.RequiredCoordinate :=
    (⟨⟨(inverseCorePackageForwardUpper G.core f).equationMap
          (backward.equationMap coordinate.1.1),
        ((inverseCorePackageForwardUpper G.core f).required_iff _).mp
          ((backward.required_iff _).mp coordinate.1.2)⟩,
      (inverseCorePackageForwardUpper G.core f).atomEquiv
        (backward.atomEquiv coordinate.2)⟩)
  change K.geometry.requirements.equationCoordinateVisibleOn
    (contextForward (PackageTotalHom.comp canonical tail) sourceW).ctx
    (requiredCoordinateMap tail forwardedCoordinate) at mapped
  change K.geometry.requirements.equationCoordinateVisibleOn
    (contextForward tail ⟨W⟩).ctx (requiredCoordinateMap tail coordinate)
  have hforwarded : forwardedCoordinate = coordinate :=
    exactPullBackwardForwardRequiredCoordinate G f coordinate
  rw [exactPullOutgoingFactorContext_eq G K f tail ⟨W⟩,
    hforwarded] at mapped
  exact mapped

/-- Violation-coordinate visibility is transported through the backward exact
context and coordinate maps. -/
theorem exactPullOutgoingFactor_violationWitnessVisibleOn
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : Site.ArchCtx G.core.object)
    (coordinate : G.site.equationSystem.Coordinate) :
    G.geometry.requirements.violationWitnessVisibleOn W coordinate →
      K.geometry.requirements.violationWitnessVisibleOn
        (contextMap tail W) (equationCoordinateMap tail coordinate) := by
  intro hvisible
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let backward := inverseCorePackageBackwardUpper G.core f
  let sourceW := contextBackward canonical (⟨W⟩ : G.site.category)
  let sourceCoordinate :
      (UpperGeometryCleavage.exactSourceGeometry G f).site.equationSystem.Coordinate :=
    (backward.equationEquiv coordinate.1, backward.atomEquiv coordinate.2)
  have sourceVisible :
      (UpperGeometryCleavage.exactSourceGeometry G f).geometry.requirements.violationWitnessVisibleOn
        sourceW.ctx sourceCoordinate := by
    change G.geometry.requirements.violationWitnessVisibleOn
      (contextForward canonical sourceW).ctx
      ((inverseCorePackageForwardUpper G.core f).equationEquiv
          (backward.equationEquiv coordinate.1),
        (inverseCorePackageForwardUpper G.core f).atomEquiv
          (backward.atomEquiv coordinate.2))
    rw [UpperGeometryCleavage.generatedExactContextForward_backward_ctx,
      exactPullBackwardForwardCoordinate]
    exact hvisible
  have mapped := H.coverage.violationWitnessVisibleOn sourceW.ctx
    sourceCoordinate sourceVisible
  let forwardedCoordinate : G.site.equationSystem.Coordinate :=
    ((inverseCorePackageForwardUpper G.core f).equationEquiv
        (backward.equationEquiv coordinate.1),
      (inverseCorePackageForwardUpper G.core f).atomEquiv
        (backward.atomEquiv coordinate.2))
  change K.geometry.requirements.violationWitnessVisibleOn
    (contextForward (PackageTotalHom.comp canonical tail) sourceW).ctx
    (equationCoordinateMap tail forwardedCoordinate) at mapped
  change K.geometry.requirements.violationWitnessVisibleOn
    (contextForward tail ⟨W⟩).ctx (equationCoordinateMap tail coordinate)
  have hforwarded : forwardedCoordinate = coordinate :=
    exactPullBackwardForwardCoordinate G f coordinate
  rw [exactPullOutgoingFactorContext_eq G K f tail ⟨W⟩,
    hforwarded] at mapped
  exact mapped

/-- All nine coverage predicates of the direct outgoing factor. -/
def exactPullOutgoingFactorCoverage
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)) :
    CoverageTransport G K tail where
  requiredSupport := exactPullOutgoingFactor_requiredSupport G K f tail H
  requiredEquationCoordinate :=
    exactPullOutgoingFactor_requiredEquationCoordinate G K f tail H
  selectedViolationWitness :=
    exactPullOutgoingFactor_selectedViolationWitness G K f tail H
  requiredAxis := exactPullOutgoingFactor_requiredAxis G K f tail H
  supportVisibleOn := exactPullOutgoingFactor_supportVisibleOn G K f tail H
  equationCoordinateVisibleOn :=
    exactPullOutgoingFactor_equationCoordinateVisibleOn G K f tail H
  violationWitnessVisibleOn :=
    exactPullOutgoingFactor_violationWitnessVisibleOn G K f tail H
  axisReadableOn := exactPullOutgoingFactor_axisReadableOn G K f tail H
  boundaryVisibleOn := exactPullOutgoingFactor_boundaryVisibleOn G K f tail H

/-- Support component of the direct outgoing factor through the exact pull
lift. -/
noncomputable def exactPullOutgoingFactorSupportComp
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : G.site.category) :
    W.ctx.Support → (contextForward tail W).ctx.Support := fun support =>
  supportEquivOfContextEq (exactPullOutgoingFactorContext_eq G K f tail W)
    (H.supportComp (contextBackward (UpperGeometryCleavage.exactBaseHom G f) W)
      (supportEquivOfContextEq (exactPullBackwardContext_eq G f W)
        (UpperGeometryCleavage.exactBackwardSupportComp G f W support)))

/-- Axis component of the direct outgoing factor through the exact pull lift. -/
noncomputable def exactPullOutgoingFactorAxisComp
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : G.site.category) :
    W.ctx.Axis → (contextForward tail W).ctx.Axis := fun axis =>
  axisEquivOfContextEq (exactPullOutgoingFactorContext_eq G K f tail W)
    (H.axisComp (contextBackward (UpperGeometryCleavage.exactBaseHom G f) W)
      (axisEquivOfContextEq (exactPullBackwardContext_eq G f W)
        (UpperGeometryCleavage.exactBackwardAxisComp G f W axis)))

/-- Observable component of the direct outgoing factor through the exact pull
lift. -/
noncomputable def exactPullOutgoingFactorObservableComp
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : G.site.category) :
    W.ctx.Observable → (contextForward tail W).ctx.Observable := fun observable =>
  observableEquivOfContextEq (exactPullOutgoingFactorContext_eq G K f tail W)
    (H.observableComp
      (contextBackward (UpperGeometryCleavage.exactBaseHom G f) W)
      (observableEquivOfContextEq (exactPullBackwardContext_eq G f W)
        (UpperGeometryCleavage.exactBackwardObservableComp G f W observable)))

/-- The direct support factor preserves material support readings. -/
theorem exactPullOutgoingFactor_supportReads
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : G.site.category) (support : W.ctx.Support) (atom : U.Atom)
    (hread : W.ctx.minimal.supportReads support atom) :
    (contextForward tail W).ctx.minimal.supportReads
      (exactPullOutgoingFactorSupportComp G K f tail H W support)
      (tail.upper.atomEquiv atom) := by
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let backward := inverseCorePackageBackwardUpper G.core f
  let backwardSupport := UpperGeometryCleavage.exactBackwardSupportComp
    G f W support
  have backwardReads := UpperGeometryCleavage.exactBackwardSupportComp_reads
    G f W support atom hread
  have sourceReads :
      (contextBackward canonical W).ctx.minimal.supportReads
        (supportEquivOfContextEq (exactPullBackwardContext_eq G f W)
          backwardSupport) (backward.atomEquiv atom) := by
    exact (supportEquivOfContextEq_reads_iff
      (exactPullBackwardContext_eq G f W) backwardSupport
      (backward.atomEquiv atom)).2 backwardReads
  have mapped := H.supportReads (contextBackward canonical W)
    _ (backward.atomEquiv atom) sourceReads
  apply (supportEquivOfContextEq_reads_iff
    (exactPullOutgoingFactorContext_eq G K f tail W)
    (H.supportComp (contextBackward canonical W)
      (supportEquivOfContextEq (exactPullBackwardContext_eq G f W)
        backwardSupport))
    (tail.upper.atomEquiv atom)).2
  change (contextForward
    (PackageTotalHom.comp canonical tail) (contextBackward canonical W)).ctx.minimal.supportReads
      _ (tail.upper.atomEquiv atom)
  change (contextForward
    (PackageTotalHom.comp canonical tail) (contextBackward canonical W)).ctx.minimal.supportReads
      _ (tail.upper.atomEquiv
        ((inverseCorePackageForwardUpper G.core f).atomEquiv
          (backward.atomEquiv atom))) at mapped
  rw [exactPullBackwardForwardAtom G f atom] at mapped
  exact mapped

/-- The direct axis factor preserves material axis readings. -/
theorem exactPullOutgoingFactor_axisReads
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : G.site.category) (axis : W.ctx.Axis)
    (hread : W.ctx.minimal.axisReads axis) :
    (contextForward tail W).ctx.minimal.axisReads
      (exactPullOutgoingFactorAxisComp G K f tail H W axis) := by
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let backwardAxis := UpperGeometryCleavage.exactBackwardAxisComp G f W axis
  have backwardReads := UpperGeometryCleavage.exactBackwardAxisComp_reads
    G f W axis hread
  have sourceReads :
      (contextBackward canonical W).ctx.minimal.axisReads
        (axisEquivOfContextEq (exactPullBackwardContext_eq G f W)
          backwardAxis) := by
    exact (axisEquivOfContextEq_reads_iff
      (exactPullBackwardContext_eq G f W) backwardAxis).2 backwardReads
  have mapped := H.axisReads (contextBackward canonical W) _ sourceReads
  exact (axisEquivOfContextEq_reads_iff
    (exactPullOutgoingFactorContext_eq G K f tail W)
    (H.axisComp (contextBackward canonical W)
      (axisEquivOfContextEq (exactPullBackwardContext_eq G f W)
        backwardAxis))).2 mapped

/-- The direct observable factor preserves material observable readings. -/
theorem exactPullOutgoingFactor_observableReads
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    (W : G.site.category) (observable : W.ctx.Observable)
    (hread : W.ctx.minimal.observableReads observable) :
    (contextForward tail W).ctx.minimal.observableReads
      (exactPullOutgoingFactorObservableComp G K f tail H W observable) := by
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let backwardObservable :=
    UpperGeometryCleavage.exactBackwardObservableComp G f W observable
  have backwardReads :=
    UpperGeometryCleavage.exactBackwardObservableComp_reads
      G f W observable hread
  have sourceReads :
      (contextBackward canonical W).ctx.minimal.observableReads
        (observableEquivOfContextEq (exactPullBackwardContext_eq G f W)
          backwardObservable) := by
    exact (observableEquivOfContextEq_reads_iff
      (exactPullBackwardContext_eq G f W) backwardObservable).2 backwardReads
  have mapped := H.observableReads (contextBackward canonical W) _ sourceReads
  exact (observableEquivOfContextEq_reads_iff
    (exactPullOutgoingFactorContext_eq G K f tail W)
    (H.observableComp (contextBackward canonical W)
      (observableEquivOfContextEq (exactPullBackwardContext_eq G f W)
        backwardObservable))).2 mapped

/-- Raw compatibility of the direct factor follows from composition of raw
transport and the exact source's generated forward cancellation. -/
theorem exactPullOutgoingFactor_raw_eq
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)) :
    K.raw = rawTransport tail H.coefficientHom := by
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  calc
    K.raw = rawTransport (PackageTotalHom.comp canonical tail)
        H.coefficientHom := H.raw_eq
    _ = rawTransport tail H.coefficientHom := by
      rw [show H.coefficientHom = H.coefficientHom.comp
          (RingHom.id G.Coefficient) by ext; rfl]
      rw [rawTransport_comp canonical tail]
      rw [show rawTransport canonical (RingHom.id G.Coefficient) = G.raw from
        (UpperGeometryCleavage.exactSourceGeometry_raw_forward G f).symm]
      rfl

/-- Selected overlaps for the direct factor are obtained from the composite
overlap after exact forward/backward context cancellation. -/
noncomputable def exactPullOutgoingFactorOverlap
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)) :
    OverlapTransport G K tail where
  overlapIso base left right := by
    let canonical := UpperGeometryCleavage.exactBaseHom G f
    refine (eqToIso ?_).trans (H.overlap.overlapIso base left right)
    apply contextObject_eq_of_ctx_eq
    change (contextForward tail
      ⟨G.geometry.overlap.overlap
        (contextBackwardMap tail base)
        (contextBackwardMap tail left)
        (contextBackwardMap tail right)⟩).ctx =
      (contextForward (PackageTotalHom.comp canonical tail)
        ⟨(UpperGeometryCleavage.exactSourceGeometry G f).geometry.overlap.overlap
          (contextBackwardMap (PackageTotalHom.comp canonical tail) base)
          (contextBackwardMap (PackageTotalHom.comp canonical tail) left)
          (contextBackwardMap (PackageTotalHom.comp canonical tail) right)⟩).ctx
    rw [contextForward_comp]
    apply congrArg (fun Z => (contextForward tail Z).ctx)
    apply contextObject_eq_of_ctx_eq
    rw [UpperGeometryCleavage.exactSourceGeometry_overlap]
    simp only [contextBackwardMap, contextBackward_comp]
    dsimp only [canonical]
    have hbase :
        (⟨(contextBackward (UpperGeometryCleavage.exactBaseHom G f)
          (contextBackward tail ⟨base⟩)).ctx⟩ :
          (UpperGeometryCleavage.exactSourceGeometry G f).site.category) =
        contextBackward (UpperGeometryCleavage.exactBaseHom G f)
          (contextBackward tail ⟨base⟩) := by
      apply contextObject_eq_of_ctx_eq
      rfl
    have hleft :
        (⟨(contextBackward (UpperGeometryCleavage.exactBaseHom G f)
          (contextBackward tail ⟨left⟩)).ctx⟩ :
          (UpperGeometryCleavage.exactSourceGeometry G f).site.category) =
        contextBackward (UpperGeometryCleavage.exactBaseHom G f)
          (contextBackward tail ⟨left⟩) := by
      apply contextObject_eq_of_ctx_eq
      rfl
    have hright :
        (⟨(contextBackward (UpperGeometryCleavage.exactBaseHom G f)
          (contextBackward tail ⟨right⟩)).ctx⟩ :
          (UpperGeometryCleavage.exactSourceGeometry G f).site.category) =
        contextBackward (UpperGeometryCleavage.exactBaseHom G f)
          (contextBackward tail ⟨right⟩) := by
      apply contextObject_eq_of_ctx_eq
      rfl
    rw [hbase, hleft, hright]
    rw [UpperGeometryCleavage.generatedExactContextForward_backward_ctx,
      UpperGeometryCleavage.generatedExactContextForward_backward_ctx,
      UpperGeometryCleavage.generatedExactContextForward_backward_ctx]
    exact (UpperGeometryCleavage.generatedExactContextForward_backward_ctx G f
      ⟨G.geometry.overlap.overlap
        (contextBackward tail ⟨base⟩).ctx
        (contextBackward tail ⟨left⟩).ctx
        (contextBackward tail ⟨right⟩).ctx⟩).symm

/-- The support component of the direct factor is natural in the target
geometry context. -/
theorem exactPullOutgoingFactor_support_naturality
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    {W V : G.site.category} (w : W ⟶ V) (support : W.ctx.Support) :
    (targetContextMorphism (f := tail) w).supportMap
        (exactPullOutgoingFactorSupportComp G K f tail H W support) =
      exactPullOutgoingFactorSupportComp G K f tail H V
        ((sourceContextMorphism w).supportMap support) := by
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let inverseArrow := (contextInverse canonical).map w
  let backwardW := UpperGeometryCleavage.exactBackwardSupportComp G f W support
  have innerNaturality :
      ((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
        (leOfHom inverseArrow)).supportMap
          (supportEquivOfContextEq (exactPullBackwardContext_eq G f W)
            backwardW) =
        supportEquivOfContextEq (exactPullBackwardContext_eq G f V)
          (UpperGeometryCleavage.exactBackwardSupportComp G f V
            ((sourceContextMorphism w).supportMap support)) := by
    calc
      _ = supportEquivOfContextEq (exactPullBackwardContext_eq G f V)
          (((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
            (leOfHom ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w))).supportMap
              backwardW) :=
        supportEquivOfContextEq_naturality
          (exactPullBackwardContext_eq G f W)
          (exactPullBackwardContext_eq G f V)
          ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w)
          inverseArrow backwardW
      _ = _ := congrArg (supportEquivOfContextEq
          (exactPullBackwardContext_eq G f V))
        (UpperGeometryCleavage.exactBackwardSupportComp_naturality
          G f w support)
  unfold exactPullOutgoingFactorSupportComp
  calc
    _ = supportEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail V)
        ((K.core.contextPreorder.morphism
          (leOfHom ((contextFunctor
            (PackageTotalHom.comp canonical tail)).map inverseArrow))).supportMap
          (H.supportComp (contextBackward canonical W)
            (supportEquivOfContextEq (exactPullBackwardContext_eq G f W)
              backwardW))) :=
      supportEquivOfContextEq_naturality
        (exactPullOutgoingFactorContext_eq G K f tail W)
        (exactPullOutgoingFactorContext_eq G K f tail V)
        ((contextFunctor (PackageTotalHom.comp canonical tail)).map inverseArrow)
        ((contextFunctor tail).map w) _
    _ = supportEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail V)
        (H.supportComp (contextBackward canonical V)
          (((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
            (leOfHom inverseArrow)).supportMap
            (supportEquivOfContextEq (exactPullBackwardContext_eq G f W)
              backwardW))) := by
      exact congrArg (supportEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail V))
          (H.support_naturality inverseArrow _)
    _ = _ := congrArg
      (fun x => supportEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail V)
        (H.supportComp (contextBackward canonical V) x)) innerNaturality

/-- The axis component of the direct factor is natural in the target geometry
context. -/
theorem exactPullOutgoingFactor_axis_naturality
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    {W V : G.site.category} (w : W ⟶ V) (axis : W.ctx.Axis) :
    (targetContextMorphism (f := tail) w).axisMap
        (exactPullOutgoingFactorAxisComp G K f tail H W axis) =
      exactPullOutgoingFactorAxisComp G K f tail H V
        ((sourceContextMorphism w).axisMap axis) := by
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let inverseArrow := (contextInverse canonical).map w
  let backwardW := UpperGeometryCleavage.exactBackwardAxisComp G f W axis
  have innerNaturality :
      ((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
        (leOfHom inverseArrow)).axisMap
          (axisEquivOfContextEq (exactPullBackwardContext_eq G f W)
            backwardW) =
        axisEquivOfContextEq (exactPullBackwardContext_eq G f V)
          (UpperGeometryCleavage.exactBackwardAxisComp G f V
            ((sourceContextMorphism w).axisMap axis)) := by
    calc
      _ = axisEquivOfContextEq (exactPullBackwardContext_eq G f V)
          (((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
            (leOfHom ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w))).axisMap
              backwardW) :=
        axisEquivOfContextEq_naturality
          (exactPullBackwardContext_eq G f W)
          (exactPullBackwardContext_eq G f V)
          ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w)
          inverseArrow backwardW
      _ = _ := congrArg (axisEquivOfContextEq
          (exactPullBackwardContext_eq G f V))
        (UpperGeometryCleavage.exactBackwardAxisComp_naturality G f w axis)
  unfold exactPullOutgoingFactorAxisComp
  calc
    _ = axisEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail V)
        ((K.core.contextPreorder.morphism
          (leOfHom ((contextFunctor
            (PackageTotalHom.comp canonical tail)).map inverseArrow))).axisMap
          (H.axisComp (contextBackward canonical W)
            (axisEquivOfContextEq (exactPullBackwardContext_eq G f W)
              backwardW))) :=
      axisEquivOfContextEq_naturality
        (exactPullOutgoingFactorContext_eq G K f tail W)
        (exactPullOutgoingFactorContext_eq G K f tail V)
        ((contextFunctor (PackageTotalHom.comp canonical tail)).map inverseArrow)
        ((contextFunctor tail).map w) _
    _ = axisEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail V)
        (H.axisComp (contextBackward canonical V)
          (((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
            (leOfHom inverseArrow)).axisMap
            (axisEquivOfContextEq (exactPullBackwardContext_eq G f W)
              backwardW))) := by
      exact congrArg (axisEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail V))
          (H.axis_naturality inverseArrow _)
    _ = _ := congrArg
      (fun x => axisEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail V)
        (H.axisComp (contextBackward canonical V) x)) innerNaturality

/-- The observable component of the direct factor is natural in the
contravariant observable direction. -/
theorem exactPullOutgoingFactor_observable_naturality
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail))
    {W V : G.site.category} (w : W ⟶ V) (observable : V.ctx.Observable) :
    (targetContextMorphism (f := tail) w).observableRestrict
        (exactPullOutgoingFactorObservableComp G K f tail H V observable) =
      exactPullOutgoingFactorObservableComp G K f tail H W
        ((sourceContextMorphism w).observableRestrict observable) := by
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let inverseArrow := (contextInverse canonical).map w
  let backwardV :=
    UpperGeometryCleavage.exactBackwardObservableComp G f V observable
  have innerNaturality :
      ((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
        (leOfHom inverseArrow)).observableRestrict
          (observableEquivOfContextEq (exactPullBackwardContext_eq G f V)
            backwardV) =
        observableEquivOfContextEq (exactPullBackwardContext_eq G f W)
          (UpperGeometryCleavage.exactBackwardObservableComp G f W
            ((sourceContextMorphism w).observableRestrict observable)) := by
    calc
      _ = observableEquivOfContextEq (exactPullBackwardContext_eq G f W)
          (((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
            (leOfHom ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w))).observableRestrict
              backwardV) :=
        observableEquivOfContextEq_naturality
          (exactPullBackwardContext_eq G f W)
          (exactPullBackwardContext_eq G f V)
          ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w)
          inverseArrow backwardV
      _ = _ := congrArg (observableEquivOfContextEq
          (exactPullBackwardContext_eq G f W))
        (UpperGeometryCleavage.exactBackwardObservableComp_naturality
          G f w observable)
  unfold exactPullOutgoingFactorObservableComp
  calc
    _ = observableEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail W)
        ((K.core.contextPreorder.morphism
          (leOfHom ((contextFunctor
            (PackageTotalHom.comp canonical tail)).map inverseArrow))).observableRestrict
          (H.observableComp (contextBackward canonical V)
            (observableEquivOfContextEq (exactPullBackwardContext_eq G f V)
              backwardV))) :=
      observableEquivOfContextEq_naturality
        (exactPullOutgoingFactorContext_eq G K f tail W)
        (exactPullOutgoingFactorContext_eq G K f tail V)
        ((contextFunctor (PackageTotalHom.comp canonical tail)).map inverseArrow)
        ((contextFunctor tail).map w) _
    _ = observableEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail W)
        (H.observableComp (contextBackward canonical W)
          (((UpperGeometryCleavage.exactSourceGeometry G f).core.contextPreorder.morphism
            (leOfHom inverseArrow)).observableRestrict
            (observableEquivOfContextEq (exactPullBackwardContext_eq G f V)
              backwardV))) := by
      exact congrArg (observableEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail W))
          (H.observable_naturality inverseArrow _)
    _ = _ := congrArg
      (fun x => observableEquivOfContextEq
        (exactPullOutgoingFactorContext_eq G K f tail W)
        (H.observableComp (contextBackward canonical W) x)) innerNaturality

/-- The complete geometry-reading factor for an outgoing hom through the
generated exact pull lift. -/
noncomputable def exactPullOutgoingFactorGeomReadHom
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)) :
    GeomReadHom G K tail where
  coverage := exactPullOutgoingFactorCoverage G K f tail H
  overlap := exactPullOutgoingFactorOverlap G K f tail H
  coefficientHom := H.coefficientHom
  raw_eq := exactPullOutgoingFactor_raw_eq G K f tail H
  supportComp := exactPullOutgoingFactorSupportComp G K f tail H
  axisComp := exactPullOutgoingFactorAxisComp G K f tail H
  observableComp := exactPullOutgoingFactorObservableComp G K f tail H
  supportReads := exactPullOutgoingFactor_supportReads G K f tail H
  axisReads := exactPullOutgoingFactor_axisReads G K f tail H
  observableReads := exactPullOutgoingFactor_observableReads G K f tail H
  support_naturality :=
    exactPullOutgoingFactor_support_naturality G K f tail H
  axis_naturality := exactPullOutgoingFactor_axis_naturality G K f tail H
  observable_naturality :=
    exactPullOutgoingFactor_observable_naturality G K f tail H

/-- The total outgoing factor over the supplied lower package tail. -/
noncomputable def exactPullOutgoingTotalFactor
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (h : GeometryTotalHom
      (UpperGeometryCleavage.exactSourceGeometry G f) K)
    (hbase : h.base = PackageTotalHom.comp
      (UpperGeometryCleavage.exactBaseHom G f) tail) :
    GeometryTotalHom G K where
  base := tail
  geometry := exactPullOutgoingFactorGeomReadHom G K f tail
    (GeomReadHom.castBase hbase h.geometry)

@[simp] theorem exactPullOutgoingTotalFactor_base
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (h : GeometryTotalHom
      (UpperGeometryCleavage.exactSourceGeometry G f) K)
    (hbase : h.base = PackageTotalHom.comp
      (UpperGeometryCleavage.exactBaseHom G f) tail) :
    (exactPullOutgoingTotalFactor G K f tail h hbase).base = tail := rfl

/-- Support components cancel after precomposition with the generated exact
forward geometry hom. -/
theorem exactPullOutgoingFactor_support_fac
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)) :
    HEq
      (GeomReadHom.comp (UpperGeometryCleavage.generatedExactGeomReadHom G f)
        (exactPullOutgoingFactorGeomReadHom G K f tail H)).supportComp
      H.supportComp := by
  apply heq_of_eq
  funext W support
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let exactness := UpperGeometryCleavage.exactInversePackageRealizationExact G f
  let hbackUpper :=
    (UpperGeometryCleavage.exactInversePackageUpperEquivalence G f).forwardBackwardContext W
  have hback : contextBackward canonical (contextForward canonical W) = W := by
    apply contextObject_eq_of_ctx_eq
    calc
      _ = ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
          (contextForward canonical W)).ctx :=
        congrArg (fun Z => Z.ctx)
          (exactPullBackwardContext_eq G f (contextForward canonical W)).symm
      _ = W.ctx := congrArg (fun Z => Z.ctx) hbackUpper
  let sourceSupport :
      (contextBackward canonical (contextForward canonical W)).ctx.Support :=
    supportEquivOfContextEq
      (exactPullBackwardContext_eq G f (contextForward canonical W))
      (UpperGeometryCleavage.exactBackwardSupportComp G f
        (contextForward canonical W)
        (UpperGeometryCleavage.generatedExactSupportComp G f W support))
  change supportEquivOfContextEq
      (exactPullOutgoingFactorContext_eq G K f tail
        (contextForward canonical W))
      (H.supportComp (contextBackward canonical (contextForward canonical W))
        sourceSupport) = H.supportComp W support
  have htarget :
      exactPullOutgoingFactorContext_eq G K f tail
          (contextForward canonical W) =
        congrArg
          (fun Z => contextForward
            (PackageTotalHom.comp canonical tail) Z) hback := by
    apply Subsingleton.elim
  rw [htarget]
  calc
    _ = H.supportComp W (supportEquivOfContextEq hback sourceSupport) := by
      simpa [canonical] using
        (supportEquivOfContextEq_family
          (fun Z => contextForward (PackageTotalHom.comp canonical tail) Z)
          H.supportComp hback sourceSupport)
    _ = H.supportComp W support := by
      apply congrArg (H.supportComp W)
      apply eq_of_heq
      unfold supportEquivOfContextEq sourceSupport
      exact (cast_heq _ _).trans ((cast_heq _ _).trans
        ((UpperGeometryCleavage.exactBackwardSupportComp_heq G f _
          (UpperGeometryCleavage.generatedExactSupportComp G f W support)).trans
        (UpperGeometryCleavage.generatedExactSupportComp_heq G f W support)))

/-- Axis components cancel after precomposition with the generated exact
forward geometry hom. -/
theorem exactPullOutgoingFactor_axis_fac
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)) :
    HEq
      (GeomReadHom.comp (UpperGeometryCleavage.generatedExactGeomReadHom G f)
        (exactPullOutgoingFactorGeomReadHom G K f tail H)).axisComp
      H.axisComp := by
  apply heq_of_eq
  funext W axis
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let exactness := UpperGeometryCleavage.exactInversePackageRealizationExact G f
  let hbackUpper :=
    (UpperGeometryCleavage.exactInversePackageUpperEquivalence G f).forwardBackwardContext W
  have hback : contextBackward canonical (contextForward canonical W) = W := by
    apply contextObject_eq_of_ctx_eq
    calc
      _ = ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
          (contextForward canonical W)).ctx :=
        congrArg (fun Z => Z.ctx)
          (exactPullBackwardContext_eq G f (contextForward canonical W)).symm
      _ = W.ctx := congrArg (fun Z => Z.ctx) hbackUpper
  let sourceAxis :
      (contextBackward canonical (contextForward canonical W)).ctx.Axis :=
    axisEquivOfContextEq
      (exactPullBackwardContext_eq G f (contextForward canonical W))
      (UpperGeometryCleavage.exactBackwardAxisComp G f
        (contextForward canonical W)
        (UpperGeometryCleavage.generatedExactAxisComp G f W axis))
  change axisEquivOfContextEq
      (exactPullOutgoingFactorContext_eq G K f tail
        (contextForward canonical W))
      (H.axisComp (contextBackward canonical (contextForward canonical W))
        sourceAxis) = H.axisComp W axis
  have htarget :
      exactPullOutgoingFactorContext_eq G K f tail
          (contextForward canonical W) =
        congrArg
          (fun Z => contextForward
            (PackageTotalHom.comp canonical tail) Z) hback := by
    apply Subsingleton.elim
  rw [htarget]
  calc
    _ = H.axisComp W (axisEquivOfContextEq hback sourceAxis) := by
      simpa [canonical] using
        (axisEquivOfContextEq_family
          (fun Z => contextForward (PackageTotalHom.comp canonical tail) Z)
          H.axisComp hback sourceAxis)
    _ = H.axisComp W axis := by
      apply congrArg (H.axisComp W)
      apply eq_of_heq
      unfold axisEquivOfContextEq sourceAxis
      exact (cast_heq _ _).trans ((cast_heq _ _).trans
        ((UpperGeometryCleavage.exactBackwardAxisComp_heq G f _
          (UpperGeometryCleavage.generatedExactAxisComp G f W axis)).trans
        (UpperGeometryCleavage.generatedExactAxisComp_heq G f W axis)))

/-- Observable components cancel after precomposition with the generated
exact forward geometry hom. -/
theorem exactPullOutgoingFactor_observable_fac
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)) :
    HEq
      (GeomReadHom.comp (UpperGeometryCleavage.generatedExactGeomReadHom G f)
        (exactPullOutgoingFactorGeomReadHom G K f tail H)).observableComp
      H.observableComp := by
  apply heq_of_eq
  funext W observable
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  let exactness := UpperGeometryCleavage.exactInversePackageRealizationExact G f
  let hbackUpper :=
    (UpperGeometryCleavage.exactInversePackageUpperEquivalence G f).forwardBackwardContext W
  have hback : contextBackward canonical (contextForward canonical W) = W := by
    apply contextObject_eq_of_ctx_eq
    calc
      _ = ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
          (contextForward canonical W)).ctx :=
        congrArg (fun Z => Z.ctx)
          (exactPullBackwardContext_eq G f (contextForward canonical W)).symm
      _ = W.ctx := congrArg (fun Z => Z.ctx) hbackUpper
  let sourceObservable :
      (contextBackward canonical (contextForward canonical W)).ctx.Observable :=
    observableEquivOfContextEq
      (exactPullBackwardContext_eq G f (contextForward canonical W))
      (UpperGeometryCleavage.exactBackwardObservableComp G f
        (contextForward canonical W)
        (UpperGeometryCleavage.generatedExactObservableComp G f W observable))
  change observableEquivOfContextEq
      (exactPullOutgoingFactorContext_eq G K f tail
        (contextForward canonical W))
      (H.observableComp
        (contextBackward canonical (contextForward canonical W))
        sourceObservable) = H.observableComp W observable
  have htarget :
      exactPullOutgoingFactorContext_eq G K f tail
          (contextForward canonical W) =
        congrArg
          (fun Z => contextForward
            (PackageTotalHom.comp canonical tail) Z) hback := by
    apply Subsingleton.elim
  rw [htarget]
  calc
    _ = H.observableComp W
        (observableEquivOfContextEq hback sourceObservable) := by
      simpa [canonical] using
        (observableEquivOfContextEq_family
          (fun Z => contextForward (PackageTotalHom.comp canonical tail) Z)
          H.observableComp hback sourceObservable)
    _ = H.observableComp W observable := by
      apply congrArg (H.observableComp W)
      apply eq_of_heq
      unfold observableEquivOfContextEq sourceObservable
      exact (cast_heq _ _).trans ((cast_heq _ _).trans
        ((UpperGeometryCleavage.exactBackwardObservableComp_heq G f _
          (UpperGeometryCleavage.generatedExactObservableComp G f W observable)).trans
        (UpperGeometryCleavage.generatedExactObservableComp_heq
          G f W observable)))

/-- The direct outgoing geometry factor composes with the generated exact
geometry hom to the supplied composite reading. -/
theorem exactPullOutgoingFactorGeomReadHom_fac
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (H : GeomReadHom (UpperGeometryCleavage.exactSourceGeometry G f) K
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)) :
    GeomReadHom.comp (UpperGeometryCleavage.generatedExactGeomReadHom G f)
      (exactPullOutgoingFactorGeomReadHom G K f tail H) = H := by
  apply GeomReadHom.ext
  · rfl
  · exact exactPullOutgoingFactor_support_fac G K f tail H
  · exact exactPullOutgoingFactor_axis_fac G K f tail H
  · exact exactPullOutgoingFactor_observable_fac G K f tail H

/-- The generated exact pull lift followed by its direct total factor is the
authored outgoing hom. -/
theorem exactPullOutgoingTotalFactor_fac
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (h : GeometryTotalHom
      (UpperGeometryCleavage.exactSourceGeometry G f) K)
    (hbase : h.base = PackageTotalHom.comp
      (UpperGeometryCleavage.exactBaseHom G f) tail) :
    GeometryTotalHom.comp (UpperGeometryCleavage.generatedExactGeometryHom G f)
      (exactPullOutgoingTotalFactor G K f tail h hbase) = h := by
  apply GeometryTotalHom.ext
  · exact hbase.symm
  · exact (heq_of_eq (exactPullOutgoingFactorGeomReadHom_fac G K f tail
      (GeomReadHom.castBase hbase h.geometry))).trans
        (geomReadHom_castBase_heq hbase h.geometry)

/-- Applying the direct factor construction to a composite recovers the
original support comparison. -/
theorem exactPullOutgoingFactor_support_of_composite
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core) (T : GeomReadHom G K tail) :
    HEq
      (exactPullOutgoingFactorGeomReadHom G K f tail
        (GeomReadHom.comp
          (UpperGeometryCleavage.generatedExactGeomReadHom G f) T)).supportComp
      T.supportComp := by
  apply heq_of_eq
  funext W support
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  have hsection : contextForward canonical (contextBackward canonical W) = W := by
    apply contextObject_eq_of_ctx_eq
    exact UpperGeometryCleavage.generatedExactContextForward_backward_ctx G f W
  let sourceSupport : (contextBackward canonical W).ctx.Support :=
    supportEquivOfContextEq (exactPullBackwardContext_eq G f W)
      (UpperGeometryCleavage.exactBackwardSupportComp G f W support)
  let transportedSupport := UpperGeometryCleavage.generatedExactSupportComp
    G f (contextBackward canonical W) sourceSupport
  change supportEquivOfContextEq
      (exactPullOutgoingFactorContext_eq G K f tail W)
      (T.supportComp (contextForward canonical (contextBackward canonical W))
        transportedSupport) = T.supportComp W support
  have htarget : exactPullOutgoingFactorContext_eq G K f tail W =
      congrArg (fun Z => contextForward tail Z) hsection := by
    apply Subsingleton.elim
  rw [htarget]
  calc
    _ = T.supportComp W
        (supportEquivOfContextEq hsection transportedSupport) := by
      exact supportEquivOfContextEq_family
        (fun Z => contextForward tail Z) T.supportComp hsection
          transportedSupport
    _ = T.supportComp W support := by
      apply congrArg (T.supportComp W)
      apply eq_of_heq
      unfold supportEquivOfContextEq transportedSupport sourceSupport
      exact (cast_heq _ _).trans
        ((UpperGeometryCleavage.generatedExactSupportComp_heq G f _ _).trans
          ((cast_heq _ _).trans
            (UpperGeometryCleavage.exactBackwardSupportComp_heq
              G f W support)))

/-- Applying the direct factor construction to a composite recovers the
original axis comparison. -/
theorem exactPullOutgoingFactor_axis_of_composite
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core) (T : GeomReadHom G K tail) :
    HEq
      (exactPullOutgoingFactorGeomReadHom G K f tail
        (GeomReadHom.comp
          (UpperGeometryCleavage.generatedExactGeomReadHom G f) T)).axisComp
      T.axisComp := by
  apply heq_of_eq
  funext W axis
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  have hsection : contextForward canonical (contextBackward canonical W) = W := by
    apply contextObject_eq_of_ctx_eq
    exact UpperGeometryCleavage.generatedExactContextForward_backward_ctx G f W
  let sourceAxis : (contextBackward canonical W).ctx.Axis :=
    axisEquivOfContextEq (exactPullBackwardContext_eq G f W)
      (UpperGeometryCleavage.exactBackwardAxisComp G f W axis)
  let transportedAxis := UpperGeometryCleavage.generatedExactAxisComp
    G f (contextBackward canonical W) sourceAxis
  change axisEquivOfContextEq
      (exactPullOutgoingFactorContext_eq G K f tail W)
      (T.axisComp (contextForward canonical (contextBackward canonical W))
        transportedAxis) = T.axisComp W axis
  have htarget : exactPullOutgoingFactorContext_eq G K f tail W =
      congrArg (fun Z => contextForward tail Z) hsection := by
    apply Subsingleton.elim
  rw [htarget]
  calc
    _ = T.axisComp W (axisEquivOfContextEq hsection transportedAxis) := by
      exact axisEquivOfContextEq_family
        (fun Z => contextForward tail Z) T.axisComp hsection transportedAxis
    _ = T.axisComp W axis := by
      apply congrArg (T.axisComp W)
      apply eq_of_heq
      unfold axisEquivOfContextEq transportedAxis sourceAxis
      exact (cast_heq _ _).trans
        ((UpperGeometryCleavage.generatedExactAxisComp_heq G f _ _).trans
          ((cast_heq _ _).trans
            (UpperGeometryCleavage.exactBackwardAxisComp_heq G f W axis)))

/-- Applying the direct factor construction to a composite recovers the
original observable comparison. -/
theorem exactPullOutgoingFactor_observable_of_composite
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core) (T : GeomReadHom G K tail) :
    HEq
      (exactPullOutgoingFactorGeomReadHom G K f tail
        (GeomReadHom.comp
          (UpperGeometryCleavage.generatedExactGeomReadHom G f) T)).observableComp
      T.observableComp := by
  apply heq_of_eq
  funext W observable
  let canonical := UpperGeometryCleavage.exactBaseHom G f
  have hsection : contextForward canonical (contextBackward canonical W) = W := by
    apply contextObject_eq_of_ctx_eq
    exact UpperGeometryCleavage.generatedExactContextForward_backward_ctx G f W
  let sourceObservable : (contextBackward canonical W).ctx.Observable :=
    observableEquivOfContextEq (exactPullBackwardContext_eq G f W)
      (UpperGeometryCleavage.exactBackwardObservableComp G f W observable)
  let transportedObservable := UpperGeometryCleavage.generatedExactObservableComp
    G f (contextBackward canonical W) sourceObservable
  change observableEquivOfContextEq
      (exactPullOutgoingFactorContext_eq G K f tail W)
      (T.observableComp
        (contextForward canonical (contextBackward canonical W))
        transportedObservable) = T.observableComp W observable
  have htarget : exactPullOutgoingFactorContext_eq G K f tail W =
      congrArg (fun Z => contextForward tail Z) hsection := by
    apply Subsingleton.elim
  rw [htarget]
  calc
    _ = T.observableComp W
        (observableEquivOfContextEq hsection transportedObservable) := by
      exact observableEquivOfContextEq_family
        (fun Z => contextForward tail Z) T.observableComp hsection
          transportedObservable
    _ = T.observableComp W observable := by
      apply congrArg (T.observableComp W)
      apply eq_of_heq
      unfold observableEquivOfContextEq transportedObservable sourceObservable
      exact (cast_heq _ _).trans
        ((UpperGeometryCleavage.generatedExactObservableComp_heq G f _ _).trans
          ((cast_heq _ _).trans
            (UpperGeometryCleavage.exactBackwardObservableComp_heq
              G f W observable)))

/-- Factoring a composite through the generated exact pull lift reconstructs
the original geometry-reading hom. -/
theorem exactPullOutgoingFactor_of_composite
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core) (T : GeomReadHom G K tail) :
    exactPullOutgoingFactorGeomReadHom G K f tail
        (GeomReadHom.comp
          (UpperGeometryCleavage.generatedExactGeomReadHom G f) T) = T := by
  apply GeomReadHom.ext
  · rfl
  · exact exactPullOutgoingFactor_support_of_composite G K f tail T
  · exact exactPullOutgoingFactor_axis_of_composite G K f tail T
  · exact exactPullOutgoingFactor_observable_of_composite G K f tail T

private theorem exactPull_comp_castBase_heq
    {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {first : PackageTotalHom G.core H.core}
    {second second' : PackageTotalHom H.core K.core}
    (hsecond : second = second') (head : GeomReadHom G H first)
    (tail : GeomReadHom H K second) :
    HEq (GeomReadHom.comp head (GeomReadHom.castBase hsecond tail))
      (GeomReadHom.comp head tail) := by
  cases hsecond
  rfl

private theorem exactPull_geometry_heq_of_total_eq
    {U : AtomCarrier.{u}}
    {G K : GeometryPackage.{u, v} U}
    {first second : GeometryTotalHom G K} (h : first = second) :
    HEq first.geometry second.geometry := by
  cases h
  rfl

/-- Any outgoing total factor over the fixed lower tail equals the directly
constructed factor. -/
theorem exactPullOutgoingTotalFactor_unique
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (h : GeometryTotalHom
      (UpperGeometryCleavage.exactSourceGeometry G f) K)
    (hbase : h.base = PackageTotalHom.comp
      (UpperGeometryCleavage.exactBaseHom G f) tail)
    (candidate : GeometryTotalHom G K)
    (candidateBase : candidate.base = tail)
    (candidateFac : GeometryTotalHom.comp
      (UpperGeometryCleavage.generatedExactGeometryHom G f) candidate = h) :
    candidate = exactPullOutgoingTotalFactor G K f tail h hbase := by
  let canonicalGeometry := UpperGeometryCleavage.generatedExactGeomReadHom G f
  let candidateGeometry :=
    GeomReadHom.castBase candidateBase candidate.geometry
  let normalizedH := GeomReadHom.castBase hbase h.geometry
  have hnormalized :
      GeomReadHom.comp canonicalGeometry candidateGeometry = normalizedH := by
    apply eq_of_heq
    exact ((exactPull_comp_castBase_heq candidateBase canonicalGeometry
      candidate.geometry).trans
        (exactPull_geometry_heq_of_total_eq candidateFac)).trans
      (geomReadHom_castBase_heq hbase h.geometry).symm
  have hcandidateGeometry : candidateGeometry =
      exactPullOutgoingFactorGeomReadHom G K f tail normalizedH := by
    calc
      candidateGeometry = exactPullOutgoingFactorGeomReadHom G K f tail
          (GeomReadHom.comp canonicalGeometry candidateGeometry) :=
        (exactPullOutgoingFactor_of_composite
          G K f tail candidateGeometry).symm
      _ = exactPullOutgoingFactorGeomReadHom G K f tail normalizedH :=
        congrArg (exactPullOutgoingFactorGeomReadHom G K f tail) hnormalized
  apply GeometryTotalHom.ext
  · exact candidateBase
  · exact (geomReadHom_castBase_heq candidateBase candidate.geometry).symm.trans
      (heq_of_eq hcandidateGeometry)

/-- Direct existence and uniqueness of the outgoing geometry factor through
the generated exact pull lift. -/
theorem exactPullOutgoingFactor_existsUnique
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G K : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (tail : PackageTotalHom G.core K.core)
    (h : GeometryTotalHom
      (UpperGeometryCleavage.exactSourceGeometry G f) K)
    (hbase : h.base = PackageTotalHom.comp
      (UpperGeometryCleavage.exactBaseHom G f) tail) :
    ∃! factor : GeometryTotalHom G K,
      factor.base = tail ∧
        GeometryTotalHom.comp
          (UpperGeometryCleavage.generatedExactGeometryHom G f) factor = h := by
  refine ⟨exactPullOutgoingTotalFactor G K f tail h hbase, ⟨rfl, ?_⟩, ?_⟩
  · exact exactPullOutgoingTotalFactor_fac G K f tail h hbase
  · intro candidate hcandidate
    exact exactPullOutgoingTotalFactor_unique G K f tail h hbase candidate
      hcandidate.1 hcandidate.2

/-- The generated exact geometry hom is strongly cocartesian over its actual
complete-core package base. -/
theorem generatedExactGeometryHom_isStronglyCocartesian
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core) :
    (geometryProjection U).IsStronglyCocartesian
      (UpperGeometryCleavage.exactBaseHom G f)
      (UpperGeometryCleavage.generatedExactGeometryHom G f) := by
  letI : (geometryProjection U).IsHomLift
      (UpperGeometryCleavage.exactBaseHom G f)
      (UpperGeometryCleavage.generatedExactGeometryHom G f) := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map
        (UpperGeometryCleavage.generatedExactGeometryHom G f))
      (UpperGeometryCleavage.generatedExactGeometryHom G f)
    infer_instance
  apply CategoryTheory.Functor.IsStronglyCocartesian.mk
  intro K tail h hLift
  have hbase : h.base = PackageTotalHom.comp
      (UpperGeometryCleavage.exactBaseHom G f) tail := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (geometryProjection U)
      (PackageTotalHom.comp (UpperGeometryCleavage.exactBaseHom G f) tail)
      h).symm
  rcases exactPullOutgoingFactor_existsUnique G K f tail h hbase with
    ⟨factor, hfactor, hunique⟩
  refine ⟨factor, ?_, ?_⟩
  · constructor
    · rw [← hfactor.1]
      change (geometryProjection U).IsHomLift
        ((geometryProjection U).map factor) factor
      infer_instance
    · exact hfactor.2
  · intro other hother
    apply hunique other
    constructor
    · letI : (geometryProjection U).IsHomLift tail other := hother.1
      exact (CategoryTheory.IsHomLift.eq_of_isHomLift
        (p := geometryProjection U) (a := G) (b := K) tail other).symm
    · exact hother.2

/-- The generated complete exact pull lift is strongly cocartesian for the
composed geometry-to-pointed projection over its actual projected arrow. -/
theorem exactGeometryPullLift_crossStageStronglyCocartesian_map
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target) :
    (crossStageProjection.{u, v} U).IsStronglyCocartesian
      ((crossStageProjection.{u, v} U).map
        (exactGeometryPullLift input target))
      (exactGeometryPullLift input target) := by
  let f := exactGeometryPullBaseHom input target
  letI : (geometryProjection U).IsStronglyCocartesian
      (exactGeometryPullLift input target).base
      (exactGeometryPullLift input target) := by
    change (geometryProjection U).IsStronglyCocartesian
      (UpperGeometryCleavage.exactBaseHom target.1 f)
      (UpperGeometryCleavage.generatedExactGeometryHom target.1 f)
    exact
      generatedExactGeometryHom_isStronglyCocartesian target.1 f
  letI : (packageProjection U).IsStronglyCocartesian
      (exactGeometryPullLift input target).base.base
      (exactGeometryPullLift input target).base := by
    change (packageProjection U).IsStronglyCocartesian
      (UpperGeometryCleavage.exactBaseHom target.1 f).base
      (UpperGeometryCleavage.exactBaseHom target.1 f)
    exact
      packageTotalHom_isStronglyCocartesian_of_upper_inverse
        (UpperGeometryCleavage.exactBaseHom target.1 f)
        (inverseCorePackageBackwardUpper target.1.core f)
        (inverseCorePackageForward_comp_backward target.1.core f)
        (inverseCorePackageBackward_comp_forward target.1.core f)
  simpa only using geometryHom_isCompositeStronglyCocartesian
    (exactGeometryPullLift input target)

/-- G-122 B1: the canonical exact complete-geometry pull lift is strongly
cocartesian over the authored realizable semantic arrow. -/
theorem exactGeometryPullLift_crossStageStronglyCocartesian
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target) :
    (crossStageProjection.{u, v} U).IsStronglyCocartesian input.semantic.hom
      (exactGeometryPullLift input target) := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      ((crossStageProjection.{u, v} U).map
        (exactGeometryPullLift input target))
      (exactGeometryPullLift input target) :=
    exactGeometryPullLift_crossStageStronglyCocartesian_map input target
  letI : (crossStageProjection.{u, v} U).IsHomLift input.semantic.hom
      (exactGeometryPullLift input target) :=
    exactGeometryPullLift_isHomLift input target
  exact stronglyCocartesian_of_isHomLift
    (crossStageProjection.{u, v} U) input.semantic.hom
    (exactGeometryPullLift input target)

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
