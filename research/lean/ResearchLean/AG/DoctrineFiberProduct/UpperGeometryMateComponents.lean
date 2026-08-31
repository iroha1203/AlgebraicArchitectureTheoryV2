import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateRealization
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationExactness

/-!
# Carrier realization for the generated upper geometry mate

The pulled-route inverse upper map is the literal composite of the exact and
realized-refinement backward transports.  This module constructs its Support,
Axis, and Observable maps from those two canonical transports and proves their
reading and restriction-naturality laws.  No completed predecessor is changed
and no comparison map is supplied by a caller.

The same concrete carrier constructions now generate bidirectional supplies
for each exact and realized-refinement inverse package.  Their componentwise
cancellation yields realization-exact inhabitants, and route-order composition
produces the base-first and pulled-first inhabitants used by the next endpoint
comparison stage.
-/

namespace AAT.AG.DoctrineFiberProduct
universe u v
open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport
namespace UpperGeometryCleavage

set_option maxHeartbeats 2000000

/-- The pulled-route backward context image preserves the support carrier. -/
theorem pulledRouteBackwardUpper_contextForward_support_type
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward
      W).ctx.Support = W.ctx.Support := by
  unfold pulledRouteBackwardUpper
  change
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward
        ((inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextForward
            W)).ctx.Support = W.ctx.Support
  rw [SelectedRefinementTransport.inverseCorePackageBackwardUpper_contextFunctor_obj_support_type,
    inverseCorePackageBackwardUpper_contextFunctor_obj_support_type]

/-- The pulled-route backward context image preserves the axis carrier. -/
theorem pulledRouteBackwardUpper_contextForward_axis_type
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward
      W).ctx.Axis = W.ctx.Axis := by
  unfold pulledRouteBackwardUpper
  change
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward
        ((inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextForward
            W)).ctx.Axis = W.ctx.Axis
  rw [SelectedRefinementTransport.inverseCorePackageBackwardUpper_contextFunctor_obj_axis_type,
    inverseCorePackageBackwardUpper_contextFunctor_obj_axis_type]

/-- The pulled-route backward context image preserves the observable carrier. -/
theorem pulledRouteBackwardUpper_contextForward_observable_type
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward
      W).ctx.Observable = W.ctx.Observable := by
  unfold pulledRouteBackwardUpper
  change
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward
        ((inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextForward
            W)).ctx.Observable = W.ctx.Observable
  rw [SelectedRefinementTransport.inverseCorePackageBackwardUpper_contextFunctor_obj_observable_type,
    inverseCorePackageBackwardUpper_contextFunctor_obj_observable_type]

private def geometryCastTargetEquationExact {U : AtomCarrier.{u}}
    {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap) :
    EquationSystemExactTransport E₀
      (castEquationReading h S).equationSystem e objectMap := by
  cases h
  exact T

private theorem geometryCastTargetEquationExact_contextForward_ctx
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (W : Site.ContextCategoryObject C₀) :
    ((geometryCastTargetEquationExact S h e objectMap T).contextForward W).ctx =
      cast (congrArg Site.ArchitectureContext h) (T.contextForward W).ctx := by
  cases h
  rfl

private theorem geometryCastTargetEquationExact_contextBackward_ctx
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (W : Site.ContextCategoryObject (castEquationReading h S).contextPreorder) :
    ((geometryCastTargetEquationExact S h e objectMap T).contextBackward W).ctx =
      (T.contextBackward
        ⟨cast (congrArg Site.ArchitectureContext h.symm) W.ctx⟩).ctx := by
  cases h
  rfl

private theorem inverseCoreEquationBackward_eq_geometryCast
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (f : X ⟶ packagePoint Q) :
    (inverseCorePackageBackwardUpper Q f).equationTransport =
      geometryCastTargetEquationExact
        (transportEquationReading f.doctrineHom.atomEquiv.symm
          Q.object Q.reading.equationReading)
        (inverseBaseObject_eq Q f).symm
        f.doctrineHom.atomEquiv.symm
        (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
        (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
          Q.object Q.reading.equationReading.contextPreorder
          Q.reading.equationReading.equationSystem) := by
  rfl

/-- The explicit exact backward context functor is the inverse context functor
of its generated forward upper map. -/
theorem inverseCorePackageBackward_contextForward_eq_forward_contextBackward
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (f : X ⟶ packagePoint Q)
    (W : Site.ContextCategoryObject Q.contextPreorder) :
    ((inverseCorePackageBackwardUpper Q f).equationTransport.contextForward W).ctx =
      ((inverseCorePackageForwardUpper Q f).equationTransport.contextBackward W).ctx := by
  rw [inverseCoreEquationBackward_eq_geometryCast,
    geometryCastTargetEquationExact_contextForward_ctx,
    inverseCorePackageForwardUpper_contextInverse_obj_eq]
  rfl

/-- The inverse context functor of the explicit exact backward map is the
generated forward context functor. -/
theorem inverseCorePackageBackward_contextBackward_eq_forward_contextForward
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U) (f : X ⟶ packagePoint Q)
    (W : Site.ContextCategoryObject (inverseCorePackage Q f).contextPreorder) :
    ((inverseCorePackageBackwardUpper Q f).equationTransport.contextBackward W).ctx =
      ((inverseCorePackageForwardUpper Q f).equationTransport.contextForward W).ctx := by
  rw [inverseCoreEquationBackward_eq_geometryCast,
    geometryCastTargetEquationExact_contextBackward_ctx,
    inverseCorePackageForwardUpper_contextFunctor_obj_eq]
  rfl

private noncomputable def geometryTransportSupportComp
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom) (W : Site.ContextCategoryObject Q.contextPreorder) :
    W.ctx.Support →
      ((transportEquationSystemExact e Q.object Q.contextPreorder
        Q.algebra.equationSystem).contextForward W).ctx.Support :=
  _root_.id

private theorem geometryTransportSupportComp_reads
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom) (W : Site.ContextCategoryObject Q.contextPreorder)
    support atom (h : W.ctx.minimal.supportReads support atom) :
    ((transportEquationSystemExact e Q.object Q.contextPreorder
      Q.algebra.equationSystem).contextForward W).ctx.minimal.supportReads
        (geometryTransportSupportComp Q e W support) (e atom) := by
  change W.ctx.minimal.supportReads support (e.symm (e atom))
  simpa using h

private theorem geometryTransportSupportComp_naturality
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    {W V : Site.ContextCategoryObject Q.contextPreorder}
    (w : W ⟶ V) support :
    ((transportContextPreorder e Q.object Q.contextPreorder).morphism
      (leOfHom ((transportEquationSystemExact e Q.object Q.contextPreorder
        Q.algebra.equationSystem).contextEquivalence.functor.map w))).supportMap
        (geometryTransportSupportComp Q e W support) =
      geometryTransportSupportComp Q e V
        ((Q.contextPreorder.morphism (leOfHom w)).supportMap support) := by
  exact transportContextFunctor_supportMap e Q.object Q.contextPreorder w support

private noncomputable def geometryTransportAxisComp
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom) (W : Site.ContextCategoryObject Q.contextPreorder) :
    W.ctx.Axis →
      ((transportEquationSystemExact e Q.object Q.contextPreorder
        Q.algebra.equationSystem).contextForward W).ctx.Axis :=
  _root_.id

private theorem geometryTransportAxisComp_reads
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom) (W : Site.ContextCategoryObject Q.contextPreorder)
    axis (h : W.ctx.minimal.axisReads axis) :
    ((transportEquationSystemExact e Q.object Q.contextPreorder
      Q.algebra.equationSystem).contextForward W).ctx.minimal.axisReads
        (geometryTransportAxisComp Q e W axis) := by
  exact h

private theorem geometryTransportAxisComp_naturality
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    {W V : Site.ContextCategoryObject Q.contextPreorder}
    (w : W ⟶ V) axis :
    ((transportContextPreorder e Q.object Q.contextPreorder).morphism
      (leOfHom ((transportEquationSystemExact e Q.object Q.contextPreorder
        Q.algebra.equationSystem).contextEquivalence.functor.map w))).axisMap
        (geometryTransportAxisComp Q e W axis) =
      geometryTransportAxisComp Q e V
        ((Q.contextPreorder.morphism (leOfHom w)).axisMap axis) := by
  exact transportContextFunctor_axisMap e Q.object Q.contextPreorder w axis

private noncomputable def geometryTransportObservableComp
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom) (W : Site.ContextCategoryObject Q.contextPreorder) :
    W.ctx.Observable →
      ((transportEquationSystemExact e Q.object Q.contextPreorder
        Q.algebra.equationSystem).contextForward W).ctx.Observable :=
  _root_.id

private theorem geometryTransportObservableComp_reads
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom) (W : Site.ContextCategoryObject Q.contextPreorder)
    observable (h : W.ctx.minimal.observableReads observable) :
    ((transportEquationSystemExact e Q.object Q.contextPreorder
      Q.algebra.equationSystem).contextForward W).ctx.minimal.observableReads
        (geometryTransportObservableComp Q e W observable) := by
  exact h

private theorem geometryTransportObservableComp_naturality
    {U : AtomCarrier.{u}} (Q : AATCorePackage U)
    (e : U.Atom ≃ U.Atom)
    {W V : Site.ContextCategoryObject Q.contextPreorder}
    (w : W ⟶ V) observable :
    ((transportContextPreorder e Q.object Q.contextPreorder).morphism
      (leOfHom ((transportEquationSystemExact e Q.object Q.contextPreorder
        Q.algebra.equationSystem).contextEquivalence.functor.map w))).observableRestrict
          (geometryTransportObservableComp Q e V observable) =
      geometryTransportObservableComp Q e W
        ((Q.contextPreorder.morphism (leOfHom w)).observableRestrict observable) := by
  exact transportContextFunctor_observableRestrict e Q.object Q.contextPreorder w observable

private noncomputable def geometryCastTargetSupportComp
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Support → (T.contextForward W).ctx.Support)
    (W : Site.ContextCategoryObject C₀) :
    W.ctx.Support →
      ((geometryCastTargetEquationExact S h e objectMap T).contextForward
        W).ctx.Support := by
  cases h
  exact comp W

private theorem geometryCastTargetSupportComp_reads
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Support → (T.contextForward W).ctx.Support)
    (comp_reads : ∀ W support atom,
      W.ctx.minimal.supportReads support atom →
        (T.contextForward W).ctx.minimal.supportReads
          (comp W support) (e atom))
    (W : Site.ContextCategoryObject C₀) support atom
    (hread : W.ctx.minimal.supportReads support atom) :
    ((geometryCastTargetEquationExact S h e objectMap T).contextForward
      W).ctx.minimal.supportReads
        (geometryCastTargetSupportComp S h e objectMap T comp W support)
        (e atom) := by
  cases h
  exact comp_reads W support atom hread

private theorem geometryCastTargetSupportComp_naturality
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Support → (T.contextForward W).ctx.Support)
    (comp_naturality : ∀ {W V : Site.ContextCategoryObject C₀}
      (w : W ⟶ V) support,
      (S.contextPreorder.morphism
        (leOfHom (T.contextEquivalence.functor.map w))).supportMap
          (comp W support) =
        comp V ((C₀.morphism (leOfHom w)).supportMap support))
    {W V : Site.ContextCategoryObject C₀}
    (w : W ⟶ V) support :
    ((castEquationReading h S).contextPreorder.morphism
      (leOfHom ((geometryCastTargetEquationExact S h e objectMap T).contextEquivalence.functor.map
        w))).supportMap
        (geometryCastTargetSupportComp S h e objectMap T comp W support) =
      geometryCastTargetSupportComp S h e objectMap T comp V
        ((C₀.morphism (leOfHom w)).supportMap support) := by
  cases h
  exact comp_naturality w support

private noncomputable def geometryCastTargetAxisComp
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Axis → (T.contextForward W).ctx.Axis)
    (W : Site.ContextCategoryObject C₀) :
    W.ctx.Axis →
      ((geometryCastTargetEquationExact S h e objectMap T).contextForward W).ctx.Axis := by
  cases h
  exact comp W

private theorem geometryCastTargetAxisComp_reads
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Axis → (T.contextForward W).ctx.Axis)
    (comp_reads : ∀ W axis, W.ctx.minimal.axisReads axis →
      (T.contextForward W).ctx.minimal.axisReads (comp W axis))
    (W : Site.ContextCategoryObject C₀) axis
    (hread : W.ctx.minimal.axisReads axis) :
    ((geometryCastTargetEquationExact S h e objectMap T).contextForward W).ctx.minimal.axisReads
        (geometryCastTargetAxisComp S h e objectMap T comp W axis) := by
  cases h
  exact comp_reads W axis hread

private theorem geometryCastTargetAxisComp_naturality
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Axis → (T.contextForward W).ctx.Axis)
    (comp_naturality : ∀ {W V : Site.ContextCategoryObject C₀}
      (w : W ⟶ V) axis,
      (S.contextPreorder.morphism
        (leOfHom (T.contextEquivalence.functor.map w))).axisMap (comp W axis) =
        comp V ((C₀.morphism (leOfHom w)).axisMap axis))
    {W V : Site.ContextCategoryObject C₀} (w : W ⟶ V) axis :
    ((castEquationReading h S).contextPreorder.morphism
      (leOfHom ((geometryCastTargetEquationExact S h e objectMap T).contextEquivalence.functor.map
        w))).axisMap
        (geometryCastTargetAxisComp S h e objectMap T comp W axis) =
      geometryCastTargetAxisComp S h e objectMap T comp V
        ((C₀.morphism (leOfHom w)).axisMap axis) := by
  cases h
  exact comp_naturality w axis

private noncomputable def geometryCastTargetObservableComp
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Observable → (T.contextForward W).ctx.Observable)
    (W : Site.ContextCategoryObject C₀) :
    W.ctx.Observable →
      ((geometryCastTargetEquationExact S h e objectMap T).contextForward W).ctx.Observable := by
  cases h
  exact comp W

private theorem geometryCastTargetObservableComp_reads
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Observable → (T.contextForward W).ctx.Observable)
    (comp_reads : ∀ W observable, W.ctx.minimal.observableReads observable →
      (T.contextForward W).ctx.minimal.observableReads (comp W observable))
    (W : Site.ContextCategoryObject C₀) observable
    (hread : W.ctx.minimal.observableReads observable) :
    ((geometryCastTargetEquationExact S h e objectMap T).contextForward W).ctx.minimal.observableReads
        (geometryCastTargetObservableComp S h e objectMap T comp W observable) := by
  cases h
  exact comp_reads W observable hread

private theorem geometryCastTargetObservableComp_naturality
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A')
    (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Observable → (T.contextForward W).ctx.Observable)
    (comp_naturality : ∀ {W V : Site.ContextCategoryObject C₀}
      (w : W ⟶ V) observable,
      (S.contextPreorder.morphism
        (leOfHom (T.contextEquivalence.functor.map w))).observableRestrict
          (comp V observable) =
        comp W ((C₀.morphism (leOfHom w)).observableRestrict observable))
    {W V : Site.ContextCategoryObject C₀} (w : W ⟶ V) observable :
    ((castEquationReading h S).contextPreorder.morphism
      (leOfHom ((geometryCastTargetEquationExact S h e objectMap T).contextEquivalence.functor.map
        w))).observableRestrict
          (geometryCastTargetObservableComp S h e objectMap T comp V observable) =
      geometryCastTargetObservableComp S h e objectMap T comp W
        ((C₀.morphism (leOfHom w)).observableRestrict observable) := by
  cases h
  exact comp_naturality w observable

/-! ## Generic exact inverse-package backward supply -/

/-- Canonical backward support comparison for an explicit exact inverse
package. -/
noncomputable def exactBackwardSupportComp {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) :
    W.ctx.Support →
      ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
        W).ctx.Support := by
  rw [inverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetSupportComp
    (transportEquationReading f.doctrineHom.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    (inverseBaseObject_eq G.core f).symm
    f.doctrineHom.atomEquiv.symm
    (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
    (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
      G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
    (geometryTransportSupportComp G.core f.doctrineHom.atomEquiv.symm) W

/-- The canonical exact backward support comparison preserves reading. -/
theorem exactBackwardSupportComp_reads {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) support atom
    (h : W.ctx.minimal.supportReads support atom) :
    ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
      W).ctx.minimal.supportReads
        (exactBackwardSupportComp G f W support)
        ((inverseCorePackageBackwardUpper G.core f).atomEquiv atom) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardSupportComp] using
    geometryCastTargetSupportComp_reads
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportSupportComp G.core f.doctrineHom.atomEquiv.symm)
      (geometryTransportSupportComp_reads G.core f.doctrineHom.atomEquiv.symm)
      W support atom h

/-- The canonical exact backward support comparison is natural in
restriction. -/
theorem exactBackwardSupportComp_naturality {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    {W V : G.site.category} (w : W ⟶ V) support :
    ((inverseCorePackage G.core f).contextPreorder.morphism
      (leOfHom ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w))).supportMap
        (exactBackwardSupportComp G f W support) =
      exactBackwardSupportComp G f V
        ((G.core.contextPreorder.morphism (leOfHom w)).supportMap support) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardSupportComp] using
    geometryCastTargetSupportComp_naturality
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportSupportComp G.core f.doctrineHom.atomEquiv.symm)
      (geometryTransportSupportComp_naturality G.core
        f.doctrineHom.atomEquiv.symm) w support

/-- Canonical backward axis comparison for an explicit exact inverse package. -/
noncomputable def exactBackwardAxisComp {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) :
    W.ctx.Axis →
      ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
        W).ctx.Axis := by
  rw [inverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetAxisComp
    (transportEquationReading f.doctrineHom.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    (inverseBaseObject_eq G.core f).symm
    f.doctrineHom.atomEquiv.symm
    (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
    (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
      G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
    (geometryTransportAxisComp G.core f.doctrineHom.atomEquiv.symm) W

/-- The canonical exact backward axis comparison preserves reading. -/
theorem exactBackwardAxisComp_reads {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) axis (h : W.ctx.minimal.axisReads axis) :
    ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
      W).ctx.minimal.axisReads (exactBackwardAxisComp G f W axis) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardAxisComp] using
    geometryCastTargetAxisComp_reads
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportAxisComp G.core f.doctrineHom.atomEquiv.symm)
      (geometryTransportAxisComp_reads G.core f.doctrineHom.atomEquiv.symm)
      W axis h

/-- The canonical exact backward axis comparison is natural in restriction. -/
theorem exactBackwardAxisComp_naturality {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    {W V : G.site.category} (w : W ⟶ V) axis :
    ((inverseCorePackage G.core f).contextPreorder.morphism
      (leOfHom ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w))).axisMap
        (exactBackwardAxisComp G f W axis) =
      exactBackwardAxisComp G f V
        ((G.core.contextPreorder.morphism (leOfHom w)).axisMap axis) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardAxisComp] using
    geometryCastTargetAxisComp_naturality
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportAxisComp G.core f.doctrineHom.atomEquiv.symm)
      (geometryTransportAxisComp_naturality G.core
        f.doctrineHom.atomEquiv.symm) w axis

/-- Canonical backward observable comparison for an explicit exact inverse
package. -/
noncomputable def exactBackwardObservableComp {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) :
    W.ctx.Observable →
      ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
        W).ctx.Observable := by
  rw [inverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetObservableComp
    (transportEquationReading f.doctrineHom.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    (inverseBaseObject_eq G.core f).symm
    f.doctrineHom.atomEquiv.symm
    (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
    (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
      G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
    (geometryTransportObservableComp G.core f.doctrineHom.atomEquiv.symm) W

/-- The canonical exact backward observable comparison preserves reading. -/
theorem exactBackwardObservableComp_reads {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) observable
    (h : W.ctx.minimal.observableReads observable) :
    ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextForward
      W).ctx.minimal.observableReads
        (exactBackwardObservableComp G f W observable) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardObservableComp] using
    geometryCastTargetObservableComp_reads
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportObservableComp G.core f.doctrineHom.atomEquiv.symm)
      (geometryTransportObservableComp_reads G.core
        f.doctrineHom.atomEquiv.symm) W observable h

/-- The canonical exact backward observable comparison is natural in
restriction. -/
theorem exactBackwardObservableComp_naturality {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    {W V : G.site.category} (w : W ⟶ V) observable :
    ((inverseCorePackage G.core f).contextPreorder.morphism
      (leOfHom ((inverseCorePackageBackwardUpper G.core f).equationTransport.contextEquivalence.functor.map w))).observableRestrict
        (exactBackwardObservableComp G f V observable) =
      exactBackwardObservableComp G f W
        ((G.core.contextPreorder.morphism
          (leOfHom w)).observableRestrict observable) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardObservableComp] using
    geometryCastTargetObservableComp_naturality
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportObservableComp G.core f.doctrineHom.atomEquiv.symm)
      (geometryTransportObservableComp_naturality G.core
        f.doctrineHom.atomEquiv.symm) w observable

private noncomputable def exactRouteBackwardSupportComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    W.ctx.Support →
      ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextForward
          W).ctx.Support := by
  rw [inverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetSupportComp
    (transportEquationReading
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      target.geometry.core.object target.geometry.core.reading.equationReading)
    (inverseBaseObject_eq target.geometry.core
      (pullbackTargetExactArrow ctx target)).symm
    (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
    (transportArchitectureObject
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
    (transportEquationSystemExact
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      target.geometry.core.object target.geometry.core.contextPreorder
      target.geometry.core.algebra.equationSystem)
    (geometryTransportSupportComp target.geometry.core
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm) W

private theorem exactRouteBackwardSupportComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) support atom
    (h : W.ctx.minimal.supportReads support atom) :
    ((inverseCorePackageBackwardUpper target.geometry.core
      (pullbackTargetExactArrow ctx target)).equationTransport.contextForward
        W).ctx.minimal.supportReads
      (exactRouteBackwardSupportComp ctx target W support)
      ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).atomEquiv atom) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardSupportComp] using
    geometryCastTargetSupportComp_reads
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportSupportComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (geometryTransportSupportComp_reads target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      W support atom h

private theorem exactRouteBackwardSupportComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : target.geometry.site.category} (w : W ⟶ V) support :
    ((inverseCorePackage target.geometry.core
      (pullbackTargetExactArrow ctx target)).contextPreorder.morphism
      (leOfHom ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map
          w))).supportMap
        (exactRouteBackwardSupportComp ctx target W support) =
      exactRouteBackwardSupportComp ctx target V
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).supportMap support) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardSupportComp] using
    geometryCastTargetSupportComp_naturality
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportSupportComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (geometryTransportSupportComp_naturality target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      w support

private theorem selectedInverseCoreEquationBackward_eq_geometryCast
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U)
    (data : SelectedRefinementTransport.SelectedTransportData X Q) :
    (SelectedRefinementTransport.inverseCorePackageBackwardUpper Q data).equationTransport =
      geometryCastTargetEquationExact
        (transportEquationReading data.atomEquiv.symm
          Q.object Q.reading.equationReading)
        (SelectedRefinementTransport.inverseBaseObject_eq Q data).symm
        data.atomEquiv.symm
        (transportArchitectureObject data.atomEquiv.symm)
        (transportEquationSystemExact data.atomEquiv.symm
          Q.object Q.contextPreorder Q.algebra.equationSystem) := by
  rfl

/-- The explicit realized-refinement backward context functor is the inverse
context functor of its generated forward upper map. -/
theorem selectedInverseCorePackageBackward_contextForward_eq_forward_contextBackward
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U)
    (data : SelectedRefinementTransport.SelectedTransportData X Q)
    (W : Site.ContextCategoryObject Q.contextPreorder) :
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper Q data).equationTransport.contextForward
      W).ctx =
      ((SelectedRefinementTransport.inverseCorePackageForwardUpper Q data).equationTransport.contextBackward
        W).ctx := by
  rw [selectedInverseCoreEquationBackward_eq_geometryCast,
    geometryCastTargetEquationExact_contextForward_ctx,
    SelectedRefinementTransport.inverseCorePackageForwardUpper_contextInverse_obj_eq]
  rfl

/-- The inverse context functor of the explicit realized-refinement backward
map is the generated forward context functor. -/
theorem selectedInverseCorePackageBackward_contextBackward_eq_forward_contextForward
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U)
    (data : SelectedRefinementTransport.SelectedTransportData X Q)
    (W : Site.ContextCategoryObject
      (SelectedRefinementTransport.inverseCorePackage Q data).contextPreorder) :
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper Q data).equationTransport.contextBackward
      W).ctx =
      ((SelectedRefinementTransport.inverseCorePackageForwardUpper Q data).equationTransport.contextForward
        W).ctx := by
  rw [selectedInverseCoreEquationBackward_eq_geometryCast,
    geometryCastTargetEquationExact_contextBackward_ctx,
    SelectedRefinementTransport.inverseCorePackageForwardUpper_contextFunctor_obj_eq]
  rfl

/-! ## Generic realized-refinement inverse-package backward supply -/

/-- Canonical backward support comparison for the realized-refinement inverse
package. -/
noncomputable def refinementBackwardSupportComp
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category) :
    W.ctx.Support →
      ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextForward
        W).ctx.Support := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  unfold refinementSourceBackwardUpper
  rw [selectedInverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetSupportComp
    (transportEquationReading data.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
    data.atomEquiv.symm
    (transportArchitectureObject data.atomEquiv.symm)
    (transportEquationSystemExact data.atomEquiv.symm G.core.object
      G.core.contextPreorder G.core.algebra.equationSystem)
    (geometryTransportSupportComp G.core data.atomEquiv.symm) W

/-- The canonical realized-refinement backward support comparison preserves
reading. -/
theorem refinementBackwardSupportComp_reads
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category) support atom
    (h : W.ctx.minimal.supportReads support atom) :
    ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextForward
      W).ctx.minimal.supportReads
        (refinementBackwardSupportComp G r condition hG W support)
        ((refinementSourceBackwardUpper G r condition hG).atomEquiv atom) := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardSupportComp] using
    geometryCastTargetSupportComp_reads
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportSupportComp G.core data.atomEquiv.symm)
      (geometryTransportSupportComp_reads G.core data.atomEquiv.symm)
      W support atom h

/-- The canonical realized-refinement backward support comparison is natural
in restriction. -/
theorem refinementBackwardSupportComp_naturality
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) {W V : G.site.category}
    (w : W ⟶ V) support :
    ((refinementSourceGeometry G r condition hG).core.contextPreorder.morphism
      (leOfHom ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextEquivalence.functor.map w))).supportMap
        (refinementBackwardSupportComp G r condition hG W support) =
      refinementBackwardSupportComp G r condition hG V
        ((G.core.contextPreorder.morphism (leOfHom w)).supportMap support) := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardSupportComp] using
    geometryCastTargetSupportComp_naturality
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportSupportComp G.core data.atomEquiv.symm)
      (geometryTransportSupportComp_naturality G.core data.atomEquiv.symm)
      w support

/-- Canonical backward axis comparison for the realized-refinement inverse
package. -/
noncomputable def refinementBackwardAxisComp
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category) :
    W.ctx.Axis →
      ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextForward
        W).ctx.Axis := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  unfold refinementSourceBackwardUpper
  rw [selectedInverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetAxisComp
    (transportEquationReading data.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
    data.atomEquiv.symm
    (transportArchitectureObject data.atomEquiv.symm)
    (transportEquationSystemExact data.atomEquiv.symm G.core.object
      G.core.contextPreorder G.core.algebra.equationSystem)
    (geometryTransportAxisComp G.core data.atomEquiv.symm) W

/-- The canonical realized-refinement backward axis comparison preserves
reading. -/
theorem refinementBackwardAxisComp_reads
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category) axis
    (h : W.ctx.minimal.axisReads axis) :
    ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextForward
      W).ctx.minimal.axisReads
        (refinementBackwardAxisComp G r condition hG W axis) := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardAxisComp] using
    geometryCastTargetAxisComp_reads
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportAxisComp G.core data.atomEquiv.symm)
      (geometryTransportAxisComp_reads G.core data.atomEquiv.symm) W axis h

/-- The canonical realized-refinement backward axis comparison is natural in
restriction. -/
theorem refinementBackwardAxisComp_naturality
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) {W V : G.site.category}
    (w : W ⟶ V) axis :
    ((refinementSourceGeometry G r condition hG).core.contextPreorder.morphism
      (leOfHom ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextEquivalence.functor.map w))).axisMap
        (refinementBackwardAxisComp G r condition hG W axis) =
      refinementBackwardAxisComp G r condition hG V
        ((G.core.contextPreorder.morphism (leOfHom w)).axisMap axis) := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardAxisComp] using
    geometryCastTargetAxisComp_naturality
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportAxisComp G.core data.atomEquiv.symm)
      (geometryTransportAxisComp_naturality G.core data.atomEquiv.symm) w axis

/-- Canonical backward observable comparison for the realized-refinement
inverse package. -/
noncomputable def refinementBackwardObservableComp
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category) :
    W.ctx.Observable →
      ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextForward
        W).ctx.Observable := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  unfold refinementSourceBackwardUpper
  rw [selectedInverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetObservableComp
    (transportEquationReading data.atomEquiv.symm
      G.core.object G.core.reading.equationReading)
    (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
    data.atomEquiv.symm
    (transportArchitectureObject data.atomEquiv.symm)
    (transportEquationSystemExact data.atomEquiv.symm G.core.object
      G.core.contextPreorder G.core.algebra.equationSystem)
    (geometryTransportObservableComp G.core data.atomEquiv.symm) W

/-- The canonical realized-refinement backward observable comparison preserves
reading. -/
theorem refinementBackwardObservableComp_reads
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category) observable
    (h : W.ctx.minimal.observableReads observable) :
    ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextForward
      W).ctx.minimal.observableReads
        (refinementBackwardObservableComp G r condition hG W observable) := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardObservableComp] using
    geometryCastTargetObservableComp_reads
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportObservableComp G.core data.atomEquiv.symm)
      (geometryTransportObservableComp_reads G.core data.atomEquiv.symm)
      W observable h

/-- The canonical realized-refinement backward observable comparison is
natural in restriction. -/
theorem refinementBackwardObservableComp_naturality
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) {W V : G.site.category}
    (w : W ⟶ V) observable :
    ((refinementSourceGeometry G r condition hG).core.contextPreorder.morphism
      (leOfHom ((refinementSourceBackwardUpper G r condition hG).equationTransport.contextEquivalence.functor.map w))).observableRestrict
        (refinementBackwardObservableComp G r condition hG V observable) =
      refinementBackwardObservableComp G r condition hG W
        ((G.core.contextPreorder.morphism
          (leOfHom w)).observableRestrict observable) := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardObservableComp] using
    geometryCastTargetObservableComp_naturality
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportObservableComp G.core data.atomEquiv.symm)
      (geometryTransportObservableComp_naturality G.core data.atomEquiv.symm)
      w observable

private noncomputable def refinementRouteBackwardSupportComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category) :
    W.ctx.Support →
      ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextForward
          W).ctx.Support := by
  rw [selectedInverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetSupportComp
    (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
      (pullbackTargetGeometry ctx target).core.object
      (pullbackTargetGeometry ctx target).core.reading.equationReading)
    (SelectedRefinementTransport.inverseBaseObject_eq
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).symm
    (pulledRouteTransportData ctx target).atomEquiv.symm
    (transportArchitectureObject
      (pulledRouteTransportData ctx target).atomEquiv.symm)
    (transportEquationSystemExact
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (pullbackTargetGeometry ctx target).core.object
      (pullbackTargetGeometry ctx target).core.contextPreorder
      (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
    (geometryTransportSupportComp (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target).atomEquiv.symm) W

private theorem refinementRouteBackwardSupportComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category) support atom
    (h : W.ctx.minimal.supportReads support atom) :
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward W).ctx.minimal.supportReads
      (refinementRouteBackwardSupportComp ctx target W support)
      ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).atomEquiv atom) := by
  simpa only [SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementRouteBackwardSupportComp] using
    geometryCastTargetSupportComp_reads
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportSupportComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (geometryTransportSupportComp_reads (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      W support atom h

private theorem refinementRouteBackwardSupportComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : (pullbackTargetGeometry ctx target).site.category}
    (w : W ⟶ V) support :
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextEquivalence.functor.map
          w))).supportMap
        (refinementRouteBackwardSupportComp ctx target W support) =
      refinementRouteBackwardSupportComp ctx target V
        (((pullbackTargetGeometry ctx target).core.contextPreorder.morphism
          (leOfHom w)).supportMap support) := by
  simpa only [SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementRouteBackwardSupportComp] using
    geometryCastTargetSupportComp_naturality
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportSupportComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (geometryTransportSupportComp_naturality
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      w support

/-- Support comparison generated by the two pulled-route backward transports. -/
noncomputable def pulledRouteBackwardSupportComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    W.ctx.Support →
      ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward
        W).ctx.Support := by
  change W.ctx.Support →
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward
        ((inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextForward
            W)).ctx.Support
  exact fun support => refinementRouteBackwardSupportComp ctx target _
    (exactRouteBackwardSupportComp ctx target W support)

/-- The generated backward support comparison preserves support readings. -/
theorem pulledRouteBackwardSupportComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) support atom
    (h : W.ctx.minimal.supportReads support atom) :
    ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward
      W).ctx.minimal.supportReads
        (pulledRouteBackwardSupportComp ctx target W support)
        ((pulledRouteBackwardUpper ctx target).atomEquiv atom) := by
  apply refinementRouteBackwardSupportComp_reads
  exact exactRouteBackwardSupportComp_reads ctx target W support atom h

/-- The generated backward support comparison is natural in restriction. -/
theorem pulledRouteBackwardSupportComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : target.geometry.site.category} (w : W ⟶ V) support :
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((pulledRouteBackwardUpper ctx target).equationTransport.contextEquivalence.functor.map
        w))).supportMap
        (pulledRouteBackwardSupportComp ctx target W support) =
      pulledRouteBackwardSupportComp ctx target V
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).supportMap support) := by
  change
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextEquivalence.functor.map
            ((inverseCorePackageBackwardUpper target.geometry.core
              (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map
                w)))).supportMap
      (refinementRouteBackwardSupportComp ctx target _
        (exactRouteBackwardSupportComp ctx target W support)) =
    refinementRouteBackwardSupportComp ctx target _
      (exactRouteBackwardSupportComp ctx target V
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).supportMap support))
  rw [refinementRouteBackwardSupportComp_naturality ctx target
    ((inverseCorePackageBackwardUpper target.geometry.core
      (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map w)
    (exactRouteBackwardSupportComp ctx target W support)]
  exact congrArg (refinementRouteBackwardSupportComp ctx target
      ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextForward V))
    (exactRouteBackwardSupportComp_naturality ctx target w support)

private noncomputable def exactRouteBackwardAxisComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    W.ctx.Axis →
      ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W).ctx.Axis := by
  rw [inverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetAxisComp
    (transportEquationReading
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      target.geometry.core.object target.geometry.core.reading.equationReading)
    (inverseBaseObject_eq target.geometry.core
      (pullbackTargetExactArrow ctx target)).symm
    (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
    (transportArchitectureObject
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
    (transportEquationSystemExact
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      target.geometry.core.object target.geometry.core.contextPreorder
      target.geometry.core.algebra.equationSystem)
    (geometryTransportAxisComp target.geometry.core
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm) W

private theorem exactRouteBackwardAxisComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) axis
    (h : W.ctx.minimal.axisReads axis) :
    ((inverseCorePackageBackwardUpper target.geometry.core
      (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W).ctx.minimal.axisReads
      (exactRouteBackwardAxisComp ctx target W axis) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardAxisComp] using
    geometryCastTargetAxisComp_reads
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportAxisComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (geometryTransportAxisComp_reads target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      W axis h

private theorem exactRouteBackwardAxisComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : target.geometry.site.category} (w : W ⟶ V) axis :
    ((inverseCorePackage target.geometry.core
      (pullbackTargetExactArrow ctx target)).contextPreorder.morphism
      (leOfHom ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map
          w))).axisMap (exactRouteBackwardAxisComp ctx target W axis) =
      exactRouteBackwardAxisComp ctx target V
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).axisMap axis) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardAxisComp] using
    geometryCastTargetAxisComp_naturality
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportAxisComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (geometryTransportAxisComp_naturality target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      w axis

private noncomputable def exactRouteBackwardObservableComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    W.ctx.Observable →
      ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W).ctx.Observable := by
  rw [inverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetObservableComp
    (transportEquationReading
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      target.geometry.core.object target.geometry.core.reading.equationReading)
    (inverseBaseObject_eq target.geometry.core
      (pullbackTargetExactArrow ctx target)).symm
    (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
    (transportArchitectureObject
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
    (transportEquationSystemExact
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      target.geometry.core.object target.geometry.core.contextPreorder
      target.geometry.core.algebra.equationSystem)
    (geometryTransportObservableComp target.geometry.core
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm) W

private theorem exactRouteBackwardObservableComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) observable
    (h : W.ctx.minimal.observableReads observable) :
    ((inverseCorePackageBackwardUpper target.geometry.core
      (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W).ctx.minimal.observableReads
      (exactRouteBackwardObservableComp ctx target W observable) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardObservableComp] using
    geometryCastTargetObservableComp_reads
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportObservableComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (geometryTransportObservableComp_reads target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      W observable h

private theorem exactRouteBackwardObservableComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : target.geometry.site.category} (w : W ⟶ V) observable :
    ((inverseCorePackage target.geometry.core
      (pullbackTargetExactArrow ctx target)).contextPreorder.morphism
      (leOfHom ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map
          w))).observableRestrict
        (exactRouteBackwardObservableComp ctx target V observable) =
      exactRouteBackwardObservableComp ctx target W
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).observableRestrict observable) := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardObservableComp] using
    geometryCastTargetObservableComp_naturality
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportObservableComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (geometryTransportObservableComp_naturality target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      w observable

private noncomputable def refinementRouteBackwardAxisComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category) :
    W.ctx.Axis →
      ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextForward W).ctx.Axis := by
  rw [selectedInverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetAxisComp
    (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
      (pullbackTargetGeometry ctx target).core.object
      (pullbackTargetGeometry ctx target).core.reading.equationReading)
    (SelectedRefinementTransport.inverseBaseObject_eq
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).symm
    (pulledRouteTransportData ctx target).atomEquiv.symm
    (transportArchitectureObject
      (pulledRouteTransportData ctx target).atomEquiv.symm)
    (transportEquationSystemExact
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (pullbackTargetGeometry ctx target).core.object
      (pullbackTargetGeometry ctx target).core.contextPreorder
      (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
    (geometryTransportAxisComp (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target).atomEquiv.symm) W

private theorem refinementRouteBackwardAxisComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category) axis
    (h : W.ctx.minimal.axisReads axis) :
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward W).ctx.minimal.axisReads
      (refinementRouteBackwardAxisComp ctx target W axis) := by
  simpa only [SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementRouteBackwardAxisComp] using
    geometryCastTargetAxisComp_reads
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportAxisComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (geometryTransportAxisComp_reads (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      W axis h

private theorem refinementRouteBackwardAxisComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : (pullbackTargetGeometry ctx target).site.category}
    (w : W ⟶ V) axis :
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextEquivalence.functor.map
          w))).axisMap (refinementRouteBackwardAxisComp ctx target W axis) =
      refinementRouteBackwardAxisComp ctx target V
        (((pullbackTargetGeometry ctx target).core.contextPreorder.morphism
          (leOfHom w)).axisMap axis) := by
  simpa only [SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementRouteBackwardAxisComp] using
    geometryCastTargetAxisComp_naturality
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportAxisComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (geometryTransportAxisComp_naturality
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      w axis

private noncomputable def refinementRouteBackwardObservableComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category) :
    W.ctx.Observable →
      ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextForward W).ctx.Observable := by
  rw [selectedInverseCoreEquationBackward_eq_geometryCast]
  exact geometryCastTargetObservableComp
    (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
      (pullbackTargetGeometry ctx target).core.object
      (pullbackTargetGeometry ctx target).core.reading.equationReading)
    (SelectedRefinementTransport.inverseBaseObject_eq
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).symm
    (pulledRouteTransportData ctx target).atomEquiv.symm
    (transportArchitectureObject
      (pulledRouteTransportData ctx target).atomEquiv.symm)
    (transportEquationSystemExact
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (pullbackTargetGeometry ctx target).core.object
      (pullbackTargetGeometry ctx target).core.contextPreorder
      (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
    (geometryTransportObservableComp (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target).atomEquiv.symm) W

private theorem refinementRouteBackwardObservableComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category) observable
    (h : W.ctx.minimal.observableReads observable) :
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward W).ctx.minimal.observableReads
      (refinementRouteBackwardObservableComp ctx target W observable) := by
  simpa only [SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementRouteBackwardObservableComp] using
    geometryCastTargetObservableComp_reads
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportObservableComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (geometryTransportObservableComp_reads (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      W observable h

private theorem refinementRouteBackwardObservableComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : (pullbackTargetGeometry ctx target).site.category}
    (w : W ⟶ V) observable :
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextEquivalence.functor.map
          w))).observableRestrict
        (refinementRouteBackwardObservableComp ctx target V observable) =
      refinementRouteBackwardObservableComp ctx target W
        (((pullbackTargetGeometry ctx target).core.contextPreorder.morphism
          (leOfHom w)).observableRestrict observable) := by
  simpa only [SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementRouteBackwardObservableComp] using
    geometryCastTargetObservableComp_naturality
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportObservableComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (geometryTransportObservableComp_naturality
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      w observable

/-- Axis comparison generated by the two pulled-route backward transports. -/
noncomputable def pulledRouteBackwardAxisComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    W.ctx.Axis →
      ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward W).ctx.Axis := by
  change W.ctx.Axis →
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward
        ((inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W)).ctx.Axis
  exact fun axis => refinementRouteBackwardAxisComp ctx target _
    (exactRouteBackwardAxisComp ctx target W axis)

/-- The generated backward axis comparison preserves axis readings. -/
theorem pulledRouteBackwardAxisComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) axis
    (h : W.ctx.minimal.axisReads axis) :
    ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward W).ctx.minimal.axisReads
      (pulledRouteBackwardAxisComp ctx target W axis) := by
  apply refinementRouteBackwardAxisComp_reads
  exact exactRouteBackwardAxisComp_reads ctx target W axis h

/-- The generated backward axis comparison is natural in restriction. -/
theorem pulledRouteBackwardAxisComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : target.geometry.site.category} (w : W ⟶ V) axis :
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((pulledRouteBackwardUpper ctx target).equationTransport.contextEquivalence.functor.map
        w))).axisMap
        (pulledRouteBackwardAxisComp ctx target W axis) =
      pulledRouteBackwardAxisComp ctx target V
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).axisMap axis) := by
  change
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextEquivalence.functor.map
          ((inverseCorePackageBackwardUpper target.geometry.core
            (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map
              w)))).axisMap
      (refinementRouteBackwardAxisComp ctx target _
        (exactRouteBackwardAxisComp ctx target W axis)) =
    refinementRouteBackwardAxisComp ctx target _
      (exactRouteBackwardAxisComp ctx target V
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).axisMap axis))
  rw [refinementRouteBackwardAxisComp_naturality ctx target
    ((inverseCorePackageBackwardUpper target.geometry.core
      (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map w)
    (exactRouteBackwardAxisComp ctx target W axis)]
  exact congrArg (refinementRouteBackwardAxisComp ctx target
      ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextForward V))
    (exactRouteBackwardAxisComp_naturality ctx target w axis)

/-- Observable comparison generated by the two pulled-route backward transports. -/
noncomputable def pulledRouteBackwardObservableComp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) :
    W.ctx.Observable →
      ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward W).ctx.Observable := by
  change W.ctx.Observable →
    ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
      (pullbackTargetGeometry ctx target).core
      (pulledRouteTransportData ctx target)).equationTransport.contextForward
        ((inverseCorePackageBackwardUpper target.geometry.core
          (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W)).ctx.Observable
  exact fun observable => refinementRouteBackwardObservableComp ctx target _
    (exactRouteBackwardObservableComp ctx target W observable)

/-- The generated backward observable comparison preserves observable readings. -/
theorem pulledRouteBackwardObservableComp_reads
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) observable
    (h : W.ctx.minimal.observableReads observable) :
    ((pulledRouteBackwardUpper ctx target).equationTransport.contextForward W).ctx.minimal.observableReads
        (pulledRouteBackwardObservableComp ctx target W observable) := by
  apply refinementRouteBackwardObservableComp_reads
  exact exactRouteBackwardObservableComp_reads ctx target W observable h

/-- The generated backward observable comparison is natural in restriction. -/
theorem pulledRouteBackwardObservableComp_naturality
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    {W V : target.geometry.site.category} (w : W ⟶ V) observable :
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((pulledRouteBackwardUpper ctx target).equationTransport.contextEquivalence.functor.map
        w))).observableRestrict
        (pulledRouteBackwardObservableComp ctx target V observable) =
      pulledRouteBackwardObservableComp ctx target W
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).observableRestrict observable) := by
  change
    ((pulledRouteGeometry ctx target).core.contextPreorder.morphism
      (leOfHom ((SelectedRefinementTransport.inverseCorePackageBackwardUpper
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).equationTransport.contextEquivalence.functor.map
          ((inverseCorePackageBackwardUpper target.geometry.core
            (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map
              w)))).observableRestrict
      (refinementRouteBackwardObservableComp ctx target _
        (exactRouteBackwardObservableComp ctx target V observable)) =
    refinementRouteBackwardObservableComp ctx target _
      (exactRouteBackwardObservableComp ctx target W
        ((target.geometry.core.contextPreorder.morphism
          (leOfHom w)).observableRestrict observable))
  rw [refinementRouteBackwardObservableComp_naturality ctx target
    ((inverseCorePackageBackwardUpper target.geometry.core
      (pullbackTargetExactArrow ctx target)).equationTransport.contextEquivalence.functor.map w)
    (exactRouteBackwardObservableComp ctx target V observable)]
  exact congrArg (refinementRouteBackwardObservableComp ctx target
      ((inverseCorePackageBackwardUpper target.geometry.core
        (pullbackTargetExactArrow ctx target)).equationTransport.contextForward W))
    (exactRouteBackwardObservableComp_naturality ctx target w observable)

private theorem geometryCastTargetSupportComp_heq
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A') (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Support → (T.contextForward W).ctx.Support)
    (hcomp : ∀ W support, HEq (comp W support) support)
    (W : Site.ContextCategoryObject C₀) (support : W.ctx.Support) :
    HEq (geometryCastTargetSupportComp S h e objectMap T comp W support) support := by
  cases h
  exact hcomp W support

/-- The canonical exact backward support comparison preserves its carrier
value up to the dependent context identification. -/
theorem exactBackwardSupportComp_heq {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) (support : W.ctx.Support) :
    HEq (exactBackwardSupportComp G f W support) support := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardSupportComp] using
    geometryCastTargetSupportComp_heq
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportSupportComp G.core f.doctrineHom.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W support

/-- The canonical realized-refinement backward support comparison preserves its
carrier value up to the dependent context identification. -/
theorem refinementBackwardSupportComp_heq
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category)
    (support : W.ctx.Support) :
    HEq (refinementBackwardSupportComp G r condition hG W support) support := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardSupportComp] using
    geometryCastTargetSupportComp_heq
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportSupportComp G.core data.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W support

private theorem exactRouteBackwardSupportComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (support : W.ctx.Support) :
    HEq (exactRouteBackwardSupportComp ctx target W support) support := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardSupportComp] using
    geometryCastTargetSupportComp_heq
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportSupportComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W support

private theorem refinementRouteBackwardSupportComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category)
    (support : W.ctx.Support) :
    HEq (refinementRouteBackwardSupportComp ctx target W support) support := by
  simpa only [refinementRouteBackwardSupportComp] using
    geometryCastTargetSupportComp_heq
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportSupportComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (fun _ _ => HEq.rfl) W support

/-- The pulled-route backward support comparison preserves its carrier value. -/
theorem pulledRouteBackwardSupportComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (support : W.ctx.Support) :
    HEq (pulledRouteBackwardSupportComp ctx target W support) support := by
  apply HEq.trans
    (refinementRouteBackwardSupportComp_heq ctx target _
      (exactRouteBackwardSupportComp ctx target W support))
  exact exactRouteBackwardSupportComp_heq ctx target W support

private theorem geometryCastTargetAxisComp_heq
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A') (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Axis → (T.contextForward W).ctx.Axis)
    (hcomp : ∀ W axis, HEq (comp W axis) axis)
    (W : Site.ContextCategoryObject C₀) (axis : W.ctx.Axis) :
    HEq (geometryCastTargetAxisComp S h e objectMap T comp W axis) axis := by
  cases h
  exact hcomp W axis

/-- The canonical exact backward axis comparison preserves its carrier value
up to the dependent context identification. -/
theorem exactBackwardAxisComp_heq {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) (axis : W.ctx.Axis) :
    HEq (exactBackwardAxisComp G f W axis) axis := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardAxisComp] using
    geometryCastTargetAxisComp_heq
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportAxisComp G.core f.doctrineHom.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W axis

/-- The canonical realized-refinement backward axis comparison preserves its
carrier value up to the dependent context identification. -/
theorem refinementBackwardAxisComp_heq
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category)
    (axis : W.ctx.Axis) :
    HEq (refinementBackwardAxisComp G r condition hG W axis) axis := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardAxisComp] using
    geometryCastTargetAxisComp_heq
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportAxisComp G.core data.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W axis

private theorem exactRouteBackwardAxisComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (axis : W.ctx.Axis) :
    HEq (exactRouteBackwardAxisComp ctx target W axis) axis := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardAxisComp] using
    geometryCastTargetAxisComp_heq
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportAxisComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W axis

private theorem refinementRouteBackwardAxisComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category) (axis : W.ctx.Axis) :
    HEq (refinementRouteBackwardAxisComp ctx target W axis) axis := by
  simpa only [refinementRouteBackwardAxisComp] using
    geometryCastTargetAxisComp_heq
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportAxisComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (fun _ _ => HEq.rfl) W axis

/-- The pulled-route backward axis comparison preserves its carrier value. -/
theorem pulledRouteBackwardAxisComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (axis : W.ctx.Axis) :
    HEq (pulledRouteBackwardAxisComp ctx target W axis) axis := by
  apply HEq.trans
    (refinementRouteBackwardAxisComp_heq ctx target _
      (exactRouteBackwardAxisComp ctx target W axis))
  exact exactRouteBackwardAxisComp_heq ctx target W axis

private theorem geometryCastTargetObservableComp_heq
    {U : AtomCarrier.{u}} {A₀ A A' : ArchitectureObject U}
    {C₀ : Site.ContextPreorderCategory A₀}
    {E₀ : ArchitecturalEquationSystem C₀}
    (S : EquationReading A) (h : A = A') (e : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (T : EquationSystemExactTransport E₀ S.equationSystem e objectMap)
    (comp : ∀ W : Site.ContextCategoryObject C₀,
      W.ctx.Observable → (T.contextForward W).ctx.Observable)
    (hcomp : ∀ W observable, HEq (comp W observable) observable)
    (W : Site.ContextCategoryObject C₀) (observable : W.ctx.Observable) :
    HEq (geometryCastTargetObservableComp S h e objectMap T comp W observable)
      observable := by
  cases h
  exact hcomp W observable

/-- The canonical exact backward observable comparison preserves its carrier
value up to the dependent context identification. -/
theorem exactBackwardObservableComp_heq {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core)
    (W : G.site.category) (observable : W.ctx.Observable) :
    HEq (exactBackwardObservableComp G f W observable) observable := by
  simpa only [inverseCorePackageBackwardUpper,
    exactBackwardObservableComp] using
    geometryCastTargetObservableComp_heq
      (transportEquationReading f.doctrineHom.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (inverseBaseObject_eq G.core f).symm
      f.doctrineHom.atomEquiv.symm
      (transportArchitectureObject f.doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact f.doctrineHom.atomEquiv.symm
        G.core.object G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportObservableComp G.core f.doctrineHom.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W observable

/-- The canonical realized-refinement backward observable comparison preserves
its carrier value up to the dependent context identification. -/
theorem refinementBackwardObservableComp_heq
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) (W : G.site.category)
    (observable : W.ctx.Observable) :
    HEq (refinementBackwardObservableComp G r condition hG W observable)
      observable := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  simpa only [refinementSourceBackwardUpper,
    SelectedRefinementTransport.inverseCorePackageBackwardUpper,
    refinementBackwardObservableComp] using
    geometryCastTargetObservableComp_heq
      (transportEquationReading data.atomEquiv.symm
        G.core.object G.core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq G.core data).symm
      data.atomEquiv.symm
      (transportArchitectureObject data.atomEquiv.symm)
      (transportEquationSystemExact data.atomEquiv.symm G.core.object
        G.core.contextPreorder G.core.algebra.equationSystem)
      (geometryTransportObservableComp G.core data.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W observable

private theorem exactRouteBackwardObservableComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (observable : W.ctx.Observable) :
    HEq (exactRouteBackwardObservableComp ctx target W observable) observable := by
  simpa only [inverseCorePackageBackwardUpper,
    exactRouteBackwardObservableComp] using
    geometryCastTargetObservableComp_heq
      (transportEquationReading
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.reading.equationReading)
      (inverseBaseObject_eq target.geometry.core
        (pullbackTargetExactArrow ctx target)).symm
      (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
      (transportArchitectureObject
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (transportEquationSystemExact
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm
        target.geometry.core.object target.geometry.core.contextPreorder
        target.geometry.core.algebra.equationSystem)
      (geometryTransportObservableComp target.geometry.core
        (pullbackTargetExactArrow ctx target).doctrineHom.atomEquiv.symm)
      (fun _ _ => HEq.rfl) W observable

private theorem refinementRouteBackwardObservableComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : (pullbackTargetGeometry ctx target).site.category)
    (observable : W.ctx.Observable) :
    HEq (refinementRouteBackwardObservableComp ctx target W observable) observable := by
  simpa only [refinementRouteBackwardObservableComp] using
    geometryCastTargetObservableComp_heq
      (transportEquationReading (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.reading.equationReading)
      (SelectedRefinementTransport.inverseBaseObject_eq
        (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target)).symm
      (pulledRouteTransportData ctx target).atomEquiv.symm
      (transportArchitectureObject
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (transportEquationSystemExact
        (pulledRouteTransportData ctx target).atomEquiv.symm
        (pullbackTargetGeometry ctx target).core.object
        (pullbackTargetGeometry ctx target).core.contextPreorder
        (pullbackTargetGeometry ctx target).core.algebra.equationSystem)
      (geometryTransportObservableComp (pullbackTargetGeometry ctx target).core
        (pulledRouteTransportData ctx target).atomEquiv.symm)
      (fun _ _ => HEq.rfl) W observable

/-- The pulled-route backward observable comparison preserves its carrier value. -/
theorem pulledRouteBackwardObservableComp_heq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx)
    (W : target.geometry.site.category) (observable : W.ctx.Observable) :
    HEq (pulledRouteBackwardObservableComp ctx target W observable) observable := by
  apply HEq.trans
    (refinementRouteBackwardObservableComp_heq ctx target _
      (exactRouteBackwardObservableComp ctx target W observable))
  exact exactRouteBackwardObservableComp_heq ctx target W observable

/-! ## Canonical exact realization-exact inhabitant -/

/-- Transport a heterogeneous component equality along its authored index
path. -/
private theorem cast_eq_of_heq_along {A : Type u} {F : A → Type v}
    {a b : A} (h : a = b) {x : F a} {y : F b} (hxy : HEq x y) :
    cast (congrArg F h) x = y := by
  cases h
  exact eq_of_heq hxy

/-- The explicit exact inverse package carries its authored forward/backward
upper equivalence. -/
noncomputable def exactInversePackageUpperEquivalence
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    ExactUpperEquivalence (exactSourceGeometry G f).core G.core where
  forward := inverseCorePackageForwardUpper G.core f
  backward := inverseCorePackageBackwardUpper G.core f
  forward_backward := inverseCorePackageForward_comp_backward G.core f
  backward_forward := inverseCorePackageBackward_comp_forward G.core f

/-- Forward realization supply generated by the exact inverse-package
transport.

Implementation notes: all carrier maps, reading laws, and naturality laws are
the concrete generated exact comparisons; no `HGeom` or realization field is
accepted from a caller. -/
noncomputable def exactForwardUpperRealizationSupply
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    UpperRealizationTransportSupply (exactSourceGeometry G f).core G.core
      (exactInversePackageUpperEquivalence G f).forward where
  supportComp := generatedExactSupportComp G f
  axisComp := generatedExactAxisComp G f
  observableComp := generatedExactObservableComp G f
  supportReads := generatedExactSupportComp_reads G f
  axisReads := generatedExactAxisComp_reads G f
  observableReads := generatedExactObservableComp_reads G f
  support_naturality := generatedExactSupportComp_naturality G f
  axis_naturality := generatedExactAxisComp_naturality G f
  observable_naturality := generatedExactObservableComp_naturality G f

/-- Backward realization supply generated by the exact inverse-package
transport.

Implementation notes: this is the genuine backward upper map, not the inverse
context functor of the forward supply repackaged as a certificate. -/
noncomputable def exactBackwardUpperRealizationSupply
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    UpperRealizationTransportSupply G.core (exactSourceGeometry G f).core
      (exactInversePackageUpperEquivalence G f).backward where
  supportComp := exactBackwardSupportComp G f
  axisComp := exactBackwardAxisComp G f
  observableComp := exactBackwardObservableComp G f
  supportReads := exactBackwardSupportComp_reads G f
  axisReads := exactBackwardAxisComp_reads G f
  observableReads := exactBackwardObservableComp_reads G f
  support_naturality := exactBackwardSupportComp_naturality G f
  axis_naturality := exactBackwardAxisComp_naturality G f
  observable_naturality := exactBackwardObservableComp_naturality G f

/-- The explicit canonical exact inverse package is realization-exact.

Implementation notes: the two supplies are generated independently from the
authored forward and backward upper transports.  Each of the six inverse laws
is extracted from the corresponding carrier-preservation HEq, so no lower
inverse or opaque selected-domain is used. -/
noncomputable def exactInversePackageRealizationExact
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    RealizationExactUpperEquivalence
      (exactInversePackageUpperEquivalence G f) where
  homSupply := exactForwardUpperRealizationSupply G f
  invSupply := exactBackwardUpperRealizationSupply G f
  support_hom_inv W support := by
    exact cast_eq_of_heq_along
      (F := fun X : (exactSourceGeometry G f).site.category => X.ctx.Support)
      ((exactInversePackageUpperEquivalence G f).forwardBackwardContext W)
      ((exactBackwardSupportComp_heq G f _
        (generatedExactSupportComp G f W support)).trans
          (generatedExactSupportComp_heq G f W support))
  support_inv_hom W support := by
    exact cast_eq_of_heq_along
      (F := fun X : G.site.category => X.ctx.Support)
      ((exactInversePackageUpperEquivalence G f).backwardForwardContext W)
      ((generatedExactSupportComp_heq G f _
        (exactBackwardSupportComp G f W support)).trans
          (exactBackwardSupportComp_heq G f W support))
  axis_hom_inv W axis := by
    exact cast_eq_of_heq_along
      (F := fun X : (exactSourceGeometry G f).site.category => X.ctx.Axis)
      ((exactInversePackageUpperEquivalence G f).forwardBackwardContext W)
      ((exactBackwardAxisComp_heq G f _
        (generatedExactAxisComp G f W axis)).trans
          (generatedExactAxisComp_heq G f W axis))
  axis_inv_hom W axis := by
    exact cast_eq_of_heq_along
      (F := fun X : G.site.category => X.ctx.Axis)
      ((exactInversePackageUpperEquivalence G f).backwardForwardContext W)
      ((generatedExactAxisComp_heq G f _
        (exactBackwardAxisComp G f W axis)).trans
          (exactBackwardAxisComp_heq G f W axis))
  observable_hom_inv W observable := by
    exact cast_eq_of_heq_along
      (F := fun X : (exactSourceGeometry G f).site.category => X.ctx.Observable)
      ((exactInversePackageUpperEquivalence G f).forwardBackwardContext W)
      ((exactBackwardObservableComp_heq G f _
        (generatedExactObservableComp G f W observable)).trans
          (generatedExactObservableComp_heq G f W observable))
  observable_inv_hom W observable := by
    exact cast_eq_of_heq_along
      (F := fun X : G.site.category => X.ctx.Observable)
      ((exactInversePackageUpperEquivalence G f).backwardForwardContext W)
      ((generatedExactObservableComp_heq G f _
        (exactBackwardObservableComp G f W observable)).trans
          (exactBackwardObservableComp_heq G f W observable))

/-- The realized-refinement inverse package carries its authored
forward/backward upper equivalence. -/
noncomputable def refinementInversePackageUpperEquivalence
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    ExactUpperEquivalence (refinementSourceGeometry G r condition hG).core
      G.core where
  forward := (refinementBaseHom G r condition hG).upper
  backward := refinementSourceBackwardUpper G r condition hG
  forward_backward := by
    subst Y
    exact SelectedRefinementTransport.inverseCorePackageForward_comp_backward
      G.core (selectedTransportDataOfRealizedReflection r condition
        ⟨G.core, rfl⟩)
  backward_forward := by
    subst Y
    exact SelectedRefinementTransport.inverseCorePackageBackward_comp_forward
      G.core (selectedTransportDataOfRealizedReflection r condition
        ⟨G.core, rfl⟩)

/-- Forward realization supply generated by the realized-refinement inverse
package.

Implementation notes: the carrier maps and laws are the generated refinement
comparisons selected from realized reflection; no route leg or realization
certificate is supplied by a caller. -/
noncomputable def refinementForwardUpperRealizationSupply
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    UpperRealizationTransportSupply
      (refinementSourceGeometry G r condition hG).core G.core
      (refinementInversePackageUpperEquivalence G r condition hG).forward where
  supportComp := generatedRefinementSupportComp G r condition hG
  axisComp := generatedRefinementAxisComp G r condition hG
  observableComp := generatedRefinementObservableComp G r condition hG
  supportReads := generatedRefinementSupportComp_reads G r condition hG
  axisReads := generatedRefinementAxisComp_reads G r condition hG
  observableReads := generatedRefinementObservableComp_reads G r condition hG
  support_naturality :=
    generatedRefinementSupportComp_naturality G r condition hG
  axis_naturality :=
    generatedRefinementAxisComp_naturality G r condition hG
  observable_naturality :=
    generatedRefinementObservableComp_naturality G r condition hG

/-- Backward realization supply generated by the realized-refinement inverse
package.

Implementation notes: the supply uses the explicit selected backward upper
transport and its direct carrier-reading laws, independently of the forward
supply. -/
noncomputable def refinementBackwardUpperRealizationSupply
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    UpperRealizationTransportSupply G.core
      (refinementSourceGeometry G r condition hG).core
      (refinementInversePackageUpperEquivalence G r condition hG).backward where
  supportComp := refinementBackwardSupportComp G r condition hG
  axisComp := refinementBackwardAxisComp G r condition hG
  observableComp := refinementBackwardObservableComp G r condition hG
  supportReads := refinementBackwardSupportComp_reads G r condition hG
  axisReads := refinementBackwardAxisComp_reads G r condition hG
  observableReads := refinementBackwardObservableComp_reads G r condition hG
  support_naturality :=
    refinementBackwardSupportComp_naturality G r condition hG
  axis_naturality := refinementBackwardAxisComp_naturality G r condition hG
  observable_naturality :=
    refinementBackwardObservableComp_naturality G r condition hG

/-- The explicit realized-refinement inverse package is realization-exact.

Implementation notes: both upper supplies are theorem-generated from realized
reflection.  The six component inverse laws use the forward and backward
carrier-preservation HEqs and do not retain the source reflection theorem as a
certificate field. -/
noncomputable def refinementInversePackageRealizationExact
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    RealizationExactUpperEquivalence
      (refinementInversePackageUpperEquivalence G r condition hG) where
  homSupply := refinementForwardUpperRealizationSupply G r condition hG
  invSupply := refinementBackwardUpperRealizationSupply G r condition hG
  support_hom_inv W support := by
    exact cast_eq_of_heq_along
      (F := fun X : (refinementSourceGeometry G r condition hG).site.category =>
        X.ctx.Support)
      ((refinementInversePackageUpperEquivalence G r condition hG).forwardBackwardContext
        W)
      ((refinementBackwardSupportComp_heq G r condition hG _
        (generatedRefinementSupportComp G r condition hG W support)).trans
          (generatedRefinementSupportComp_heq G r condition hG W support))
  support_inv_hom W support := by
    exact cast_eq_of_heq_along
      (F := fun X : G.site.category => X.ctx.Support)
      ((refinementInversePackageUpperEquivalence G r condition hG).backwardForwardContext
        W)
      ((generatedRefinementSupportComp_heq G r condition hG _
        (refinementBackwardSupportComp G r condition hG W support)).trans
          (refinementBackwardSupportComp_heq G r condition hG W support))
  axis_hom_inv W axis := by
    exact cast_eq_of_heq_along
      (F := fun X : (refinementSourceGeometry G r condition hG).site.category =>
        X.ctx.Axis)
      ((refinementInversePackageUpperEquivalence G r condition hG).forwardBackwardContext
        W)
      ((refinementBackwardAxisComp_heq G r condition hG _
        (generatedRefinementAxisComp G r condition hG W axis)).trans
          (generatedRefinementAxisComp_heq G r condition hG W axis))
  axis_inv_hom W axis := by
    exact cast_eq_of_heq_along
      (F := fun X : G.site.category => X.ctx.Axis)
      ((refinementInversePackageUpperEquivalence G r condition hG).backwardForwardContext
        W)
      ((generatedRefinementAxisComp_heq G r condition hG _
        (refinementBackwardAxisComp G r condition hG W axis)).trans
          (refinementBackwardAxisComp_heq G r condition hG W axis))
  observable_hom_inv W observable := by
    exact cast_eq_of_heq_along
      (F := fun X : (refinementSourceGeometry G r condition hG).site.category =>
        X.ctx.Observable)
      ((refinementInversePackageUpperEquivalence G r condition hG).forwardBackwardContext
        W)
      ((refinementBackwardObservableComp_heq G r condition hG _
        (generatedRefinementObservableComp G r condition hG W observable)).trans
          (generatedRefinementObservableComp_heq G r condition hG W observable))
  observable_inv_hom W observable := by
    exact cast_eq_of_heq_along
      (F := fun X : G.site.category => X.ctx.Observable)
      ((refinementInversePackageUpperEquivalence G r condition hG).backwardForwardContext
        W)
      ((generatedRefinementObservableComp_heq G r condition hG _
        (refinementBackwardObservableComp G r condition hG W observable)).trans
          (refinementBackwardObservableComp_heq G r condition hG W observable))

/-! ## Generated base and pulled route inhabitants -/

/-- Realization-exact upper equivalence for the base route's canonical exact
leg. -/
noncomputable def baseRouteExactRealizationExact
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  exactInversePackageRealizationExact (baseRefinementGeometry ctx target)
    (baseRouteExactArrow ctx target)

/-- Realization-exact upper equivalence for the base route's
realized-refinement leg. -/
noncomputable def baseRouteRefinementRealizationExact
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  refinementInversePackageRealizationExact target.geometry
    (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
    target.packagePoint_eq

/-- The base-first route realization-exact equivalence is generated by
composing its exact and realized-refinement inhabitants in route order. -/
noncomputable def baseRouteRealizationExact
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  (baseRouteExactRealizationExact ctx target).comp
    (baseRouteRefinementRealizationExact ctx target)

/-- The generated base-route realization equivalence has the actual route
upper map. -/
theorem baseRouteRealizationExact_forward_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    ((exactInversePackageUpperEquivalence (baseRefinementGeometry ctx target)
      (baseRouteExactArrow ctx target)).comp
      (refinementInversePackageUpperEquivalence target.geometry
        (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
        target.packagePoint_eq)).forward =
      (baseRouteGeometryHom ctx target).base.upper := rfl

/-- Realization-exact upper equivalence for the pulled route's
realized-refinement leg. -/
noncomputable def pulledRouteRefinementRealizationExact
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  refinementInversePackageRealizationExact (pullbackTargetGeometry ctx target)
    (ctx.configuration.pulledRefinementAt ctx.source)
    (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
    (pullbackTargetGeometry_packagePoint_eq ctx target)

/-- Realization-exact upper equivalence for the pulled route's canonical exact
leg. -/
noncomputable def pullbackTargetExactRealizationExact
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  exactInversePackageRealizationExact target.geometry
    (pullbackTargetExactArrow ctx target)

/-- The pulled-first route realization-exact equivalence is generated by
composing its realized-refinement and exact inhabitants in route order. -/
noncomputable def pulledRouteRealizationExact
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :=
  (pulledRouteRefinementRealizationExact ctx target).comp
    (pullbackTargetExactRealizationExact ctx target)

/-- The generated pulled-route realization equivalence has the actual route
upper map. -/
theorem pulledRouteRealizationExact_forward_eq
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    ((refinementInversePackageUpperEquivalence
      (pullbackTargetGeometry ctx target)
      (ctx.configuration.pulledRefinementAt ctx.source)
      (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
      (pullbackTargetGeometry_packagePoint_eq ctx target)).comp
      (exactInversePackageUpperEquivalence target.geometry
        (pullbackTargetExactArrow ctx target))).forward =
      (pulledRouteGeometryHom ctx target).base.upper := rfl

end UpperGeometryCleavage
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
