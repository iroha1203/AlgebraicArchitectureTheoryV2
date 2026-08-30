import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateRealization

/-!
# Carrier realization for the generated upper geometry mate

The pulled-route inverse upper map is the literal composite of the exact and
realized-refinement backward transports.  This module constructs its Support,
Axis, and Observable maps from those two canonical transports and proves their
reading and restriction-naturality laws.  No completed predecessor is changed
and no comparison map is supplied by a caller.
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

end UpperGeometryCleavage
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
