import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldBackwardToggleResidual
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualContextInverseProjection
import Formal.Util.AssertStandardAxioms

/-!
# Local actions of the normalized finite-axis-fold backward toggle

The source-owned Extension toggle has identity forward Support, Axis, and
Observable comparisons.  This module follows those complete dependent actions through the fixed
source-to-southwest transport, exact-left pull, top transport, and canonical
normalization.  The two opcartesian steps are cancelled using the respective
canonical sections; the exact pull is cancelled using injectivity of each
generated exact local comparison.

The result is pointwise over every context and every local value.  It does not
assume a local-action certificate: the three identities are constructed from
the same source automorphism and place it in the actual joint local-fiber
kernel.
-/

namespace AAT.AG.RealizationReconstruction

universe u v

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option maxHeartbeats 1200000

local instance finiteAxisFoldBackwardLocalActionAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Complete dependent Support maps -/

private noncomputable def geometrySupportSigmaMap
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : GeometryTotalHom G H) :
    (Sigma fun context : G.site.category => context.ctx.Support) ->
      (Sigma fun context : H.site.category => context.ctx.Support)
  | ⟨context, support⟩ =>
      ⟨contextForward hom.base context, hom.geometry.supportComp context support⟩

private theorem geometrySupportSigmaMap_comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : GeometryTotalHom G H) (second : GeometryTotalHom H K) :
    geometrySupportSigmaMap (first.comp second) =
      geometrySupportSigmaMap second ∘ geometrySupportSigmaMap first :=
  rfl

private theorem support_eq_of_sigma_eq
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    {first second : Site.ContextCategoryObject P.contextPreorder}
    {support : first.ctx.Support} {support' : second.ctx.Support}
    (equality :
      (⟨first, support⟩ : Sigma fun context => context.ctx.Support) =
        ⟨second, support'⟩) :
    supportEquivOfContextEq (congrArg Sigma.fst equality) support = support' := by
  cases equality
  rfl

private theorem context_object_eq_of_ctx_eq
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

private theorem canonicalGeometrySupportSigmaMap_surjective
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    Function.Surjective
      (geometrySupportSigmaMap (geomTransportAlongHom G sigma)) := by
  rintro ⟨context, support⟩
  let canonical := transportAlongHom G.core sigma
  let sourceContext := contextBackward canonical context
  let sourceSupport :=
    (canonicalSectionSupportEquiv G sigma context).symm support
  refine ⟨⟨sourceContext, sourceSupport⟩, ?_⟩
  apply Sigma.ext (canonicalContextSection_eq G sigma context)
  change HEq
    (geomTransportSupportComp G sigma sourceContext sourceSupport) support
  have sectionEquality :=
    (canonicalSectionSupportEquiv G sigma context).apply_symm_apply support
  exact (cast_heq _ _).symm.trans (heq_of_eq sectionEquality)

private theorem geomFiberLiftSupportSigmaMap_surjective
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (sigma : X ⟶ Y) (source : GeomFiber.{u, v} X) :
    Function.Surjective
      (geometrySupportSigmaMap (geomFiberLift sigma source)) := by
  simpa [geomFiberLift] using
    canonicalGeometrySupportSigmaMap_surjective source.1
      (geomFiberBaseHom sigma source).doctrineHom

private theorem exactGeometryPullSupportSigmaMap_injective
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target) :
    Function.Injective
      (geometrySupportSigmaMap (exactGeometryPullLift input target)) := by
  rintro ⟨firstContext, firstSupport⟩ ⟨secondContext, secondSupport⟩ equality
  have forwardContextEquality := congrArg Sigma.fst equality
  have contextEquality : firstContext = secondContext := by
    apply context_object_eq_of_ctx_eq
    change contextForward (exactGeometryPullLift input target).base firstContext =
      contextForward (exactGeometryPullLift input target).base secondContext at forwardContextEquality
    have cancelled := congrArg
      (fun context => (contextBackward (exactGeometryPullLift input target).base
        context).ctx) forwardContextEquality
    have firstCancel :=
      UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
        target.1 (exactGeometryPullBaseHom input target) firstContext
    have secondCancel :=
      UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
        target.1 (exactGeometryPullBaseHom input target) secondContext
    change
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom target.1
          (exactGeometryPullBaseHom input target))
        (contextForward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target)) firstContext)).ctx =
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom target.1
          (exactGeometryPullBaseHom input target))
        (contextForward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target)) secondContext)).ctx at cancelled
    have firstCancel' :
        (contextBackward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target))
          (contextForward
            (UpperGeometryCleavage.exactBaseHom target.1
              (exactGeometryPullBaseHom input target)) firstContext)).ctx =
          firstContext.ctx := by simpa using firstCancel
    have secondCancel' :
        (contextBackward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target))
          (contextForward
            (UpperGeometryCleavage.exactBaseHom target.1
              (exactGeometryPullBaseHom input target)) secondContext)).ctx =
          secondContext.ctx := by simpa using secondCancel
    rw [firstCancel', secondCancel'] at cancelled
    exact cancelled
  subst secondContext
  have supportEquality :
      (exactGeometryPullLift input target).geometry.supportComp
          firstContext firstSupport =
        (exactGeometryPullLift input target).geometry.supportComp
          firstContext secondSupport :=
    eq_of_heq (Sigma.ext_iff.mp equality).2
  exact Sigma.ext rfl (heq_of_eq
    (UpperGeometryCleavage.generatedExactSupportComp_injective
      target.1 (exactGeometryPullBaseHom input target) firstContext
      supportEquality))

/-! ## Source and transported Support identities -/

theorem finiteAxisFoldExtensionBackward_supportSigmaMap_eq_id :
    geometrySupportSigmaMap finiteAxisFoldExtensionBackwardGeometry =
      _root_.id := by
  funext value
  rcases value with ⟨context, support⟩
  rfl

theorem finiteAxisFoldSouthwestExtensionBackward_supportSigmaMap_eq_id :
    geometrySupportSigmaMap
        finiteAxisFoldSouthwestExtensionBackwardAut.hom.1 =
      _root_.id := by
  let canonical :=
    geomFiberLift finiteAxisFoldSourceToSouthwestExtInstHom
      (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  have canonicalSurjective :
      Function.Surjective (geometrySupportSigmaMap canonical) := by
    exact geomFiberLiftSupportSigmaMap_surjective
      finiteAxisFoldSourceToSouthwestExtInstHom
      (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  funext value
  obtain ⟨sourceValue, rfl⟩ := canonicalSurjective value
  have factorization := congrArg geometrySupportSigmaMap
    (geomFiberTransportMap_fac
      finiteAxisFoldSourceToSouthwestExtInstHom
      finiteAxisFoldExtensionBackwardGeometryFiberAut.hom)
  have pointwise := congrFun factorization sourceValue
  simpa [geometrySupportSigmaMap_comp,
    finiteAxisFoldSouthwestExtensionBackwardAut,
    finiteAxisFoldTransportedExtensionBackwardAut,
    finiteAxisFoldExtensionBackwardGeometryFiberAut,
    finiteAxisFoldExtensionBackwardGeometryFiberHom,
    finiteAxisFoldExtensionBackward_supportSigmaMap_eq_id,
    canonical] using pointwise

private noncomputable abbrev FiniteAxisFoldBackwardLocalActionPulledGeometryFiber :=
  (exactGeometryPullFunctor
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).obj
      finiteAxisFoldSouthwestGeometryFiber

theorem finiteAxisFoldExactLeftExtensionBackward_supportSigmaMap_eq_id :
    geometrySupportSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 =
      _root_.id := by
  let lift := exactGeometryPullLift
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
    finiteAxisFoldSouthwestGeometryFiber
  have liftInjective : Function.Injective (geometrySupportSigmaMap lift) := by
    exact exactGeometryPullSupportSigmaMap_injective
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber
  funext value
  apply liftInjective
  have factorization := congrArg geometrySupportSigmaMap
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestExtensionBackwardAut.hom)
  have pointwise := congrFun factorization value
  change geometrySupportSigmaMap lift
      (geometrySupportSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 value) =
    geometrySupportSigmaMap finiteAxisFoldSouthwestExtensionBackwardAut.hom.1
      (geometrySupportSigmaMap lift value) at pointwise
  rw [finiteAxisFoldSouthwestExtensionBackward_supportSigmaMap_eq_id]
    at pointwise
  simpa using pointwise

theorem finiteAxisFoldActualDirectExtensionBackward_supportSigmaMap_eq_id :
    geometrySupportSigmaMap
        finiteAxisFoldActualDirectExtensionBackwardAut.hom.1 =
      _root_.id := by
  let lift :=
    geomFiberLift
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldBackwardLocalActionPulledGeometryFiber
  have liftSurjective :
      Function.Surjective (geometrySupportSigmaMap lift) := by
    exact geomFiberLiftSupportSigmaMap_surjective
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldBackwardLocalActionPulledGeometryFiber
  funext value
  obtain ⟨sourceValue, rfl⟩ := liftSurjective value
  have factorization := congrArg geometrySupportSigmaMap
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          finiteAxisFoldSouthwestExtensionBackwardAut.hom))
  have pointwise := congrFun factorization sourceValue
  change geometrySupportSigmaMap
      finiteAxisFoldActualDirectExtensionBackwardAut.hom.1
      (geometrySupportSigmaMap lift sourceValue) =
    geometrySupportSigmaMap lift
      (geometrySupportSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 sourceValue)
      at pointwise
  rw [finiteAxisFoldExactLeftExtensionBackward_supportSigmaMap_eq_id]
    at pointwise
  simpa using pointwise

theorem finiteAxisFoldNormalizedExtensionBackward_supportSigmaMap_eq_id :
    geometrySupportSigmaMap
        finiteAxisFoldNormalizedExtensionBackwardAut.hom.f.hom =
      _root_.id := by
  change geometrySupportSigmaMap
      finiteAxisFoldActualDirectExtensionBackwardAut.hom.1 = _root_.id
  exact finiteAxisFoldActualDirectExtensionBackward_supportSigmaMap_eq_id

/-! ## The complete Support-family conclusion -/

theorem finiteAxisFoldNormalizedExtensionBackward_supportEquiv_eq_one
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelSupportEquiv
        finiteAxisFoldNormalizedExtensionBackwardContextKernel context = 1 := by
  apply Equiv.ext
  intro support
  rw [finiteAxisFoldResidualContextKernelSupportEquiv_apply]
  have pairEquality := congrFun
    finiteAxisFoldNormalizedExtensionBackward_supportSigmaMap_eq_id
    (⟨context, support⟩ :
      Sigma fun value : FiniteAxisFoldResidualContextObject =>
        value.ctx.Support)
  have localEquality := support_eq_of_sigma_eq pairEquality
  convert localEquality using 1

/-! ## Complete dependent Axis maps -/

private noncomputable def geometryAxisSigmaMap
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : GeometryTotalHom G H) :
    (Sigma fun context : G.site.category => context.ctx.Axis) ->
      (Sigma fun context : H.site.category => context.ctx.Axis)
  | ⟨context, axis⟩ =>
      ⟨contextForward hom.base context, hom.geometry.axisComp context axis⟩

private theorem geometryAxisSigmaMap_comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : GeometryTotalHom G H) (second : GeometryTotalHom H K) :
    geometryAxisSigmaMap (first.comp second) =
      geometryAxisSigmaMap second ∘ geometryAxisSigmaMap first :=
  rfl

private theorem axis_eq_of_sigma_eq
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    {first second : Site.ContextCategoryObject P.contextPreorder}
    {axis : first.ctx.Axis} {axis' : second.ctx.Axis}
    (equality :
      (⟨first, axis⟩ : Sigma fun context => context.ctx.Axis) =
        ⟨second, axis'⟩) :
    axisEquivOfContextEq (congrArg Sigma.fst equality) axis = axis' := by
  cases equality
  rfl

private theorem canonicalGeometryAxisSigmaMap_surjective
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    Function.Surjective
      (geometryAxisSigmaMap (geomTransportAlongHom G sigma)) := by
  rintro ⟨context, axis⟩
  let canonical := transportAlongHom G.core sigma
  let sourceContext := contextBackward canonical context
  let sourceAxis := (canonicalSectionAxisEquiv G sigma context).symm axis
  refine ⟨⟨sourceContext, sourceAxis⟩, ?_⟩
  apply Sigma.ext (canonicalContextSection_eq G sigma context)
  change HEq (geomTransportAxisComp G sigma sourceContext sourceAxis) axis
  have sectionEquality :=
    (canonicalSectionAxisEquiv G sigma context).apply_symm_apply axis
  exact (cast_heq _ _).symm.trans (heq_of_eq sectionEquality)

private theorem geomFiberLiftAxisSigmaMap_surjective
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (sigma : X ⟶ Y) (source : GeomFiber.{u, v} X) :
    Function.Surjective (geometryAxisSigmaMap (geomFiberLift sigma source)) := by
  simpa [geomFiberLift] using
    canonicalGeometryAxisSigmaMap_surjective source.1
      (geomFiberBaseHom sigma source).doctrineHom

private theorem exactGeometryPullAxisSigmaMap_injective
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target) :
    Function.Injective (geometryAxisSigmaMap (exactGeometryPullLift input target)) := by
  rintro ⟨firstContext, firstAxis⟩ ⟨secondContext, secondAxis⟩ equality
  have forwardContextEquality := congrArg Sigma.fst equality
  have contextEquality : firstContext = secondContext := by
    apply context_object_eq_of_ctx_eq
    change contextForward (exactGeometryPullLift input target).base firstContext =
      contextForward (exactGeometryPullLift input target).base secondContext at forwardContextEquality
    have cancelled := congrArg
      (fun context => (contextBackward (exactGeometryPullLift input target).base context).ctx)
      forwardContextEquality
    have firstCancel :=
      UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
        target.1 (exactGeometryPullBaseHom input target) firstContext
    have secondCancel :=
      UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
        target.1 (exactGeometryPullBaseHom input target) secondContext
    change
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom target.1
          (exactGeometryPullBaseHom input target))
        (contextForward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target)) firstContext)).ctx =
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom target.1
          (exactGeometryPullBaseHom input target))
        (contextForward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target)) secondContext)).ctx at cancelled
    have firstCancel' :
        (contextBackward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target))
          (contextForward
            (UpperGeometryCleavage.exactBaseHom target.1
              (exactGeometryPullBaseHom input target)) firstContext)).ctx =
          firstContext.ctx := by simpa using firstCancel
    have secondCancel' :
        (contextBackward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target))
          (contextForward
            (UpperGeometryCleavage.exactBaseHom target.1
              (exactGeometryPullBaseHom input target)) secondContext)).ctx =
          secondContext.ctx := by simpa using secondCancel
    rw [firstCancel', secondCancel'] at cancelled
    exact cancelled
  subst secondContext
  have axisEquality :
      (exactGeometryPullLift input target).geometry.axisComp firstContext firstAxis =
        (exactGeometryPullLift input target).geometry.axisComp firstContext secondAxis :=
    eq_of_heq (Sigma.ext_iff.mp equality).2
  exact Sigma.ext rfl (heq_of_eq
    (UpperGeometryCleavage.generatedExactAxisComp_injective
      target.1 (exactGeometryPullBaseHom input target) firstContext axisEquality))

theorem finiteAxisFoldExtensionBackward_axisSigmaMap_eq_id :
    geometryAxisSigmaMap finiteAxisFoldExtensionBackwardGeometry =
      _root_.id := by
  funext value
  rcases value with ⟨context, axis⟩
  rfl

theorem finiteAxisFoldSouthwestExtensionBackward_axisSigmaMap_eq_id :
    geometryAxisSigmaMap finiteAxisFoldSouthwestExtensionBackwardAut.hom.1 =
      _root_.id := by
  let canonical := geomFiberLift finiteAxisFoldSourceToSouthwestExtInstHom
    (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  have canonicalSurjective : Function.Surjective (geometryAxisSigmaMap canonical) := by
    exact geomFiberLiftAxisSigmaMap_surjective
      finiteAxisFoldSourceToSouthwestExtInstHom
      (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  funext value
  obtain ⟨sourceValue, rfl⟩ := canonicalSurjective value
  have factorization := congrArg geometryAxisSigmaMap
    (geomFiberTransportMap_fac finiteAxisFoldSourceToSouthwestExtInstHom
      finiteAxisFoldExtensionBackwardGeometryFiberAut.hom)
  have pointwise := congrFun factorization sourceValue
  simpa [geometryAxisSigmaMap_comp,
    finiteAxisFoldSouthwestExtensionBackwardAut,
    finiteAxisFoldTransportedExtensionBackwardAut,
    finiteAxisFoldExtensionBackwardGeometryFiberAut,
    finiteAxisFoldExtensionBackwardGeometryFiberHom,
    finiteAxisFoldExtensionBackward_axisSigmaMap_eq_id, canonical] using pointwise

theorem finiteAxisFoldExactLeftExtensionBackward_axisSigmaMap_eq_id :
    geometryAxisSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 =
      _root_.id := by
  let lift := exactGeometryPullLift
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
    finiteAxisFoldSouthwestGeometryFiber
  have liftInjective : Function.Injective (geometryAxisSigmaMap lift) := by
    exact exactGeometryPullAxisSigmaMap_injective
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber
  funext value
  apply liftInjective
  have factorization := congrArg geometryAxisSigmaMap
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestExtensionBackwardAut.hom)
  have pointwise := congrFun factorization value
  change geometryAxisSigmaMap lift
      (geometryAxisSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 value) =
    geometryAxisSigmaMap finiteAxisFoldSouthwestExtensionBackwardAut.hom.1
      (geometryAxisSigmaMap lift value) at pointwise
  rw [finiteAxisFoldSouthwestExtensionBackward_axisSigmaMap_eq_id] at pointwise
  simpa using pointwise

theorem finiteAxisFoldActualDirectExtensionBackward_axisSigmaMap_eq_id :
    geometryAxisSigmaMap finiteAxisFoldActualDirectExtensionBackwardAut.hom.1 =
      _root_.id := by
  let lift := geomFiberLift
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    FiniteAxisFoldBackwardLocalActionPulledGeometryFiber
  have liftSurjective : Function.Surjective (geometryAxisSigmaMap lift) := by
    exact geomFiberLiftAxisSigmaMap_surjective
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldBackwardLocalActionPulledGeometryFiber
  funext value
  obtain ⟨sourceValue, rfl⟩ := liftSurjective value
  have factorization := congrArg geometryAxisSigmaMap
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          finiteAxisFoldSouthwestExtensionBackwardAut.hom))
  have pointwise := congrFun factorization sourceValue
  change geometryAxisSigmaMap finiteAxisFoldActualDirectExtensionBackwardAut.hom.1
      (geometryAxisSigmaMap lift sourceValue) =
    geometryAxisSigmaMap lift
      (geometryAxisSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 sourceValue) at pointwise
  rw [finiteAxisFoldExactLeftExtensionBackward_axisSigmaMap_eq_id] at pointwise
  simpa using pointwise

theorem finiteAxisFoldNormalizedExtensionBackward_axisSigmaMap_eq_id :
    geometryAxisSigmaMap finiteAxisFoldNormalizedExtensionBackwardAut.hom.f.hom =
      _root_.id := by
  change geometryAxisSigmaMap finiteAxisFoldActualDirectExtensionBackwardAut.hom.1 =
    _root_.id
  exact finiteAxisFoldActualDirectExtensionBackward_axisSigmaMap_eq_id

theorem finiteAxisFoldNormalizedExtensionBackward_axisEquiv_eq_one
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelAxisEquiv
        finiteAxisFoldNormalizedExtensionBackwardContextKernel context = 1 := by
  apply Equiv.ext
  intro axis
  rw [finiteAxisFoldResidualContextKernelAxisEquiv_apply]
  have pairEquality := congrFun
    finiteAxisFoldNormalizedExtensionBackward_axisSigmaMap_eq_id
    (⟨context, axis⟩ : Sigma fun value : FiniteAxisFoldResidualContextObject =>
      value.ctx.Axis)
  have localEquality := axis_eq_of_sigma_eq pairEquality
  convert localEquality using 1

/-! ## Complete dependent Observable maps -/

private noncomputable def geometryObservableSigmaMap
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (hom : GeometryTotalHom G H) :
    (Sigma fun context : G.site.category => context.ctx.Observable) ->
      (Sigma fun context : H.site.category => context.ctx.Observable)
  | ⟨context, observable⟩ =>
      ⟨contextForward hom.base context,
        hom.geometry.observableComp context observable⟩

private theorem geometryObservableSigmaMap_comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : GeometryTotalHom G H) (second : GeometryTotalHom H K) :
    geometryObservableSigmaMap (first.comp second) =
      geometryObservableSigmaMap second ∘ geometryObservableSigmaMap first :=
  rfl

private theorem observable_eq_of_sigma_eq
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    {first second : Site.ContextCategoryObject P.contextPreorder}
    {observable : first.ctx.Observable} {observable' : second.ctx.Observable}
    (equality :
      (⟨first, observable⟩ : Sigma fun context => context.ctx.Observable) =
        ⟨second, observable'⟩) :
    observableEquivOfContextEq (congrArg Sigma.fst equality) observable =
      observable' := by
  cases equality
  rfl

private theorem canonicalGeometryObservableSigmaMap_surjective
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    Function.Surjective
      (geometryObservableSigmaMap (geomTransportAlongHom G sigma)) := by
  rintro ⟨context, observable⟩
  let canonical := transportAlongHom G.core sigma
  let sourceContext := contextBackward canonical context
  let sourceObservable :=
    (canonicalSectionObservableEquiv G sigma context).symm observable
  refine ⟨⟨sourceContext, sourceObservable⟩, ?_⟩
  apply Sigma.ext (canonicalContextSection_eq G sigma context)
  change HEq
    (geomTransportObservableComp G sigma sourceContext sourceObservable) observable
  have sectionEquality :=
    (canonicalSectionObservableEquiv G sigma context).apply_symm_apply observable
  exact (cast_heq _ _).symm.trans (heq_of_eq sectionEquality)

private theorem geomFiberLiftObservableSigmaMap_surjective
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (sigma : X ⟶ Y) (source : GeomFiber.{u, v} X) :
    Function.Surjective
      (geometryObservableSigmaMap (geomFiberLift sigma source)) := by
  simpa [geomFiberLift] using
    canonicalGeometryObservableSigmaMap_surjective source.1
      (geomFiberBaseHom sigma source).doctrineHom

private theorem exactGeometryPullObservableSigmaMap_injective
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target) :
    Function.Injective
      (geometryObservableSigmaMap (exactGeometryPullLift input target)) := by
  rintro ⟨firstContext, firstObservable⟩ ⟨secondContext, secondObservable⟩ equality
  have forwardContextEquality := congrArg Sigma.fst equality
  have contextEquality : firstContext = secondContext := by
    apply context_object_eq_of_ctx_eq
    change contextForward (exactGeometryPullLift input target).base firstContext =
      contextForward (exactGeometryPullLift input target).base secondContext at forwardContextEquality
    have cancelled := congrArg
      (fun context => (contextBackward (exactGeometryPullLift input target).base context).ctx)
      forwardContextEquality
    have firstCancel :=
      UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
        target.1 (exactGeometryPullBaseHom input target) firstContext
    have secondCancel :=
      UpperGeometryCleavage.generatedExactContextBackward_forward_ctx
        target.1 (exactGeometryPullBaseHom input target) secondContext
    change
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom target.1
          (exactGeometryPullBaseHom input target))
        (contextForward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target)) firstContext)).ctx =
      (contextBackward
        (UpperGeometryCleavage.exactBaseHom target.1
          (exactGeometryPullBaseHom input target))
        (contextForward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target)) secondContext)).ctx at cancelled
    have firstCancel' :
        (contextBackward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target))
          (contextForward
            (UpperGeometryCleavage.exactBaseHom target.1
              (exactGeometryPullBaseHom input target)) firstContext)).ctx =
          firstContext.ctx := by simpa using firstCancel
    have secondCancel' :
        (contextBackward
          (UpperGeometryCleavage.exactBaseHom target.1
            (exactGeometryPullBaseHom input target))
          (contextForward
            (UpperGeometryCleavage.exactBaseHom target.1
              (exactGeometryPullBaseHom input target)) secondContext)).ctx =
          secondContext.ctx := by simpa using secondCancel
    rw [firstCancel', secondCancel'] at cancelled
    exact cancelled
  subst secondContext
  have observableEquality :
      (exactGeometryPullLift input target).geometry.observableComp
          firstContext firstObservable =
        (exactGeometryPullLift input target).geometry.observableComp
          firstContext secondObservable :=
    eq_of_heq (Sigma.ext_iff.mp equality).2
  exact Sigma.ext rfl (heq_of_eq
    (UpperGeometryCleavage.generatedExactObservableComp_injective
      target.1 (exactGeometryPullBaseHom input target) firstContext
      observableEquality))

theorem finiteAxisFoldExtensionBackward_observableSigmaMap_eq_id :
    geometryObservableSigmaMap finiteAxisFoldExtensionBackwardGeometry =
      _root_.id := by
  funext value
  rcases value with ⟨context, observable⟩
  rfl

theorem finiteAxisFoldSouthwestExtensionBackward_observableSigmaMap_eq_id :
    geometryObservableSigmaMap finiteAxisFoldSouthwestExtensionBackwardAut.hom.1 =
      _root_.id := by
  let canonical := geomFiberLift finiteAxisFoldSourceToSouthwestExtInstHom
    (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  have canonicalSurjective :
      Function.Surjective (geometryObservableSigmaMap canonical) := by
    exact geomFiberLiftObservableSigmaMap_surjective
      finiteAxisFoldSourceToSouthwestExtInstHom
      (geomFiberMk finiteAxisFoldSourceGeometryPackage)
  funext value
  obtain ⟨sourceValue, rfl⟩ := canonicalSurjective value
  have factorization := congrArg geometryObservableSigmaMap
    (geomFiberTransportMap_fac finiteAxisFoldSourceToSouthwestExtInstHom
      finiteAxisFoldExtensionBackwardGeometryFiberAut.hom)
  have pointwise := congrFun factorization sourceValue
  simpa [geometryObservableSigmaMap_comp,
    finiteAxisFoldSouthwestExtensionBackwardAut,
    finiteAxisFoldTransportedExtensionBackwardAut,
    finiteAxisFoldExtensionBackwardGeometryFiberAut,
    finiteAxisFoldExtensionBackwardGeometryFiberHom,
    finiteAxisFoldExtensionBackward_observableSigmaMap_eq_id, canonical] using pointwise

theorem finiteAxisFoldExactLeftExtensionBackward_observableSigmaMap_eq_id :
    geometryObservableSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 =
      _root_.id := by
  let lift := exactGeometryPullLift
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
    finiteAxisFoldSouthwestGeometryFiber
  have liftInjective : Function.Injective (geometryObservableSigmaMap lift) := by
    exact exactGeometryPullObservableSigmaMap_injective
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestGeometryFiber
  funext value
  apply liftInjective
  have factorization := congrArg geometryObservableSigmaMap
    (exactGeometryPullMap_fac
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      finiteAxisFoldSouthwestExtensionBackwardAut.hom)
  have pointwise := congrFun factorization value
  change geometryObservableSigmaMap lift
      (geometryObservableSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 value) =
    geometryObservableSigmaMap finiteAxisFoldSouthwestExtensionBackwardAut.hom.1
      (geometryObservableSigmaMap lift value) at pointwise
  rw [finiteAxisFoldSouthwestExtensionBackward_observableSigmaMap_eq_id]
    at pointwise
  simpa using pointwise

theorem finiteAxisFoldActualDirectExtensionBackward_observableSigmaMap_eq_id :
    geometryObservableSigmaMap
        finiteAxisFoldActualDirectExtensionBackwardAut.hom.1 =
      _root_.id := by
  let lift := geomFiberLift
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    FiniteAxisFoldBackwardLocalActionPulledGeometryFiber
  have liftSurjective :
      Function.Surjective (geometryObservableSigmaMap lift) := by
    exact geomFiberLiftObservableSigmaMap_surjective
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      FiniteAxisFoldBackwardLocalActionPulledGeometryFiber
  funext value
  obtain ⟨sourceValue, rfl⟩ := liftSurjective value
  have factorization := congrArg geometryObservableSigmaMap
    (geomFiberTransportMap_fac
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      ((exactGeometryPullFunctor
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
          finiteAxisFoldSouthwestExtensionBackwardAut.hom))
  have pointwise := congrFun factorization sourceValue
  change geometryObservableSigmaMap
      finiteAxisFoldActualDirectExtensionBackwardAut.hom.1
      (geometryObservableSigmaMap lift sourceValue) =
    geometryObservableSigmaMap lift
      (geometryObservableSigmaMap
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).map
            finiteAxisFoldSouthwestExtensionBackwardAut.hom).1 sourceValue) at pointwise
  rw [finiteAxisFoldExactLeftExtensionBackward_observableSigmaMap_eq_id]
    at pointwise
  simpa using pointwise

theorem finiteAxisFoldNormalizedExtensionBackward_observableSigmaMap_eq_id :
    geometryObservableSigmaMap
        finiteAxisFoldNormalizedExtensionBackwardAut.hom.f.hom =
      _root_.id := by
  change geometryObservableSigmaMap
      finiteAxisFoldActualDirectExtensionBackwardAut.hom.1 = _root_.id
  exact finiteAxisFoldActualDirectExtensionBackward_observableSigmaMap_eq_id

theorem finiteAxisFoldNormalizedExtensionBackward_observableEquiv_eq_one
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelObservableEquiv
        finiteAxisFoldNormalizedExtensionBackwardContextKernel context = 1 := by
  apply Equiv.ext
  intro observable
  rw [finiteAxisFoldResidualContextKernelObservableEquiv_apply]
  have pairEquality := congrFun
    finiteAxisFoldNormalizedExtensionBackward_observableSigmaMap_eq_id
    (⟨context, observable⟩ :
      Sigma fun value : FiniteAxisFoldResidualContextObject =>
        value.ctx.Observable)
  have localEquality := observable_eq_of_sigma_eq pairEquality
  convert localEquality using 1

/-! ## Joint local-fiber kernel conclusion -/

theorem finiteAxisFoldNormalizedExtensionBackward_mem_localFiberKernel :
    finiteAxisFoldNormalizedExtensionBackwardContextKernel ∈
      FiniteAxisFoldResidualLocalFiberKernel := by
  rw [finiteAxisFoldResidualLocalFiberKernel_mem_iff]
  exact ⟨finiteAxisFoldNormalizedExtensionBackward_supportEquiv_eq_one,
    finiteAxisFoldNormalizedExtensionBackward_axisEquiv_eq_one,
      finiteAxisFoldNormalizedExtensionBackward_observableEquiv_eq_one⟩

/-- The faithful residual action of the source-owned candidate is concentrated
in its stored backward-context factor. -/
theorem finiteAxisFoldNormalizedExtensionBackward_backwardProjection_ne_one :
    finiteAxisFoldResidualContextKernelBackwardProjection
        finiteAxisFoldNormalizedExtensionBackwardContextKernel ≠ 1 := by
  intro equality
  have unopEquality := congrArg MulOpposite.unop equality
  have evaluated := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      permutation finiteAxisFoldActualBackwardToggleContext)
    unopEquality
  apply finiteAxisFoldNormalizedExtensionBackward_moves_context
  exact evaluated

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
