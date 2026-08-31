import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleEndpointGeometryIsos

/-!
# Component laws for the complete endpoint comparison isomorphisms

This module exposes the lower projection, category inverse, coefficient, and
dependent Support / Axis / Observable inverse laws carried by the complete
base and pulled endpoint geometry isomorphisms.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

private theorem endpointIsoSupport_hom_inv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (e : (⟨G⟩ : RefinementGeometryCategory U) ≅ ⟨H⟩)
    (W : G.site.category) (support : W.ctx.Support) :
    HEq
      (e.inv.geometry.supportComp
        (refinementGeometryContextForward e.hom.base W)
        (e.hom.geometry.supportComp W support))
      support := by
  change HEq ((e.hom ≫ e.inv).geometry.supportComp W support) support
  rw [e.hom_inv_id]
  rfl

private theorem endpointIsoSupport_inv_hom
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (e : (⟨G⟩ : RefinementGeometryCategory U) ≅ ⟨H⟩)
    (W : H.site.category) (support : W.ctx.Support) :
    HEq
      (e.hom.geometry.supportComp
        (refinementGeometryContextForward e.inv.base W)
        (e.inv.geometry.supportComp W support))
      support := by
  change HEq ((e.inv ≫ e.hom).geometry.supportComp W support) support
  rw [e.inv_hom_id]
  rfl

private theorem endpointIsoAxis_hom_inv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (e : (⟨G⟩ : RefinementGeometryCategory U) ≅ ⟨H⟩)
    (W : G.site.category) (axis : W.ctx.Axis) :
    HEq
      (e.inv.geometry.axisComp
        (refinementGeometryContextForward e.hom.base W)
        (e.hom.geometry.axisComp W axis))
      axis := by
  change HEq ((e.hom ≫ e.inv).geometry.axisComp W axis) axis
  rw [e.hom_inv_id]
  rfl

private theorem endpointIsoAxis_inv_hom
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (e : (⟨G⟩ : RefinementGeometryCategory U) ≅ ⟨H⟩)
    (W : H.site.category) (axis : W.ctx.Axis) :
    HEq
      (e.hom.geometry.axisComp
        (refinementGeometryContextForward e.inv.base W)
        (e.inv.geometry.axisComp W axis))
      axis := by
  change HEq ((e.inv ≫ e.hom).geometry.axisComp W axis) axis
  rw [e.inv_hom_id]
  rfl

private theorem endpointIsoObservable_hom_inv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (e : (⟨G⟩ : RefinementGeometryCategory U) ≅ ⟨H⟩)
    (W : G.site.category) (observable : W.ctx.Observable) :
    HEq
      (e.inv.geometry.observableComp
        (refinementGeometryContextForward e.hom.base W)
        (e.hom.geometry.observableComp W observable))
      observable := by
  change HEq ((e.hom ≫ e.inv).geometry.observableComp W observable) observable
  rw [e.hom_inv_id]
  rfl

private theorem endpointIsoObservable_inv_hom
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (e : (⟨G⟩ : RefinementGeometryCategory U) ≅ ⟨H⟩)
    (W : H.site.category) (observable : W.ctx.Observable) :
    HEq
      (e.hom.geometry.observableComp
        (refinementGeometryContextForward e.inv.base W)
        (e.inv.geometry.observableComp W observable))
      observable := by
  change HEq ((e.inv ≫ e.hom).geometry.observableComp W observable) observable
  rw [e.inv_hom_id]
  rfl

namespace UpperGeometryCompatibleProblemInputData

/-- The base endpoint comparison hom lies over the identity core projection. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.base =
      𝟙 (⟨(input.canonicalAuthoredBaseRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) := by
  let generated := input.generatedBaseRouteLegAt i
  let canonical := input.canonicalAuthoredBaseRouteGeometryHomAt i
  letI : (refinementGeometryProjection U).IsStronglyCartesian generated.base
      generated := input.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian canonical.base
      canonical := input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian i
  let baseIso :
      (⟨(input.canonicalAuthoredBaseRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) ≅
      ⟨(input.generatedBaseRouteGeometryAt i).core⟩ :=
    eqToIso (by rfl)
  have base_fac : canonical.base = baseIso.hom ≫ generated.base := by
    simp [baseIso, generated, canonical]
  let comparison := CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U) (g := baseIso)
    (f := generated.base) (f' := canonical.base) base_fac generated canonical
  change comparison.hom.base = _
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    baseIso.hom comparison.hom).symm

/-- The base endpoint comparison inverse also lies over the identity. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.base =
      𝟙 (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) := by
  let generated := input.generatedBaseRouteLegAt i
  let canonical := input.canonicalAuthoredBaseRouteGeometryHomAt i
  letI : (refinementGeometryProjection U).IsStronglyCartesian generated.base
      generated := input.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian canonical.base
      canonical := input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian i
  let baseIso :
      (⟨(input.canonicalAuthoredBaseRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) ≅
      ⟨(input.generatedBaseRouteGeometryAt i).core⟩ :=
    eqToIso (by rfl)
  have base_fac : canonical.base = baseIso.hom ≫ generated.base := by
    simp [baseIso, generated, canonical]
  let comparison := CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U) (g := baseIso)
    (f := generated.base) (f' := canonical.base) base_fac generated canonical
  change comparison.inv.base = _
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    baseIso.inv comparison.inv).symm

/-- Named base-route category hom-inverse law. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv =
      𝟙 (⟨input.canonicalAuthoredBaseRouteGeometryAt i⟩ :
        RefinementGeometryCategory U) :=
  (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom_inv_id

/-- Named base-route category inverse-hom law. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom =
      𝟙 (⟨input.generatedBaseRouteGeometryAt i⟩ :
        RefinementGeometryCategory U) :=
  (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv_hom_id

/-- The base comparison hom fixes the authored coefficient ring. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac i)
  change
    (input.generatedBaseRouteLegAt i).geometry.coefficientHom.comp
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.geometry.coefficientHom =
      (input.canonicalAuthoredBaseRouteGeometryHomAt i).geometry.coefficientHom at h
  rw [input.generatedBaseRouteLegAt_coefficient_id,
    input.canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom] at h
  simpa only [RingHom.id_comp] using h

/-- The base comparison inverse fixes the authored coefficient ring. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_fac i)
  change
    (input.canonicalAuthoredBaseRouteGeometryHomAt i).geometry.coefficientHom.comp
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.geometry.coefficientHom =
      (input.generatedBaseRouteLegAt i).geometry.coefficientHom at h
  rw [input.canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom,
    input.generatedBaseRouteLegAt_coefficient_id] at h
  simpa only [RingHom.id_comp] using h

/-- Base-route Support cancellation in the hom-inverse direction. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_support_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.canonicalAuthoredBaseRouteGeometryAt i).site.category)
    (support : W.ctx.Support) :
    HEq
      ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.geometry.supportComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.base W)
        ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.geometry.supportComp
          W support))
      support :=
  endpointIsoSupport_hom_inv _ W support

/-- Base-route Support cancellation in the inverse-hom direction. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_support_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedBaseRouteGeometryAt i).site.category)
    (support : W.ctx.Support) :
    HEq
      ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.geometry.supportComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.base W)
        ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.geometry.supportComp
          W support))
      support :=
  endpointIsoSupport_inv_hom _ W support

/-- Base-route Axis cancellation in the hom-inverse direction. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_axis_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.canonicalAuthoredBaseRouteGeometryAt i).site.category)
    (axis : W.ctx.Axis) :
    HEq
      ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.geometry.axisComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.base W)
        ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.geometry.axisComp W axis))
      axis :=
  endpointIsoAxis_hom_inv _ W axis

/-- Base-route Axis cancellation in the inverse-hom direction. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_axis_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedBaseRouteGeometryAt i).site.category)
    (axis : W.ctx.Axis) :
    HEq
      ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.geometry.axisComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.base W)
        ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.geometry.axisComp W axis))
      axis :=
  endpointIsoAxis_inv_hom _ W axis

/-- Base-route Observable cancellation in the hom-inverse direction. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_observable_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.canonicalAuthoredBaseRouteGeometryAt i).site.category)
    (observable : W.ctx.Observable) :
    HEq
      ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.geometry.observableComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.base W)
        ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.geometry.observableComp
          W observable))
      observable :=
  endpointIsoObservable_hom_inv _ W observable

/-- Base-route Observable cancellation in the inverse-hom direction. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_observable_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedBaseRouteGeometryAt i).site.category)
    (observable : W.ctx.Observable) :
    HEq
      ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.geometry.observableComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.base W)
        ((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.geometry.observableComp
          W observable))
      observable :=
  endpointIsoObservable_inv_hom _ W observable

-- Pulled-route laws are stated separately to retain route provenance.

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.base =
      𝟙 (⟨(input.canonicalAuthoredPulledRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) := by
  let generated := input.generatedPulledRouteLegAt i
  let canonical := input.canonicalAuthoredPulledRouteGeometryHomAt i
  letI : (refinementGeometryProjection U).IsStronglyCartesian generated.base
      generated := input.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian canonical.base
      canonical := input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian i
  let baseIso :
      (⟨(input.canonicalAuthoredPulledRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) ≅
      ⟨(input.generatedPulledRouteGeometryAt i).core⟩ :=
    eqToIso (by rfl)
  have base_fac : canonical.base = baseIso.hom ≫ generated.base := by
    simp [baseIso, generated, canonical]
  let comparison := CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U) (g := baseIso)
    (f := generated.base) (f' := canonical.base) base_fac generated canonical
  change comparison.hom.base = _
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    baseIso.hom comparison.hom).symm

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.base =
      𝟙 (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) := by
  let generated := input.generatedPulledRouteLegAt i
  let canonical := input.canonicalAuthoredPulledRouteGeometryHomAt i
  letI : (refinementGeometryProjection U).IsStronglyCartesian generated.base
      generated := input.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian canonical.base
      canonical := input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian i
  let baseIso :
      (⟨(input.canonicalAuthoredPulledRouteGeometryAt i).core⟩ :
        RefinementPackageTotalCategory U) ≅
      ⟨(input.generatedPulledRouteGeometryAt i).core⟩ :=
    eqToIso (by rfl)
  have base_fac : canonical.base = baseIso.hom ≫ generated.base := by
    simp [baseIso, generated, canonical]
  let comparison := CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U) (g := baseIso)
    (f := generated.base) (f' := canonical.base) base_fac generated canonical
  change comparison.inv.base = _
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    baseIso.inv comparison.inv).symm

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom ≫
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv =
      𝟙 (⟨input.canonicalAuthoredPulledRouteGeometryAt i⟩ :
        RefinementGeometryCategory U) :=
  (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom_inv_id

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv ≫
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom =
      𝟙 (⟨input.generatedPulledRouteGeometryAt i⟩ :
        RefinementGeometryCategory U) :=
  (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv_hom_id

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac i)
  change
    (input.generatedPulledRouteLegAt i).geometry.coefficientHom.comp
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.geometry.coefficientHom =
      (input.canonicalAuthoredPulledRouteGeometryHomAt i).geometry.coefficientHom at h
  rw [input.generatedPulledRouteLegAt_coefficient_id,
    input.canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom] at h
  simpa only [RingHom.id_comp] using h

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_fac i)
  change
    (input.canonicalAuthoredPulledRouteGeometryHomAt i).geometry.coefficientHom.comp
        (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.geometry.coefficientHom =
      (input.generatedPulledRouteLegAt i).geometry.coefficientHom at h
  rw [input.canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom,
    input.generatedPulledRouteLegAt_coefficient_id] at h
  simpa only [RingHom.id_comp] using h

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_support_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.canonicalAuthoredPulledRouteGeometryAt i).site.category)
    (support : W.ctx.Support) :
    HEq
      ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.geometry.supportComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.base W)
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.geometry.supportComp
          W support))
      support :=
  endpointIsoSupport_hom_inv _ W support

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_support_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedPulledRouteGeometryAt i).site.category)
    (support : W.ctx.Support) :
    HEq
      ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.geometry.supportComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.base W)
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.geometry.supportComp
          W support))
      support :=
  endpointIsoSupport_inv_hom _ W support

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_axis_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.canonicalAuthoredPulledRouteGeometryAt i).site.category)
    (axis : W.ctx.Axis) :
    HEq
      ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.geometry.axisComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.base W)
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.geometry.axisComp W axis))
      axis :=
  endpointIsoAxis_hom_inv _ W axis

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_axis_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedPulledRouteGeometryAt i).site.category)
    (axis : W.ctx.Axis) :
    HEq
      ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.geometry.axisComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.base W)
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.geometry.axisComp W axis))
      axis :=
  endpointIsoAxis_inv_hom _ W axis

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_observable_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.canonicalAuthoredPulledRouteGeometryAt i).site.category)
    (observable : W.ctx.Observable) :
    HEq
      ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.geometry.observableComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.base W)
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.geometry.observableComp
          W observable))
      observable :=
  endpointIsoObservable_hom_inv _ W observable

theorem canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_observable_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (W : (input.generatedPulledRouteGeometryAt i).site.category)
    (observable : W.ctx.Observable) :
    HEq
      ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.geometry.observableComp
        (refinementGeometryContextForward
          (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.base W)
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.geometry.observableComp
          W observable))
      observable :=
  endpointIsoObservable_inv_hom _ W observable

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
