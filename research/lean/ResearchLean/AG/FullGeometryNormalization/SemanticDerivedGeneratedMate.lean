import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedPullbackComparison
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryTransportUnitIso
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonFixedDecision

/-!
# The semantic-derived generated complete-geometry mate

An arbitrary semantic exact square with an explicit pullback proof generates
its G-118 route mate in the mixed pullback fiber. The source comparison moves
that mate to the original northwest fiber, then the top arrow moves it to the
original northeast fiber.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

noncomputable local instance semanticGeneratedMateAtomDecidableEq
    (U : AtomCarrier.{u}) : DecidableEq U.Atom := Classical.decEq _

/-! ## Generated route geometries in the mixed pullback fiber -/

/-- The generated base-first route geometry, placed over the semantic
mixed pullback source using its constructor's package-point theorem. -/
noncomputable def semanticDerivedGeneratedBaseRouteFiberAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber
      ((semanticDerivedRefinementBCConfiguration input).pullbackSourceAt
        (semanticDerivedRefinementBCCompatibleSource input)) :=
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  let ctx := semanticDerivedRefinementBCContext input
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  ⟨problem.generatedBaseRouteGeometryAt PUnit.unit,
    UpperGeometryCleavage.baseRouteGeometry_packagePoint_eq
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
      (problem.sourceTargetGeometryAt PUnit.unit)⟩

/-- The generated pulled-first route geometry, placed over the same
semantic mixed pullback source. -/
noncomputable def semanticDerivedGeneratedPulledRouteFiberAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    GeomFiber
      ((semanticDerivedRefinementBCConfiguration input).pullbackSourceAt
        (semanticDerivedRefinementBCCompatibleSource input)) :=
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  let ctx := semanticDerivedRefinementBCContext input
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  ⟨problem.generatedPulledRouteGeometryAt PUnit.unit,
    UpperGeometryCleavage.pulledRouteGeometry_packagePoint_eq
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
      (problem.sourceTargetGeometryAt PUnit.unit)⟩

/-- The existing G-118 generated complete-geometry mate, regarded as a
vertical morphism in the semantic mixed pullback fiber. -/
noncomputable def semanticDerivedGeneratedMateInMixedFiberAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    semanticDerivedGeneratedBaseRouteFiberAt input Q k g endpoint_eq ⟶
      semanticDerivedGeneratedPulledRouteFiberAt input Q k g endpoint_eq := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  let ctx := semanticDerivedRefinementBCContext input
    (semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq)
  let mate := problem.generatedCompatibleUpperGeometryMateAt PUnit.unit
  letI coreLift : (packageProjection U).IsHomLift
      (𝟙 ((semanticDerivedRefinementBCConfiguration input).pullbackSourceAt
        (semanticDerivedRefinementBCCompatibleSource input))) mate.base := by
    rw [show mate.base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
        (problem.sourceTargetGeometryAt PUnit.unit)).1 from
          problem.generatedCompatibleUpperGeometryMateAt_base PUnit.unit]
    exact (UpperGeometryCleavage.generatedRouteCoreMate
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
      (problem.sourceTargetGeometryAt PUnit.unit)).2
  refine ⟨mate, ?_⟩
  apply CategoryTheory.IsHomLift.of_fac'
    (crossStageProjection.{u, v} U)
    (𝟙 ((semanticDerivedRefinementBCConfiguration input).pullbackSourceAt
      (semanticDerivedRefinementBCCompatibleSource input))) mate
    (UpperGeometryCleavage.baseRouteGeometry_packagePoint_eq
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
      (problem.sourceTargetGeometryAt PUnit.unit))
    (UpperGeometryCleavage.pulledRouteGeometry_packagePoint_eq
      (ctx.retarget (problem.sourceFiberDiagram.obj ⟨PUnit.unit⟩))
      (problem.sourceTargetGeometryAt PUnit.unit))
  rw [crossStageProjection_map]
  exact CategoryTheory.IsHomLift.fac'
    (packageProjection U)
    (𝟙 ((semanticDerivedRefinementBCConfiguration input).pullbackSourceAt
      (semanticDerivedRefinementBCCompatibleSource input)))
    mate.base

/-! ## Transport to the original square and push along its top edge -/

/-- The generated base-route geometry transported from the mixed pullback to
the original northwest point. -/
noncomputable def semanticDerivedGeneratedBaseRouteNorthwestAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    GeomFiber input.square.northwest :=
  (geomFiberTransportFunctor (semanticDerivedPullbackSourceIso input square_isPullback).hom).obj
    (semanticDerivedGeneratedBaseRouteFiberAt input Q k g endpoint_eq)

/-- The generated pulled-route geometry transported from the mixed pullback
to the original northwest point. -/
noncomputable def semanticDerivedGeneratedPulledRouteNorthwestAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    GeomFiber input.square.northwest :=
  (geomFiberTransportFunctor (semanticDerivedPullbackSourceIso input square_isPullback).hom).obj
    (semanticDerivedGeneratedPulledRouteFiberAt input Q k g endpoint_eq)

/-- `m_z`: the actual generated G-118 mate transported through the
semantic mixed-pullback comparison to the original northwest fiber. -/
noncomputable def semanticDerivedGeneratedMateNorthwestAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    semanticDerivedGeneratedBaseRouteNorthwestAt input Q k g endpoint_eq square_isPullback ⟶
      semanticDerivedGeneratedPulledRouteNorthwestAt input Q k g endpoint_eq square_isPullback :=
  (geomFiberTransportFunctor (semanticDerivedPullbackSourceIso input square_isPullback).hom).map
    (semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq)

/-- The top-edge push of `m_z`, a vertical comparison in the original
northeast fiber. -/
noncomputable def semanticDerivedGeneratedMateTopPushAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :=
  (geomFiberTransportFunctor input.square.top).map
    (semanticDerivedGeneratedMateNorthwestAt input Q k g endpoint_eq square_isPullback)

/-! ## Coefficient control -/

/-- The semantic mixed-fiber mate is invertible because it is the actual
G-118 generated comparison, whose invertibility was proved from the generated
cleavage rather than supplied as a new premise. -/
theorem semanticDerivedGeneratedMateInMixedFiberAt_isIso
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    IsIso (semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq) := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  have generatedIsIso : IsIso (show
      problem.generatedBaseRouteGeometryAt PUnit.unit ⟶
        problem.generatedPulledRouteGeometryAt PUnit.unit from
      problem.generatedCompatibleUpperGeometryMateAt PUnit.unit) :=
    problem.generatedCompatibleUpperGeometryMateAt_isIso PUnit.unit
  letI := generatedIsIso
  letI : IsIso (semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq).1 := by
    change IsIso (show
      problem.generatedBaseRouteGeometryAt PUnit.unit ⟶
        problem.generatedPulledRouteGeometryAt PUnit.unit from
      problem.generatedCompatibleUpperGeometryMateAt PUnit.unit)
    infer_instance
  exact geomFiberHom_isIso_of_total_isIso
    (semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq)

/-- Transport through the semantic source comparison preserves the
invertibility of the generated mate. -/
theorem semanticDerivedGeneratedMateNorthwestAt_isIso
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    IsIso (semanticDerivedGeneratedMateNorthwestAt input Q k g endpoint_eq square_isPullback) := by
  letI := semanticDerivedGeneratedMateInMixedFiberAt_isIso input Q k g endpoint_eq
  dsimp only [semanticDerivedGeneratedMateNorthwestAt]
  infer_instance

/-- Pushing along the original top edge preserves the invertibility of the
generated mate. -/
theorem semanticDerivedGeneratedMateTopPushAt_isIso
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    IsIso (semanticDerivedGeneratedMateTopPushAt input Q k g endpoint_eq square_isPullback) := by
  letI := semanticDerivedGeneratedMateNorthwestAt_isIso input Q k g endpoint_eq square_isPullback
  dsimp only [semanticDerivedGeneratedMateTopPushAt]
  infer_instance

/-- The mixed-fiber generated mate fixes the selected coefficient ring.  The
identity is forced by its generated route triangle and the two literal route
coefficient identities. -/
theorem semanticDerivedGeneratedMateInMixedFiberAt_coefficient_id
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :
    (semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq).1.geometry.coefficientHom =
      RingHom.id k := by
  let problem := semanticDerivedCompatibleProblemData input Q k g endpoint_eq
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (problem.generatedCompatibleUpperGeometryMateAt_triangle PUnit.unit)
  change
    (problem.generatedPulledRouteLegAt PUnit.unit).geometry.coefficientHom.comp
        (problem.generatedCompatibleUpperGeometryMateAt
          PUnit.unit).geometry.coefficientHom =
      (problem.generatedBaseRouteLegAt PUnit.unit).geometry.coefficientHom at h
  have hpulled :
      (problem.generatedPulledRouteLegAt PUnit.unit).geometry.coefficientHom =
        RingHom.id k := by
    ext x
    rfl
  have hbase :
      (problem.generatedBaseRouteLegAt PUnit.unit).geometry.coefficientHom =
        RingHom.id k := by
    ext x
    rfl
  rw [hpulled, hbase] at h
  simpa only [RingHom.id_comp] using h

/-- Transporting the generated mate to the northwest fiber preserves its
coefficient identity. -/
theorem semanticDerivedGeneratedMateNorthwestAt_coefficient_id
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedGeneratedMateNorthwestAt input Q k g endpoint_eq square_isPullback).1.geometry.coefficientHom =
      RingHom.id k := by
  dsimp only [semanticDerivedGeneratedMateNorthwestAt]
  change (geomFiberTransportMap (semanticDerivedPullbackSourceIso input square_isPullback).hom
      (semanticDerivedGeneratedMateInMixedFiberAt input Q k g endpoint_eq)).1.geometry.coefficientHom =
    RingHom.id k
  rw [geomFiberTransportMap_coefficientHom]
  exact semanticDerivedGeneratedMateInMixedFiberAt_coefficient_id input Q k g endpoint_eq

/-- The top-edge push of the generated mate still fixes the semantic
coefficient ring. -/
theorem semanticDerivedGeneratedMateTopPushAt_coefficient_id
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (Q : AATCorePackage U)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right) :
    (semanticDerivedGeneratedMateTopPushAt input Q k g endpoint_eq square_isPullback).1.geometry.coefficientHom =
      RingHom.id k := by
  dsimp only [semanticDerivedGeneratedMateTopPushAt]
  change (geomFiberTransportMap input.square.top
      (semanticDerivedGeneratedMateNorthwestAt input Q k g endpoint_eq square_isPullback)).1.geometry.coefficientHom =
    RingHom.id k
  rw [geomFiberTransportMap_coefficientHom]
  exact semanticDerivedGeneratedMateNorthwestAt_coefficient_id input Q k g endpoint_eq square_isPullback

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
