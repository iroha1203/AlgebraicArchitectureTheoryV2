import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleRouteGeometryQualifications
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredReselectionEquivalence

/-!
# Source presentation replacement: typing gate

This file begins the revision-2 source-side presentation replacement required
by G-118.  The change datum contains only replacement source objects and exact
complete-geometry isomorphisms over selected core-fiber isomorphisms.  The
changed diagram, edges, comparator, qualification proofs, and coefficient laws
are reconstructed below; none of them is accepted as a certificate.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

/-- A source-only complete-geometry presentation change.  Its fields stop at
the replacement objects and the selected exact isomorphisms; in particular it
does not contain a changed input or any generated endpoint comparison. -/
structure UpperGeometryCompatibleSourcePresentationChange
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) where
  /-- Replacement object in the same selected source core fiber. -/
  sourceFiber : P.Vertex →
    CoreFiber (ctx.configuration.targetPointAt ctx.source)
  /-- Replacement fixed-coefficient complete geometry. -/
  sourceGeometry : (i : P.Vertex) →
    FixedCoefficientGeometryAt (sourceFiber i).1 k
  /-- Selected comparison to the original core-fiber object. -/
  coreIso : (i : P.Vertex) →
    sourceFiber i ≅ input.sourceFiberDiagram.obj ⟨i⟩
  /-- Selected exact complete-geometry comparison over `coreIso`. -/
  geometryIso : (i : P.Vertex) →
    (sourceGeometry i).package ≅ (input.sourceGeometry i).package
  /-- The forward exact comparison projects to the selected core comparison. -/
  geometryIso_hom_base : ∀ i,
    (geometryIso i).hom.base = (coreIso i).hom.1
  /-- The inverse exact comparison projects to the selected inverse. -/
  geometryIso_inv_base : ∀ i,
    (geometryIso i).inv.base = (coreIso i).inv.1
  /-- The forward comparison fixes the selected coefficient ring. -/
  geometryIso_hom_coefficient_id : ∀ i,
    (geometryIso i).hom.geometry.coefficientHom = RingHom.id k
  /-- The inverse comparison fixes the selected coefficient ring. -/
  geometryIso_inv_coefficient_id : ∀ i,
    (geometryIso i).inv.geometry.coefficientHom = RingHom.id k

namespace UpperGeometryCompatibleSourcePresentationChange

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- The replacement core-fiber diagram, obtained by conjugating every actual
path map by the selected vertex isomorphisms. -/
noncomputable def changedSourceFiberDiagram
    (change : UpperGeometryCompatibleSourcePresentationChange input) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.targetPointAt ctx.source) where
  obj i := change.sourceFiber i.vertex
  map {i j} path :=
    (change.coreIso i.vertex).hom ≫ input.sourceFiberDiagram.map path ≫
      (change.coreIso j.vertex).inv
  map_id i := by simp
  map_comp first second := by simp [Category.assoc]

/-- The selected core comparisons assemble to the actual natural isomorphism
from the reconstructed source diagram to the original one. -/
noncomputable def sourceFiberDiagramIso
    (change : UpperGeometryCompatibleSourcePresentationChange input) :
    change.changedSourceFiberDiagram ≅ input.sourceFiberDiagram :=
  NatIso.ofComponents (fun i => change.coreIso i.vertex)
    (by simp [changedSourceFiberDiagram])

/-- The changed source edge is the literal conjugate of the old source edge. -/
noncomputable def changedEdgeLift
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (change.sourceGeometry i).package
      (change.sourceGeometry j).package :=
  (change.geometryIso i).hom ≫ input.sourceTransport.edgeLift edge ≫
    (change.geometryIso j).inv

/-- The changed edge projects to the actual conjugated core-fiber diagram
map. -/
theorem changedEdgeLift_base
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (change.changedEdgeLift edge).base =
      (change.changedSourceFiberDiagram.map
        (presentedEdgePath edge)).1 := by
  simp only [changedEdgeLift, changedSourceFiberDiagram]
  change ((change.geometryIso i).hom.base.comp
      (input.sourceTransport.edgeLift edge).base).comp
        (change.geometryIso j).inv.base = _
  rw [change.geometryIso_hom_base, change.geometryIso_inv_base,
    input.sourceTransport.edge_base]
  rfl

/-- Conjugation preserves the geometry-stage strongly-cocartesian source-edge
qualification.  The old edge's isomorphism is itself derived from its stored
strongly-cocartesian qualification. -/
theorem changedEdgeLift_geometryStrong
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (geometryProjection U).IsStronglyCocartesian
      (change.changedEdgeLift edge).base (change.changedEdgeLift edge) := by
  letI : IsIso (show (input.sourceGeometry i).package ⟶
      (input.sourceGeometry j).package from
        input.sourceTransport.edgeLift edge) :=
    input.sourceTransportGeometryEdge_isIso edge
  letI : IsIso (show (change.sourceGeometry i).package ⟶
      (change.sourceGeometry j).package from change.changedEdgeLift edge) := by
    unfold changedEdgeLift
    infer_instance
  letI : (geometryProjection U).IsHomLift
      (change.changedEdgeLift edge).base (change.changedEdgeLift edge) := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map (change.changedEdgeLift edge))
      (change.changedEdgeLift edge)
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := geometryProjection U) (f := (change.changedEdgeLift edge).base)
    (change.changedEdgeLift edge)

/-- Conjugation independently preserves the core-stage qualification. -/
theorem changedEdgeLift_coreStrong
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      (change.changedEdgeLift edge).base.base
      (change.changedEdgeLift edge).base := by
  letI : IsIso (show (input.sourceGeometry i).package ⟶
      (input.sourceGeometry j).package from
        input.sourceTransport.edgeLift edge) :=
    input.sourceTransportGeometryEdge_isIso edge
  letI : IsIso (show (change.sourceGeometry i).package ⟶
      (change.sourceGeometry j).package from change.changedEdgeLift edge) := by
    unfold changedEdgeLift
    infer_instance
  letI : IsIso (show (change.sourceGeometry i).package.core ⟶
      (change.sourceGeometry j).package.core from
        (change.changedEdgeLift edge).base) := by
    change IsIso ((geometryProjection U).map (change.changedEdgeLift edge))
    infer_instance
  letI : (packageProjection U).IsHomLift
      (change.changedEdgeLift edge).base.base
      (change.changedEdgeLift edge).base := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map (change.changedEdgeLift edge).base)
      (change.changedEdgeLift edge).base
    infer_instance
  exact CategoryTheory.Functor.IsStronglyCocartesian.of_isIso
    (p := packageProjection U) (f := (change.changedEdgeLift edge).base.base)
    (change.changedEdgeLift edge).base

/-- The changed source edge fixes coefficients, derived from the three
independent coefficient identities in its defining composite. -/
theorem changedEdgeLift_coefficient_id
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (change.changedEdgeLift edge).geometry.coefficientHom = RingHom.id k := by
  change ((change.geometryIso j).inv.geometry.coefficientHom.comp
      (input.sourceTransport.edgeLift edge).geometry.coefficientHom).comp
        (change.geometryIso i).hom.geometry.coefficientHom = RingHom.id k
  rw [change.geometryIso_hom_coefficient_id,
    change.geometryIso_inv_coefficient_id,
    input.sourceTransport.edge_coefficient_id]
  ext x
  rfl

/-- The changed authored comparator is reconstructed by complete-geometry
conjugation at the target vertex. -/
noncomputable def changedComparator
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (cell : P.TwoCell) :
    CompositeFiberAut
      ((change.sourceGeometry (P.twoTarget cell)).package) :=
  CompositeFiberAut.conjugationEquiv
    (change.geometryIso (P.twoTarget cell)).symm
    (input.sourceTransport.comparator cell)

/-- The reconstructed comparator fixes coefficients. -/
theorem changedComparator_coefficient_id
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (change.changedComparator cell)).geometry.coefficientHom =
        RingHom.id k := by
  change (((change.geometryIso (P.twoTarget cell)).inv.geometry.coefficientHom.comp
      (CompositeFiberAut.hom
        (input.sourceTransport.comparator cell)).geometry.coefficientHom).comp
      (change.geometryIso (P.twoTarget cell)).hom.geometry.coefficientHom) =
        RingHom.id k
  rw [change.geometryIso_hom_coefficient_id,
    change.geometryIso_inv_coefficient_id,
    input.sourceTransport.comparator_coefficient_id]
  ext x
  rfl

/-- The reconstructed edge family with both independently derived local
qualifications. -/
noncomputable def changedTwoLayerLiftData
    (change : UpperGeometryCompatibleSourcePresentationChange input) :
    TwoLayerLiftData.{u, v} P U where
  geometry i := (change.sourceGeometry i).package
  edgeLift edge := change.changedEdgeLift edge
  edgeGeometryStrong edge := change.changedEdgeLift_geometryStrong edge
  edgeCoreStrong edge := change.changedEdgeLift_coreStrong edge

/-- Evaluation of every changed path projects to the corresponding map of the
reconstructed core-fiber diagram. -/
theorem changedPathLift_base
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    {i j : P.Vertex} (path : P.Path i j) :
    (change.changedTwoLayerLiftData.pathLift path).base =
      (change.changedSourceFiberDiagram.map path).1 := by
  induction path with
  | nil vertex =>
      change (GeometryTotalHom.id
          (change.sourceGeometry vertex).package).base =
        (change.changedSourceFiberDiagram.map (𝟙 ⟨vertex⟩)).1
      have h := congrArg (fun hom => hom.1)
        (change.changedSourceFiberDiagram.map_id ⟨vertex⟩)
      exact h.symm
  | cons edge tail inductionHypothesis =>
      change (change.changedEdgeLift edge).base.comp
          (change.changedTwoLayerLiftData.pathLift tail).base =
        (change.changedSourceFiberDiagram.map (.cons edge tail)).1
      rw [change.changedEdgeLift_base edge, inductionHypothesis]
      change ((change.changedSourceFiberDiagram.map
          (presentedEdgePath edge)) ≫
        change.changedSourceFiberDiagram.map tail).1 = _
      rw [← Functor.map_comp]
      rfl

/-- The two changed paths of every authored two-cell have the same pointed
base because both are actual morphisms in the same reconstructed core fiber. -/
theorem changedTwoCellBase
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (cell : P.TwoCell) :
    ((change.changedTwoLayerLiftData.pathLift
      (P.twoLeft cell)).base.base) =
      ((change.changedTwoLayerLiftData.pathLift
        (P.twoRight cell)).base.base) := by
  rw [change.changedPathLift_base, change.changedPathLift_base]
  let left := change.changedSourceFiberDiagram.map (P.twoLeft cell)
  let right := change.changedSourceFiberDiagram.map (P.twoRight cell)
  letI : (packageProjection U).IsHomLift
      (𝟙 (ctx.configuration.targetPointAt ctx.source)) left.1 := left.2
  letI : (packageProjection U).IsHomLift
      (𝟙 (ctx.configuration.targetPointAt ctx.source)) right.1 := right.2
  have leftFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U)
    (𝟙 (ctx.configuration.targetPointAt ctx.source)) left.1
  have rightFac := CategoryTheory.IsHomLift.fac'
    (packageProjection U)
    (𝟙 (ctx.configuration.targetPointAt ctx.source)) right.1
  simpa only using leftFac.trans rightFac.symm

/-- The complete changed source transport reconstructed from `input` and the
source presentation change alone. -/
noncomputable def changedSourceTransport
    (change : UpperGeometryCompatibleSourcePresentationChange input) :
    FixedCoefficientTwoLayerTransportOver P
      change.changedSourceFiberDiagram k change.sourceGeometry where
  edgeLift edge := change.changedEdgeLift edge
  edge_base edge := change.changedEdgeLift_base edge
  edgeGeometryStrong edge := change.changedEdgeLift_geometryStrong edge
  edgeCoreStrong edge := change.changedEdgeLift_coreStrong edge
  twoCellBase cell := change.changedTwoCellBase cell
  comparator cell := change.changedComparator cell
  edge_coefficient_id edge := change.changedEdgeLift_coefficient_id edge
  comparator_coefficient_id cell := change.changedComparator_coefficient_id cell

/-- Certificate-free reconstruction of the changed compatible input.  The
root, reachability paths, context, presentation, and coefficient ring are
unchanged. -/
noncomputable def changedInput
    (change : UpperGeometryCompatibleSourcePresentationChange input) :
    UpperGeometryCompatibleProblemInputData ctx P k where
  root := input.root
  rootPath := input.rootPath
  sourceFiberDiagram := change.changedSourceFiberDiagram
  sourceGeometry := change.sourceGeometry
  sourceTransport := change.changedSourceTransport

/-! ## Generated base endpoint comparison -/

/-- Exact core-fiber comparison between the independently generated base-route
endpoints.  The middle factor is the actual reverse-route image of `coreIso`;
the outer factors are the generator's own exact normalizations. -/
noncomputable def generatedBaseRouteExactCoreIsoAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.changedInput.generatedBaseRouteGeometryAt i).core ≅
      (input.generatedBaseRouteGeometryAt i).core :=
  (CategoryTheory.Functor.Fiber.fiberInclusion.mapIso
    ((change.changedInput.generatedBaseRouteCoreIsoAt i) ≪≫
      (((ctx.legacyRegime).reverseBase ⋙
        exact_bottom_semantic_global_reindex_functor
          (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst).mapIso
            (change.coreIso i)) ≪≫
      (input.generatedBaseRouteCoreIsoAt i).symm))

/-- The exact lower comparison satisfies the required factorization between
the two independently generated base-route legs. -/
theorem generatedBaseRouteExactCoreIsoAt_hom_fac
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactPackageToRefinement U).map
        (change.generatedBaseRouteExactCoreIsoAt i).hom ≫
      (input.generatedBaseRouteLegAt i).base =
    (change.changedInput.generatedBaseRouteLegAt i).base ≫
      (exactPackageToRefinement U).map (change.geometryIso i).hom.base := by
  change (exactPackageToRefinement U).map
      (((change.changedInput.generatedBaseRouteCoreIsoAt i).hom.1 ≫
        ((((ctx.legacyRegime).reverseBase ⋙
          exact_bottom_semantic_global_reindex_functor
            (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst).map
              (change.coreIso i).hom).1)) ≫
        (input.generatedBaseRouteCoreIsoAt i).inv.1) ≫
      (input.generatedBaseRouteLegAt i).base = _
  rw [Functor.map_comp, Functor.map_comp]
  have hInv : (exactPackageToRefinement U).map
        (input.generatedBaseRouteCoreIsoAt i).inv.1 ≫
      (input.generatedBaseRouteLegAt i).base =
        ctx.baseCompositeLegAt (input.sourceFiberDiagram.obj ⟨i⟩) := by
    dsimp only [UpperGeometryCompatibleProblemInputData.generatedBaseRouteCoreIsoAt,
      UpperGeometryCleavage.baseRouteComparisonCoreIso]
    rw [UpperGeometryCleavage.baseRouteComparisonCoreInv_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
      UpperGeometryCompatibleProblemInputData.generatedBaseRouteLegAt,
      ActiveRefinementBCContext.baseCompositeLegAt] using
        UpperGeometryCleavage.baseRouteComparisonInv_fac
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
          (input.sourceTargetGeometryAt i)
  have hNat := ctx.baseCompositeLegAt_naturality (change.coreIso i).hom
  change (exactPackageToRefinement U).map
      (((ctx.legacyRegime).reverseBase ⋙
        exact_bottom_semantic_global_reindex_functor
          (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst).map
            (change.coreIso i).hom).1 ≫
      ctx.baseCompositeLegAt (input.sourceFiberDiagram.obj ⟨i⟩) =
    ctx.baseCompositeLegAt (change.sourceFiber i) ≫
      (exactPackageToRefinement U).map (change.coreIso i).hom.1 at hNat
  have hHom : (exactPackageToRefinement U).map
        (change.changedInput.generatedBaseRouteCoreIsoAt i).hom.1 ≫
      ctx.baseCompositeLegAt (change.sourceFiber i) =
        (change.changedInput.generatedBaseRouteLegAt i).base := by
    dsimp only [UpperGeometryCompatibleProblemInputData.generatedBaseRouteCoreIsoAt,
      UpperGeometryCleavage.baseRouteComparisonCoreIso]
    rw [UpperGeometryCleavage.baseRouteComparisonCoreHom_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
      UpperGeometryCompatibleProblemInputData.generatedBaseRouteLegAt,
      ActiveRefinementBCContext.baseCompositeLegAt,
      changedInput, changedSourceFiberDiagram] using
        UpperGeometryCleavage.baseRouteComparisonHom_fac
          (ctx.retarget (change.sourceFiber i))
          (change.changedInput.sourceTargetGeometryAt i)
  simp only [Category.assoc]
  rw [hInv, hNat]
  rw [← Category.assoc, hHom, change.geometryIso_hom_base]

/-- Strongly-cartesian uniqueness lifts the exact lower naturality square to
the complete refinement-geometry comparison of the two generated base
endpoints. -/
noncomputable def generatedBaseRouteRefinementGeometryIsoAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (⟨change.changedInput.generatedBaseRouteGeometryAt i⟩ :
      RefinementGeometryCategory.{u, v} U) ≅
    ⟨input.generatedBaseRouteGeometryAt i⟩ := by
  let oldLeg := input.generatedBaseRouteLegAt i
  let newLeg := change.changedInput.generatedBaseRouteLegAt i
  let sourceIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.geometryIso i)
  let candidate := newLeg ≫ sourceIso.hom
  let lowerIso := (exactPackageToRefinement U).mapIso
    (change.generatedBaseRouteExactCoreIsoAt i)
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      oldLeg.base oldLeg := input.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      newLeg.base newLeg :=
    change.changedInput.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsHomLift
      sourceIso.hom.base sourceIso.hom :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      sourceIso.hom.base sourceIso.hom :=
    CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (p := refinementGeometryProjection U) (f := sourceIso.hom.base)
      sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      candidate.base candidate := by
    dsimp only [candidate]
    exact CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)
  have base_fac : candidate.base = lowerIso.hom ≫ oldLeg.base := by
    dsimp only [candidate, lowerIso, sourceIso, oldLeg, newLeg]
    exact (change.generatedBaseRouteExactCoreIsoAt_hom_fac i).symm
  exact CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U) (g := lowerIso)
    (f := oldLeg.base) (f' := candidate.base) base_fac oldLeg candidate

/-- The refinement comparison hom has exactly the generated lower naturality
map as projection. -/
theorem generatedBaseRouteRefinementGeometryIsoAt_hom_base
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedBaseRouteRefinementGeometryIsoAt i).hom.base =
      (exactPackageToRefinement U).map
        (change.generatedBaseRouteExactCoreIsoAt i).hom := by
  let oldLeg := input.generatedBaseRouteLegAt i
  let newLeg := change.changedInput.generatedBaseRouteLegAt i
  let sourceIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.geometryIso i)
  let candidate := newLeg ≫ sourceIso.hom
  let lowerIso := (exactPackageToRefinement U).mapIso
    (change.generatedBaseRouteExactCoreIsoAt i)
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      oldLeg.base oldLeg := input.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      newLeg.base newLeg :=
    change.changedInput.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsHomLift
      sourceIso.hom.base sourceIso.hom :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      sourceIso.hom.base sourceIso.hom :=
    CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (p := refinementGeometryProjection U) (f := sourceIso.hom.base)
      sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      candidate.base candidate := by
    dsimp only [candidate]
    exact CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)
  have base_fac : candidate.base = lowerIso.hom ≫ oldLeg.base := by
    dsimp only [candidate, lowerIso, sourceIso, oldLeg, newLeg]
    exact (change.generatedBaseRouteExactCoreIsoAt_hom_fac i).symm
  let comparison := CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U) (g := lowerIso)
    (f := oldLeg.base) (f' := candidate.base) base_fac oldLeg candidate
  change comparison.hom.base = lowerIso.hom
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U) lowerIso.hom comparison.hom).symm

/-- The inverse refinement comparison projects to the inverse exact lower
map. -/
theorem generatedBaseRouteRefinementGeometryIsoAt_inv_base
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedBaseRouteRefinementGeometryIsoAt i).inv.base =
      (exactPackageToRefinement U).map
        (change.generatedBaseRouteExactCoreIsoAt i).inv := by
  let comparison := change.generatedBaseRouteRefinementGeometryIsoAt i
  let lowerIso := (exactPackageToRefinement U).mapIso
    (change.generatedBaseRouteExactCoreIsoAt i)
  change comparison.inv.base = lowerIso.inv
  change (refinementGeometryProjection U).map comparison.inv = lowerIso.inv
  have hhom : (refinementGeometryProjection U).map comparison.hom =
      lowerIso.hom := by
    exact change.generatedBaseRouteRefinementGeometryIsoAt_hom_base i
  have hcomp := congrArg
    (fun hom => (refinementGeometryProjection U).map hom)
    comparison.hom_inv_id
  simp only [Functor.map_comp] at hcomp
  rw [hhom] at hcomp
  apply (cancel_epi lowerIso.hom).1
  rw [hcomp, lowerIso.hom_inv_id]
  exact (refinementGeometryProjection U).map_id _

/-- Exactification of the generated base comparison hom. -/
noncomputable def generatedBaseRouteExactGeometryHomAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    GeometryTotalHom
      (change.changedInput.generatedBaseRouteGeometryAt i)
      (input.generatedBaseRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (change.generatedBaseRouteExactCoreIsoAt i).hom
    (change.generatedBaseRouteRefinementGeometryIsoAt i).hom
    (change.generatedBaseRouteRefinementGeometryIsoAt_hom_base i)

/-- Exactification of the independently generated inverse. -/
noncomputable def generatedBaseRouteExactGeometryInvAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    GeometryTotalHom
      (input.generatedBaseRouteGeometryAt i)
      (change.changedInput.generatedBaseRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (change.generatedBaseRouteExactCoreIsoAt i).inv
    (change.generatedBaseRouteRefinementGeometryIsoAt i).inv
    (change.generatedBaseRouteRefinementGeometryIsoAt_inv_base i)

/-- Re-embedding the exact base comparison recovers the cartesian-uniqueness
comparison. -/
theorem generatedBaseRouteExactGeometryHomAt_toRefinement
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (change.generatedBaseRouteExactGeometryHomAt i) =
      (change.generatedBaseRouteRefinementGeometryIsoAt i).hom :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- Re-embedding the exact inverse recovers the independently constructed
refinement inverse. -/
theorem generatedBaseRouteExactGeometryInvAt_toRefinement
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (change.generatedBaseRouteExactGeometryInvAt i) =
      (change.generatedBaseRouteRefinementGeometryIsoAt i).inv :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The generated base endpoint comparison is an exact complete-geometry
isomorphism, constructed rather than supplied. -/
noncomputable def generatedBaseRouteExactGeometryIsoAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.changedInput.generatedBaseRouteGeometryAt i ≅
      input.generatedBaseRouteGeometryAt i where
  hom := change.generatedBaseRouteExactGeometryHomAt i
  inv := change.generatedBaseRouteExactGeometryInvAt i
  hom_inv_id := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    rw [Functor.map_comp,
      change.generatedBaseRouteExactGeometryHomAt_toRefinement,
      change.generatedBaseRouteExactGeometryInvAt_toRefinement]
    calc
      _ = 𝟙 _ :=
        (change.generatedBaseRouteRefinementGeometryIsoAt i).hom_inv_id
      _ = (exactGeometryToRefinementGeometry U).map (𝟙 _) :=
        ((exactGeometryToRefinementGeometry U).map_id _).symm
  inv_hom_id := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    rw [Functor.map_comp,
      change.generatedBaseRouteExactGeometryInvAt_toRefinement,
      change.generatedBaseRouteExactGeometryHomAt_toRefinement]
    calc
      _ = 𝟙 _ :=
        (change.generatedBaseRouteRefinementGeometryIsoAt i).inv_hom_id
      _ = (exactGeometryToRefinementGeometry U).map (𝟙 _) :=
        ((exactGeometryToRefinementGeometry U).map_id _).symm

/-! ## Generated pulled endpoint comparison -/

/-- Exact core-fiber comparison between the independently generated pulled
endpoints. -/
noncomputable def generatedPulledRouteExactCoreIsoAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.changedInput.generatedPulledRouteGeometryAt i).core ≅
      (input.generatedPulledRouteGeometryAt i).core :=
  (CategoryTheory.Functor.Fiber.fiberInclusion.mapIso
    ((change.changedInput.generatedPulledRouteCoreIsoAt i) ≪≫
      ((exact_bottom_semantic_global_reindex_functor
          (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst ⋙
        (ctx.legacyRegime).reversePullback).mapIso (change.coreIso i)) ≪≫
      (input.generatedPulledRouteCoreIsoAt i).symm))

/-- The pulled exact lower comparison satisfies the naturality factorization
between the independently generated legs. -/
theorem generatedPulledRouteExactCoreIsoAt_hom_fac
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactPackageToRefinement U).map
        (change.generatedPulledRouteExactCoreIsoAt i).hom ≫
      (input.generatedPulledRouteLegAt i).base =
    (change.changedInput.generatedPulledRouteLegAt i).base ≫
      (exactPackageToRefinement U).map (change.geometryIso i).hom.base := by
  change (exactPackageToRefinement U).map
      (((change.changedInput.generatedPulledRouteCoreIsoAt i).hom.1 ≫
        ((exact_bottom_semantic_global_reindex_functor
          (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst ⋙
          (ctx.legacyRegime).reversePullback).map
            (change.coreIso i).hom).1) ≫
        (input.generatedPulledRouteCoreIsoAt i).inv.1) ≫
      (input.generatedPulledRouteLegAt i).base = _
  rw [Functor.map_comp, Functor.map_comp]
  have hInv : (exactPackageToRefinement U).map
        (input.generatedPulledRouteCoreIsoAt i).inv.1 ≫
      (input.generatedPulledRouteLegAt i).base =
        ctx.pulledCompositeLegAt (input.sourceFiberDiagram.obj ⟨i⟩) := by
    dsimp only [UpperGeometryCompatibleProblemInputData.generatedPulledRouteCoreIsoAt,
      UpperGeometryCleavage.pulledRouteComparisonCoreIso]
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreInv_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
      UpperGeometryCompatibleProblemInputData.generatedPulledRouteLegAt,
      ActiveRefinementBCContext.pulledCompositeLegAt] using
        UpperGeometryCleavage.pulledRouteComparisonInv_fac
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
          (input.sourceTargetGeometryAt i)
  have hNat := ctx.pulledCompositeLegAt_naturality (change.coreIso i).hom
  change (exactPackageToRefinement U).map
      ((exact_bottom_semantic_global_reindex_functor
        (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst ⋙
        (ctx.legacyRegime).reversePullback).map (change.coreIso i).hom).1 ≫
      ctx.pulledCompositeLegAt (input.sourceFiberDiagram.obj ⟨i⟩) =
    ctx.pulledCompositeLegAt (change.sourceFiber i) ≫
      (exactPackageToRefinement U).map (change.coreIso i).hom.1 at hNat
  have hHom : (exactPackageToRefinement U).map
        (change.changedInput.generatedPulledRouteCoreIsoAt i).hom.1 ≫
      ctx.pulledCompositeLegAt (change.sourceFiber i) =
        (change.changedInput.generatedPulledRouteLegAt i).base := by
    dsimp only [UpperGeometryCompatibleProblemInputData.generatedPulledRouteCoreIsoAt,
      UpperGeometryCleavage.pulledRouteComparisonCoreIso]
    rw [UpperGeometryCleavage.pulledRouteComparisonCoreHom_toRefinement]
    simpa [RefinementPackageHom.comp,
      UpperGeometryCleavage.retargetedContext,
      UpperGeometryCleavage.targetCoreFiber,
      UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
      UpperGeometryCompatibleProblemInputData.generatedPulledRouteLegAt,
      ActiveRefinementBCContext.pulledCompositeLegAt,
      changedInput, changedSourceFiberDiagram] using
        UpperGeometryCleavage.pulledRouteComparisonHom_fac
          (ctx.retarget (change.sourceFiber i))
          (change.changedInput.sourceTargetGeometryAt i)
  simp only [Category.assoc]
  rw [hInv, hNat]
  rw [← Category.assoc, hHom, change.geometryIso_hom_base]

/-- Strongly-cartesian uniqueness lifts pulled lower naturality to complete
refinement geometry. -/
noncomputable def generatedPulledRouteRefinementGeometryIsoAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (⟨change.changedInput.generatedPulledRouteGeometryAt i⟩ :
      RefinementGeometryCategory.{u, v} U) ≅
    ⟨input.generatedPulledRouteGeometryAt i⟩ := by
  let oldLeg := input.generatedPulledRouteLegAt i
  let newLeg := change.changedInput.generatedPulledRouteLegAt i
  let sourceIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.geometryIso i)
  let candidate := newLeg ≫ sourceIso.hom
  let lowerIso := (exactPackageToRefinement U).mapIso
    (change.generatedPulledRouteExactCoreIsoAt i)
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      oldLeg.base oldLeg := input.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      newLeg.base newLeg :=
    change.changedInput.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsHomLift
      sourceIso.hom.base sourceIso.hom :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      sourceIso.hom.base sourceIso.hom :=
    CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (p := refinementGeometryProjection U) (f := sourceIso.hom.base)
      sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      candidate.base candidate := by
    dsimp only [candidate]
    exact CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)
  have base_fac : candidate.base = lowerIso.hom ≫ oldLeg.base := by
    dsimp only [candidate, lowerIso, sourceIso, oldLeg, newLeg]
    exact (change.generatedPulledRouteExactCoreIsoAt_hom_fac i).symm
  exact CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U) (g := lowerIso)
    (f := oldLeg.base) (f' := candidate.base) base_fac oldLeg candidate

/-- Projection of the pulled refinement comparison hom. -/
theorem generatedPulledRouteRefinementGeometryIsoAt_hom_base
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedPulledRouteRefinementGeometryIsoAt i).hom.base =
      (exactPackageToRefinement U).map
        (change.generatedPulledRouteExactCoreIsoAt i).hom := by
  let oldLeg := input.generatedPulledRouteLegAt i
  let newLeg := change.changedInput.generatedPulledRouteLegAt i
  let sourceIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.geometryIso i)
  let candidate := newLeg ≫ sourceIso.hom
  let lowerIso := (exactPackageToRefinement U).mapIso
    (change.generatedPulledRouteExactCoreIsoAt i)
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      oldLeg.base oldLeg := input.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      newLeg.base newLeg :=
    change.changedInput.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsHomLift
      sourceIso.hom.base sourceIso.hom :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      sourceIso.hom.base sourceIso.hom :=
    CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (p := refinementGeometryProjection U) (f := sourceIso.hom.base)
      sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      candidate.base candidate := by
    dsimp only [candidate]
    exact CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)
  have base_fac : candidate.base = lowerIso.hom ≫ oldLeg.base := by
    dsimp only [candidate, lowerIso, sourceIso, oldLeg, newLeg]
    exact (change.generatedPulledRouteExactCoreIsoAt_hom_fac i).symm
  let comparison := CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementGeometryProjection U) (g := lowerIso)
    (f := oldLeg.base) (f' := candidate.base) base_fac oldLeg candidate
  change comparison.hom.base = lowerIso.hom
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U) lowerIso.hom comparison.hom).symm

/-- Projection of the pulled refinement comparison inverse. -/
theorem generatedPulledRouteRefinementGeometryIsoAt_inv_base
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedPulledRouteRefinementGeometryIsoAt i).inv.base =
      (exactPackageToRefinement U).map
        (change.generatedPulledRouteExactCoreIsoAt i).inv := by
  let comparison := change.generatedPulledRouteRefinementGeometryIsoAt i
  let lowerIso := (exactPackageToRefinement U).mapIso
    (change.generatedPulledRouteExactCoreIsoAt i)
  change (refinementGeometryProjection U).map comparison.inv = lowerIso.inv
  have hhom : (refinementGeometryProjection U).map comparison.hom =
      lowerIso.hom := by
    exact change.generatedPulledRouteRefinementGeometryIsoAt_hom_base i
  have hcomp := congrArg
    (fun hom => (refinementGeometryProjection U).map hom)
    comparison.hom_inv_id
  simp only [Functor.map_comp] at hcomp
  rw [hhom] at hcomp
  apply (cancel_epi lowerIso.hom).1
  rw [hcomp, lowerIso.hom_inv_id]
  exact (refinementGeometryProjection U).map_id _

/-- Exact pulled comparison hom. -/
noncomputable def generatedPulledRouteExactGeometryHomAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    GeometryTotalHom
      (change.changedInput.generatedPulledRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (change.generatedPulledRouteExactCoreIsoAt i).hom
    (change.generatedPulledRouteRefinementGeometryIsoAt i).hom
    (change.generatedPulledRouteRefinementGeometryIsoAt_hom_base i)

/-- Exact pulled comparison inverse. -/
noncomputable def generatedPulledRouteExactGeometryInvAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    GeometryTotalHom
      (input.generatedPulledRouteGeometryAt i)
      (change.changedInput.generatedPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (change.generatedPulledRouteExactCoreIsoAt i).inv
    (change.generatedPulledRouteRefinementGeometryIsoAt i).inv
    (change.generatedPulledRouteRefinementGeometryIsoAt_inv_base i)

/-- Re-embedding the exact pulled comparison recovers the independently
constructed cartesian-uniqueness comparison. -/
theorem generatedPulledRouteExactGeometryHomAt_toRefinement
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (change.generatedPulledRouteExactGeometryHomAt i) =
      (change.generatedPulledRouteRefinementGeometryIsoAt i).hom :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- Re-embedding the exact pulled inverse recovers the independently
constructed refinement inverse. -/
theorem generatedPulledRouteExactGeometryInvAt_toRefinement
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (change.generatedPulledRouteExactGeometryInvAt i) =
      (change.generatedPulledRouteRefinementGeometryIsoAt i).inv :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The generated pulled endpoint comparison is an exact complete-geometry
isomorphism, independently constructed from the pulled route. -/
noncomputable def generatedPulledRouteExactGeometryIsoAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.changedInput.generatedPulledRouteGeometryAt i ≅
      input.generatedPulledRouteGeometryAt i where
  hom := change.generatedPulledRouteExactGeometryHomAt i
  inv := change.generatedPulledRouteExactGeometryInvAt i
  hom_inv_id := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    rw [Functor.map_comp,
      change.generatedPulledRouteExactGeometryHomAt_toRefinement,
      change.generatedPulledRouteExactGeometryInvAt_toRefinement]
    calc
      _ = 𝟙 _ :=
        (change.generatedPulledRouteRefinementGeometryIsoAt i).hom_inv_id
      _ = (exactGeometryToRefinementGeometry U).map (𝟙 _) :=
        ((exactGeometryToRefinementGeometry U).map_id _).symm
  inv_hom_id := by
    apply (exactGeometryToRefinementGeometry U).map_injective
    rw [Functor.map_comp,
      change.generatedPulledRouteExactGeometryInvAt_toRefinement,
      change.generatedPulledRouteExactGeometryHomAt_toRefinement]
    calc
      _ = 𝟙 _ :=
        (change.generatedPulledRouteRefinementGeometryIsoAt i).inv_hom_id
      _ = (exactGeometryToRefinementGeometry U).map (𝟙 _) :=
        ((exactGeometryToRefinementGeometry U).map_id _).symm
end UpperGeometryCompatibleSourcePresentationChange

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
