import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSolutionContracts

/-!
# Endpoint-conjugation equivalence of compatible upper solutions

Arbitrary canonical-authored solutions are transported to the generated
endpoint diagrams by `base.inv ≫ component ≫ pulled.hom`; generated solutions
are transported back by the reverse conjugation.  The construction acts on
the complete geometry component itself and never stores the source solution in
the result.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-! ## Forward component: canonical-authored to generated -/

/-- Exact lower map of a forward-transported arbitrary solution component. -/
noncomputable def canonicalSolutionForwardCoreAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    PackageTotalHom (input.generatedBaseRouteGeometryAt i).core
      (input.generatedPulledRouteGeometryAt i).core := by
  simpa only [input.canonicalAuthoredBaseRouteGeometryAt_core,
    input.canonicalAuthoredPulledRouteGeometryAt_core] using
      (solution.component i).base

/-- Complete refinement presentation of forward endpoint conjugation. -/
noncomputable def canonicalSolutionForwardRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    RefinementGeometryHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
    (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom

/-- The forward conjugation lies over the source solution's exact lower map. -/
theorem canonicalSolutionForwardRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    (input.canonicalSolutionForwardRefinementAt solution i).base =
      (exactPackageToRefinement U).map
        (input.canonicalSolutionForwardCoreAt solution i) := by
  unfold canonicalSolutionForwardRefinementAt
  change
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv.base ≫
      (exactPackageToRefinement U).map (solution.component i).base ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom.base = _
  rw [input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_base,
    input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_base]
  simp only [Category.id_comp]
  rfl

/-- Exact complete geometry component of forward solution transport. -/
noncomputable def canonicalSolutionForwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    GeometryTotalHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.canonicalSolutionForwardCoreAt solution i)
    (input.canonicalSolutionForwardRefinementAt solution i)
    (input.canonicalSolutionForwardRefinementAt_base solution i)

/-- Re-embedding the forward component recovers the full conjugation. -/
theorem canonicalSolutionForwardAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (input.canonicalSolutionForwardAt solution i) =
      input.canonicalSolutionForwardRefinementAt solution i :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- Forward transport preserves the fixed G-115 lower component. -/
@[simp] theorem canonicalSolutionForwardAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    (input.canonicalSolutionForwardAt solution i).base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1 := by
  exact solution.component_base i

/-- Forward endpoint conjugation preserves the geometry factorization
triangle. -/
theorem canonicalSolutionForwardAt_triangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalSolutionForwardAt solution i))
        (input.generatedPulledRouteLegAt i) =
      input.generatedBaseRouteLegAt i := by
  rw [input.canonicalSolutionForwardAt_toRefinement]
  unfold canonicalSolutionForwardRefinementAt
  change
    (((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
      (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom) ≫
        input.generatedPulledRouteLegAt i) = _
  calc
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom ≫
          input.generatedPulledRouteLegAt i) := by
      simp only [Category.assoc]
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
        input.canonicalAuthoredPulledRouteGeometryHomAt i := by
      rw [input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_hom_fac]
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        input.canonicalAuthoredBaseRouteGeometryHomAt i := by
      exact congrArg
        (fun hom =>
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫ hom)
        (solution.triangle i)
    _ = _ :=
      input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_inv_fac i

/-- Forward transport preserves coefficient identity. -/
theorem canonicalSolutionForwardAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    (input.canonicalSolutionForwardAt solution i).geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.canonicalSolutionForwardAt_triangle solution i)
  change
    (input.generatedPulledRouteLegAt i).geometry.coefficientHom.comp
        (input.canonicalSolutionForwardAt solution i).geometry.coefficientHom =
      (input.generatedBaseRouteLegAt i).geometry.coefficientHom at h
  rw [input.generatedPulledRouteLegAt_coefficient_id,
    input.generatedBaseRouteLegAt_coefficient_id] at h
  simpa only [RingHom.id_comp] using h

/-- Inverse form of base endpoint naturality. -/
theorem canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    {i j : P.Vertex} (edge : P.Edge i j) :
    ((exactGeometryToRefinementGeometry U).map
      (input.generatedBaseRouteGeometryEdge edge)) ≫
        (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).inv =
      (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredBaseRouteGeometryEdge edge)) := by
  let sourceComparison :=
    input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i
  let targetComparison :=
    input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j
  let generatedEdge := (exactGeometryToRefinementGeometry U).map
    (input.generatedBaseRouteGeometryEdge edge)
  let canonicalEdge := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredBaseRouteGeometryEdge edge)
  have hnaturality : canonicalEdge ≫ targetComparison.hom =
      sourceComparison.hom ≫ generatedEdge := by
    exact input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality edge
  calc
    generatedEdge ≫ targetComparison.inv =
        sourceComparison.inv ≫ (sourceComparison.hom ≫ generatedEdge) ≫
          targetComparison.inv := by simp
    _ = sourceComparison.inv ≫ (canonicalEdge ≫ targetComparison.hom) ≫
          targetComparison.inv := by rw [hnaturality]
    _ = sourceComparison.inv ≫ canonicalEdge := by simp

/-- Forward endpoint conjugation preserves edge naturality. -/
theorem canonicalSolutionForwardAt_edge_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.generatedBaseRouteGeometryEdge edge).comp
        (input.canonicalSolutionForwardAt solution j) =
      (input.canonicalSolutionForwardAt solution i).comp
        (input.generatedPulledRouteGeometryEdge edge) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change
    ((exactGeometryToRefinementGeometry U).map
      (input.generatedBaseRouteGeometryEdge edge)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalSolutionForwardAt solution j)) =
      ((exactGeometryToRefinementGeometry U).map
        (input.canonicalSolutionForwardAt solution i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedPulledRouteGeometryEdge edge))
  rw [input.canonicalSolutionForwardAt_toRefinement,
    input.canonicalSolutionForwardAt_toRefinement]
  unfold canonicalSolutionForwardRefinementAt
  let gb := (exactGeometryToRefinementGeometry U).map
    (input.generatedBaseRouteGeometryEdge edge)
  let bi := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv
  let bj := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).inv
  let cb := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredBaseRouteGeometryEdge edge)
  let si := (exactGeometryToRefinementGeometry U).map (solution.component i)
  let sj := (exactGeometryToRefinementGeometry U).map (solution.component j)
  let cp := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredPulledRouteGeometryEdge edge)
  let pi := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom
  let pj := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).hom
  let gp := (exactGeometryToRefinementGeometry U).map
    (input.generatedPulledRouteGeometryEdge edge)
  have hbase :=
    input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality_inv edge
  change gb ≫ bj = bi ≫ cb at hbase
  have hsolution := congrArg
    (exactGeometryToRefinementGeometry U).map
    (solution.edge_naturality edge)
  change cb ≫ sj = si ≫ cp at hsolution
  have hpulled :=
    input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality edge
  change cp ≫ pj = pi ≫ gp at hpulled
  change gb ≫ (bj ≫ sj ≫ pj) = (bi ≫ si ≫ pi) ≫ gp
  calc
    gb ≫ (bj ≫ sj ≫ pj) = ((gb ≫ bj) ≫ sj) ≫ pj := by
      simp only [Category.assoc]
    _ = ((bi ≫ cb) ≫ sj) ≫ pj := by rw [hbase]
    _ = (bi ≫ (cb ≫ sj)) ≫ pj := by
      exact congrArg (fun hom => hom ≫ pj) (Category.assoc bi cb sj)
    _ = (bi ≫ (si ≫ cp)) ≫ pj := by rw [hsolution]
    _ = bi ≫ si ≫ (cp ≫ pj) := by simp only [Category.assoc]
    _ = bi ≫ si ≫ (pi ≫ gp) := by rw [hpulled]
    _ = (bi ≫ si ≫ pi) ≫ gp := by simp only [Category.assoc]

/-- Forward endpoint conjugation preserves the literal authored comparator
equation. -/
theorem canonicalSolutionForwardAt_comparator_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (input.generatedBaseRouteComparator cell)).comp
        (input.canonicalSolutionForwardAt solution (P.twoTarget cell)) =
      (input.canonicalSolutionForwardAt solution (P.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedBaseRouteComparator cell))) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalSolutionForwardAt solution (P.twoTarget cell))) =
      ((exactGeometryToRefinementGeometry U).map
        (input.canonicalSolutionForwardAt solution (P.twoTarget cell))) ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell)))
  rw [input.canonicalSolutionForwardAt_toRefinement]
  unfold canonicalSolutionForwardRefinementAt
  let gb := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))
  let b := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
    (P.twoTarget cell)).inv
  let cb := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredBaseRouteComparator cell)
  let s := (exactGeometryToRefinementGeometry U).map
    (solution.component (P.twoTarget cell))
  let cp := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredPulledRouteComparator cell)
  let p := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
    (P.twoTarget cell)).hom
  let gp := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell))
  have hbase := input.canonicalAuthoredBaseRouteComparator_conjugation_inv cell
  change gb ≫ b = b ≫ cb at hbase
  have hsolution := congrArg
    (exactGeometryToRefinementGeometry U).map
    (solution.comparator_intertwining cell)
  change cb ≫ s = s ≫ cp at hsolution
  have hpulled :=
    input.canonicalAuthoredPulledRouteComparator_conjugation cell
  change cp ≫ p = p ≫ gp at hpulled
  change gb ≫ (b ≫ s ≫ p) = (b ≫ s ≫ p) ≫ gp
  calc
    gb ≫ (b ≫ s ≫ p) = ((gb ≫ b) ≫ s) ≫ p := by
      simp only [Category.assoc]
    _ = ((b ≫ cb) ≫ s) ≫ p := by rw [hbase]
    _ = (b ≫ (cb ≫ s)) ≫ p := by
      exact congrArg (fun hom => hom ≫ p) (Category.assoc b cb s)
    _ = (b ≫ (s ≫ cp)) ≫ p := by rw [hsolution]
    _ = b ≫ s ≫ (cp ≫ p) := by simp only [Category.assoc]
    _ = b ≫ s ≫ (p ≫ gp) := by rw [hpulled]
    _ = (b ≫ s ≫ p) ≫ gp := by simp only [Category.assoc]

/-- Forward transported components are natural on every generated path. -/
theorem canonicalSolutionForwardAt_path_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input)
    {i j : P.Vertex} (path : P.Path i j) :
    (input.generatedBaseRouteLiftData.pathLift path).comp
        (input.canonicalSolutionForwardAt solution j) =
      (input.canonicalSolutionForwardAt solution i).comp
        (input.generatedPulledRouteLiftData.pathLift path) := by
  induction path with
  | nil vertex =>
      change (GeometryTotalHom.id _).comp
          (input.canonicalSolutionForwardAt solution vertex) =
        (input.canonicalSolutionForwardAt solution vertex).comp
          (GeometryTotalHom.id _)
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (input.canonicalSolutionForwardAt solution vertex)).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ (input.canonicalSolutionForwardAt solution vertex)).symm
  | cons edge tail inductionHypothesis =>
      change ((input.generatedBaseRouteGeometryEdge edge).comp
          (input.generatedBaseRouteLiftData.pathLift tail)).comp
          (input.canonicalSolutionForwardAt solution _) =
        (input.canonicalSolutionForwardAt solution _).comp
          ((input.generatedPulledRouteGeometryEdge edge).comp
            (input.generatedPulledRouteLiftData.pathLift tail))
      calc
        _ = (input.generatedBaseRouteGeometryEdge edge).comp
            ((input.generatedBaseRouteLiftData.pathLift tail).comp
              (input.canonicalSolutionForwardAt solution _)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (input.generatedBaseRouteGeometryEdge edge)
            (input.generatedBaseRouteLiftData.pathLift tail)
            (input.canonicalSolutionForwardAt solution _)
        _ = (input.generatedBaseRouteGeometryEdge edge).comp
            ((input.canonicalSolutionForwardAt solution _).comp
              (input.generatedPulledRouteLiftData.pathLift tail)) :=
          congrArg _ inductionHypothesis
        _ = ((input.generatedBaseRouteGeometryEdge edge).comp
              (input.canonicalSolutionForwardAt solution _)).comp
            (input.generatedPulledRouteLiftData.pathLift tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (input.generatedBaseRouteGeometryEdge edge)
            (input.canonicalSolutionForwardAt solution _)
            (input.generatedPulledRouteLiftData.pathLift tail)).symm
        _ = ((input.canonicalSolutionForwardAt solution _).comp
              (input.generatedPulledRouteGeometryEdge edge)).comp
            (input.generatedPulledRouteLiftData.pathLift tail) :=
          congrArg (fun hom => hom.comp
            (input.generatedPulledRouteLiftData.pathLift tail))
            (input.canonicalSolutionForwardAt_edge_naturality solution edge)
        _ = _ := @Category.assoc
          (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ _ _ (input.canonicalSolutionForwardAt solution _)
          (input.generatedPulledRouteGeometryEdge edge)
          (input.generatedPulledRouteLiftData.pathLift tail)

/-- Forward transport satisfies generated authored two-cell pasting. -/
theorem canonicalSolutionForwardAt_authored_twoCell_pasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input)
    (cell : P.TwoCell) :
    ((input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell)).comp
      (CompositeFiberAut.hom
        (input.generatedBaseRouteComparator cell))).comp
        (input.canonicalSolutionForwardAt solution (P.twoTarget cell)) =
      (input.canonicalSolutionForwardAt solution (P.twoSource cell)).comp
        ((input.generatedPulledRouteLiftData.pathLift (P.twoLeft cell)).comp
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell))) := by
  calc
    _ = (input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell)).comp
        ((CompositeFiberAut.hom
          (input.generatedBaseRouteComparator cell)).comp
          (input.canonicalSolutionForwardAt solution
            (P.twoTarget cell))) := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell))
      (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))
      (input.canonicalSolutionForwardAt solution (P.twoTarget cell))
    _ = (input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell)).comp
        ((input.canonicalSolutionForwardAt solution
          (P.twoTarget cell)).comp
          (CompositeFiberAut.hom
            (input.generatedPulledRouteComparator cell))) :=
      congrArg _ (input.canonicalSolutionForwardAt_comparator_intertwining
        solution cell)
    _ = ((input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell)).comp
          (input.canonicalSolutionForwardAt solution
            (P.twoTarget cell))).comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (input.generatedBaseRouteLiftData.pathLift (P.twoLeft cell))
        (input.canonicalSolutionForwardAt solution (P.twoTarget cell))
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell))).symm
    _ = ((input.canonicalSolutionForwardAt solution
          (P.twoSource cell)).comp
          (input.generatedPulledRouteLiftData.pathLift
            (P.twoLeft cell))).comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)) :=
      congrArg (fun hom => hom.comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteComparator cell)))
        (input.canonicalSolutionForwardAt_path_naturality solution
          (P.twoLeft cell))
    _ = _ := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (input.canonicalSolutionForwardAt solution (P.twoSource cell))
      (input.generatedPulledRouteLiftData.pathLift (P.twoLeft cell))
      (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell))

/-- Forward transport of an arbitrary canonical-authored solution. -/
noncomputable def canonicalSolutionForward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) :
    GeometryCompatibleUpperRefinementBCSolution input where
  component := input.canonicalSolutionForwardAt solution
  component_base := input.canonicalSolutionForwardAt_base solution
  component_coefficient_id :=
    input.canonicalSolutionForwardAt_coefficient_id solution
  triangle := input.canonicalSolutionForwardAt_triangle solution
  edge_naturality := input.canonicalSolutionForwardAt_edge_naturality solution
  comparator_intertwining :=
    input.canonicalSolutionForwardAt_comparator_intertwining solution
  nil_naturality i :=
    input.canonicalSolutionForwardAt_path_naturality solution (.nil i)
  append_naturality first second :=
    input.canonicalSolutionForwardAt_path_naturality solution
      (first.append second)
  authored_twoCell_pasting :=
    input.canonicalSolutionForwardAt_authored_twoCell_pasting solution

/-! ## Backward component: generated to canonical-authored -/

/-- Exact lower map of a backward-transported arbitrary solution component. -/
noncomputable def generatedSolutionBackwardCoreAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    PackageTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i).core
      (input.canonicalAuthoredPulledRouteGeometryAt i).core := by
  simpa only [input.canonicalAuthoredBaseRouteGeometryAt_core,
    input.canonicalAuthoredPulledRouteGeometryAt_core] using
      (solution.component i).base

/-- Complete refinement presentation of backward endpoint conjugation. -/
noncomputable def generatedSolutionBackwardRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    RefinementGeometryHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.canonicalAuthoredPulledRouteGeometryAt i) :=
  (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
    (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
    (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv

/-- The backward conjugation lies over the source solution's exact lower map. -/
theorem generatedSolutionBackwardRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    (input.generatedSolutionBackwardRefinementAt solution i).base =
      (exactPackageToRefinement U).map
        (input.generatedSolutionBackwardCoreAt solution i) := by
  unfold generatedSolutionBackwardRefinementAt
  change
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom.base ≫
      (exactPackageToRefinement U).map (solution.component i).base ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv.base = _
  rw [input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_base,
    input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_base]
  simp only [Category.id_comp]
  rfl

/-- Exact complete geometry component of backward solution transport. -/
noncomputable def generatedSolutionBackwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    GeometryTotalHom (input.canonicalAuthoredBaseRouteGeometryAt i)
      (input.canonicalAuthoredPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.generatedSolutionBackwardCoreAt solution i)
    (input.generatedSolutionBackwardRefinementAt solution i)
    (input.generatedSolutionBackwardRefinementAt_base solution i)

/-- Re-embedding the backward component recovers the full conjugation. -/
theorem generatedSolutionBackwardAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
        (input.generatedSolutionBackwardAt solution i) =
      input.generatedSolutionBackwardRefinementAt solution i :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- Backward transport preserves the fixed G-115 lower component. -/
@[simp] theorem generatedSolutionBackwardAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    (input.generatedSolutionBackwardAt solution i).base =
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)).1 := by
  exact solution.component_base i

/-- Backward endpoint conjugation preserves the geometry triangle. -/
theorem generatedSolutionBackwardAt_triangle
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    RefinementGeometryHom.comp
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedSolutionBackwardAt solution i))
        (input.canonicalAuthoredPulledRouteGeometryHomAt i) =
      input.canonicalAuthoredBaseRouteGeometryHomAt i := by
  rw [input.generatedSolutionBackwardAt_toRefinement]
  unfold generatedSolutionBackwardRefinementAt
  change
    (((input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
      (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv) ≫
        input.canonicalAuthoredPulledRouteGeometryHomAt i) = _
  calc
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
        ((input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv ≫
          input.canonicalAuthoredPulledRouteGeometryHomAt i) := by
      simp only [Category.assoc]
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        (exactGeometryToRefinementGeometry U).map (solution.component i) ≫
        input.generatedPulledRouteLegAt i := by
      rw [input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_inv_fac]
    _ = (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
        input.generatedBaseRouteLegAt i := by
      exact congrArg
        (fun hom =>
          (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫ hom)
        (solution.triangle i)
    _ = _ :=
      input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_hom_fac i

/-- Backward transport preserves coefficient identity. -/
theorem generatedSolutionBackwardAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    (input.generatedSolutionBackwardAt solution i).geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedSolutionBackwardAt_triangle solution i)
  change
    (input.canonicalAuthoredPulledRouteGeometryHomAt i).geometry.coefficientHom.comp
        (input.generatedSolutionBackwardAt solution i).geometry.coefficientHom =
      (input.canonicalAuthoredBaseRouteGeometryHomAt i).geometry.coefficientHom at h
  rw [input.canonicalAuthoredPulledRouteGeometryHomAt_coefficientHom,
    input.canonicalAuthoredBaseRouteGeometryHomAt_coefficientHom] at h
  simpa only [RingHom.id_comp] using h

/-- Backward endpoint conjugation preserves edge naturality. -/
theorem generatedSolutionBackwardAt_edge_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
        (input.generatedSolutionBackwardAt solution j) =
      (input.generatedSolutionBackwardAt solution i).comp
        (input.canonicalAuthoredPulledRouteGeometryEdge edge) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteGeometryEdge edge)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedSolutionBackwardAt solution j)) =
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedSolutionBackwardAt solution i)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteGeometryEdge edge))
  rw [input.generatedSolutionBackwardAt_toRefinement,
    input.generatedSolutionBackwardAt_toRefinement]
  unfold generatedSolutionBackwardRefinementAt
  let cb := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredBaseRouteGeometryEdge edge)
  let bi := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom
  let bj := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt j).hom
  let gb := (exactGeometryToRefinementGeometry U).map
    (input.generatedBaseRouteGeometryEdge edge)
  let si := (exactGeometryToRefinementGeometry U).map (solution.component i)
  let sj := (exactGeometryToRefinementGeometry U).map (solution.component j)
  let gp := (exactGeometryToRefinementGeometry U).map
    (input.generatedPulledRouteGeometryEdge edge)
  let pi := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv
  let pj := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt j).inv
  let cp := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredPulledRouteGeometryEdge edge)
  have hbase :=
    input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality edge
  change cb ≫ bj = bi ≫ gb at hbase
  have hsolution := congrArg
    (exactGeometryToRefinementGeometry U).map
    (solution.edge_naturality edge)
  change gb ≫ sj = si ≫ gp at hsolution
  have hpulled :=
    input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality_inv edge
  change gp ≫ pj = pi ≫ cp at hpulled
  change cb ≫ (bj ≫ sj ≫ pj) = (bi ≫ si ≫ pi) ≫ cp
  calc
    cb ≫ (bj ≫ sj ≫ pj) = ((cb ≫ bj) ≫ sj) ≫ pj := by
      simp only [Category.assoc]
    _ = ((bi ≫ gb) ≫ sj) ≫ pj := by rw [hbase]
    _ = (bi ≫ (gb ≫ sj)) ≫ pj := by
      exact congrArg (fun hom => hom ≫ pj) (Category.assoc bi gb sj)
    _ = (bi ≫ (si ≫ gp)) ≫ pj := by rw [hsolution]
    _ = bi ≫ si ≫ (gp ≫ pj) := by simp only [Category.assoc]
    _ = bi ≫ si ≫ (pi ≫ cp) := by rw [hpulled]
    _ = (bi ≫ si ≫ pi) ≫ cp := by simp only [Category.assoc]

/-- Backward endpoint conjugation preserves the literal comparator equation. -/
theorem generatedSolutionBackwardAt_comparator_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (cell : P.TwoCell) :
    (input.canonicalAuthoredBaseRouteComparator cell).comp
        (input.generatedSolutionBackwardAt solution (P.twoTarget cell)) =
      (input.generatedSolutionBackwardAt solution (P.twoTarget cell)).comp
        (input.canonicalAuthoredPulledRouteComparator cell) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change
    ((exactGeometryToRefinementGeometry U).map
      (input.canonicalAuthoredBaseRouteComparator cell)) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.generatedSolutionBackwardAt solution (P.twoTarget cell))) =
      ((exactGeometryToRefinementGeometry U).map
        (input.generatedSolutionBackwardAt solution (P.twoTarget cell))) ≫
        ((exactGeometryToRefinementGeometry U).map
          (input.canonicalAuthoredPulledRouteComparator cell))
  rw [input.generatedSolutionBackwardAt_toRefinement]
  unfold generatedSolutionBackwardRefinementAt
  let cb := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredBaseRouteComparator cell)
  let b := (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt
    (P.twoTarget cell)).hom
  let gb := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom (input.generatedBaseRouteComparator cell))
  let s := (exactGeometryToRefinementGeometry U).map
    (solution.component (P.twoTarget cell))
  let gp := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom (input.generatedPulledRouteComparator cell))
  let p := (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt
    (P.twoTarget cell)).inv
  let cp := (exactGeometryToRefinementGeometry U).map
    (input.canonicalAuthoredPulledRouteComparator cell)
  have hbase := input.canonicalAuthoredBaseRouteComparator_conjugation cell
  change cb ≫ b = b ≫ gb at hbase
  have hsolution := congrArg
    (exactGeometryToRefinementGeometry U).map
    (solution.comparator_intertwining cell)
  change gb ≫ s = s ≫ gp at hsolution
  have hpulled :=
    input.canonicalAuthoredPulledRouteComparator_conjugation_inv cell
  change gp ≫ p = p ≫ cp at hpulled
  change cb ≫ (b ≫ s ≫ p) = (b ≫ s ≫ p) ≫ cp
  calc
    cb ≫ (b ≫ s ≫ p) = ((cb ≫ b) ≫ s) ≫ p := by
      simp only [Category.assoc]
    _ = ((b ≫ gb) ≫ s) ≫ p := by rw [hbase]
    _ = (b ≫ (gb ≫ s)) ≫ p := by
      exact congrArg (fun hom => hom ≫ p) (Category.assoc b gb s)
    _ = (b ≫ (s ≫ gp)) ≫ p := by rw [hsolution]
    _ = b ≫ s ≫ (gp ≫ p) := by simp only [Category.assoc]
    _ = b ≫ s ≫ (p ≫ cp) := by rw [hpulled]
    _ = (b ≫ s ≫ p) ≫ cp := by simp only [Category.assoc]

/-- Backward transported components are natural on every canonical-authored
path. -/
theorem generatedSolutionBackwardAt_path_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    {i j : P.Vertex} (path : P.Path i j) :
    (input.canonicalAuthoredBaseRoutePathLift path).comp
        (input.generatedSolutionBackwardAt solution j) =
      (input.generatedSolutionBackwardAt solution i).comp
        (input.canonicalAuthoredPulledRoutePathLift path) := by
  induction path with
  | nil vertex =>
      change (GeometryTotalHom.id _).comp
          (input.generatedSolutionBackwardAt solution vertex) =
        (input.generatedSolutionBackwardAt solution vertex).comp
          (GeometryTotalHom.id _)
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (input.generatedSolutionBackwardAt solution vertex)).trans
          (@Category.comp_id
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ (input.generatedSolutionBackwardAt solution vertex)).symm
  | cons edge tail inductionHypothesis =>
      change ((input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
          (input.canonicalAuthoredBaseRoutePathLift tail)).comp
          (input.generatedSolutionBackwardAt solution _) =
        (input.generatedSolutionBackwardAt solution _).comp
          ((input.canonicalAuthoredPulledRouteGeometryEdge edge).comp
            (input.canonicalAuthoredPulledRoutePathLift tail))
      calc
        _ = (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
            ((input.canonicalAuthoredBaseRoutePathLift tail).comp
              (input.generatedSolutionBackwardAt solution _)) :=
          @Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (input.canonicalAuthoredBaseRouteGeometryEdge edge)
            (input.canonicalAuthoredBaseRoutePathLift tail)
            (input.generatedSolutionBackwardAt solution _)
        _ = (input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
            ((input.generatedSolutionBackwardAt solution _).comp
              (input.canonicalAuthoredPulledRoutePathLift tail)) :=
          congrArg _ inductionHypothesis
        _ = ((input.canonicalAuthoredBaseRouteGeometryEdge edge).comp
              (input.generatedSolutionBackwardAt solution _)).comp
            (input.canonicalAuthoredPulledRoutePathLift tail) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ (input.canonicalAuthoredBaseRouteGeometryEdge edge)
            (input.generatedSolutionBackwardAt solution _)
            (input.canonicalAuthoredPulledRoutePathLift tail)).symm
        _ = ((input.generatedSolutionBackwardAt solution _).comp
              (input.canonicalAuthoredPulledRouteGeometryEdge edge)).comp
            (input.canonicalAuthoredPulledRoutePathLift tail) :=
          congrArg (fun hom => hom.comp
            (input.canonicalAuthoredPulledRoutePathLift tail))
            (input.generatedSolutionBackwardAt_edge_naturality solution edge)
        _ = _ := @Category.assoc
          (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ _ _ (input.generatedSolutionBackwardAt solution _)
          (input.canonicalAuthoredPulledRouteGeometryEdge edge)
          (input.canonicalAuthoredPulledRoutePathLift tail)

/-- Backward transport satisfies literal authored two-cell pasting. -/
theorem generatedSolutionBackwardAt_authored_twoCell_pasting
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (cell : P.TwoCell) :
    ((input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
      (input.canonicalAuthoredBaseRouteComparator cell)).comp
        (input.generatedSolutionBackwardAt solution (P.twoTarget cell)) =
      (input.generatedSolutionBackwardAt solution (P.twoSource cell)).comp
        ((input.canonicalAuthoredPulledRoutePathLift (P.twoLeft cell)).comp
          (input.canonicalAuthoredPulledRouteComparator cell)) := by
  calc
    _ = (input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
        ((input.canonicalAuthoredBaseRouteComparator cell).comp
          (input.generatedSolutionBackwardAt solution
            (P.twoTarget cell))) := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell))
      (input.canonicalAuthoredBaseRouteComparator cell)
      (input.generatedSolutionBackwardAt solution (P.twoTarget cell))
    _ = (input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
        ((input.generatedSolutionBackwardAt solution
          (P.twoTarget cell)).comp
          (input.canonicalAuthoredPulledRouteComparator cell)) :=
      congrArg _ (input.generatedSolutionBackwardAt_comparator_intertwining
        solution cell)
    _ = ((input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell)).comp
          (input.generatedSolutionBackwardAt solution
            (P.twoTarget cell))).comp
        (input.canonicalAuthoredPulledRouteComparator cell) :=
      (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (input.canonicalAuthoredBaseRoutePathLift (P.twoLeft cell))
        (input.generatedSolutionBackwardAt solution (P.twoTarget cell))
        (input.canonicalAuthoredPulledRouteComparator cell)).symm
    _ = ((input.generatedSolutionBackwardAt solution
          (P.twoSource cell)).comp
          (input.canonicalAuthoredPulledRoutePathLift
            (P.twoLeft cell))).comp
        (input.canonicalAuthoredPulledRouteComparator cell) :=
      congrArg (fun hom => hom.comp
        (input.canonicalAuthoredPulledRouteComparator cell))
        (input.generatedSolutionBackwardAt_path_naturality solution
          (P.twoLeft cell))
    _ = _ := @Category.assoc
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ _ (input.generatedSolutionBackwardAt solution (P.twoSource cell))
      (input.canonicalAuthoredPulledRoutePathLift (P.twoLeft cell))
      (input.canonicalAuthoredPulledRouteComparator cell)

/-- Backward transport of an arbitrary generated compatible solution. -/
noncomputable def generatedSolutionBackward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input) :
    CanonicalUpperRefinementBCSolution input where
  component := input.generatedSolutionBackwardAt solution
  component_base := input.generatedSolutionBackwardAt_base solution
  component_coefficient_id :=
    input.generatedSolutionBackwardAt_coefficient_id solution
  triangle := input.generatedSolutionBackwardAt_triangle solution
  edge_naturality := input.generatedSolutionBackwardAt_edge_naturality solution
  comparator_intertwining :=
    input.generatedSolutionBackwardAt_comparator_intertwining solution
  nil_naturality i :=
    input.generatedSolutionBackwardAt_path_naturality solution (.nil i)
  append_naturality first second :=
    input.generatedSolutionBackwardAt_path_naturality solution
      (first.append second)
  authored_twoCell_pasting :=
    input.generatedSolutionBackwardAt_authored_twoCell_pasting solution

/-! ## Component and solution cancellation -/

/-- Backward after forward endpoint conjugation recovers each original
canonical-authored complete component. -/
theorem generatedSolutionBackwardAt_canonicalSolutionForward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) (i : P.Vertex) :
    input.generatedSolutionBackwardAt
        (input.canonicalSolutionForward solution) i =
      solution.component i := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  rw [input.generatedSolutionBackwardAt_toRefinement]
  unfold generatedSolutionBackwardRefinementAt
  change
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).hom ≫
      (exactGeometryToRefinementGeometry U).map
        (input.canonicalSolutionForwardAt solution i) ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).inv =
    (exactGeometryToRefinementGeometry U).map (solution.component i)
  rw [input.canonicalSolutionForwardAt_toRefinement]
  unfold canonicalSolutionForwardRefinementAt
  simp

/-- Forward after backward endpoint conjugation recovers each original
generated complete component. -/
theorem canonicalSolutionForwardAt_generatedSolutionBackward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    input.canonicalSolutionForwardAt
        (input.generatedSolutionBackward solution) i =
      solution.component i := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  rw [input.canonicalSolutionForwardAt_toRefinement]
  unfold canonicalSolutionForwardRefinementAt
  change
    (input.canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt i).inv ≫
      (exactGeometryToRefinementGeometry U).map
        (input.generatedSolutionBackwardAt solution i) ≫
      (input.canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt i).hom =
    (exactGeometryToRefinementGeometry U).map (solution.component i)
  rw [input.generatedSolutionBackwardAt_toRefinement]
  unfold generatedSolutionBackwardRefinementAt
  simp

/-- Canonical-authored solutions are determined by their complete component
family; all remaining fields are propositions over that family. -/
@[ext] theorem CanonicalUpperRefinementBCSolution.ext
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {left right : CanonicalUpperRefinementBCSolution input}
    (hcomponent : left.component = right.component) : left = right := by
  cases left
  cases right
  cases hcomponent
  rfl

/-- Generated compatible solutions are determined by their complete component
family; all remaining fields are propositions over that family. -/
@[ext] theorem GeometryCompatibleUpperRefinementBCSolution.ext
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {left right : GeometryCompatibleUpperRefinementBCSolution input}
    (hcomponent : left.component = right.component) : left = right := by
  cases left
  cases right
  cases hcomponent
  rfl

/-- Backward after forward is the identity on the canonical-authored solution
type, not merely on a wrapper carrying the original solution. -/
theorem generatedSolutionBackward_canonicalSolutionForward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : CanonicalUpperRefinementBCSolution input) :
    input.generatedSolutionBackward (input.canonicalSolutionForward solution) =
      solution := by
  apply CanonicalUpperRefinementBCSolution.ext
  funext i
  exact input.generatedSolutionBackwardAt_canonicalSolutionForward solution i

/-- Forward after backward is the identity on the generated solution type. -/
theorem canonicalSolutionForward_generatedSolutionBackward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input) :
    input.canonicalSolutionForward (input.generatedSolutionBackward solution) =
      solution := by
  apply GeometryCompatibleUpperRefinementBCSolution.ext
  funext i
  exact input.canonicalSolutionForwardAt_generatedSolutionBackward solution i

/-- Wrapper-free endpoint-conjugation equivalence between the two actual
solution types. -/
noncomputable def canonicalGeneratedUpperRefinementBCSolutionEquiv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    CanonicalUpperRefinementBCSolution input ≃
      GeometryCompatibleUpperRefinementBCSolution input where
  toFun := input.canonicalSolutionForward
  invFun := input.generatedSolutionBackward
  left_inv := input.generatedSolutionBackward_canonicalSolutionForward
  right_inv := input.canonicalSolutionForward_generatedSolutionBackward

/-- Named canonical companion solution obtained from the actual solution-type
equivalence and the theorem-generated compatible solution. -/
noncomputable def canonicalCompanionUpperRefinementBCSolution
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    CanonicalUpperRefinementBCSolution input :=
  (input.canonicalGeneratedUpperRefinementBCSolutionEquiv).symm
    input.generatedGeometryCompatibleUpperRefinementBCSolution

/-- The named companion returns to the generated canonical solution under the
forward equivalence. -/
theorem canonicalGeneratedUpperRefinementBCSolutionEquiv_companion
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    input.canonicalGeneratedUpperRefinementBCSolutionEquiv
        input.canonicalCompanionUpperRefinementBCSolution =
      input.generatedGeometryCompatibleUpperRefinementBCSolution := by
  exact Equiv.apply_symm_apply _ _

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
