import ResearchLean.AG.CrossStageCoherence.ObstructionGroups

/-!
# The total upper obstruction and its projection

This module lifts the G-106 finite-presentation vocabulary to the geometry
stage.  Each generator carries independent strong-cocartesian qualifications
for the geometry and core projections.  Composite strength is derived, never
stored.  Parallel-path equality is required only after both projections.

The resulting canonical comparator and raw defect take values in `C_G`.
Projection constructs an ordinary G-106 data set and is proved to preserve
edge reselection, path evaluation, canonical comparison, and the raw defect.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

/-- Two independently qualified layers of edge lifts over a finite presentation. -/
structure TwoLayerLiftData (P : FiniteTransportPresentation.{u})
    (U : AtomCarrier.{u}) where
  /-- Geometry package interpreting each vertex. -/
  geometry : P.Vertex → GeometryPackage.{u, v} U
  /-- Geometry-stage lift interpreting each directed edge. -/
  edgeLift : {i j : P.Vertex} → P.Edge i j →
    GeometryTotalHom (geometry i) (geometry j)
  /-- Local qualification at the geometry projection. -/
  edgeGeometryStrong : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (geometryProjection U).IsStronglyCocartesian
      (edgeLift edge).base (edgeLift edge)
  /-- Independent local qualification after projection to core packages. -/
  edgeCoreStrong : ∀ {i j : P.Vertex} (edge : P.Edge i j),
    (packageProjection U).IsStronglyCocartesian
      (edgeLift edge).base.base (edgeLift edge).base

namespace TwoLayerLiftData

/-- Evaluate a path by composing its selected geometry lifts. -/
noncomputable def pathLift {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U) :
    {i j : P.Vertex} → P.Path i j →
      GeometryTotalHom (data.geometry i) (data.geometry j)
  | _, _, .nil vertex => GeometryTotalHom.id (data.geometry vertex)
  | _, _, .cons edge tail =>
      (data.edgeLift edge).comp (data.pathLift tail)

/-- Forget geometry and retain the G-106 core edge-lift data. -/
noncomputable def coreLiftData {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U) :
    AdmissibleLiftData P U where
  package vertex := (data.geometry vertex).core
  edgeLift edge := (data.edgeLift edge).base
  edgeStrong edge := data.edgeCoreStrong edge

/-- Projecting a geometry path evaluation gives the core path evaluation. -/
theorem pathLift_base {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U)
    {i j : P.Vertex} (path : P.Path i j) :
    (data.pathLift path).base = (data.coreLiftData.pathLift path) := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      change (data.edgeLift edge).base.comp (data.pathLift tail).base =
        (data.edgeLift edge).base.comp (data.coreLiftData.pathLift tail)
      rw [inductionHypothesis]

/-- Path evaluation preserves concatenation. -/
theorem pathLift_append {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U)
    {i j k : P.Vertex} (first : P.Path i j) (second : P.Path j k) :
    data.pathLift (first.append second) =
      (data.pathLift first).comp (data.pathLift second) := by
  induction first with
  | nil vertex =>
      change data.pathLift second =
        (GeometryTotalHom.id (data.geometry vertex)).comp
          (data.pathLift second)
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        (data.geometry vertex) (data.geometry k)
        (data.pathLift second)).symm
  | cons edge tail inductionHypothesis =>
      simp only [PresentedPath.append, pathLift]
      rw [inductionHypothesis]
      exact (@Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (data.edgeLift edge) (data.pathLift tail)
        (data.pathLift second)).symm

/-- Geometry-stage local qualifications close under path composition. -/
theorem pathLift_geometryStrong {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U)
    {i j : P.Vertex} (path : P.Path i j) :
    (geometryProjection U).IsStronglyCocartesian
      (data.pathLift path).base (data.pathLift path) := by
  induction path with
  | nil vertex =>
      letI : (geometryProjection U).IsHomLift
          (𝟙 (data.geometry vertex).core)
          (Iso.refl (data.geometry vertex)).hom :=
        CategoryTheory.IsHomLift.id rfl
      simpa only [pathLift] using
        (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
          (geometryProjection U) (𝟙 (data.geometry vertex).core)
          (Iso.refl (data.geometry vertex)))
  | cons edge tail inductionHypothesis =>
      letI : (geometryProjection U).IsStronglyCocartesian
          (data.edgeLift edge).base (data.edgeLift edge) :=
        data.edgeGeometryStrong edge
      letI : (geometryProjection U).IsStronglyCocartesian
          (data.pathLift tail).base (data.pathLift tail) :=
        inductionHypothesis
      simpa only [pathLift] using
        (CategoryTheory.Functor.IsStronglyCocartesian.comp
          (geometryProjection U))

/-- Core-stage local qualifications close under the same path composition. -/
theorem pathLift_coreStrong {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U)
    {i j : P.Vertex} (path : P.Path i j) :
    (packageProjection U).IsStronglyCocartesian
      (data.pathLift path).base.base (data.pathLift path).base := by
  rw [data.pathLift_base path]
  exact data.coreLiftData.pathLift_isStronglyCocartesian path

/-- The two path certificates generate strong cocartesianness for the composite. -/
theorem pathLift_compositeStrong {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U)
    {i j : P.Vertex} (path : P.Path i j) :
    (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (data.pathLift path).base.base (data.pathLift path) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (data.pathLift path).base (data.pathLift path) :=
    data.pathLift_geometryStrong path
  letI : (packageProjection U).IsStronglyCocartesian
      (data.pathLift path).base.base (data.pathLift path).base :=
    data.pathLift_coreStrong path
  exact geometryHom_isCompositeStronglyCocartesian (data.pathLift path)

end TwoLayerLiftData

/-- Two-layer comparison data with parallelism fixed only at `ExtInst`. -/
structure TwoLayerTransportData (P : FiniteTransportPresentation.{u})
    (U : AtomCarrier.{u}) where
  /-- Independently qualified edge lifts. -/
  lift : TwoLayerLiftData.{u, v} P U
  /-- Parallel paths agree after the composite projection, not necessarily in core. -/
  twoCellBase : ∀ cell : P.TwoCell,
    (lift.pathLift (P.twoLeft cell)).base.base =
      (lift.pathLift (P.twoRight cell)).base.base
  /-- Authored upper comparator; it is not constrained to be canonical. -/
  comparator : (cell : P.TwoCell) →
    CompositeFiberAut (lift.geometry (P.twoTarget cell))

namespace TwoLayerTransportData

/-- Projected data in the original G-106 core-stage vocabulary. -/
noncomputable def coreData {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U) :
    AdmissibleTransportData P U where
  lift := data.lift.coreLiftData
  twoCellBase cell := by
    rw [← data.lift.pathLift_base (P.twoLeft cell),
      ← data.lift.pathLift_base (P.twoRight cell)]
    exact data.twoCellBase cell
  comparator cell :=
    compositeFiberPushforward (data.lift.geometry (P.twoTarget cell))
      (data.comparator cell)

end TwoLayerTransportData

/-- A geometry-stage edge reselection assigns one `C_G` element to every edge. -/
abbrev UpperEdgeReselection {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerLiftData.{u, v} P U) :=
  (i j : P.Vertex) → (edge : P.Edge i j) →
    CompositeFiberAut (data.geometry j)

/-- Push an upper edge reselection to the G-106 core coordinate. -/
noncomputable def pushforwardEdgeReselection
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) :
    EdgeReselection data.coreLiftData :=
  fun i j edge =>
    compositeFiberPushforward (data.geometry j) (reselection i j edge)

/-- Reselect an edge by postcomposing its upper target-fiber automorphism. -/
noncomputable def upperReselectedEdgeLift
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j : P.Vertex} (edge : P.Edge i j) :
    GeometryTotalHom (data.geometry i) (data.geometry j) :=
  (data.edgeLift edge).comp
    (CompositeFiberAut.hom (reselection i j edge))

/-- Projection of an upper reselected edge is the G-106 reselected edge. -/
theorem upperReselectedEdgeLift_base
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift data reselection edge).base =
      reselectedEdgeLift data.coreLiftData
        (pushforwardEdgeReselection data reselection) edge :=
  rfl

/-- Upper edge reselection preserves geometry-stage strong cocartesianness. -/
theorem upperReselectedEdgeLift_geometryStrong
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (geometryProjection U).IsStronglyCocartesian
      (upperReselectedEdgeLift data reselection edge).base
      (upperReselectedEdgeLift data reselection edge) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (data.edgeLift edge).base (data.edgeLift edge) :=
    data.edgeGeometryStrong edge
  letI : (geometryProjection U).IsHomLift
      (reselection i j edge).1.hom.base
      (reselection i j edge).1.hom := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map
        (reselection i j edge).1.hom)
      (reselection i j edge).1.hom
    infer_instance
  letI : (geometryProjection U).IsStronglyCocartesian
      (CompositeFiberAut.hom (reselection i j edge)).base
      (CompositeFiberAut.hom (reselection i j edge)) := by
    change (geometryProjection U).IsStronglyCocartesian
      (reselection i j edge).1.hom.base
      (reselection i j edge).1.hom
    exact CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (geometryProjection U) (reselection i j edge).1.hom.base
      (reselection i j edge).1
  exact CategoryTheory.Functor.IsStronglyCocartesian.comp
    (geometryProjection U)

/-- Upper edge reselection preserves the independent core-stage certificate. -/
theorem upperReselectedEdgeLift_coreStrong
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (packageProjection U).IsStronglyCocartesian
      (upperReselectedEdgeLift data reselection edge).base.base
      (upperReselectedEdgeLift data reselection edge).base := by
  rw [upperReselectedEdgeLift_base]
  exact reselectedEdgeLift_isStronglyCocartesian
    data.coreLiftData (pushforwardEdgeReselection data reselection) edge

/-- The two-layer lift data after an upper edge reselection. -/
noncomputable def upperReselectLiftData
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) :
    TwoLayerLiftData.{u, v} P U where
  geometry := data.geometry
  edgeLift := upperReselectedEdgeLift data reselection
  edgeGeometryStrong := upperReselectedEdgeLift_geometryStrong data reselection
  edgeCoreStrong := upperReselectedEdgeLift_coreStrong data reselection

/-- Evaluate a path after upper edge reselection. -/
noncomputable def upperReselectedPathLift
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j : P.Vertex} (path : P.Path i j) :
    GeometryTotalHom (data.geometry i) (data.geometry j) :=
  (upperReselectLiftData data reselection).pathLift path

/-- Projected reselected path evaluation agrees with G-106 path evaluation. -/
theorem upperReselectedPathLift_base
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift data reselection path).base =
      reselectedPathLift data.coreLiftData
        (pushforwardEdgeReselection data reselection) path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      change (upperReselectedEdgeLift data reselection edge).base.comp
          (upperReselectedPathLift data reselection tail).base =
        (reselectedEdgeLift data.coreLiftData
          (pushforwardEdgeReselection data reselection) edge).comp
        (reselectedPathLift data.coreLiftData
          (pushforwardEdgeReselection data reselection) tail)
      rw [upperReselectedEdgeLift_base, inductionHypothesis]

/-- Upper reselection does not change the composite base of one edge. -/
theorem upperReselectedEdgeLift_base_base
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (upperReselectedEdgeLift data reselection edge).base.base =
      (data.edgeLift edge).base.base := by
  change (data.edgeLift edge).base.base.comp
      (CompositeFiberAut.hom (reselection i j edge)).base.base =
    (data.edgeLift edge).base.base
  rw [CompositeFiberAut.hom_base_base_eq]
  exact (@Category.comp_id
    (ExtractionInstance U) (ExtInstHom.extractionInstanceCategory U)
    _ _ (data.edgeLift edge).base.base)

/-- Upper reselection does not change the composite base of a path. -/
theorem upperReselectedPathLift_base_base
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift data reselection path).base.base =
      (data.pathLift path).base.base := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      change (upperReselectedEdgeLift data reselection edge).base.base.comp
          (upperReselectedPathLift data reselection tail).base.base =
        (data.edgeLift edge).base.base.comp (data.pathLift tail).base.base
      rw [upperReselectedEdgeLift_base_base, inductionHypothesis]

/-- The declared ExtInst-level parallelism survives every upper reselection. -/
theorem upperReselectedTwoCellBase
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base.base =
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base.base := by
  rw [upperReselectedPathLift_base_base,
    upperReselectedPathLift_base_base]
  exact data.twoCellBase cell

/-- The `C_G` canonical comparator after an upper edge reselection. -/
noncomputable def upperCanonicalTwoCellComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    CompositeFiberAut (data.lift.geometry (P.twoTarget cell)) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoLeft cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoRight cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoLeft cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoRight cell)
  exact canonicalCompositeFiberComparator
    (upperReselectedPathLift data.lift reselection (P.twoLeft cell))
    (upperReselectedPathLift data.lift reselection (P.twoRight cell))
    (upperReselectedTwoCellBase data reselection cell)

/-- The upper canonical comparator identifies the two reselected path lifts. -/
theorem upperCanonicalTwoCellComparator_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    (upperReselectedPathLift data.lift reselection
      (P.twoLeft cell)).comp
        (CompositeFiberAut.hom
          (upperCanonicalTwoCellComparator data reselection cell)) =
      upperReselectedPathLift data.lift reselection
        (P.twoRight cell) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoLeft cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoRight cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoLeft cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoRight cell)
  exact canonicalCompositeFiberComparator_fac
    (upperReselectedPathLift data.lift reselection (P.twoLeft cell))
    (upperReselectedPathLift data.lift reselection (P.twoRight cell))
    (upperReselectedTwoCellBase data reselection cell)

/-- Projection preserves the upper canonical 2-cell comparator. -/
theorem pushforward_upperCanonicalTwoCellComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    compositeFiberPushforward
        (data.lift.geometry (P.twoTarget cell))
        (upperCanonicalTwoCellComparator data reselection cell) =
      canonicalTwoCellComparator data.coreData
        (pushforwardEdgeReselection data.lift reselection) cell := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoLeft cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoRight cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoLeft cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoRight cell)
  unfold upperCanonicalTwoCellComparator canonicalTwoCellComparator
  simpa only [upperReselectedPathLift_base] using
    compositeFiberPushforward_canonicalComparator
      (upperReselectedPathLift data.lift reselection (P.twoLeft cell))
      (upperReselectedPathLift data.lift reselection (P.twoRight cell))
      (upperReselectedTwoCellBase data reselection cell)

/-- The unconditional upper raw defect `u * phi⁻¹` in `C_G`. -/
noncomputable def upperRawTwoCellDefect
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    CompositeFiberAut (data.lift.geometry (P.twoTarget cell)) :=
  data.comparator cell *
    (upperCanonicalTwoCellComparator data reselection cell)⁻¹

/-- Pushforward sends the upper raw defect to the G-106 raw defect. -/
theorem pushforward_upperRawTwoCellDefect
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    compositeFiberPushforward
        (data.lift.geometry (P.twoTarget cell))
        (upperRawTwoCellDefect data reselection cell) =
      rawTwoCellDefect data.coreData
        (pushforwardEdgeReselection data.lift reselection) cell := by
  rw [upperRawTwoCellDefect, map_mul, map_inv,
    pushforward_upperCanonicalTwoCellComparator]
  rfl

/-- `C_G`-valued raw defect cochains. -/
abbrev UpperDefectCochain {P : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : TwoLayerTransportData.{u, v} P U) :=
  (cell : P.TwoCell) →
    CompositeFiberAut (data.lift.geometry (P.twoTarget cell))

/-- Evaluate the upper raw cochain at one edge coordinate. -/
noncomputable def upperRawDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    UpperDefectCochain data :=
  fun cell => upperRawTwoCellDefect data reselection cell

/-- The independently defined identity upper cochain. -/
noncomputable def upperIdentityDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    UpperDefectCochain data :=
  fun _ => 1

/-- Upper orbit membership under edge-level `C_G` reselection only. -/
def InUpperReselectionOrbit
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (cochain : UpperDefectCochain data) : Prop :=
  ∃ reselection : UpperEdgeReselection data.lift,
    upperRawDefectCochain data reselection = cochain

/-- Vanishing of the total upper obstruction. -/
def UpperTransportObstructionVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  InUpperReselectionOrbit data (upperIdentityDefectCochain data)

/-- Push an upper cochain pointwise to the G-106 core cochain. -/
noncomputable def pushforwardUpperCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (cochain : UpperDefectCochain data) : DefectCochain data.coreData :=
  fun cell => compositeFiberPushforward
    (data.lift.geometry (P.twoTarget cell)) (cochain cell)

/-- Pushforward preserves the entire raw cochain at every edge coordinate. -/
theorem pushforward_upperRawDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    pushforwardUpperCochain data (upperRawDefectCochain data reselection) =
      rawDefectCochain data.coreData
        (pushforwardEdgeReselection data.lift reselection) := by
  funext cell
  exact pushforward_upperRawTwoCellDefect data reselection cell

/-- Pushforward preserves the independent identity cochain. -/
theorem pushforward_upperIdentityDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    pushforwardUpperCochain data (upperIdentityDefectCochain data) =
      identityDefectCochain data.coreData := by
  funext cell
  exact map_one _

/-- Upper orbit vanishing pushes forward to core-stage obstruction vanishing. -/
theorem upperTransportObstructionVanishes_core
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    UpperTransportObstructionVanishes data →
      TransportObstructionVanishes data.coreData := by
  rintro ⟨reselection, rawIdentity⟩
  refine ⟨pushforwardEdgeReselection data.lift reselection, ?_⟩
  rw [← pushforward_upperRawDefectCochain data reselection,
    rawIdentity, pushforward_upperIdentityDefectCochain]

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
