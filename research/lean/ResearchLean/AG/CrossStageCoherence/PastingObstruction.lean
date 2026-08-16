import ResearchLean.AG.CrossStageCoherence.GlobalVanishing
import ResearchLean.AG.TransportCoherence.PastingObstruction

/-!
# Typed upper pasting obstruction and conditional cocycle

This module evaluates complete typed rewrite pastings in the composite-fiber
groups `C_G`.  Local authored and canonical comparisons are oriented and
whiskered separately; their quotient is formed only after the complete route
has been composed.  Projection to the core stage commutes with every layer of
the evaluator.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 4000000

/-! ## Composite-fiber whiskering -/

/-- Compose a composite-fiber automorphism with an upper reselected path. -/
noncomputable def upperFiberAutThenPath
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    GeometryTotalHom (data.geometry i) (data.geometry j) :=
  (CompositeFiberAut.hom automorphism).comp
    (upperReselectedPathLift data reselection path)

/-- The upper composite used for whiskering is geometry-strong. -/
theorem upperFiberAutThenPath_geometryStrong
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    (geometryProjection U).IsStronglyCocartesian
    (upperFiberAutThenPath data reselection automorphism path).base
      (upperFiberAutThenPath data reselection automorphism path) := by
  letI : (geometryProjection U).IsHomLift
      automorphism.1.hom.base automorphism.1.hom := by
    change (geometryProjection U).IsHomLift
      ((geometryProjection U).map automorphism.1.hom)
      automorphism.1.hom
    infer_instance
  letI : (geometryProjection U).IsStronglyCocartesian
      (CompositeFiberAut.hom automorphism).base
      (CompositeFiberAut.hom automorphism) := by
    change (geometryProjection U).IsStronglyCocartesian
      automorphism.1.hom.base automorphism.1.hom
    exact CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (geometryProjection U) automorphism.1.hom.base
      automorphism.1
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data reselection path).base
      (upperReselectedPathLift data reselection path) :=
    (upperReselectLiftData data reselection).pathLift_geometryStrong path
  change (geometryProjection U).IsStronglyCocartesian
    ((CompositeFiberAut.hom automorphism).base.comp
      (upperReselectedPathLift data reselection path).base)
    ((CompositeFiberAut.hom automorphism).comp
      (upperReselectedPathLift data reselection path))
  exact CategoryTheory.Functor.IsStronglyCocartesian.comp (geometryProjection U)

/-- The projected upper composite used for whiskering is core-strong. -/
theorem upperFiberAutThenPath_coreStrong
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    (packageProjection U).IsStronglyCocartesian
      (upperFiberAutThenPath data reselection automorphism path).base.base
      (upperFiberAutThenPath data reselection automorphism path).base := by
  let projectedIso : (data.geometry i).core ≅ (data.geometry i).core :=
    (geometryProjection U).mapIso automorphism.1
  letI : (packageProjection U).IsHomLift
      projectedIso.hom.base projectedIso.hom := by
    change (packageProjection U).IsHomLift
      ((packageProjection U).map projectedIso.hom) projectedIso.hom
    infer_instance
  letI : (packageProjection U).IsStronglyCocartesian
      (CompositeFiberAut.hom automorphism).base.base
      (CompositeFiberAut.hom automorphism).base := by
    change (packageProjection U).IsStronglyCocartesian
      projectedIso.hom.base projectedIso.hom
    exact CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (packageProjection U) projectedIso.hom.base
      projectedIso
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data reselection path).base.base
      (upperReselectedPathLift data reselection path).base :=
    (upperReselectLiftData data reselection).pathLift_coreStrong path
  change (packageProjection U).IsStronglyCocartesian
    ((CompositeFiberAut.hom automorphism).base.base.comp
      (upperReselectedPathLift data reselection path).base.base)
    ((CompositeFiberAut.hom automorphism).base.comp
      (upperReselectedPathLift data reselection path).base)
  exact CategoryTheory.Functor.IsStronglyCocartesian.comp (packageProjection U)

/-- Whiskering preserves the exact ExtInst-level base arrow. -/
theorem upperFiberAutThenPath_base_eq
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    (upperFiberAutThenPath data reselection automorphism path).base.base =
      (upperReselectedPathLift data reselection path).base.base := by
  change (CompositeFiberAut.hom automorphism).base.base.comp
      (upperReselectedPathLift data reselection path).base.base = _
  rw [CompositeFiberAut.hom_base_base_eq]
  exact (@Category.id_comp
    (ExtractionInstance U) (ExtInstHom.extractionInstanceCategory U)
    _ _ (upperReselectedPathLift data reselection path).base.base)

/-- Transport a `C_G` automorphism along an upper reselected path. -/
noncomputable def upperWhiskerCompositeFiberAut
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) : CompositeFiberAut (data.geometry j) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data reselection path).base
      (upperReselectedPathLift data reselection path) :=
    (upperReselectLiftData data reselection).pathLift_geometryStrong path
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperFiberAutThenPath data reselection automorphism path).base
      (upperFiberAutThenPath data reselection automorphism path) :=
    upperFiberAutThenPath_geometryStrong data reselection automorphism path
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data reselection path).base.base
      (upperReselectedPathLift data reselection path).base :=
    (upperReselectLiftData data reselection).pathLift_coreStrong path
  letI : (packageProjection U).IsStronglyCocartesian
      (upperFiberAutThenPath data reselection automorphism path).base.base
      (upperFiberAutThenPath data reselection automorphism path).base :=
    upperFiberAutThenPath_coreStrong data reselection automorphism path
  exact canonicalCompositeFiberComparator
    (upperReselectedPathLift data reselection path)
    (upperFiberAutThenPath data reselection automorphism path)
    (upperFiberAutThenPath_base_eq
      data reselection automorphism path).symm

/-- Characterizing factorization of upper whiskering. -/
theorem upperWhiskerCompositeFiberAut_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    (upperReselectedPathLift data reselection path).comp
      (CompositeFiberAut.hom
        (upperWhiskerCompositeFiberAut data reselection automorphism path)) =
      upperFiberAutThenPath data reselection automorphism path := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data reselection path).base
      (upperReselectedPathLift data reselection path) :=
    (upperReselectLiftData data reselection).pathLift_geometryStrong path
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperFiberAutThenPath data reselection automorphism path).base
      (upperFiberAutThenPath data reselection automorphism path) :=
    upperFiberAutThenPath_geometryStrong data reselection automorphism path
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data reselection path).base.base
      (upperReselectedPathLift data reselection path).base :=
    (upperReselectLiftData data reselection).pathLift_coreStrong path
  letI : (packageProjection U).IsStronglyCocartesian
      (upperFiberAutThenPath data reselection automorphism path).base.base
      (upperFiberAutThenPath data reselection automorphism path).base :=
    upperFiberAutThenPath_coreStrong data reselection automorphism path
  exact canonicalCompositeFiberComparator_fac
    (upperReselectedPathLift data reselection path)
    (upperFiberAutThenPath data reselection automorphism path)
    (upperFiberAutThenPath_base_eq
      data reselection automorphism path).symm

/-- Projection commutes with composite-fiber whiskering. -/
theorem pushforward_upperWhiskerCompositeFiberAut
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    compositeFiberPushforward (data.geometry j)
        (upperWhiskerCompositeFiberAut data reselection automorphism path) =
      whiskerFiberAut data.coreLiftData
        (pushforwardEdgeReselection data reselection)
        (compositeFiberPushforward (data.geometry i) automorphism) path := by
  let corePath := reselectedPathLift data.coreLiftData
    (pushforwardEdgeReselection data reselection) path
  letI : (packageProjection U).IsStronglyCocartesian
      corePath.base corePath :=
    reselectedPathLift_isStronglyCocartesian data.coreLiftData
      (pushforwardEdgeReselection data reselection) path
  apply PackageFiberAut.ext_of_strong_fac corePath
  calc
    corePath.comp (PackageFiberAut.hom
        (compositeFiberPushforward (data.geometry j)
          (upperWhiskerCompositeFiberAut data reselection automorphism path))) =
      ((upperReselectedPathLift data reselection path).comp
        (CompositeFiberAut.hom
          (upperWhiskerCompositeFiberAut
            data reselection automorphism path))).base := by
      change corePath.comp (PackageFiberAut.hom
          (compositeFiberPushforward (data.geometry j)
            (upperWhiskerCompositeFiberAut
              data reselection automorphism path))) =
        (upperReselectedPathLift data reselection path).base.comp
          (CompositeFiberAut.hom
            (upperWhiskerCompositeFiberAut
              data reselection automorphism path)).base
      rw [upperReselectedPathLift_base]
      rfl
    _ = (upperFiberAutThenPath data reselection automorphism path).base :=
      congrArg GeometryTotalHom.base
        (upperWhiskerCompositeFiberAut_fac
          data reselection automorphism path)
    _ = fiberAutThenPath data.coreLiftData
        (pushforwardEdgeReselection data reselection)
        (compositeFiberPushforward (data.geometry i) automorphism) path := by
      unfold upperFiberAutThenPath fiberAutThenPath
      change (CompositeFiberAut.hom automorphism).base.comp
          (upperReselectedPathLift data reselection path).base =
        (PackageFiberAut.hom
          (compositeFiberPushforward (data.geometry i) automorphism)).comp
          (reselectedPathLift data.coreLiftData
            (pushforwardEdgeReselection data reselection) path)
      rw [upperReselectedPathLift_base]
      rfl
    _ = corePath.comp (PackageFiberAut.hom
        (whiskerFiberAut data.coreLiftData
          (pushforwardEdgeReselection data reselection)
          (compositeFiberPushforward (data.geometry i) automorphism) path)) :=
      (whiskerFiberAut_fac data.coreLiftData
        (pushforwardEdgeReselection data reselection)
        (compositeFiberPushforward (data.geometry i) automorphism) path).symm

/-! ## Typed upper pasting evaluator -/

/-- A family of composite-fiber comparators on the declared 2-cells. -/
abbrev UpperTwoCellComparatorFamily
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) := UpperDefectCochain data

/-- The authored upper comparator family. -/
def upperAuthoredComparatorFamily
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    UpperTwoCellComparatorFamily data :=
  data.comparator

/-- The generated upper comparator family at one edge coordinate. -/
noncomputable def upperCanonicalComparatorFamily
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    UpperTwoCellComparatorFamily data :=
  upperCanonicalTwoCellComparator data reselection

/-- Pointwise pushforward of an upper comparator family. -/
noncomputable def pushforwardUpperComparatorFamily
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (family : UpperTwoCellComparatorFamily data) :
    TwoCellComparatorFamily data.coreData :=
  fun cell => compositeFiberPushforward
    (data.lift.geometry (P.twoTarget cell)) (family cell)

/-- Orient and whisker one upper comparator to the target of a typed face. -/
noncomputable def upperOrientedFaceComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (family : UpperTwoCellComparatorFamily data)
    {source target : P.Vertex}
    (face : WhiskeredFace P.toFiniteTransportTwoPresentation source target) :
    CompositeFiberAut (data.lift.geometry target) :=
  let localComparator :=
    match face.orientation with
    | .forward => family face.cell
    | .backward => (family face.cell)⁻¹
  upperWhiskerCompositeFiberAut data.lift reselection
    localComparator face.outgoing

/-- Temporal product of one comparator family along a typed rewrite pasting. -/
noncomputable def upperPastingComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (family : UpperTwoCellComparatorFamily data)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    CompositeFiberAut (data.lift.geometry target) :=
  match pasting with
  | .nil _ => 1
  | .cons step tail =>
      upperPastingComparator data reselection family tail *
        upperOrientedFaceComparator data reselection family step.face

/-- Complete authored upper route comparator. -/
noncomputable def upperAuthoredPastingComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    CompositeFiberAut (data.lift.geometry target) :=
  upperPastingComparator data reselection
    (upperAuthoredComparatorFamily data) pasting

/-- Complete canonical upper route comparator. -/
noncomputable def upperCanonicalPastingComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    CompositeFiberAut (data.lift.geometry target) :=
  upperPastingComparator data reselection
    (upperCanonicalComparatorFamily data reselection) pasting

/-- Raw upper obstruction of a complete typed route. -/
noncomputable def upperPastingRawDefect
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    CompositeFiberAut (data.lift.geometry target) :=
  upperAuthoredPastingComparator data reselection pasting *
    (upperCanonicalPastingComparator data reselection pasting)⁻¹

/-- Public typed upper cocycle evaluator. -/
noncomputable def upperDefectPastingProduct
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    CompositeFiberAut (data.lift.geometry target) :=
  upperPastingRawDefect data reselection pasting

/-- Projection commutes with one oriented, whiskered face. -/
theorem pushforward_upperOrientedFaceComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (family : UpperTwoCellComparatorFamily data)
    {source target : P.Vertex}
    (face : WhiskeredFace P.toFiniteTransportTwoPresentation source target) :
    compositeFiberPushforward (data.lift.geometry target)
        (upperOrientedFaceComparator data reselection family face) =
      orientedFaceComparator data.coreData
        (pushforwardEdgeReselection data.lift reselection)
        (pushforwardUpperComparatorFamily data family) face := by
  rcases face with ⟨cell, incoming, outgoing, orientation⟩
  cases orientation <;>
    simp only [upperOrientedFaceComparator, orientedFaceComparator,
      pushforwardUpperComparatorFamily] <;>
    apply pushforward_upperWhiskerCompositeFiberAut

/-- Projection commutes with a complete temporal comparator product. -/
theorem pushforward_upperPastingComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (family : UpperTwoCellComparatorFamily data)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    compositeFiberPushforward (data.lift.geometry target)
        (upperPastingComparator data reselection family pasting) =
      pastingComparator data.coreData
        (pushforwardEdgeReselection data.lift reselection)
        (pushforwardUpperComparatorFamily data family) pasting := by
  induction pasting with
  | nil path => exact map_one _
  | cons step tail inductionHypothesis =>
      simp only [upperPastingComparator, pastingComparator, map_mul]
      rw [inductionHypothesis,
        pushforward_upperOrientedFaceComparator]

/-- Projection sends the authored upper route to the authored core route. -/
theorem pushforward_upperAuthoredPastingComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    compositeFiberPushforward (data.lift.geometry target)
        (upperAuthoredPastingComparator data reselection pasting) =
      authoredPastingComparator data.coreData
        (pushforwardEdgeReselection data.lift reselection) pasting := by
  unfold upperAuthoredPastingComparator authoredPastingComparator
  rw [pushforward_upperPastingComparator]
  rfl

/-- Projection sends the canonical upper route to the canonical core route. -/
theorem pushforward_upperCanonicalPastingComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    compositeFiberPushforward (data.lift.geometry target)
        (upperCanonicalPastingComparator data reselection pasting) =
      canonicalPastingComparator data.coreData
        (pushforwardEdgeReselection data.lift reselection) pasting := by
  unfold upperCanonicalPastingComparator canonicalPastingComparator
  rw [pushforward_upperPastingComparator]
  apply congrArg (fun family => pastingComparator data.coreData
    (pushforwardEdgeReselection data.lift reselection) family pasting)
  funext cell
  exact pushforward_upperCanonicalTwoCellComparator data reselection cell

/-- Projection preserves the complete upper pasting defect. -/
theorem pushforward_upperDefectPastingProduct
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    compositeFiberPushforward (data.lift.geometry target)
        (upperDefectPastingProduct data reselection pasting) =
      defectPastingProduct data.coreData
        (pushforwardEdgeReselection data.lift reselection) pasting := by
  unfold upperDefectPastingProduct upperPastingRawDefect defectPastingProduct
  unfold pastingRawDefect
  rw [map_mul, map_inv, pushforward_upperAuthoredPastingComparator,
    pushforward_upperCanonicalPastingComparator]

/-! ## Canonical factorization and route independence -/

/-- Upper reselected path evaluation preserves concatenation. -/
theorem upperReselectedPathLift_append
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data)
    {i j k : P.Vertex} (first : P.Path i j) (second : P.Path j k) :
    upperReselectedPathLift data reselection (first.append second) =
      (upperReselectedPathLift data reselection first).comp
        (upperReselectedPathLift data reselection second) :=
  (upperReselectLiftData data reselection).pathLift_append first second

/-- Authored comparison carried by one oriented upper face. -/
noncomputable def upperOrientedFaceAuthoredComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    (face : WhiskeredFace P.toFiniteTransportTwoPresentation source target) :
    CompositeFiberAut (data.lift.geometry target) :=
  upperOrientedFaceComparator data reselection
    (upperAuthoredComparatorFamily data) face

/-- Canonical comparison carried by one oriented upper face. -/
noncomputable def upperOrientedFaceCanonicalComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    (face : WhiskeredFace P.toFiniteTransportTwoPresentation source target) :
    CompositeFiberAut (data.lift.geometry target) :=
  upperOrientedFaceComparator data reselection
    (upperCanonicalComparatorFamily data reselection) face

/-- The inverse upper canonical comparator factors the reversed local relation. -/
theorem upperCanonicalTwoCellComparator_inv_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    (upperReselectedPathLift data.lift reselection (P.twoRight cell)).comp
      (CompositeFiberAut.hom
        (upperCanonicalTwoCellComparator data reselection cell)⁻¹) =
      upperReselectedPathLift data.lift reselection (P.twoLeft cell) := by
  let comparator := upperCanonicalTwoCellComparator data reselection cell
  change (upperReselectedPathLift data.lift reselection
      (P.twoRight cell)).comp (CompositeFiberAut.inv comparator) = _
  calc
    _ = ((upperReselectedPathLift data.lift reselection
          (P.twoLeft cell)).comp
        (CompositeFiberAut.hom comparator)).comp
          (CompositeFiberAut.inv comparator) := by
      exact congrArg
        (fun morphism => morphism.comp (CompositeFiberAut.inv comparator))
        (upperCanonicalTwoCellComparator_fac data reselection cell).symm
    _ = (upperReselectedPathLift data.lift reselection
          (P.twoLeft cell)).comp
        ((CompositeFiberAut.hom comparator).comp
          (CompositeFiberAut.inv comparator)) :=
      @Category.assoc
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _
        (upperReselectedPathLift data.lift reselection (P.twoLeft cell))
        (CompositeFiberAut.hom comparator) (CompositeFiberAut.inv comparator)
    _ = (upperReselectedPathLift data.lift reselection
          (P.twoLeft cell)).comp
        (𝟙 (data.lift.geometry (P.twoTarget cell))) := by
      exact congrArg
        (fun morphism =>
          (upperReselectedPathLift data.lift reselection
            (P.twoLeft cell)).comp morphism)
        comparator.1.hom_inv_id
    _ = _ := @Category.comp_id
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ (upperReselectedPathLift data.lift reselection (P.twoLeft cell))

/-- One oriented canonical upper face identifies its complete typed paths. -/
theorem upperOrientedFaceCanonicalComparator_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    (face : WhiskeredFace P.toFiniteTransportTwoPresentation source target) :
    (upperReselectedPathLift data.lift reselection face.before).comp
      (CompositeFiberAut.hom
        (upperOrientedFaceCanonicalComparator data reselection face)) =
      upperReselectedPathLift data.lift reselection face.after := by
  rcases face with ⟨cell, incoming, outgoing, orientation⟩
  cases orientation <;>
    simp only [WhiskeredFace.before, WhiskeredFace.after,
      WhiskeredFace.localBefore, WhiskeredFace.localAfter,
      upperOrientedFaceCanonicalComparator, upperOrientedFaceComparator,
      upperCanonicalComparatorFamily]
  · rw [upperReselectedPathLift_append, upperReselectedPathLift_append,
      upperReselectedPathLift_append, upperReselectedPathLift_append]
    calc
      _ = (upperReselectedPathLift data.lift reselection incoming).comp
          (((upperReselectedPathLift data.lift reselection
              (P.twoLeft cell)).comp
            (upperReselectedPathLift data.lift reselection outgoing)).comp
            (CompositeFiberAut.hom
              (upperWhiskerCompositeFiberAut data.lift reselection
                (upperCanonicalTwoCellComparator data reselection cell)
                outgoing))) :=
        @Category.assoc
          (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ _ _ _ _ _
      _ = (upperReselectedPathLift data.lift reselection incoming).comp
          ((upperReselectedPathLift data.lift reselection
              (P.twoLeft cell)).comp
            ((upperReselectedPathLift data.lift reselection outgoing).comp
              (CompositeFiberAut.hom
                (upperWhiskerCompositeFiberAut data.lift reselection
                  (upperCanonicalTwoCellComparator data reselection cell)
                  outgoing)))) := by
        exact congrArg
          (fun morphism =>
            (upperReselectedPathLift data.lift reselection incoming).comp morphism)
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _)
      _ = (upperReselectedPathLift data.lift reselection incoming).comp
          ((upperReselectedPathLift data.lift reselection
              (P.twoLeft cell)).comp
            ((CompositeFiberAut.hom
              (upperCanonicalTwoCellComparator data reselection cell)).comp
              (upperReselectedPathLift data.lift reselection outgoing))) := by
        rw [upperWhiskerCompositeFiberAut_fac]
        rfl
      _ = (upperReselectedPathLift data.lift reselection incoming).comp
          (((upperReselectedPathLift data.lift reselection
              (P.twoLeft cell)).comp
            (CompositeFiberAut.hom
              (upperCanonicalTwoCellComparator data reselection cell))).comp
            (upperReselectedPathLift data.lift reselection outgoing)) := by
        exact congrArg
          (fun morphism =>
            (upperReselectedPathLift data.lift reselection incoming).comp morphism)
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _).symm
      _ = _ := by rw [upperCanonicalTwoCellComparator_fac]
  · rw [upperReselectedPathLift_append, upperReselectedPathLift_append,
      upperReselectedPathLift_append, upperReselectedPathLift_append]
    calc
      _ = (upperReselectedPathLift data.lift reselection incoming).comp
          (((upperReselectedPathLift data.lift reselection
              (P.twoRight cell)).comp
            (upperReselectedPathLift data.lift reselection outgoing)).comp
            (CompositeFiberAut.hom
              (upperWhiskerCompositeFiberAut data.lift reselection
                (upperCanonicalTwoCellComparator data reselection cell)⁻¹
                outgoing))) :=
        @Category.assoc
          (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ _ _ _ _ _
      _ = (upperReselectedPathLift data.lift reselection incoming).comp
          ((upperReselectedPathLift data.lift reselection
              (P.twoRight cell)).comp
            ((upperReselectedPathLift data.lift reselection outgoing).comp
              (CompositeFiberAut.hom
                (upperWhiskerCompositeFiberAut data.lift reselection
                  (upperCanonicalTwoCellComparator data reselection cell)⁻¹
                  outgoing)))) := by
        exact congrArg
          (fun morphism =>
            (upperReselectedPathLift data.lift reselection incoming).comp morphism)
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _)
      _ = (upperReselectedPathLift data.lift reselection incoming).comp
          ((upperReselectedPathLift data.lift reselection
              (P.twoRight cell)).comp
            ((CompositeFiberAut.hom
              (upperCanonicalTwoCellComparator data reselection cell)⁻¹).comp
              (upperReselectedPathLift data.lift reselection outgoing))) := by
        rw [upperWhiskerCompositeFiberAut_fac]
        rfl
      _ = (upperReselectedPathLift data.lift reselection incoming).comp
          (((upperReselectedPathLift data.lift reselection
              (P.twoRight cell)).comp
            (CompositeFiberAut.hom
              (upperCanonicalTwoCellComparator data reselection cell)⁻¹)).comp
            (upperReselectedPathLift data.lift reselection outgoing)) := by
        exact congrArg
          (fun morphism =>
            (upperReselectedPathLift data.lift reselection incoming).comp morphism)
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _ _ _ _).symm
      _ = _ := by rw [upperCanonicalTwoCellComparator_inv_fac]

/-- A typed rewrite step's upper canonical comparator factors its paths. -/
theorem upperRewriteStepCanonicalComparator_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (step : RewriteStep P.toFiniteTransportTwoPresentation before finish) :
    (upperReselectedPathLift data.lift reselection before).comp
      (CompositeFiberAut.hom
        (upperOrientedFaceCanonicalComparator data reselection step.face)) =
      upperReselectedPathLift data.lift reselection finish := by
  rcases step with ⟨face, beforeEq, finishEq⟩
  subst before
  subst finish
  exact upperOrientedFaceCanonicalComparator_fac data reselection face

/-- The canonical comparator of a complete upper pasting factors its endpoints. -/
theorem upperCanonicalPastingComparator_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (pasting : RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    (upperReselectedPathLift data.lift reselection before).comp
      (CompositeFiberAut.hom
        (upperCanonicalPastingComparator data reselection pasting)) =
      upperReselectedPathLift data.lift reselection finish := by
  induction pasting with
  | nil path =>
      change (upperReselectedPathLift data.lift reselection path).comp
        (𝟙 (data.lift.geometry target)) = _
      exact (@Category.comp_id
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (upperReselectedPathLift data.lift reselection path))
  | cons step tail inductionHypothesis =>
      simp only [upperCanonicalPastingComparator, upperPastingComparator]
      change (upperReselectedPathLift data.lift reselection _).comp
        ((CompositeFiberAut.hom
          (upperOrientedFaceCanonicalComparator data reselection step.face)).comp
          (CompositeFiberAut.hom
            (upperPastingComparator data reselection
              (upperCanonicalComparatorFamily data reselection) tail))) = _
      calc
        _ = ((upperReselectedPathLift data.lift reselection _).comp
            (CompositeFiberAut.hom
              (upperOrientedFaceCanonicalComparator
                data reselection step.face))).comp
            (CompositeFiberAut.hom
              (upperPastingComparator data reselection
                (upperCanonicalComparatorFamily data reselection) tail)) :=
          (@Category.assoc
            (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
            _ _ _ _
            (upperReselectedPathLift data.lift reselection _)
            (CompositeFiberAut.hom
              (upperOrientedFaceCanonicalComparator data reselection step.face))
            (CompositeFiberAut.hom
              (upperPastingComparator data reselection
                (upperCanonicalComparatorFamily data reselection) tail))).symm
        _ = _ := by
          rw [upperRewriteStepCanonicalComparator_fac]
          exact inductionHypothesis

/-- The generated upper route comparator is independent of the typed pasting. -/
theorem upperCanonicalPastingComparator_unique
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex} {before finish : P.Path source target}
    (left right :
      RewritePasting P.toFiniteTransportTwoPresentation before finish) :
    upperCanonicalPastingComparator data reselection left =
      upperCanonicalPastingComparator data reselection right := by
  let lift := upperReselectedPathLift data.lift reselection before
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      lift.base.base lift :=
    (upperReselectLiftData data.lift reselection).pathLift_compositeStrong before
  apply CompositeFiberAut.ext_of_strong_fac lift
  exact (upperCanonicalPastingComparator_fac data reselection left).trans
    (upperCanonicalPastingComparator_fac data reselection right).symm

/-! ## Conditional upper cocycle and projection -/

/--
The direction hypothesis compares only the two authored upper route
comparators.  It contains no raw-vanishing or coherentizability certificate.
-/
def UpperSyzygyCompatible
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) : Prop :=
  ∀ cell : P.ThreeCell,
    upperAuthoredPastingComparator data reselection (P.threeLeft cell) =
      upperAuthoredPastingComparator data reselection (P.threeRight cell)

/-- Pointwise total coherence implies the authored upper syzygy equations. -/
theorem upperSyzygyCompatible_of_crossStageCoherentAt
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data reselection) :
    UpperSyzygyCompatible data reselection := by
  have familyEquality : upperAuthoredComparatorFamily data =
      upperCanonicalComparatorFamily data reselection := by
    funext cell
    let lift := upperReselectedPathLift data.lift reselection (P.twoLeft cell)
    letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
        lift.base.base lift :=
      (upperReselectLiftData data.lift reselection).pathLift_compositeStrong
        (P.twoLeft cell)
    apply CompositeFiberAut.ext_of_strong_fac lift
    exact (coherent cell).trans
      (upperCanonicalTwoCellComparator_fac data reselection cell).symm
  intro cell
  change upperPastingComparator data reselection
      (upperAuthoredComparatorFamily data) (P.threeLeft cell) =
    upperPastingComparator data reselection
      (upperAuthoredComparatorFamily data) (P.threeRight cell)
  rw [familyEquality]
  exact upperCanonicalPastingComparator_unique data reselection
    (P.threeLeft cell) (P.threeRight cell)

/-- Conditional `C_G` cocycle theorem for every declared typed 3-cell. -/
theorem upperRawDefect_cocycle_of_syzygy
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (compatible : UpperSyzygyCompatible data reselection)
    (cell : P.ThreeCell) :
    upperDefectPastingProduct data reselection (P.threeLeft cell) =
      upperDefectPastingProduct data reselection (P.threeRight cell) := by
  unfold upperDefectPastingProduct upperPastingRawDefect
  rw [compatible cell]
  rw [upperCanonicalPastingComparator_unique data reselection
    (P.threeLeft cell) (P.threeRight cell)]

/-- Projection of upper syzygy compatibility is G-106 syzygy compatibility. -/
theorem pushforward_upperSyzygyCompatible
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (compatible : UpperSyzygyCompatible data reselection) :
    SyzygyCompatible data.coreData
      (pushforwardEdgeReselection data.lift reselection) := by
  intro cell
  have projected := congrArg
    (compositeFiberPushforward
      (data.lift.geometry (P.threeTarget cell))) (compatible cell)
  simpa only [pushforward_upperAuthoredPastingComparator] using projected

/-- Applying `p` to an upper cocycle equation yields the core cocycle equation. -/
theorem pushforward_upperCocycleEquation
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (cell : P.ThreeCell)
    (equation :
      upperDefectPastingProduct data reselection (P.threeLeft cell) =
        upperDefectPastingProduct data reselection (P.threeRight cell)) :
    defectPastingProduct data.coreData
        (pushforwardEdgeReselection data.lift reselection)
        (P.threeLeft cell) =
      defectPastingProduct data.coreData
        (pushforwardEdgeReselection data.lift reselection)
        (P.threeRight cell) := by
  have projected := congrArg
    (compositeFiberPushforward
      (data.lift.geometry (P.threeTarget cell))) equation
  simpa only [pushforward_upperDefectPastingProduct] using projected

/-- The conditional upper theorem projects to the inherited conditional theorem. -/
theorem pushforward_upperRawDefect_cocycle_of_syzygy
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (compatible : UpperSyzygyCompatible data reselection)
    (cell : P.ThreeCell) :
    defectPastingProduct data.coreData
        (pushforwardEdgeReselection data.lift reselection)
        (P.threeLeft cell) =
      defectPastingProduct data.coreData
        (pushforwardEdgeReselection data.lift reselection)
        (P.threeRight cell) :=
  rawDefect_cocycle_of_syzygy data.coreData
    (pushforwardEdgeReselection data.lift reselection)
    (pushforward_upperSyzygyCompatible data reselection compatible) cell

/-! ## Nondegenerate syzygy support -/

/-- A typed rewrite pasting contains at least one actual face. -/
def RewritePastingHasFace
    {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex} {before finish : P.Path source target} :
    RewritePasting P.toFiniteTransportTwoPresentation before finish → Prop
  | .nil _ => False
  | .cons _ _ => True

/-- A declared 2-cell occurs in the support of a typed rewrite pasting. -/
def RewritePastingUsesCell
    {P : FiniteTransportPresentation.{u}} (cell : P.TwoCell)
    {source target : P.Vertex} {before finish : P.Path source target} :
    RewritePasting P.toFiniteTransportTwoPresentation before finish → Prop
  | .nil _ => False
  | .cons step tail => step.face.cell = cell ∨ RewritePastingUsesCell cell tail

/--
A nontrivial 3-cell has distinct, nonempty left and right typed pastings and an
actual declared face in their combined support.
-/
def NontrivialSyzygyAt
    {P : FiniteTransportPresentation.{u}} (cell : P.ThreeCell) : Prop :=
  P.threeLeft cell ≠ P.threeRight cell ∧
    RewritePastingHasFace (P.threeLeft cell) ∧
    RewritePastingHasFace (P.threeRight cell) ∧
    ∃ face : P.TwoCell,
      RewritePastingUsesCell face (P.threeLeft cell) ∨
        RewritePastingUsesCell face (P.threeRight cell)

/-- A syzygy support contains a genuinely nonidentity upper raw face. -/
def SyzygySupportHasNonidentityRaw
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (cell : P.ThreeCell) : Prop :=
  ∃ face : P.TwoCell,
    (RewritePastingUsesCell face (P.threeLeft cell) ∨
      RewritePastingUsesCell face (P.threeRight cell)) ∧
    upperRawTwoCellDefect data reselection face ≠ 1

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
