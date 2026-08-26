import ResearchLean.AG.DoctrineFiberProduct.IndexedBCRestrictionComparison
import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticVanishing
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticNaturalIsoCompatibility
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPastingCoherence
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticSourceFiberBridge

/-!
# Diagnostic components of the indexed Beck--Chevalley restriction

This module compares the indexed assembly on constant diagnostic diagrams
with fiberwise transport along the actual Beck--Chevalley routes.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Every path in a constant diagram evaluates to the identity. -/
theorem indexedConstantPath_eq_id
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    IndexedBasePath.eval (fun _ => X) (fun _ => 𝟙 X) path = 𝟙 X := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedBasePath.eval, inductionHypothesis, Category.id_comp]

/-- A diagnostic presentation interpreted constantly in one extraction fiber. -/
noncomputable def indexedConstantDiagram
    (G : IndexedBaseTwoShape.{u}) {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) : IndexedBaseDiagram G U where
  vertex := fun _ => X
  edge := fun _ => 𝟙 X
  relation := fun cell => by simp only [indexedConstantPath_eq_id]

/-- One base arrow induces a coherent hom between constant diagnostic diagrams. -/
noncomputable def indexedConstantDiagramHom
    (G : IndexedBaseTwoShape.{u}) {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y) :
    IndexedBaseDiagramHom (indexedConstantDiagram G X)
      (indexedConstantDiagram G Y) where
  app := fun _ => f
  naturality := fun _ => by
    change f ≫ 𝟙 Y = 𝟙 X ≫ f
    simp

/-- Fiberwise diagnostic data as an indexed interpretation of its constant base. -/
noncomputable def FiberwiseAdmissibleTransportData.toIndexedInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X) :
    IndexedDiagnosticInterpretation (indexedConstantDiagram G X) where
  package := data.packageTotal
  vertexBase := fun vertex => (data.package vertex).2
  edgeLift := data.edgeLift
  edgeOver := fun edge => (data.edgeIso edge).hom.2
  edgeStrong := fun edge => by
    letI : (packageProjection U).IsStronglyCocartesian
        ((packageProjection U).map (data.edgeLift edge))
        (data.edgeLift edge) := by
      simpa only [packageProjection_map] using
        data.edgeLift_isStronglyCocartesian edge
    letI : (packageProjection U).IsHomLift (𝟙 X) (data.edgeLift edge) :=
      (data.edgeIso edge).hom.2
    exact stronglyCocartesian_of_isHomLift
      (packageProjection U) (𝟙 X) (data.edgeLift edge)
  comparator := data.comparator

/-- Incidence of an indexed interpretation on its one constant core fiber. -/
noncomputable def IndexedDiagnosticInterpretation.constantFiberIncidence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (source : IndexedDiagnosticInterpretation (indexedConstantDiagram G X)) :
    DiagnosticSourceFiberIncidence U source.toAdmissibleTransportData X where
  vertexBase := source.vertexBase
  edgeVertical := fun edge => by
    simpa only [indexedConstantDiagram] using source.edgeOver edge

/-- Recover fiberwise diagnostic data from an interpretation on a constant
base diagram.  Edge invertibility is derived from strong cocartesianness over
the identity by the reviewed source-incidence bridge. -/
noncomputable def IndexedDiagnosticInterpretation.toFiberwiseOfConstant
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X : ExtractionInstance U}
    (source : IndexedDiagnosticInterpretation (indexedConstantDiagram G X)) :
    FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X :=
  source.constantFiberIncidence.toFiberwise

/-- Constant indexed transport generates the same package as fiberwise transport. -/
theorem indexedConstantTransport_package
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X)
    (vertex : G.Vertex) :
    ((indexedConstantDiagramHom G f).transportedInterpretation
      data.toIndexedInterpretation).package vertex =
      ((data.map (coreFiberTransportFunctor f)).package vertex).1 := by
  change (coreFiberTransportObj
      ((indexedConstantDiagramHom G f).vertexIndex vertex).decode
      (data.package vertex)).1 =
    (coreFiberTransportObj f (data.package vertex)).1
  rfl

/-- Constant indexed transport generates the same edge as fiberwise transport. -/
theorem indexedConstantTransport_edge
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X)
    {i j : G.Vertex} (edge : G.Edge i j) :
    ((indexedConstantDiagramHom G f).transportedInterpretation
      data.toIndexedInterpretation).edgeLift edge =
      ((data.map (coreFiberTransportFunctor f)).edgeIso edge).hom.1 := by
  letI : (packageProjection U).IsStronglyCocartesian f
      (coreFiberLift f (data.package i)) :=
    coreFiberLift_isStronglyCocartesian f (data.package i)
  letI : (packageProjection U).IsHomLift (𝟙 Y)
      (((indexedConstantDiagramHom G f).transportedInterpretation
        data.toIndexedInterpretation).edgeLift edge) :=
    (indexedConstantDiagramHom G f).transportedEdgeLift_isHomLift
      data.toIndexedInterpretation edge
  letI : (packageProjection U).IsHomLift (𝟙 Y)
      ((data.map (coreFiberTransportFunctor f)).edgeIso edge).hom.1 :=
    ((data.map (coreFiberTransportFunctor f)).edgeIso edge).hom.2
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) f (coreFiberLift f (data.package i)) (𝟙 Y)
  exact (indexedUniversalSquareEdgeLaw
      ((indexedConstantDiagramHom G f).validatedEdgeSquare edge)
      (data.package i) (data.package j) (data.edgeLift edge)
        (data.edgeIso edge).hom.2).trans
    (coreFiberTransportMap_fac f (data.edgeIso edge).hom).symm

/-- Constant indexed transport generates the same comparator as fiberwise transport. -/
theorem indexedConstantTransport_comparator
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X)
    (cell : G.TwoCell) :
    ((indexedConstantDiagramHom G f).transportedInterpretation
      data.toIndexedInterpretation).comparator cell =
      (data.map (coreFiberTransportFunctor f)).comparator cell := by
  rfl

/-- Constant indexed transport generates the same path as fiberwise transport. -/
theorem indexedConstantTransport_path
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    ((indexedConstantDiagramHom G f).transportedInterpretation
      data.toIndexedInterpretation).pathLift path =
      ((data.map (coreFiberTransportFunctor f)).toIndexedInterpretation).pathLift
        path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.pathLift]
      rw [indexedConstantTransport_edge, inductionHypothesis]
      rfl

/-- Constant indexed K3 uses the same endpoint action as fiberwise transport. -/
theorem indexedConstantTransport_endpointAction
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X)
    (vertex : G.Vertex) :
    (indexedConstantDiagramHom G f).endpointAction data.toIndexedInterpretation vertex =
      coreFiberFunctorPackageAutHom (coreFiberTransportFunctor f)
        (data.package vertex) := by
  rfl

/-- Constant indexed K3 maps each reselection by the same endpoint action as
the fiberwise transport API. -/
theorem indexedConstantTransport_reselection
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X)
    (reselection : EdgeReselection data.toLiftData)
    (i j : G.Vertex) (edge : G.Edge i j) :
    (indexedConstantDiagramHom G f).transportedReselection
        data.toIndexedInterpretation reselection i j edge =
      mapEdgeReselection data (coreFiberTransportFunctor f)
        reselection i j edge := by
  rfl

/-- Constant indexed K3 reselected edges are the total maps underlying the
fiberwise reselected edges. -/
theorem indexedConstantTransport_reselectedEdge
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (edge : G.Edge i j) :
    ((indexedConstantDiagramHom G f).transportedInterpretation
        data.toIndexedInterpretation).reselectedEdgeLift
          ((indexedConstantDiagramHom G f).transportedReselection
            data.toIndexedInterpretation reselection) edge =
      (fiberReselectedEdge (data.map (coreFiberTransportFunctor f))
        (mapEdgeReselection data (coreFiberTransportFunctor f) reselection) edge).1 := by
  unfold IndexedDiagnosticInterpretation.reselectedEdgeLift fiberReselectedEdge
  rw [indexedConstantTransport_edge, indexedConstantTransport_reselection]
  change
    ((data.map (coreFiberTransportFunctor f)).edgeIso edge).hom.1 ≫
        PackageFiberAut.hom
          (mapEdgeReselection data (coreFiberTransportFunctor f)
            reselection i j edge) =
      ((data.map (coreFiberTransportFunctor f)).edgeIso edge).hom.1 ≫
        (packageFiberAutCoreFiberEquiv
          ((data.map (coreFiberTransportFunctor f)).package j)
          (mapEdgeReselection data (coreFiberTransportFunctor f)
            reselection i j edge)).hom.1
  rw [packageFiberAutCoreFiberEquiv_hom_val]

/-- Constant indexed K3 reselected paths agree with the underlying fiberwise
reselected paths. -/
theorem indexedConstantTransport_reselectedPath
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (f : X ⟶ Y)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U X)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    ((indexedConstantDiagramHom G f).transportedInterpretation
        data.toIndexedInterpretation).reselectedPathLift
          ((indexedConstantDiagramHom G f).transportedReselection
            data.toIndexedInterpretation reselection) path =
      (fiberReselectedPath (data.map (coreFiberTransportFunctor f))
        (mapEdgeReselection data (coreFiberTransportFunctor f) reselection)
        path.toPresentedPath).1 := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.reselectedPathLift,
        IndexedBasePath.toPresentedPath, fiberReselectedPath]
      rw [indexedConstantTransport_reselectedEdge, inductionHypothesis]
      rfl

/-! ## Pointed Beck--Chevalley specialization -/

/-- The reviewed left reindex factor, retained outside the covariant indexed hom. -/
noncomputable abbrev indexedBCLeftReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcLeftPresentation presentation))

/-- The reviewed right reindex factor, retained outside the covariant indexed hom. -/
noncomputable abbrev indexedBCRightReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :=
  selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcRightPresentation presentation))

/-- The direct route first applies the reviewed left reindex, then performs the
top arrow by the actual indexed diagnostic assembly. -/
noncomputable def indexedBCDirectInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) :=
  (indexedConstantDiagramHom G
      (typedPresentationToSemantic (bcTopPresentation presentation))).transportedInterpretation
    (data.map (indexedBCLeftReindexFunctor presentation)).toIndexedInterpretation

/-- The actual K2 bottom transport before the external right reindex factor. -/
noncomputable def indexedBCBottomInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) :=
  (indexedConstantDiagramHom G
      (typedPresentationToSemantic
        (bcBottomPresentation presentation))).transportedInterpretation
    data.toIndexedInterpretation

/-- The actual indexed bottom output, re-expressed in its constant core fiber,
is the reviewed fiberwise bottom transport. -/
theorem indexedBCBottomFiberwise_eq_map
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) :
    (indexedBCBottomInterpretation presentation data).toFiberwiseOfConstant =
      data.map (coreFiberTransportFunctor
        (typedPresentationToSemantic (bcBottomPresentation presentation))) := by
  apply fiberwiseAdmissibleTransportData_ext
  · funext vertex
    apply Subtype.ext
    exact indexedConstantTransport_package _ data vertex
  · apply heq_of_eq
    funext i j edge
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    change (indexedBCBottomInterpretation presentation data).edgeLift edge = _
    exact indexedConstantTransport_edge _ data edge
  · apply heq_of_eq
    funext cell
    exact indexedConstantTransport_comparator _ data cell

/-- The via-base route performs the actual bottom indexed assembly, converts
that generated output inside its constant fiber, and only then applies the
reviewed external right reindex factor. -/
noncomputable def indexedBCViaBaseInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) :=
  ((((indexedBCBottomInterpretation presentation data).toFiberwiseOfConstant).map
      (indexedBCRightReindexFunctor presentation)).toIndexedInterpretation)

/-- C1 package comparison on the direct staged indexed route. -/
theorem indexedBCDirect_package_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (vertex : G.Vertex) :
    (indexedBCDirectInterpretation presentation data).package vertex =
      ((data.map (bcDiagnosticDirectFunctor presentation)).package vertex).1 := by
  calc
    _ = (((data.map (indexedBCLeftReindexFunctor presentation)).map
        (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcTopPresentation presentation)))).package
            vertex).1 := indexedConstantTransport_package _ _ _
    _ = ((data.map (indexedBCRestrictionDirectFunctor presentation)).package
          vertex).1 := by
      rw [← fiberwiseAdmissibleTransportData_map_comp]
      rfl
    _ = _ := by rw [indexedBCRestrictionDirectFunctor_eq_g110]

/-- C1 package comparison on the via-base staged indexed route. -/
theorem indexedBCViaBase_package_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (vertex : G.Vertex) :
    (indexedBCViaBaseInterpretation presentation data).package vertex =
      ((data.map (bcDiagnosticViaBaseFunctor presentation)).package vertex).1 := by
  unfold indexedBCViaBaseInterpretation
  rw [indexedBCBottomFiberwise_eq_map]
  change ((((data.map _).map _).package vertex).1) = _
  rw [← fiberwiseAdmissibleTransportData_map_comp]
  change ((data.map (indexedBCRestrictionViaBaseFunctor presentation)).package
      vertex).1 = _
  rw [indexedBCRestrictionViaBaseFunctor_eq_g110]

/-- C1 edge comparison on the direct staged indexed route. -/
theorem indexedBCDirect_edge_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    {i j : G.Vertex} (edge : G.Edge i j) :
    (indexedBCDirectInterpretation presentation data).edgeLift edge =
      ((data.map (bcDiagnosticDirectFunctor presentation)).edgeIso edge).hom.1 := by
  simpa only [indexedBCDirectInterpretation, bcDiagnosticDirectFunctor,
    indexedBCLeftReindexFunctor] using
      indexedConstantTransport_edge
        (typedPresentationToSemantic (bcTopPresentation presentation))
        (data.map (indexedBCLeftReindexFunctor presentation)) edge

/-- C1 edge comparison on the via-base staged indexed route. -/
theorem indexedBCViaBase_edge_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    {i j : G.Vertex} (edge : G.Edge i j) :
    (indexedBCViaBaseInterpretation presentation data).edgeLift edge =
      ((data.map (bcDiagnosticViaBaseFunctor presentation)).edgeIso edge).hom.1 := by
  unfold indexedBCViaBaseInterpretation bcDiagnosticViaBaseFunctor
  rfl

/-- C1 direct comparator is generated by the two actual route factors. -/
theorem indexedBCDirect_comparator_factor
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (cell : G.TwoCell) :
    (indexedBCDirectInterpretation presentation data).comparator cell =
      coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcTopPresentation presentation)))
        ((data.map (indexedBCLeftReindexFunctor presentation)).package
          (G.twoTarget cell))
        ((data.map (indexedBCLeftReindexFunctor presentation)).comparator cell) :=
  indexedConstantTransport_comparator _ _ _

/-- C1 via-base comparator is generated by the two actual route factors. -/
theorem indexedBCViaBase_comparator_factor
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (cell : G.TwoCell) :
    (indexedBCViaBaseInterpretation presentation data).comparator cell =
      coreFiberFunctorPackageAutHom (indexedBCRightReindexFunctor presentation)
        ((data.map (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation)))).package
            (G.twoTarget cell))
        ((data.map (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation)))).comparator
            cell) := by
  rfl

/-- C2 identifies the full direct endpoint action with its two reviewed factors. -/
theorem indexedBCDirect_endpointAction_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (P : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    coreFiberFunctorPackageAutHom (indexedBCRestrictionDirectFunctor presentation) P =
      (coreFiberFunctorPackageAutHom
        (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcTopPresentation presentation)))
        ((indexedBCLeftReindexFunctor presentation).obj P)).comp
          (coreFiberFunctorPackageAutHom
            (indexedBCLeftReindexFunctor presentation) P) := by
  exact coreFiberFunctorPackageAutHom_comp _ _ _

/-- C2 identifies the full via-base endpoint action with its two reviewed factors. -/
theorem indexedBCViaBase_endpointAction_comp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (P : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    coreFiberFunctorPackageAutHom (indexedBCRestrictionViaBaseFunctor presentation) P =
      (coreFiberFunctorPackageAutHom (indexedBCRightReindexFunctor presentation)
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation))).obj P)).comp
          (coreFiberFunctorPackageAutHom
            (coreFiberTransportFunctor
              (typedPresentationToSemantic (bcBottomPresentation presentation))) P) := by
  exact coreFiberFunctorPackageAutHom_comp _ _ _

/-- C2 direct endpoint action is the actual G-110 endpoint action. -/
theorem indexedBCDirect_endpointAction_eq_g110
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (P : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    coreFiberFunctorPackageAutHom (indexedBCRestrictionDirectFunctor presentation) P =
      coreFiberFunctorPackageAutHom (bcDiagnosticDirectFunctor presentation) P := by
  rfl

/-- C2 via-base endpoint action is the actual G-110 endpoint action. -/
theorem indexedBCViaBase_endpointAction_eq_g110
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (P : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    coreFiberFunctorPackageAutHom (indexedBCRestrictionViaBaseFunctor presentation) P =
      coreFiberFunctorPackageAutHom (bcDiagnosticViaBaseFunctor presentation) P := by
  rfl

/-- C1 direct comparator is the actual G-110 generated comparator. -/
theorem indexedBCDirect_comparator_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (cell : G.TwoCell) :
    (indexedBCDirectInterpretation presentation data).comparator cell =
      (data.map (bcDiagnosticDirectFunctor presentation)).comparator cell := by
  rw [indexedBCDirect_comparator_factor]
  simpa only [FiberwiseAdmissibleTransportData.map, bcDiagnosticDirectFunctor]
    using congrArg (fun action => action (data.comparator cell))
      (indexedBCDirect_endpointAction_comp presentation
        (data.package (G.twoTarget cell))).symm

/-- C1 via-base comparator is the actual G-110 generated comparator. -/
theorem indexedBCViaBase_comparator_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (cell : G.TwoCell) :
    (indexedBCViaBaseInterpretation presentation data).comparator cell =
      (data.map (bcDiagnosticViaBaseFunctor presentation)).comparator cell := by
  rw [indexedBCViaBase_comparator_factor]
  simpa only [FiberwiseAdmissibleTransportData.map, bcDiagnosticViaBaseFunctor]
    using congrArg (fun action => action (data.comparator cell))
      (indexedBCViaBase_endpointAction_comp presentation
        (data.package (G.twoTarget cell))).symm

/-- C1 compares every direct indexed path with the corresponding G-110 path. -/
theorem indexedBCDirect_path_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (indexedBCDirectInterpretation presentation data).pathLift path =
      ((data.map (bcDiagnosticDirectFunctor presentation)).toIndexedInterpretation).pathLift
        path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.pathLift]
      rw [indexedBCDirect_edge_eq_g110, inductionHypothesis]
      rfl

/-- C1 compares every via-base indexed path with the corresponding G-110 path. -/
theorem indexedBCViaBase_path_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (indexedBCViaBaseInterpretation presentation data).pathLift path =
      ((data.map (bcDiagnosticViaBaseFunctor presentation)).toIndexedInterpretation).pathLift
        path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.pathLift]
      rw [indexedBCViaBase_edge_eq_g110, inductionHypothesis]
      rfl

/-- C1 identifies the direct indexed and G-110 two-cell base equations by
comparing both actual path components. -/
theorem indexedBCDirect_twoCellBase_iff_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (cell : G.TwoCell) :
    (((indexedBCDirectInterpretation presentation data).pathLift
          (G.twoLeft cell)).base =
        ((indexedBCDirectInterpretation presentation data).pathLift
          (G.twoRight cell)).base) ↔
      ((((data.map (bcDiagnosticDirectFunctor presentation)).toIndexedInterpretation).pathLift
          (G.twoLeft cell)).base =
        (((data.map (bcDiagnosticDirectFunctor presentation)).toIndexedInterpretation).pathLift
          (G.twoRight cell)).base) := by
  rw [indexedBCDirect_path_eq_g110, indexedBCDirect_path_eq_g110]

/-- C1 identifies the via-base indexed and G-110 two-cell base equations by
comparing both actual path components. -/
theorem indexedBCViaBase_twoCellBase_iff_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (cell : G.TwoCell) :
    (((indexedBCViaBaseInterpretation presentation data).pathLift
          (G.twoLeft cell)).base =
        ((indexedBCViaBaseInterpretation presentation data).pathLift
          (G.twoRight cell)).base) ↔
      ((((data.map (bcDiagnosticViaBaseFunctor presentation)).toIndexedInterpretation).pathLift
          (G.twoLeft cell)).base =
        (((data.map (bcDiagnosticViaBaseFunctor presentation)).toIndexedInterpretation).pathLift
          (G.twoRight cell)).base) := by
  rw [indexedBCViaBase_path_eq_g110, indexedBCViaBase_path_eq_g110]

/-! ## Native K3 restriction components -/

/-- The direct K3 reselection: external left reindex followed by the actual
indexed top endpoint action. -/
noncomputable def indexedBCDirectTransportedReselection
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData) :
    IndexedEdgeReselection (indexedBCDirectInterpretation presentation data) :=
  (indexedConstantDiagramHom G
      (typedPresentationToSemantic (bcTopPresentation presentation))).transportedReselection
    (data.map (indexedBCLeftReindexFunctor presentation)).toIndexedInterpretation
    (mapEdgeReselection data (indexedBCLeftReindexFunctor presentation) reselection)

/-- The via K3 reselection: actual indexed bottom endpoint action followed by
the external right reindex action. -/
noncomputable def indexedBCViaBaseTransportedReselection
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData) :
    IndexedEdgeReselection (indexedBCViaBaseInterpretation presentation data) :=
  mapEdgeReselection
    (indexedBCBottomInterpretation presentation data).toFiberwiseOfConstant
    (indexedBCRightReindexFunctor presentation)
    ((indexedConstantDiagramHom G
      (typedPresentationToSemantic
        (bcBottomPresentation presentation))).transportedReselection
      data.toIndexedInterpretation reselection)

/-- Direct native K3 endpoint action composes to the actual G-110 endpoint. -/
theorem indexedBCDirect_K3_endpointAction_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (vertex : G.Vertex) :
    ((indexedConstantDiagramHom G
        (typedPresentationToSemantic (bcTopPresentation presentation))).endpointAction
      (data.map (indexedBCLeftReindexFunctor presentation)).toIndexedInterpretation
      vertex).comp
        (coreFiberFunctorPackageAutHom (indexedBCLeftReindexFunctor presentation)
          (data.package vertex)) =
      coreFiberFunctorPackageAutHom (bcDiagnosticDirectFunctor presentation)
        (data.package vertex) := by
  simpa only [indexedConstantTransport_endpointAction,
    bcDiagnosticDirectFunctor, indexedBCLeftReindexFunctor] using
      (coreFiberFunctorPackageAutHom_comp
        (indexedBCLeftReindexFunctor presentation)
        (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcTopPresentation presentation)))
        (data.package vertex)).symm

/-- Via native K3 endpoint action composes with the external right factor to
the actual G-110 endpoint. -/
theorem indexedBCViaBase_K3_endpointAction_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (vertex : G.Vertex) :
    (coreFiberFunctorPackageAutHom (indexedBCRightReindexFunctor presentation)
      ((indexedBCBottomInterpretation presentation data).toFiberwiseOfConstant.package
        vertex)).comp
      ((indexedConstantDiagramHom G
        (typedPresentationToSemantic (bcBottomPresentation presentation))).endpointAction
        data.toIndexedInterpretation vertex) =
      coreFiberFunctorPackageAutHom (bcDiagnosticViaBaseFunctor presentation)
        (data.package vertex) := by
  simpa only [indexedConstantTransport_endpointAction,
    bcDiagnosticViaBaseFunctor, indexedBCRightReindexFunctor] using
      (coreFiberFunctorPackageAutHom_comp
        (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation)))
        (indexedBCRightReindexFunctor presentation)
        (data.package vertex)).symm

/-- Direct transported reselection agrees coordinatewise with G-110. -/
theorem indexedBCDirectTransportedReselection_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    (i j : G.Vertex) (edge : G.Edge i j) :
    indexedBCDirectTransportedReselection presentation data reselection i j edge =
      mapEdgeReselection data (bcDiagnosticDirectFunctor presentation)
        reselection i j edge := by
  unfold indexedBCDirectTransportedReselection
  rw [indexedConstantTransport_reselection]
  exact congrFun (congrFun (congrFun
    (congrArg (fun mapped => mapped)
      (mapEdgeReselection_comp data
        (indexedBCLeftReindexFunctor presentation)
        (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcTopPresentation presentation)))
        reselection).symm) i) j) edge

/-- Via transported reselection agrees coordinatewise with G-110. -/
theorem indexedBCViaBaseTransportedReselection_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    (i j : G.Vertex) (edge : G.Edge i j) :
    indexedBCViaBaseTransportedReselection presentation data reselection i j edge =
      mapEdgeReselection data (bcDiagnosticViaBaseFunctor presentation)
        reselection i j edge := by
  unfold indexedBCViaBaseTransportedReselection
  change
    coreFiberFunctorPackageAutHom (indexedBCRightReindexFunctor presentation)
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation))).obj
            (data.package j))
        (coreFiberFunctorPackageAutHom
          (coreFiberTransportFunctor
            (typedPresentationToSemantic (bcBottomPresentation presentation)))
          (data.package j) (reselection i j edge)) =
      coreFiberFunctorPackageAutHom (bcDiagnosticViaBaseFunctor presentation)
        (data.package j) (reselection i j edge)
  simpa only [bcDiagnosticViaBaseFunctor, indexedBCRightReindexFunctor] using
    congrArg (fun action => action (reselection i j edge))
      (coreFiberFunctorPackageAutHom_comp
        (coreFiberTransportFunctor
          (typedPresentationToSemantic (bcBottomPresentation presentation)))
        (indexedBCRightReindexFunctor presentation) (data.package j)).symm

/-- Direct actual indexed reselected edges agree with the G-110 total maps. -/
theorem indexedBCDirect_reselectedEdge_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (edge : G.Edge i j) :
    (indexedBCDirectInterpretation presentation data).reselectedEdgeLift
        (indexedBCDirectTransportedReselection presentation data reselection) edge =
      (fiberReselectedEdge (data.map (bcDiagnosticDirectFunctor presentation))
        (mapEdgeReselection data (bcDiagnosticDirectFunctor presentation)
          reselection) edge).1 := by
  unfold IndexedDiagnosticInterpretation.reselectedEdgeLift fiberReselectedEdge
  rw [indexedBCDirect_edge_eq_g110,
    indexedBCDirectTransportedReselection_eq_g110]
  change _ ≫ PackageFiberAut.hom _ = _ ≫
    (packageFiberAutCoreFiberEquiv _ _).hom.1
  rw [packageFiberAutCoreFiberEquiv_hom_val]

/-- Via actual indexed reselected edges agree with the G-110 total maps. -/
theorem indexedBCViaBase_reselectedEdge_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (edge : G.Edge i j) :
    (indexedBCViaBaseInterpretation presentation data).reselectedEdgeLift
        (indexedBCViaBaseTransportedReselection presentation data reselection) edge =
      (fiberReselectedEdge (data.map (bcDiagnosticViaBaseFunctor presentation))
        (mapEdgeReselection data (bcDiagnosticViaBaseFunctor presentation)
          reselection) edge).1 := by
  unfold IndexedDiagnosticInterpretation.reselectedEdgeLift fiberReselectedEdge
  rw [indexedBCViaBase_edge_eq_g110,
    indexedBCViaBaseTransportedReselection_eq_g110]
  change _ ≫ PackageFiberAut.hom _ = _ ≫
    (packageFiberAutCoreFiberEquiv _ _).hom.1
  rw [packageFiberAutCoreFiberEquiv_hom_val]

/-- Direct actual indexed reselected paths agree with G-110 path evaluation. -/
theorem indexedBCDirect_reselectedPath_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (indexedBCDirectInterpretation presentation data).reselectedPathLift
        (indexedBCDirectTransportedReselection presentation data reselection) path =
      (fiberReselectedPath (data.map (bcDiagnosticDirectFunctor presentation))
        (mapEdgeReselection data (bcDiagnosticDirectFunctor presentation)
          reselection) path.toPresentedPath).1 := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.reselectedPathLift,
        IndexedBasePath.toPresentedPath, fiberReselectedPath]
      rw [indexedBCDirect_reselectedEdge_eq_g110, inductionHypothesis]
      rfl

/-- Via actual indexed reselected paths agree with G-110 path evaluation. -/
theorem indexedBCViaBase_reselectedPath_eq_g110
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (indexedBCViaBaseInterpretation presentation data).reselectedPathLift
        (indexedBCViaBaseTransportedReselection presentation data reselection) path =
      (fiberReselectedPath (data.map (bcDiagnosticViaBaseFunctor presentation))
        (mapEdgeReselection data (bcDiagnosticViaBaseFunctor presentation)
          reselection) path.toPresentedPath).1 := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      simp only [IndexedDiagnosticInterpretation.reselectedPathLift,
        IndexedBasePath.toPresentedPath, fiberReselectedPath]
      rw [indexedBCViaBase_reselectedEdge_eq_g110, inductionHypothesis]
      rfl

/-- The exact indexed restriction mate is invertible. -/
noncomputable instance indexedBCRestrictionMate_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    IsIso (indexedBCRestrictionMate presentation) := by
  rw [indexedBCRestrictionMate_eq_g110]
  exact coreBeckChevalleyMate_isIso presentation

/-- The indexed restriction mate as the generated cross-route isomorphism. -/
noncomputable def indexedBCRestrictionMateIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    indexedBCRestrictionDirectFunctor presentation ≅
      indexedBCRestrictionViaBaseFunctor presentation :=
  asIso (indexedBCRestrictionMate presentation)

/-- C1--C2 diagnostic components generated from the indexed restriction mate. -/
noncomputable def indexedBCRestrictionDiagnosticCompatibility
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) :
    FiberwiseDiagnosticNaturalIsoCompatibility data
      (indexedBCRestrictionDirectFunctor presentation)
      (indexedBCRestrictionViaBaseFunctor presentation)
      (indexedBCRestrictionMateIso presentation) :=
  fiberwiseDiagnosticNaturalIsoCompatibility data _ _ _

/-- C2 mapped reselections are conjugate through the indexed mate component. -/
theorem indexedBCRestriction_mappedReselection_naturality
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (edge : G.Edge i j) :
    packageFiberAutMulEquivOfCoreFiberIso
        ((indexedBCRestrictionMateIso presentation).app (data.package j))
        (mapEdgeReselection data
          (indexedBCRestrictionDirectFunctor presentation) reselection i j edge) =
      mapEdgeReselection data
        (indexedBCRestrictionViaBaseFunctor presentation) reselection i j edge :=
  (indexedBCRestrictionDiagnosticCompatibility presentation data).mappedReselection_naturality
    reselection edge

/-- C2 reselected generating edges commute through the indexed mate component. -/
theorem indexedBCRestriction_reselectedEdge_naturality
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex} (edge : G.Edge i j) :
    fiberReselectedEdge
          (data.map (indexedBCRestrictionDirectFunctor presentation))
          (mapEdgeReselection data
            (indexedBCRestrictionDirectFunctor presentation) reselection) edge ≫
        (indexedBCRestrictionMateIso presentation).hom.app (data.package j) =
      (indexedBCRestrictionMateIso presentation).hom.app (data.package i) ≫
        fiberReselectedEdge
          (data.map (indexedBCRestrictionViaBaseFunctor presentation))
          (mapEdgeReselection data
            (indexedBCRestrictionViaBaseFunctor presentation) reselection) edge :=
  (indexedBCRestrictionDiagnosticCompatibility presentation data).reselectedEdge_naturality
    reselection edge

/-- C2 reselected paths commute through the same indexed mate components. -/
theorem indexedBCRestriction_reselectedPath_naturality
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData)
    {i j : G.Vertex}
    (path : G.toFiniteTransportPresentation.Path i j) :
    fiberReselectedPath
          (data.map (indexedBCRestrictionDirectFunctor presentation))
          (mapEdgeReselection data
            (indexedBCRestrictionDirectFunctor presentation) reselection) path ≫
        (indexedBCRestrictionMateIso presentation).hom.app (data.package j) =
      (indexedBCRestrictionMateIso presentation).hom.app (data.package i) ≫
        fiberReselectedPath
          (data.map (indexedBCRestrictionViaBaseFunctor presentation))
          (mapEdgeReselection data
            (indexedBCRestrictionViaBaseFunctor presentation) reselection) path :=
  (indexedBCRestrictionDiagnosticCompatibility presentation data).reselectedPath_naturality
    reselection path

/-- The C3 indexed-to-direct side is the canonical equality isomorphism. -/
noncomputable def indexedBCToDirectIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    indexedBCRestrictionDirectFunctor presentation ≅
      bcDiagnosticDirectFunctor presentation :=
  eqToIso (indexedBCRestrictionDirectFunctor_eq_g110 presentation)

/-- The reviewed G-110 comparison as a natural isomorphism. -/
noncomputable def g110BCComparisonIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    bcDiagnosticDirectFunctor presentation ≅
      bcDiagnosticViaBaseFunctor presentation := by
  letI : IsIso (coreBeckChevalleyMate presentation) :=
    coreBeckChevalleyMate_isIso presentation
  exact asIso (coreBeckChevalleyMate presentation)

/-- The C3 indexed-to-via side follows the indexed mate and the via equality. -/
noncomputable def indexedBCToViaBaseIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    indexedBCRestrictionDirectFunctor presentation ≅
      bcDiagnosticViaBaseFunctor presentation :=
  indexedBCRestrictionMateIso presentation ≪≫
    eqToIso (indexedBCRestrictionViaBaseFunctor_eq_g110 presentation)

/-- C3 component triangle on every source package.  The two equality sides
are identities because Cycle 16 identifies the indexed functors with the
actual G-110 functors; the middle side is the generated indexed mate. -/
theorem indexedBCRestriction_comparison_triangle_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U)
    (package : CoreFiber presentation.1.cospan.firstSource.toSemantic) :
    (indexedBCToDirectIso presentation).hom.app package ≫
        (g110BCComparisonIso presentation).hom.app package =
      (indexedBCToViaBaseIso presentation).hom.app package := by
  change
    (𝟙 ((indexedBCRestrictionDirectFunctor presentation).obj package)) ≫
        (coreBeckChevalleyMate presentation).app package =
      (indexedBCRestrictionMate presentation).app package ≫
        𝟙 ((indexedBCRestrictionViaBaseFunctor presentation).obj package)
  simp only [Category.id_comp, Category.comp_id]
  exact congrArg (fun transformation => transformation.app package)
    (indexedBCRestrictionMate_eq_g110 presentation).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
