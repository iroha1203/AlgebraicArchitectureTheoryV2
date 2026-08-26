import ResearchLean.AG.DoctrineFiberProduct.IndexedBCRestrictionComparison
import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticVanishing
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticNaturalIsoCompatibility
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPastingCoherence

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

/-- The via-base route performs the bottom indexed assembly and then retains
the reviewed right reindex as its external second factor. -/
noncomputable def indexedBCViaBaseInterpretation
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) :=
  (((data.map (coreFiberTransportFunctor
      (typedPresentationToSemantic (bcBottomPresentation presentation)))).map
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

/-- C1 records the indexed and G-110 direct two-cell equations generated from
the same constant target relation. -/
theorem indexedBCDirect_twoCellBase_pair
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (cell : G.TwoCell) :
    ((indexedBCDirectInterpretation presentation data).pathLift
        (G.twoLeft cell)).base =
      ((indexedBCDirectInterpretation presentation data).pathLift
        (G.twoRight cell)).base ∧
    (IndexedDiagnosticInterpretation.pathLift
          ((data.map (bcDiagnosticDirectFunctor presentation)).toIndexedInterpretation)
          (G.twoLeft cell)).base =
        (IndexedDiagnosticInterpretation.pathLift
          ((data.map (bcDiagnosticDirectFunctor presentation)).toIndexedInterpretation)
          (G.twoRight cell)).base :=
  ⟨(indexedBCDirectInterpretation presentation data).twoCellBase cell,
    IndexedDiagnosticInterpretation.twoCellBase
      ((data.map (bcDiagnosticDirectFunctor presentation)).toIndexedInterpretation)
      cell⟩

/-- C1 records the indexed and G-110 via-base two-cell equations generated from
the same constant target relation. -/
theorem indexedBCViaBase_twoCellBase_pair
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (presentation : BCPresentation U)
    (data : FiberwiseAdmissibleTransportData G.toFiniteTransportPresentation U
      presentation.1.cospan.firstSource.toSemantic) (cell : G.TwoCell) :
    ((indexedBCViaBaseInterpretation presentation data).pathLift
        (G.twoLeft cell)).base =
      ((indexedBCViaBaseInterpretation presentation data).pathLift
        (G.twoRight cell)).base ∧
    (IndexedDiagnosticInterpretation.pathLift
          ((data.map (bcDiagnosticViaBaseFunctor presentation)).toIndexedInterpretation)
          (G.twoLeft cell)).base =
        (IndexedDiagnosticInterpretation.pathLift
          ((data.map (bcDiagnosticViaBaseFunctor presentation)).toIndexedInterpretation)
          (G.twoRight cell)).base :=
  ⟨(indexedBCViaBaseInterpretation presentation data).twoCellBase cell,
    IndexedDiagnosticInterpretation.twoCellBase
      ((data.map (bcDiagnosticViaBaseFunctor presentation)).toIndexedInterpretation)
      cell⟩

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
    (𝟙 ((indexedBCRestrictionDirectFunctor presentation).obj package)) ≫
        (coreBeckChevalleyMate presentation).app package =
      (indexedBCRestrictionMate presentation).app package ≫
        𝟙 ((indexedBCRestrictionViaBaseFunctor presentation).obj package) := by
  simp only [Category.id_comp, Category.comp_id]
  exact congrArg (fun transformation => transformation.app package)
    (indexedBCRestrictionMate_eq_g110 presentation).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
