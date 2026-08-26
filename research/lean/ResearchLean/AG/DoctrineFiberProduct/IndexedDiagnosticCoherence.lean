import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticReselection

/-!
# Indexed diagnostic coherence covariance

This module proves G-111 `(d5)`.  Reselected edges and paths are evaluated in
their native vertex-indexed packages.  The canonical vertex lifts intertwine
each source reselected edge with the generated target reselected edge; path
induction then transports the authored two-cell coherence equation.

No common source fiber, target coherence certificate, or target vanishing
certificate is accepted as input.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- The underlying fiber morphism of the generated endpoint action. -/
private theorem mappedPackageFiberAut_hom
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (F : CategoryTheory.Functor (CoreFiber X) (CoreFiber Y))
    (P : CoreFiber X)
    (automorphism : PackageFiberAut P.1) :
    (packageFiberAutCoreFiberEquiv (F.obj P)
      (coreFiberFunctorPackageAutHom F P automorphism)).hom =
      F.map (packageFiberAutCoreFiberEquiv P automorphism).hom := by
  change
    ((packageFiberAutCoreFiberEquiv (F.obj P))
      ((packageFiberAutCoreFiberEquiv (F.obj P)).symm
        ((F.mapAut P) ((packageFiberAutCoreFiberEquiv P) automorphism)))).hom =
      F.map ((packageFiberAutCoreFiberEquiv P) automorphism).hom
  have equality := (packageFiberAutCoreFiberEquiv (F.obj P)).apply_symm_apply
    ((F.mapAut P) ((packageFiberAutCoreFiberEquiv P) automorphism))
  exact congrArg Iso.hom equality

/-- Forgetting the fiber tag recovers the package-total automorphism morphism. -/
private theorem packageFiberAutCoreFiberEquiv_hom_value
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : CoreFiber X) (automorphism : PackageFiberAut P.1) :
    ((packageFiberAutCoreFiberEquiv P) automorphism).hom.1 =
      PackageFiberAut.hom automorphism := by
  rcases P with ⟨P, rfl⟩
  rfl

/-- Package-total composition in the ambient category is associative. -/
private theorem packageTotalHom_comp_assoc
    {U : AtomCarrier.{u}} {P Q R S : AATCorePackage U}
    (first : PackageTotalHom P Q) (second : PackageTotalHom Q R)
    (third : PackageTotalHom R S) :
    first.comp (second.comp third) = (first.comp second).comp third := by
  let packageCategory : Category (AATCorePackage U) := inferInstance
  exact (@Category.assoc (AATCorePackage U) packageCategory
    P Q R S first second third).symm

namespace IndexedDiagnosticInterpretation

/-- Apply one authored endpoint reselection after a generating edge lift. -/
def reselectedEdgeLift {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (edge : G.Edge i j) :
    PackageTotalHom (source.package i) (source.package j) :=
  (source.edgeLift edge).comp
    (PackageFiberAut.hom (reselection i j edge))

/-- Evaluate the reselected source lifts along a finite indexed base path. -/
def reselectedPathLift {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) :
    {i j : G.Vertex} → IndexedBasePath G.toIndexedBaseShape i j →
      PackageTotalHom (source.package i) (source.package j)
  | _, _, .nil vertex => PackageTotalHom.id (source.package vertex)
  | _, _, .cons edge tail =>
      (source.reselectedEdgeLift reselection edge).comp
        (source.reselectedPathLift reselection tail)

/-- A reselected generating edge remains over its fixed indexed base edge. -/
theorem reselectedEdgeLift_isHomLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (edge : G.Edge i j) :
    (packageProjection U).IsHomLift (D.edge edge)
      (source.reselectedEdgeLift reselection edge) := by
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection U) (D.edge edge)
    (source.reselectedEdgeLift reselection edge)
    (source.vertexBase i) (source.vertexBase j)
  change
    ((source.edgeLift edge).base ≫
        (PackageFiberAut.hom (reselection i j edge)).base) ≫
          eqToHom (source.vertexBase j) =
      eqToHom (source.vertexBase i) ≫ D.edge edge
  rw [PackageFiberAut.hom_base_eq, Category.comp_id]
  letI : (packageProjection U).IsHomLift
      (D.edge edge) (source.edgeLift edge) := source.edgeOver edge
  have fac := CategoryTheory.IsHomLift.fac'
    (packageProjection U) (D.edge edge) (source.edgeLift edge)
  calc
    (source.edgeLift edge).base ≫ eqToHom (source.vertexBase j) =
        (eqToHom (source.vertexBase i) ≫ D.edge edge ≫
          eqToHom (source.vertexBase j).symm) ≫
            eqToHom (source.vertexBase j) := congrArg
              (fun base => base ≫ eqToHom (source.vertexBase j)) fac
    _ = eqToHom (source.vertexBase i) ≫ D.edge edge := by simp

/-- Every reselected source path remains over the corresponding fixed path. -/
theorem reselectedPathLift_isHomLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (packageProjection U).IsHomLift (D.path path)
      (source.reselectedPathLift reselection path) := by
  induction path with
  | nil vertex =>
      apply CategoryTheory.IsHomLift.of_commsq
        (packageProjection U) (𝟙 (D.vertex vertex))
        (PackageTotalHom.id (source.package vertex))
        (source.vertexBase vertex) (source.vertexBase vertex)
      change (𝟙 _) ≫ eqToHom (source.vertexBase vertex) =
        eqToHom (source.vertexBase vertex) ≫ 𝟙 _
      simp
  | cons edge tail inductionHypothesis =>
      letI : (packageProjection U).IsHomLift
          (D.edge edge) (source.reselectedEdgeLift reselection edge) :=
        source.reselectedEdgeLift_isHomLift reselection edge
      letI : (packageProjection U).IsHomLift
          (D.path tail) (source.reselectedPathLift reselection tail) :=
        inductionHypothesis
      exact CategoryTheory.IsHomLift.comp
        (p := packageProjection U) (D.edge edge) (D.path tail)
        (source.reselectedEdgeLift reselection edge)
        (source.reselectedPathLift reselection tail)

/-- The actual authored two-cell equation at one indexed reselection. -/
def IndexedCoherentAt
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D : IndexedBaseDiagram G U} (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) : Prop :=
  ∀ cell : G.TwoCell,
    (source.reselectedPathLift reselection (G.twoLeft cell)).comp
        (PackageFiberAut.hom (source.comparator cell)) =
      source.reselectedPathLift reselection (G.twoRight cell)

end IndexedDiagnosticInterpretation

namespace IndexedBaseDiagramHom

/-- The canonical source-to-target lift at one indexed diagnostic vertex. -/
noncomputable def diagnosticVertexLift
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageTotalHom (source.package vertex)
      ((hom.transportedInterpretation source).package vertex) :=
  indexedTotalLift (hom.vertexIndex vertex) (source.fiberPackage vertex)

/-- A vertex lift is the canonical strongly cocartesian indexed lift. -/
theorem diagnosticVertexLift_isStronglyCocartesian
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    (packageProjection U).IsStronglyCocartesian (hom.app vertex)
      (hom.diagnosticVertexLift source vertex) :=
  indexedTotalLift_isStronglyCocartesian
    (hom.vertexIndex vertex) (source.fiberPackage vertex)

/-- A canonical vertex lift intertwines every endpoint automorphism and its action. -/
theorem diagnosticVertexLift_endpointAction_naturality
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (automorphism : PackageFiberAut (source.package vertex)) :
    (hom.diagnosticVertexLift source vertex).comp
        (PackageFiberAut.hom
          (hom.endpointAction source vertex automorphism)) =
      (PackageFiberAut.hom automorphism).comp
        (hom.diagnosticVertexLift source vertex) := by
  let P := source.fiberPackage vertex
  let F := indexedFiberAction (hom.vertexIndex vertex)
  let fiberAut := packageFiberAutCoreFiberEquiv P automorphism
  change
    indexedTotalLift (hom.vertexIndex vertex) P ≫
        PackageFiberAut.hom
          (coreFiberFunctorPackageAutHom F P automorphism) =
      PackageFiberAut.hom automorphism ≫
        indexedTotalLift (hom.vertexIndex vertex) P
  calc
    _ = indexedTotalLift (hom.vertexIndex vertex) P ≫
          (packageFiberAutCoreFiberEquiv (F.obj P)
            (coreFiberFunctorPackageAutHom F P automorphism)).hom.1 := by
          rw [packageFiberAutCoreFiberEquiv_hom_value]
    _ = indexedTotalLift (hom.vertexIndex vertex) P ≫
          (F.map fiberAut.hom).1 := by
          rw [mappedPackageFiberAut_hom]
    _ = fiberAut.hom.1 ≫
          indexedTotalLift (hom.vertexIndex vertex) P :=
        indexedUniversalEdgeLaw (hom.vertexIndex vertex) fiberAut.hom
    _ = _ := by rw [packageFiberAutCoreFiberEquiv_hom_value]

/-- The canonical vertex lifts intertwine one source and target reselected edge. -/
theorem diagnosticVertexLift_reselectedEdge_naturality
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (edge : G.Edge i j) :
    (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedEdgeLift
          (hom.transportedReselection source reselection) edge) =
      (source.reselectedEdgeLift reselection edge).comp
        (hom.diagnosticVertexLift source j) := by
  change
    indexedTotalLift (hom.vertexIndex i) (source.fiberPackage i) ≫
        (indexedSquareTotalMap (hom.validatedEdgeSquare edge)
          (source.fiberPackage i) (source.fiberPackage j)
          (source.edgeLift edge) (source.edgeOver edge) ≫
          PackageFiberAut.hom
            (hom.endpointAction source j (reselection i j edge))) =
      (source.edgeLift edge ≫
          PackageFiberAut.hom (reselection i j edge)) ≫
        indexedTotalLift (hom.vertexIndex j) (source.fiberPackage j)
  have edgeSquareLaw :
      indexedTotalLift (hom.vertexIndex i) (source.fiberPackage i) ≫
          indexedSquareTotalMap (hom.validatedEdgeSquare edge)
            (source.fiberPackage i) (source.fiberPackage j)
            (source.edgeLift edge) (source.edgeOver edge) =
        source.edgeLift edge ≫
          indexedTotalLift (hom.vertexIndex j) (source.fiberPackage j) := by
    simpa only [indexedTotalLift] using
      (indexedUniversalSquareEdgeLaw (hom.validatedEdgeSquare edge)
        (source.fiberPackage i) (source.fiberPackage j)
        (source.edgeLift edge) (source.edgeOver edge))
  have endpointNaturality :
    PackageFiberAut.hom (reselection i j edge) ≫
        indexedTotalLift (hom.vertexIndex j) (source.fiberPackage j) =
      indexedTotalLift (hom.vertexIndex j) (source.fiberPackage j) ≫
        PackageFiberAut.hom (hom.endpointAction source j
          (reselection i j edge)) := by
    exact (hom.diagnosticVertexLift_endpointAction_naturality source j
      (reselection i j edge)).symm
  calc
    _ = (indexedTotalLift (hom.vertexIndex i) (source.fiberPackage i) ≫
          indexedSquareTotalMap (hom.validatedEdgeSquare edge)
            (source.fiberPackage i) (source.fiberPackage j)
            (source.edgeLift edge) (source.edgeOver edge)) ≫
          PackageFiberAut.hom
            (hom.endpointAction source j (reselection i j edge)) := by
          rw [Category.assoc]
    _ = (source.edgeLift edge ≫
          indexedTotalLift (hom.vertexIndex j) (source.fiberPackage j)) ≫
          PackageFiberAut.hom
            (hom.endpointAction source j (reselection i j edge)) := by
          rw [edgeSquareLaw]
    _ = source.edgeLift edge ≫
          (PackageFiberAut.hom (reselection i j edge) ≫
            indexedTotalLift (hom.vertexIndex j) (source.fiberPackage j)) := by
          rw [Category.assoc, endpointNaturality]
    _ = _ := by rw [← Category.assoc]

/-- Vertex-lift naturality extends from generating edges to every finite path. -/
theorem diagnosticVertexLift_reselectedPath_naturality
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source) {i j : G.Vertex}
    (path : IndexedBasePath G.toIndexedBaseShape i j) :
    (hom.diagnosticVertexLift source i).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (hom.transportedReselection source reselection) path) =
      (source.reselectedPathLift reselection path).comp
        (hom.diagnosticVertexLift source j) := by
  induction path with
  | nil vertex =>
      change
        (hom.diagnosticVertexLift source vertex) ≫
            𝟙 ((hom.transportedInterpretation source).package vertex) =
          𝟙 (source.package vertex) ≫
            hom.diagnosticVertexLift source vertex
      simp
  | cons edge tail inductionHypothesis =>
      calc
        _ = ((hom.diagnosticVertexLift source _).comp
              ((hom.transportedInterpretation source).reselectedEdgeLift
                (hom.transportedReselection source reselection) edge)).comp
              ((hom.transportedInterpretation source).reselectedPathLift
                (hom.transportedReselection source reselection) tail) :=
            packageTotalHom_comp_assoc _ _ _
        _ = ((source.reselectedEdgeLift reselection edge).comp
              (hom.diagnosticVertexLift source _)).comp
              ((hom.transportedInterpretation source).reselectedPathLift
                (hom.transportedReselection source reselection) tail) := by
            rw [hom.diagnosticVertexLift_reselectedEdge_naturality
              source reselection edge]
        _ = (source.reselectedEdgeLift reselection edge).comp
              ((hom.diagnosticVertexLift source _).comp
                ((hom.transportedInterpretation source).reselectedPathLift
                  (hom.transportedReselection source reselection) tail)) :=
            (packageTotalHom_comp_assoc _ _ _).symm
        _ = (source.reselectedEdgeLift reselection edge).comp
              ((source.reselectedPathLift reselection tail).comp
                (hom.diagnosticVertexLift source _)) := by
            rw [inductionHypothesis]
        _ = _ := by
            simpa only [IndexedDiagnosticInterpretation.reselectedPathLift] using
              packageTotalHom_comp_assoc
                (source.reselectedEdgeLift reselection edge)
                (source.reselectedPathLift reselection tail)
                (hom.diagnosticVertexLift source _)

/-- Canonical vertex lifts intertwine source and generated target comparators. -/
theorem diagnosticVertexLift_comparator_naturality
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (cell : G.TwoCell) :
    (hom.diagnosticVertexLift source (G.twoTarget cell)).comp
        (PackageFiberAut.hom
          ((hom.transportedInterpretation source).comparator cell)) =
      (PackageFiberAut.hom (source.comparator cell)).comp
        (hom.diagnosticVertexLift source (G.twoTarget cell)) := by
  exact hom.diagnosticVertexLift_endpointAction_naturality source
    (G.twoTarget cell) (source.comparator cell)

/-- `(d5)`: every coherent source reselection generates a coherent target reselection. -/
theorem indexedCoherentAt_transport
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source)
    (coherent : source.IndexedCoherentAt reselection) :
    (hom.transportedInterpretation source).IndexedCoherentAt
      (hom.transportedReselection source reselection) := by
  intro cell
  let vertexLift := hom.diagnosticVertexLift source (G.twoSource cell)
  let targetLeft :=
    ((hom.transportedInterpretation source).reselectedPathLift
      (hom.transportedReselection source reselection) (G.twoLeft cell)).comp
        (PackageFiberAut.hom
          ((hom.transportedInterpretation source).comparator cell))
  let targetRight :=
    (hom.transportedInterpretation source).reselectedPathLift
      (hom.transportedReselection source reselection) (G.twoRight cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (hom.app (G.twoSource cell)) vertexLift :=
    hom.diagnosticVertexLift_isStronglyCocartesian source _
  letI : (packageProjection U).IsHomLift
      (E.path (G.twoLeft cell))
      ((hom.transportedInterpretation source).reselectedPathLift
        (hom.transportedReselection source reselection) (G.twoLeft cell)) :=
    (hom.transportedInterpretation source).reselectedPathLift_isHomLift _ _
  letI : (packageProjection U).IsHomLift
      (𝟙 (E.vertex (G.twoTarget cell)))
      (PackageFiberAut.hom
        ((hom.transportedInterpretation source).comparator cell)) := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (𝟙 (E.vertex (G.twoTarget cell)))
      (PackageFiberAut.hom
        ((hom.transportedInterpretation source).comparator cell))
      ((hom.transportedInterpretation source).vertexBase (G.twoTarget cell))
      ((hom.transportedInterpretation source).vertexBase (G.twoTarget cell))
    rw [packageProjection_map, PackageFiberAut.hom_base_eq]
    rw [Category.comp_id]
    exact Category.id_comp _
  letI : (packageProjection U).IsHomLift
      (E.path (G.twoLeft cell)) targetLeft := by
    have composite : (packageProjection U).IsHomLift
        (E.path (G.twoLeft cell) ≫ 𝟙 (E.vertex (G.twoTarget cell)))
        targetLeft := CategoryTheory.IsHomLift.comp
          (packageProjection U) (E.path (G.twoLeft cell))
          (𝟙 (E.vertex (G.twoTarget cell)))
          ((hom.transportedInterpretation source).reselectedPathLift
            (hom.transportedReselection source reselection) (G.twoLeft cell))
          (PackageFiberAut.hom
            ((hom.transportedInterpretation source).comparator cell))
    simpa using composite
  letI : (packageProjection U).IsHomLift
      (E.path (G.twoLeft cell)) targetRight := by
    rw [E.relation_path cell]
    exact (hom.transportedInterpretation source).reselectedPathLift_isHomLift _ _
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (hom.app (G.twoSource cell)) vertexLift
    (E.path (G.twoLeft cell))
  dsimp only [vertexLift, targetLeft, targetRight]
  calc
    _ = ((hom.diagnosticVertexLift source (G.twoSource cell)).comp
          ((hom.transportedInterpretation source).reselectedPathLift
            (hom.transportedReselection source reselection)
            (G.twoLeft cell))).comp
          (PackageFiberAut.hom
            ((hom.transportedInterpretation source).comparator cell)) :=
        packageTotalHom_comp_assoc _ _ _
    _ = ((source.reselectedPathLift reselection (G.twoLeft cell)).comp
          (hom.diagnosticVertexLift source (G.twoTarget cell))).comp
          (PackageFiberAut.hom
            ((hom.transportedInterpretation source).comparator cell)) := by
        rw [hom.diagnosticVertexLift_reselectedPath_naturality source reselection
          (G.twoLeft cell)]
    _ = (source.reselectedPathLift reselection (G.twoLeft cell)).comp
          ((hom.diagnosticVertexLift source (G.twoTarget cell)).comp
            (PackageFiberAut.hom
              ((hom.transportedInterpretation source).comparator cell))) :=
        (packageTotalHom_comp_assoc _ _ _).symm
    _ = (source.reselectedPathLift reselection (G.twoLeft cell)).comp
          ((PackageFiberAut.hom (source.comparator cell)).comp
            (hom.diagnosticVertexLift source (G.twoTarget cell))) := by
        rw [hom.diagnosticVertexLift_comparator_naturality source cell]
    _ = ((source.reselectedPathLift reselection (G.twoLeft cell)).comp
          (PackageFiberAut.hom (source.comparator cell))).comp
            (hom.diagnosticVertexLift source (G.twoTarget cell)) :=
        packageTotalHom_comp_assoc _ _ _
    _ = (source.reselectedPathLift reselection (G.twoRight cell)).comp
          (hom.diagnosticVertexLift source (G.twoTarget cell)) := by
        rw [coherent cell]
    _ = _ := (hom.diagnosticVertexLift_reselectedPath_naturality source
      reselection (G.twoRight cell)).symm

end IndexedBaseDiagramHom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
