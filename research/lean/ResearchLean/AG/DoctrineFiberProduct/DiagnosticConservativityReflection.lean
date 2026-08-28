import ResearchLean.AG.DoctrineFiberProduct.DiagnosticConservativityNormalization
import ResearchLean.AG.DoctrineFiberProduct.CartesianTransport

/-!
# Unconditional reflection of indexed diagnostic vanishing

Canonical package transport is simultaneously strongly cocartesian and
strongly cartesian. Cartesian factorization reflects every automorphism of a
transported endpoint package; cocartesian uniqueness shows that transporting
the reflected automorphism returns the original one. These two universal
properties reflect indexed coherence and hence obstruction vanishing along
every indexed diagram hom.

This is stronger than the first G-113 class candidate. In particular, it
rules out the fixed target's required class-exterior O16 counterexample.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Package-total composition in the ambient category is associative. -/
private theorem packageTotalHom_comp_assoc
    {U : AtomCarrier.{u}} {P Q R S : AATCorePackage U}
    (first : PackageTotalHom P Q) (second : PackageTotalHom Q R)
    (third : PackageTotalHom R S) :
    first.comp (second.comp third) = (first.comp second).comp third := by
  let packageCategory : Category (AATCorePackage U) := inferInstance
  exact (@Category.assoc (AATCorePackage U) packageCategory
    P Q R S first second third).symm

/-! ## Automorphism reflection for one generated fiber action -/

/-- The canonical indexed lift is strongly cartesian over its decoded base arrow. -/
theorem indexedTotalLift_isStronglyCartesian
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U X Y) (P : CoreFiber X) :
    (packageProjection U).IsStronglyCartesian term.decode
      (indexedTotalLift term P) := by
  let lift := indexedTotalLift term P
  letI : (packageProjection U).IsStronglyCartesian
      ((packageProjection U).map lift) lift := by
    change (packageProjection U).IsStronglyCartesian
      ((transportAlongHom P.1 (coreFiberBaseHom term.decode P).doctrineHom).base)
      (transportAlongHom P.1 (coreFiberBaseHom term.decode P).doctrineHom)
    exact transportAlongHom_isStronglyCartesian P.1
      (coreFiberBaseHom term.decode P).doctrineHom
  letI : (packageProjection U).IsHomLift term.decode lift := by
    letI : (packageProjection U).IsStronglyCocartesian term.decode lift :=
      indexedTotalLift_isStronglyCocartesian term P
    infer_instance
  exact stronglyCartesian_of_isHomLift_support
    (packageProjection U) term.decode lift

/-- Reflect a vertical target-fiber morphism through the canonical cartesian lift. -/
noncomputable def coreFiberTransportReflectMap
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U X Y) (P : CoreFiber X)
    (targetHom : (indexedFiberAction term).obj P ⟶
      (indexedFiberAction term).obj P) : P ⟶ P := by
  let lift := indexedTotalLift term P
  letI : (packageProjection U).IsStronglyCartesian term.decode lift :=
    indexedTotalLift_isStronglyCartesian term P
  letI : (packageProjection U).IsHomLift (𝟙 Y) targetHom.1 := targetHom.2
  letI : (packageProjection U).IsHomLift
      term.decode (lift ≫ targetHom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (term.decode ≫ 𝟙 Y) (lift ≫ targetHom.1))
  refine ⟨CategoryTheory.Functor.IsStronglyCartesian.map
      (packageProjection U) term.decode lift
      (g := 𝟙 X) (f' := term.decode)
      (Category.id_comp term.decode).symm
      (lift ≫ targetHom.1), ?_⟩
  infer_instance

/-- The reflected map followed by the lift is the target map after the lift. -/
theorem coreFiberTransportReflectMap_fac
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U X Y) (P : CoreFiber X)
    (targetHom : (indexedFiberAction term).obj P ⟶
      (indexedFiberAction term).obj P) :
    (coreFiberTransportReflectMap term P targetHom).1 ≫ indexedTotalLift term P =
      indexedTotalLift term P ≫ targetHom.1 := by
  let lift := indexedTotalLift term P
  letI : (packageProjection U).IsStronglyCartesian term.decode lift :=
    indexedTotalLift_isStronglyCartesian term P
  letI : (packageProjection U).IsHomLift (𝟙 Y) targetHom.1 := targetHom.2
  letI : (packageProjection U).IsHomLift
      term.decode (lift ≫ targetHom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (term.decode ≫ 𝟙 Y) (lift ≫ targetHom.1))
  unfold coreFiberTransportReflectMap
  dsimp only
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (packageProjection U) term.decode lift
    (Category.id_comp term.decode).symm
    (lift ≫ targetHom.1)

/-- Reflect an automorphism of a transported object to the source fiber. -/
noncomputable def coreFiberTransportReflectAut
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U X Y) (P : CoreFiber X)
    (targetAut : Aut ((indexedFiberAction term).obj P)) : Aut P where
  hom := coreFiberTransportReflectMap term P targetAut.hom
  inv := coreFiberTransportReflectMap term P targetAut.inv
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    let lift := indexedTotalLift term P
    letI : (packageProjection U).IsStronglyCartesian term.decode lift :=
      indexedTotalLift_isStronglyCartesian term P
    letI : (packageProjection U).IsHomLift
        (𝟙 X)
        ((coreFiberTransportReflectMap term P targetAut.hom).1 ≫
          (coreFiberTransportReflectMap term P targetAut.inv).1) := by
      simpa using
        (coreFiberTransportReflectMap term P targetAut.hom ≫
          coreFiberTransportReflectMap term P targetAut.inv).2
    letI : (packageProjection U).IsHomLift
        (𝟙 X) (𝟙 P : P ⟶ P).1 := (𝟙 P : P ⟶ P).2
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (packageProjection U) term.decode lift (𝟙 X)
    change
      ((coreFiberTransportReflectMap term P targetAut.hom).1 ≫
          (coreFiberTransportReflectMap term P targetAut.inv).1) ≫ lift =
        (𝟙 P : P ⟶ P).1 ≫ lift
    rw [Category.assoc, coreFiberTransportReflectMap_fac]
    rw [← Category.assoc, coreFiberTransportReflectMap_fac]
    have targetHomInv : targetAut.hom.1 ≫ targetAut.inv.1 =
        PackageTotalHom.id ((indexedFiberAction term).obj P).1 := by
      have equality := congrArg Subtype.val targetAut.hom_inv_id
      exact equality
    calc
      _ = indexedTotalLift term P ≫
          (targetAut.hom.1 ≫ targetAut.inv.1) := Category.assoc _ _ _
      _ = indexedTotalLift term P ≫
          PackageTotalHom.id ((indexedFiberAction term).obj P).1 := by
        rw [targetHomInv]
      _ = _ := (Category.comp_id _).trans (Category.id_comp _).symm
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    let lift := indexedTotalLift term P
    letI : (packageProjection U).IsStronglyCartesian term.decode lift :=
      indexedTotalLift_isStronglyCartesian term P
    letI : (packageProjection U).IsHomLift
        (𝟙 X)
        ((coreFiberTransportReflectMap term P targetAut.inv).1 ≫
          (coreFiberTransportReflectMap term P targetAut.hom).1) := by
      simpa using
        (coreFiberTransportReflectMap term P targetAut.inv ≫
          coreFiberTransportReflectMap term P targetAut.hom).2
    letI : (packageProjection U).IsHomLift
        (𝟙 X) (𝟙 P : P ⟶ P).1 := (𝟙 P : P ⟶ P).2
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (packageProjection U) term.decode lift (𝟙 X)
    change
      ((coreFiberTransportReflectMap term P targetAut.inv).1 ≫
          (coreFiberTransportReflectMap term P targetAut.hom).1) ≫ lift =
        (𝟙 P : P ⟶ P).1 ≫ lift
    rw [Category.assoc, coreFiberTransportReflectMap_fac]
    rw [← Category.assoc, coreFiberTransportReflectMap_fac]
    have targetInvHom : targetAut.inv.1 ≫ targetAut.hom.1 =
        PackageTotalHom.id ((indexedFiberAction term).obj P).1 := by
      have equality := congrArg Subtype.val targetAut.inv_hom_id
      exact equality
    calc
      _ = indexedTotalLift term P ≫
          (targetAut.inv.1 ≫ targetAut.hom.1) := Category.assoc _ _ _
      _ = indexedTotalLift term P ≫
          PackageTotalHom.id ((indexedFiberAction term).obj P).1 := by
        rw [targetInvHom]
      _ = _ := (Category.comp_id _).trans (Category.id_comp _).symm

/-- Transporting a reflected automorphism returns the target automorphism. -/
theorem coreFiberTransportMapAut_reflect
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (term : ValidatedIndexedBaseHom U X Y) (P : CoreFiber X)
    (targetAut : Aut ((indexedFiberAction term).obj P)) :
    (indexedFiberAction term).mapAut P
        (coreFiberTransportReflectAut term P targetAut) = targetAut := by
  apply Iso.ext
  apply CategoryTheory.Functor.Fiber.hom_ext
  let lift := indexedTotalLift term P
  letI : (packageProjection U).IsStronglyCocartesian term.decode lift :=
    indexedTotalLift_isStronglyCocartesian term P
  letI : (packageProjection U).IsHomLift
      (𝟙 Y)
      ((indexedFiberAction term).mapAut P
        (coreFiberTransportReflectAut term P targetAut)).hom.1 := by
    exact ((indexedFiberAction term).mapAut P
      (coreFiberTransportReflectAut term P targetAut)).hom.2
  letI : (packageProjection U).IsHomLift
      (𝟙 Y) targetAut.hom.1 := targetAut.hom.2
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) term.decode lift (𝟙 Y)
  change indexedTotalLift term P ≫
      ((indexedFiberAction term).map
        (coreFiberTransportReflectMap term P targetAut.hom)).1 =
    indexedTotalLift term P ≫ targetAut.hom.1
  rw [indexedUniversalEdgeLaw, coreFiberTransportReflectMap_fac]

namespace IndexedBaseDiagramHom

/-- The canonical diagnostic vertex lift is also strongly cartesian. -/
theorem diagnosticVertexLift_isStronglyCartesian
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    (packageProjection U).IsStronglyCartesian (hom.app vertex)
      (hom.diagnosticVertexLift source vertex) := by
  let lift := hom.diagnosticVertexLift source vertex
  letI : (packageProjection U).IsStronglyCartesian
      ((packageProjection U).map lift) lift := by
    change (packageProjection U).IsStronglyCartesian
      ((transportAlongHom (source.fiberPackage vertex).1
        (coreFiberBaseHom (hom.vertexIndex vertex).decode
          (source.fiberPackage vertex)).doctrineHom).base)
      (transportAlongHom (source.fiberPackage vertex).1
        (coreFiberBaseHom (hom.vertexIndex vertex).decode
          (source.fiberPackage vertex)).doctrineHom)
    exact transportAlongHom_isStronglyCartesian
      (source.fiberPackage vertex).1
      (coreFiberBaseHom (hom.vertexIndex vertex).decode
        (source.fiberPackage vertex)).doctrineHom
  letI : (packageProjection U).IsHomLift (hom.app vertex) lift := by
    letI : (packageProjection U).IsStronglyCocartesian
        (hom.app vertex) lift :=
      hom.diagnosticVertexLift_isStronglyCocartesian source vertex
    infer_instance
  exact stronglyCartesian_of_isHomLift_support
    (packageProjection U) (hom.app vertex) lift

/-- Reflect one target endpoint automorphism through its generated fiber action. -/
noncomputable def reflectedEndpointAut
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (targetAut : PackageFiberAut
      ((hom.transportedInterpretation source).package vertex)) :
    PackageFiberAut (source.package vertex) :=
  (packageFiberAutCoreFiberEquiv (source.fiberPackage vertex)).symm
    (coreFiberTransportReflectAut (hom.vertexIndex vertex)
      (source.fiberPackage vertex)
      (packageFiberAutCoreFiberEquiv
        ((hom.transportedInterpretation source).fiberPackage vertex)
        targetAut))

/-- Mapping a reflected endpoint automorphism recovers the target automorphism. -/
theorem endpointAction_reflectedEndpointAut
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (targetAut : PackageFiberAut
      ((hom.transportedInterpretation source).package vertex)) :
    hom.endpointAction source vertex
        (hom.reflectedEndpointAut source vertex targetAut) = targetAut := by
  unfold endpointAction reflectedEndpointAut coreFiberFunctorPackageAutHom
  dsimp only [MonoidHom.comp, Function.comp_apply]
  change
    (packageFiberAutCoreFiberEquiv
      ((hom.transportedInterpretation source).fiberPackage vertex)).symm
        ((indexedFiberAction (hom.vertexIndex vertex)).mapAut
          (source.fiberPackage vertex)
          (packageFiberAutCoreFiberEquiv (source.fiberPackage vertex)
            ((packageFiberAutCoreFiberEquiv
              (source.fiberPackage vertex)).symm
              (coreFiberTransportReflectAut (hom.vertexIndex vertex)
                (source.fiberPackage vertex)
                (packageFiberAutCoreFiberEquiv
                  ((hom.transportedInterpretation source).fiberPackage vertex)
                  targetAut))))) = targetAut
  rw [MulEquiv.apply_symm_apply]
  apply (packageFiberAutCoreFiberEquiv
    ((hom.transportedInterpretation source).fiberPackage vertex)).injective
  rw [MulEquiv.apply_symm_apply]
  simpa using
      coreFiberTransportMapAut_reflect (hom.vertexIndex vertex)
        (source.fiberPackage vertex)
        (packageFiberAutCoreFiberEquiv
          ((hom.transportedInterpretation source).fiberPackage vertex) targetAut)

/-- The generated endpoint action is surjective at every vertex. -/
theorem endpointAction_surjective
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    Function.Surjective (hom.endpointAction source vertex) := by
  intro targetAut
  exact ⟨hom.reflectedEndpointAut source vertex targetAut,
    hom.endpointAction_reflectedEndpointAut source vertex targetAut⟩

/-- Reflect a target edge reselection pointwise through endpoint actions. -/
noncomputable def reflectedReselection
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) :
    IndexedEdgeReselection source :=
  fun i j edge => hom.reflectedEndpointAut source j
    (targetReselection i j edge)

/-- Mapping the reflected reselection recovers the target reselection. -/
theorem transportedReselection_reflectedReselection
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (targetReselection : IndexedEdgeReselection
      (hom.transportedInterpretation source)) :
    hom.transportedReselection source
        (hom.reflectedReselection source targetReselection) =
      targetReselection := by
  funext i j edge
  exact hom.endpointAction_reflectedEndpointAut source j
    (targetReselection i j edge)

/-- Coherence of a mapped reselection reflects through cartesian vertex lifts. -/
theorem indexedCoherentAt_reflect
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (reselection : IndexedEdgeReselection source)
    (coherent : (hom.transportedInterpretation source).IndexedCoherentAt
      (hom.transportedReselection source reselection)) :
    source.IndexedCoherentAt reselection := by
  intro cell
  let lift := hom.diagnosticVertexLift source (G.twoTarget cell)
  let sourceLeft :=
    (source.reselectedPathLift reselection (G.twoLeft cell)).comp
      (PackageFiberAut.hom (source.comparator cell))
  let sourceRight := source.reselectedPathLift reselection (G.twoRight cell)
  letI : (packageProjection U).IsStronglyCartesian
      (hom.app (G.twoTarget cell)) lift :=
    hom.diagnosticVertexLift_isStronglyCartesian source _
  letI : (packageProjection U).IsHomLift
      (D.path (G.twoLeft cell)) sourceLeft := by
    dsimp only [sourceLeft]
    letI : (packageProjection U).IsHomLift
        (D.path (G.twoLeft cell))
        (source.reselectedPathLift reselection (G.twoLeft cell)) :=
      source.reselectedPathLift_isHomLift reselection (G.twoLeft cell)
    letI : (packageProjection U).IsHomLift
        (𝟙 (D.vertex (G.twoTarget cell)))
        (PackageFiberAut.hom (source.comparator cell)) := by
      apply CategoryTheory.IsHomLift.of_commsq
        (packageProjection U) (𝟙 (D.vertex (G.twoTarget cell)))
        (PackageFiberAut.hom (source.comparator cell))
        (source.vertexBase (G.twoTarget cell))
        (source.vertexBase (G.twoTarget cell))
      rw [packageProjection_map, PackageFiberAut.hom_base_eq]
      rw [Category.comp_id]
      exact Category.id_comp _
    have composite : (packageProjection U).IsHomLift
        (D.path (G.twoLeft cell) ≫ 𝟙 (D.vertex (G.twoTarget cell)))
        sourceLeft := CategoryTheory.IsHomLift.comp
      (packageProjection U) (D.path (G.twoLeft cell))
      (𝟙 (D.vertex (G.twoTarget cell)))
      (source.reselectedPathLift reselection (G.twoLeft cell))
      (PackageFiberAut.hom (source.comparator cell))
    simpa using composite
  letI : (packageProjection U).IsHomLift
      (D.path (G.twoLeft cell)) sourceRight := by
    rw [D.relation_path cell]
    exact source.reselectedPathLift_isHomLift reselection (G.twoRight cell)
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) (hom.app (G.twoTarget cell)) lift
    (D.path (G.twoLeft cell))
  dsimp only [sourceLeft, sourceRight, lift]
  calc
    _ = (source.reselectedPathLift reselection (G.twoLeft cell)).comp
        ((PackageFiberAut.hom (source.comparator cell)).comp
          (hom.diagnosticVertexLift source (G.twoTarget cell))) :=
      (packageTotalHom_comp_assoc _ _ _).symm
    _ = (source.reselectedPathLift reselection (G.twoLeft cell)).comp
        ((hom.diagnosticVertexLift source (G.twoTarget cell)).comp
          (PackageFiberAut.hom
            ((hom.transportedInterpretation source).comparator cell))) := by
      rw [hom.diagnosticVertexLift_comparator_naturality source cell]
    _ = ((source.reselectedPathLift reselection (G.twoLeft cell)).comp
          (hom.diagnosticVertexLift source (G.twoTarget cell))).comp
        (PackageFiberAut.hom
          ((hom.transportedInterpretation source).comparator cell)) :=
      packageTotalHom_comp_assoc _ _ _
    _ = ((hom.diagnosticVertexLift source (G.twoSource cell)).comp
          ((hom.transportedInterpretation source).reselectedPathLift
            (hom.transportedReselection source reselection)
            (G.twoLeft cell))).comp
        (PackageFiberAut.hom
          ((hom.transportedInterpretation source).comparator cell)) := by
      rw [hom.diagnosticVertexLift_reselectedPath_naturality source reselection
        (G.twoLeft cell)]
    _ = (hom.diagnosticVertexLift source (G.twoSource cell)).comp
        (((hom.transportedInterpretation source).reselectedPathLift
            (hom.transportedReselection source reselection)
            (G.twoLeft cell)).comp
          (PackageFiberAut.hom
            ((hom.transportedInterpretation source).comparator cell))) :=
      (packageTotalHom_comp_assoc _ _ _).symm
    _ = (hom.diagnosticVertexLift source (G.twoSource cell)).comp
        ((hom.transportedInterpretation source).reselectedPathLift
          (hom.transportedReselection source reselection)
          (G.twoRight cell)) := by rw [coherent cell]
    _ = _ := hom.diagnosticVertexLift_reselectedPath_naturality
      source reselection (G.twoRight cell)

/-- Indexed obstruction vanishing reflects along every diagram hom. -/
theorem indexedTransportObstructionVanishes_reflect
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D)
    (vanishes : TransportObstructionVanishes
      (hom.transportedInterpretation source).toAdmissibleTransportData) :
    TransportObstructionVanishes source.toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable] at vanishes ⊢
  rcases vanishes with ⟨targetReselection, targetCoherent⟩
  let sourceReselection := hom.reflectedReselection source targetReselection
  have mapped : hom.transportedReselection source sourceReselection =
      targetReselection :=
    hom.transportedReselection_reflectedReselection source targetReselection
  have targetIndexed :
      (hom.transportedInterpretation source).IndexedCoherentAt
        (hom.transportedReselection source sourceReselection) := by
    rw [mapped]
    exact (IndexedDiagnosticInterpretation.indexedCoherentAt_iff_adaptedCoherentAt
      (hom.transportedInterpretation source) targetReselection).2 targetCoherent
  exact ⟨sourceReselection,
    (source.indexedCoherentAt_iff_adaptedCoherentAt sourceReselection).1
      (hom.indexedCoherentAt_reflect source sourceReselection targetIndexed)⟩

end IndexedBaseDiagramHom

/-- Diagnostic conservativity holds for every indexed diagram hom. -/
theorem diagnosticConservative_all
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    DiagnosticConservative hom := by
  intro source targetVanishes
  exact hom.indexedTransportObstructionVanishes_reflect source targetVanishes

/-- Hence no target-vanishing/source-nonvanishing counterexample exists. -/
theorem no_diagnosticConservativityCounterexample
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E) :
    ¬ ∃ source : IndexedDiagnosticInterpretation D,
      TransportObstructionVanishes
          (hom.transportedInterpretation source).toAdmissibleTransportData ∧
        ¬ TransportObstructionVanishes source.toAdmissibleTransportData := by
  rintro ⟨source, targetVanishes, sourceDoesNotVanish⟩
  exact sourceDoesNotVanish
    (diagnosticConservative_all hom source targetVanishes)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
