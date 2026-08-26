import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticVanishing
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticCovarianceWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPairwiseAxisFoldWitnesses

/-!
# Named nontrivial witness for indexed diagnostic covariance

This module supplies the G-111 diagnostic witness portfolio.  The named cell
`indexedCovarianceFace` fills two syntactically distinct parallel edges in a
connected two-vertex diagram.  Its authored comparator, initial raw defect,
source reselection, participating Atom transport, and generated target endpoint
image are all nonidentity.  The generated package family differs concretely
from the identity-action image on `componentC`.
The same source reselection is coherent, and the Cycle 14 `(d5)` and `(d6)`
theorems fire on its generated image.

This witness is independent of the non-epi coherent positive required by K5;
its participating index is the finite nonidentity Atom transport and no non-epi
causality is claimed.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- Vertex labels of the named indexed covariance disk. -/
abbrev IndexedCovarianceVertex := SingleDiskVertex FiniteModel.carrier.Atom

/-- Generating edges of the named indexed covariance disk. -/
abbrev IndexedCovarianceEdge := @SingleDiskEdge FiniteModel.carrier.Atom

/-- Declared cells of the named indexed covariance disk. -/
abbrev IndexedCovarianceCell := SingleDiskTwoCell FiniteModel.carrier.Atom

/-- The finite 0/1/2-cell skeleton of the named indexed covariance disk. -/
noncomputable abbrev indexedCovarianceBaseShape : IndexedBaseShape.{0} where
  Vertex := IndexedCovarianceVertex
  vertexFintype := inferInstance
  Edge := IndexedCovarianceEdge
  edgeFintype := fun _ _ => Fintype.ofFinite _
  TwoCell := IndexedCovarianceCell
  twoCellFintype := inferInstance
  twoSource := fun _ => SingleDiskVertex.source
  twoTarget := fun _ => SingleDiskVertex.target

/-- The finite indexed disk with two parallel edges and one named face. -/
noncomputable abbrev indexedCovarianceShape : IndexedBaseTwoShape.{0} where
  toIndexedBaseShape := indexedCovarianceBaseShape
  twoLeft := by
    intro cell
    change IndexedCovarianceCell at cell
    cases cell
    change IndexedBasePath indexedCovarianceBaseShape
      (SingleDiskVertex.source : IndexedCovarianceVertex)
      (SingleDiskVertex.target : IndexedCovarianceVertex)
    exact @IndexedBasePath.cons indexedCovarianceBaseShape
      (SingleDiskVertex.source : IndexedCovarianceVertex)
      (SingleDiskVertex.target : IndexedCovarianceVertex)
      (SingleDiskVertex.target : IndexedCovarianceVertex)
      (@SingleDiskEdge.left FiniteModel.carrier.Atom)
      (@IndexedBasePath.nil indexedCovarianceBaseShape
        (SingleDiskVertex.target : IndexedCovarianceVertex))
  twoRight := by
    intro cell
    change IndexedCovarianceCell at cell
    cases cell
    change IndexedBasePath indexedCovarianceBaseShape
      (SingleDiskVertex.source : IndexedCovarianceVertex)
      (SingleDiskVertex.target : IndexedCovarianceVertex)
    exact @IndexedBasePath.cons indexedCovarianceBaseShape
      (SingleDiskVertex.source : IndexedCovarianceVertex)
      (SingleDiskVertex.target : IndexedCovarianceVertex)
      (SingleDiskVertex.target : IndexedCovarianceVertex)
      (@SingleDiskEdge.right FiniteModel.carrier.Atom)
      (@IndexedBasePath.nil indexedCovarianceBaseShape
        (SingleDiskVertex.target : IndexedCovarianceVertex))

/-- Source vertex of the named indexed covariance disk. -/
def indexedCovarianceSourceVertex : indexedCovarianceShape.Vertex := by
  change IndexedCovarianceVertex
  exact .source

/-- Target vertex of the named indexed covariance disk. -/
def indexedCovarianceTargetVertex : indexedCovarianceShape.Vertex := by
  change IndexedCovarianceVertex
  exact .target

/-- Left generating edge of the named indexed covariance disk. -/
def indexedCovarianceLeftEdge :
    indexedCovarianceShape.Edge indexedCovarianceSourceVertex
      indexedCovarianceTargetVertex := by
  change IndexedCovarianceEdge .source .target
  exact .left

/-- Right generating edge of the named indexed covariance disk. -/
def indexedCovarianceRightEdge :
    indexedCovarianceShape.Edge indexedCovarianceSourceVertex
      indexedCovarianceTargetVertex := by
  change IndexedCovarianceEdge .source .target
  exact .right

/-- The named declared face of the indexed covariance disk. -/
def indexedCovarianceFace : indexedCovarianceShape.TwoCell := by
  change IndexedCovarianceCell
  exact .face

/-- The left boundary path of the named indexed face. -/
def indexedCovarianceLeftPath :
    IndexedBasePath indexedCovarianceShape.toIndexedBaseShape
      indexedCovarianceSourceVertex indexedCovarianceTargetVertex :=
  .cons indexedCovarianceLeftEdge (.nil indexedCovarianceTargetVertex)

/-- The right boundary path of the named indexed face. -/
def indexedCovarianceRightPath :
    IndexedBasePath indexedCovarianceShape.toIndexedBaseShape
      indexedCovarianceSourceVertex indexedCovarianceTargetVertex :=
  .cons indexedCovarianceRightEdge (.nil indexedCovarianceTargetVertex)

/-- The two authored boundary paths are syntactically distinct. -/
theorem indexedCovariance_paths_ne :
    indexedCovarianceLeftPath ≠ indexedCovarianceRightPath := by
  intro equality
  cases equality

/-- A three-axis permutation on the source package of the participating action. -/
noncomputable def indexedCovarianceSourcePermutationUpper
    (permutation : Equiv.Perm (Fin 3)) :
    SignedExactCoreReadingHom finiteWitnessSourcePackage
      finiteWitnessSourcePackage :=
  { SignedExactCoreReadingHom.refl finiteWitnessSourcePackage with
    axisMap := by
      change Fin 3 → Fin 3
      exact permutation.toFun
    coordinateEquiv := by
      intro axis
      change Fin 3 ≃ Fin 3
      exact permutation
    axis_selected_iff := fun _ => Iff.rfl
    coordinate_eq := by intro object axis; rfl }

/-- A source-axis permutation as a total endomorphism over identity. -/
noncomputable def indexedCovarianceSourcePermutationTotal
    (permutation : Equiv.Perm (Fin 3)) :
    PackageTotalHom finiteWitnessSourcePackage finiteWitnessSourcePackage where
  base := ExtInstHom.id (packagePoint finiteWitnessSourcePackage)
  upper := indexedCovarianceSourcePermutationUpper permutation
  atomEquiv_eq := rfl

/-- Source total-morphism composition follows permutation composition. -/
theorem indexedCovarianceSourcePermutationTotal_comp
    (first second : Equiv.Perm (Fin 3)) :
    (indexedCovarianceSourcePermutationTotal first).comp
        (indexedCovarianceSourcePermutationTotal second) =
      indexedCovarianceSourcePermutationTotal (first.trans second) := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

/-- The identity source-axis permutation is the package identity. -/
theorem indexedCovarianceSourcePermutationTotal_refl :
    indexedCovarianceSourcePermutationTotal (Equiv.refl (Fin 3)) =
      PackageTotalHom.id finiteWitnessSourcePackage := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · apply SignedExactCoreReadingHom.ext
    · apply Equiv.ext
      intro atom
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

/-- The source adjacent swap as a total endomorphism over identity. -/
noncomputable def indexedCovarianceSourceSwapTotal :
    PackageTotalHom finiteWitnessSourcePackage finiteWitnessSourcePackage :=
  indexedCovarianceSourcePermutationTotal (Equiv.swap (0 : Fin 3) 1)

/-- The source adjacent swap is involutive. -/
theorem indexedCovarianceSourceSwapTotal_square :
    indexedCovarianceSourceSwapTotal.comp indexedCovarianceSourceSwapTotal =
      PackageTotalHom.id finiteWitnessSourcePackage := by
  rw [indexedCovarianceSourceSwapTotal,
    indexedCovarianceSourcePermutationTotal_comp]
  rw [show (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 0 1) =
      Equiv.refl (Fin 3) by
    apply Equiv.ext
    intro axis
    fin_cases axis <;> rfl]
  exact indexedCovarianceSourcePermutationTotal_refl

/-- The source adjacent swap as a package-fiber automorphism. -/
noncomputable def indexedCovarianceSourceSwap :
    PackageFiberAut finiteWitnessSourcePackage :=
  ⟨{ hom := indexedCovarianceSourceSwapTotal
     inv := indexedCovarianceSourceSwapTotal
     hom_inv_id := indexedCovarianceSourceSwapTotal_square
     inv_hom_id := indexedCovarianceSourceSwapTotal_square }, rfl⟩

/-- The source adjacent swap visibly moves axis zero. -/
theorem indexedCovarianceSourceSwap_ne_one :
    indexedCovarianceSourceSwap ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteWitnessSourcePackage =>
      (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) equality
  change (1 : Fin 3) = 0 at axisEquality
  exact Fin.zero_ne_one axisEquality.symm

/-- The source diagnostic-free disk on the finite transport source point. -/
noncomputable def indexedCovarianceDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun _ => packagePoint finiteWitnessSourcePackage
  edge := fun _ => 𝟙 _
  relation := by
    intro cell
    cases cell
    rfl

/-- The target disk generated over the nonidentity finite Atom transport. -/
noncomputable def indexedCovarianceTargetDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun _ => packagePoint finiteWitnessTargetPackage
  edge := fun _ => 𝟙 _
  relation := by
    intro cell
    cases cell
    rfl

/-- The participating indexed hom uses the nonidentity finite Atom transport. -/
noncomputable def indexedCovarianceDiagramHom :
    IndexedBaseDiagramHom indexedCovarianceDiagram
      indexedCovarianceTargetDiagram where
  app := fun _ => finiteWitnessTransportHom.base
  naturality := by
    intro i j edge
    change finiteWitnessTransportHom.base ≫
        𝟙 (packagePoint finiteWitnessTargetPackage) =
      𝟙 (packagePoint finiteWitnessSourcePackage) ≫
        finiteWitnessTransportHom.base
    simp

/-- The participating vertex action has a nonidentity primitive Atom map. -/
theorem indexedCovariance_participatingAction_nonidentity :
    (indexedCovarianceDiagramHom.app indexedCovarianceTargetVertex).doctrineHom.atomEquiv ≠
      Equiv.refl FiniteModel.carrier.Atom := by
  simpa [indexedCovarianceDiagramHom] using
    finiteWitnessTransportHom_atomEquiv_ne_refl

/-- The source disk interpretation with identity edges and adjacent-swap comparator. -/
noncomputable def indexedCovarianceSource :
    IndexedDiagnosticInterpretation indexedCovarianceDiagram where
  package := fun _ => finiteWitnessSourcePackage
  vertexBase := fun _ => rfl
  edgeLift := fun _ => PackageTotalHom.id finiteWitnessSourcePackage
  edgeOver := by
    intro i j edge
    exact CategoryTheory.IsHomLift.id rfl
  edgeStrong := by
    intro i j edge
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 (packagePoint finiteWitnessSourcePackage))
        (Iso.refl finiteWitnessSourcePackage).hom :=
      CategoryTheory.IsHomLift.id rfl
    simpa using CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (packageProjection FiniteModel.carrier)
      (𝟙 (packagePoint finiteWitnessSourcePackage))
      (Iso.refl finiteWitnessSourcePackage)
  comparator := fun _ => indexedCovarianceSourceSwap

/-- The right-edge adjacent swap is the source reselection on the named face. -/
noncomputable def indexedCovarianceSourceReselection :
    IndexedEdgeReselection indexedCovarianceSource :=
  fun _ _ edge => match edge with
    | .left => 1
    | .right => indexedCovarianceSourceSwap

/-- The source reselection is nonidentity on the participating right edge. -/
theorem indexedCovarianceSourceReselection_right_ne_one :
    indexedCovarianceSourceReselection
        SingleDiskVertex.source SingleDiskVertex.target SingleDiskEdge.right ≠ 1 :=
  indexedCovarianceSourceSwap_ne_one

/-- Hence the source reselection family itself is nonidentity. -/
theorem indexedCovarianceSourceReselection_ne_one :
    indexedCovarianceSourceReselection ≠ 1 := by
  intro equality
  exact indexedCovarianceSourceReselection_right_ne_one
    (congrFun (congrFun (congrFun equality SingleDiskVertex.source)
      SingleDiskVertex.target) SingleDiskEdge.right)

/-- The nonidentity source reselection satisfies the named face equation. -/
theorem indexedCovarianceSourceReselection_coherent :
    indexedCovarianceSource.IndexedCoherentAt
      indexedCovarianceSourceReselection := by
  intro cell
  cases cell
  simp [indexedCovarianceShape, indexedCovarianceSource,
    indexedCovarianceSourceReselection,
    IndexedDiagnosticInterpretation.reselectedPathLift,
    IndexedDiagnosticInterpretation.reselectedEdgeLift]
  rw [show PackageFiberAut.hom
      (1 : PackageFiberAut finiteWitnessSourcePackage) =
        PackageTotalHom.id finiteWitnessSourcePackage by rfl]
  have idCompId :
      (PackageTotalHom.id finiteWitnessSourcePackage).comp
          (PackageTotalHom.id finiteWitnessSourcePackage) =
        PackageTotalHom.id finiteWitnessSourcePackage :=
    @Category.comp_id
      (AATCorePackage FiniteModel.carrier)
      (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      finiteWitnessSourcePackage finiteWitnessSourcePackage
      (PackageTotalHom.id finiteWitnessSourcePackage)
  have idCompSwap :
      (PackageTotalHom.id finiteWitnessSourcePackage).comp
          (PackageFiberAut.hom indexedCovarianceSourceSwap) =
        PackageFiberAut.hom indexedCovarianceSourceSwap :=
    @Category.id_comp
      (AATCorePackage FiniteModel.carrier)
      (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      finiteWitnessSourcePackage finiteWitnessSourcePackage
      (PackageFiberAut.hom indexedCovarianceSourceSwap)
  have swapCompId :
      (PackageFiberAut.hom indexedCovarianceSourceSwap).comp
          (PackageTotalHom.id finiteWitnessSourcePackage) =
        PackageFiberAut.hom indexedCovarianceSourceSwap :=
    @Category.comp_id
      (AATCorePackage FiniteModel.carrier)
      (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      finiteWitnessSourcePackage finiteWitnessSourcePackage
      (PackageFiberAut.hom indexedCovarianceSourceSwap)
  rw [idCompId, idCompId, idCompSwap, swapCompId]

/-- The named source diagnostic has an independently defined vanishing obstruction. -/
theorem indexedCovariance_source_obstruction_vanishes :
    TransportObstructionVanishes
      indexedCovarianceSource.toAdmissibleTransportData := by
  rw [transportObstructionVanishes_iff_coherentizable]
  exact ⟨indexedCovarianceSourceReselection,
    (indexedCovarianceSource.indexedCoherentAt_iff_adaptedCoherentAt
      indexedCovarianceSourceReselection).1
      indexedCovarianceSourceReselection_coherent⟩

/-- The initial canonical comparator on the named face is the identity. -/
theorem indexedCovariance_initialCanonicalComparator_eq_one :
    canonicalTwoCellComparator indexedCovarianceSource.toAdmissibleTransportData
        1 indexedCovarianceFace = 1 := by
  let data := indexedCovarianceSource.toAdmissibleTransportData
  let left := TransportCoherence.reselectedPathLift data.lift 1
    (indexedCovarianceLeftPath.toPresentedPath)
  letI : (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      left.base left :=
    TransportCoherence.reselectedPathLift_isStronglyCocartesian
      data.lift 1 indexedCovarianceLeftPath.toPresentedPath
  apply PackageFiberAut.ext_of_strong_fac left
  change
    (TransportCoherence.reselectedPathLift data.lift 1
        indexedCovarianceLeftPath.toPresentedPath).comp
        (PackageFiberAut.hom
          (canonicalTwoCellComparator data 1 indexedCovarianceFace)) =
      (TransportCoherence.reselectedPathLift data.lift 1
        indexedCovarianceLeftPath.toPresentedPath).comp
        (PackageFiberAut.hom 1)
  calc
    _ = TransportCoherence.reselectedPathLift data.lift 1
        indexedCovarianceRightPath.toPresentedPath :=
      canonicalTwoCellComparator_fac data 1 indexedCovarianceFace
    _ = _ := by
      simp [data, indexedCovarianceShape, indexedCovarianceSource,
        indexedCovarianceLeftPath, indexedCovarianceRightPath,
        IndexedBasePath.toPresentedPath,
        TransportCoherence.reselectedPathLift,
        TransportCoherence.reselectLiftData,
        AdmissibleLiftData.pathLift]
      rw [show PackageFiberAut.hom
          (1 : PackageFiberAut finiteWitnessSourcePackage) =
        PackageTotalHom.id finiteWitnessSourcePackage by rfl]
      have idCompId :
          (PackageTotalHom.id finiteWitnessSourcePackage).comp
              (PackageTotalHom.id finiteWitnessSourcePackage) =
            PackageTotalHom.id finiteWitnessSourcePackage :=
        @Category.comp_id
          (AATCorePackage FiniteModel.carrier)
          (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
          finiteWitnessSourcePackage finiteWitnessSourcePackage
          (PackageTotalHom.id finiteWitnessSourcePackage)
      rw [idCompId]
      exact idCompId.symm

/-- The initial raw defect on the named face is the adjacent swap. -/
theorem indexedCovariance_initialRawDefect_eq_swap :
    initialRawDefectCochain indexedCovarianceSource.toAdmissibleTransportData
        indexedCovarianceFace = indexedCovarianceSourceSwap := by
  rw [initialRawDefectCochain, rawDefectCochain, rawTwoCellDefect,
    indexedCovariance_initialCanonicalComparator_eq_one]
  simp [indexedCovarianceSource, indexedCovarianceFace]

/-- The named face has a nonidentity initial raw defect. -/
theorem indexedCovariance_initialRawDefect_ne_one :
    initialRawDefectCochain indexedCovarianceSource.toAdmissibleTransportData
        indexedCovarianceFace ≠ 1 := by
  rw [indexedCovariance_initialRawDefect_eq_swap]
  exact indexedCovarianceSourceSwap_ne_one

/-- The generated endpoint image visibly sends target axis zero to axis one. -/
theorem indexedCovariance_diagnosticVertexLift_eq_transport :
    indexedCovarianceDiagramHom.diagnosticVertexLift indexedCovarianceSource
        indexedCovarianceTargetVertex = finiteWitnessTransportHom := by
  change transportAlongHom finiteWitnessSourcePackage
      ((𝟙 (packagePoint finiteWitnessSourcePackage) ≫
        finiteWitnessTransportHom.base).doctrineHom) =
    finiteWitnessTransportHom
  have identityComp :
      𝟙 (packagePoint finiteWitnessSourcePackage) ≫
          finiteWitnessTransportHom.base = finiteWitnessTransportHom.base :=
    @Category.id_comp
      (ExtractionInstance FiniteModel.carrier)
      (ExtInstHom.extractionInstanceCategory FiniteModel.carrier)
      (packagePoint finiteWitnessSourcePackage)
      (packagePoint finiteWitnessTargetPackage)
      finiteWitnessTransportHom.base
  cases identityComp
  rfl

/-- Axis zero of the concrete generated target package. -/
def indexedCovarianceGeneratedAxisZero :
    ((indexedCovarianceDiagramHom.transportedInterpretation
      indexedCovarianceSource).package
        indexedCovarianceTargetVertex).reading.signatureReading.Axis := by
  change Fin 3
  exact 0

/-- Axis one of the concrete generated target package. -/
def indexedCovarianceGeneratedAxisOne :
    ((indexedCovarianceDiagramHom.transportedInterpretation
      indexedCovarianceSource).package
        indexedCovarianceTargetVertex).reading.signatureReading.Axis := by
  change Fin 3
  exact 1

/-- The generated endpoint image visibly sends target axis zero to axis one. -/
theorem indexedCovariance_generatedAction_axis_zero :
    (PackageFiberAut.hom
      (indexedCovarianceDiagramHom.endpointAction indexedCovarianceSource
        indexedCovarianceTargetVertex indexedCovarianceSourceSwap)).upper.axisMap
          indexedCovarianceGeneratedAxisZero =
        indexedCovarianceGeneratedAxisOne := by
  have fac := indexedCovarianceDiagramHom.diagnosticVertexLift_endpointAction_naturality
    indexedCovarianceSource indexedCovarianceTargetVertex
    indexedCovarianceSourceSwap
  rw [indexedCovariance_diagnosticVertexLift_eq_transport] at fac
  have axisEquality := congrArg
    (fun hom : PackageTotalHom finiteWitnessSourcePackage
        finiteWitnessTargetPackage => hom.upper.axisMap (0 : Fin 3)) fac
  simpa [indexedCovarianceGeneratedAxisZero,
    indexedCovarianceGeneratedAxisOne, indexedCovarianceSourceSwap,
    indexedCovarianceSourceSwapTotal,
    indexedCovarianceSourcePermutationTotal,
    indexedCovarianceSourcePermutationUpper,
    finiteWitnessTransportHom,
    transportAlongHom, transportAlongUpper] using axisEquality

/-- The generated nonidentity action sends the participating swap to a nonidentity image. -/
theorem indexedCovariance_generatedAction_image_ne_one :
    indexedCovarianceDiagramHom.endpointAction indexedCovarianceSource
        indexedCovarianceTargetVertex indexedCovarianceSourceSwap ≠ 1 := by
  intro equality
  have moved := indexedCovariance_generatedAction_axis_zero
  rw [equality] at moved
  change (0 : Fin 3) = 1 at moved
  exact Fin.zero_ne_one moved

/-- The participating action's generated package is the finite transported package. -/
theorem indexedCovariance_generatedPackage_eq_target :
    indexedCovarianceDiagramHom.transportedPackage indexedCovarianceSource
        indexedCovarianceTargetVertex = finiteWitnessTargetPackage := by
  rfl

/-- The package produced by the canonical identity action at the same source fiber. -/
noncomputable def indexedCovarianceIdentityActionPackage :
    AATCorePackage FiniteModel.carrier :=
  ((indexedFiberAction
      (.ofTerm (.identity (packagePoint finiteWitnessSourcePackage)))).obj
        (indexedCovarianceSource.fiberPackage
          indexedCovarianceTargetVertex)).1

/-- The canonical identity action retains the source package family. -/
theorem indexedCovariance_identityActionPackage_family_eq :
    indexedCovarianceIdentityActionPackage.family =
      finiteWitnessSourcePackage.family := by
  rfl

/-- The source package contains the dependency moved by the participating action. -/
theorem indexedCovariance_source_dependsAB_mem :
    finiteWitnessSourcePackage.family.mem
      FiniteModel.FiniteAtom.dependsAB := by
  simpa [finiteWitnessSourcePackage, finiteWitnessSourceReading] using
    finiteTransport_source_dependsAB_mem

/-- The identity-action image retains exclusion of `componentC`. -/
theorem indexedCovariance_identityAction_componentC_not_mem :
    ¬ indexedCovarianceIdentityActionPackage.family.mem
      FiniteModel.FiniteAtom.componentC := by
  rw [indexedCovariance_identityActionPackage_family_eq]
  simpa [finiteWitnessSourcePackage, finiteWitnessSourceReading] using
    finiteTransport_source_componentC_not_mem

/-- The generated action image contains `componentC`. -/
theorem indexedCovariance_generatedAction_componentC_mem :
    (indexedCovarianceDiagramHom.transportedPackage indexedCovarianceSource
      indexedCovarianceTargetVertex).family.mem
        FiniteModel.FiniteAtom.componentC := by
  rw [indexedCovariance_generatedPackage_eq_target, transportAlong_family_eq]
  exact ⟨FiniteModel.FiniteAtom.dependsAB,
    indexedCovariance_source_dependsAB_mem,
    finiteTransportAtomEquiv_dependsAB⟩

/-- A concrete family component separates the generated and identity actions. -/
theorem indexedCovariance_generatedAction_ne_identityAction :
    (indexedCovarianceDiagramHom.transportedPackage indexedCovarianceSource
      indexedCovarianceTargetVertex).family ≠
      indexedCovarianceIdentityActionPackage.family := by
  intro equality
  apply indexedCovariance_identityAction_componentC_not_mem
  rw [← equality]
  exact indexedCovariance_generatedAction_componentC_mem

/-- `(d4)` fires nontrivially on the participating right edge. -/
theorem indexedCovariance_targetReselection_right_ne_one :
    indexedCovarianceDiagramHom.transportedReselection indexedCovarianceSource
        indexedCovarianceSourceReselection SingleDiskVertex.source
          SingleDiskVertex.target SingleDiskEdge.right ≠ 1 := by
  simpa [indexedCovarianceSourceReselection] using
    indexedCovariance_generatedAction_image_ne_one

/-- `(d5)` fires on the same named cell and generated reselection. -/
theorem indexedCovariance_target_coherent :
    (indexedCovarianceDiagramHom.transportedInterpretation
      indexedCovarianceSource).IndexedCoherentAt
        (indexedCovarianceDiagramHom.transportedReselection
          indexedCovarianceSource indexedCovarianceSourceReselection) :=
  indexedCovarianceDiagramHom.indexedCoherentAt_transport
    indexedCovarianceSource indexedCovarianceSourceReselection
    indexedCovarianceSourceReselection_coherent

/-- `(d6)` fires on the same named cell and generated interpretation. -/
theorem indexedCovariance_target_obstruction_vanishes :
    TransportObstructionVanishes
      (indexedCovarianceDiagramHom.transportedInterpretation
        indexedCovarianceSource).toAdmissibleTransportData :=
  indexedCovarianceDiagramHom.indexedTransportObstructionVanishes_transport
    indexedCovarianceSource indexedCovariance_source_obstruction_vanishes

/-- The complete named diagnostic witness required by G-111(g). -/
theorem indexedDiagnosticCovariance_nonvacuous :
    (indexedCovarianceDiagramHom.app
        indexedCovarianceTargetVertex).doctrineHom.atomEquiv ≠
        Equiv.refl FiniteModel.carrier.Atom ∧
      indexedCovarianceLeftPath ≠ indexedCovarianceRightPath ∧
      initialRawDefectCochain
        indexedCovarianceSource.toAdmissibleTransportData indexedCovarianceFace ≠ 1 ∧
      indexedCovarianceSourceReselection ≠ 1 ∧
      indexedCovarianceDiagramHom.transportedReselection indexedCovarianceSource
        indexedCovarianceSourceReselection SingleDiskVertex.source
          SingleDiskVertex.target SingleDiskEdge.right ≠ 1 ∧
      (indexedCovarianceDiagramHom.transportedPackage indexedCovarianceSource
          indexedCovarianceTargetVertex).family ≠
        indexedCovarianceIdentityActionPackage.family ∧
      indexedCovarianceSource.IndexedCoherentAt
        indexedCovarianceSourceReselection ∧
      (indexedCovarianceDiagramHom.transportedInterpretation
        indexedCovarianceSource).IndexedCoherentAt
          (indexedCovarianceDiagramHom.transportedReselection
            indexedCovarianceSource indexedCovarianceSourceReselection) ∧
      TransportObstructionVanishes
        (indexedCovarianceDiagramHom.transportedInterpretation
          indexedCovarianceSource).toAdmissibleTransportData := by
  exact ⟨indexedCovariance_participatingAction_nonidentity,
    indexedCovariance_paths_ne,
    indexedCovariance_initialRawDefect_ne_one,
    indexedCovarianceSourceReselection_ne_one,
    indexedCovariance_targetReselection_right_ne_one,
    indexedCovariance_generatedAction_ne_identityAction,
    indexedCovarianceSourceReselection_coherent,
    indexedCovariance_target_coherent,
    indexedCovariance_target_obstruction_vanishes⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
