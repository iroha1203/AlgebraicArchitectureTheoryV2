import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticVanishing
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticCovarianceWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPairwiseAxisFoldWitnesses

/-!
# Named nontrivial witness for indexed diagnostic covariance

This module supplies the G-111 diagnostic witness portfolio.  The named cell
`indexedCovarianceFace` fills two syntactically distinct parallel edges in a
connected two-vertex diagram.  Its authored comparator, initial raw defect,
source reselection, and generated target endpoint image are all nonidentity.
The same source reselection is coherent, and the Cycle 14 `(d5)` and `(d6)`
theorems fire on its generated image.

This witness is independent of the non-epi coherent positive required by K5;
its vertex indices are identities and no non-epi causality is claimed.
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

/-- The constant diagnostic-free disk diagram on the finite support package point. -/
noncomputable def indexedCovarianceDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun _ => packagePoint finiteAxisFoldSupportPackage
  edge := fun _ => 𝟙 _
  relation := by
    intro cell
    cases cell
    rfl

/-- The identity indexed diagram hom on the named disk. -/
noncomputable def indexedCovarianceDiagramHom :
    IndexedBaseDiagramHom indexedCovarianceDiagram indexedCovarianceDiagram where
  app := fun _ => 𝟙 _
  naturality := by simp

/-- The source disk interpretation with identity edges and adjacent-swap comparator. -/
noncomputable def indexedCovarianceSource :
    IndexedDiagnosticInterpretation indexedCovarianceDiagram where
  package := fun _ => finiteAxisFoldSupportPackage
  vertexBase := fun _ => rfl
  edgeLift := fun _ => PackageTotalHom.id finiteAxisFoldSupportPackage
  edgeOver := by
    intro i j edge
    exact CategoryTheory.IsHomLift.id rfl
  edgeStrong := by
    intro i j edge
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 (packagePoint finiteAxisFoldSupportPackage))
        (Iso.refl finiteAxisFoldSupportPackage).hom :=
      CategoryTheory.IsHomLift.id rfl
    simpa using CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (packageProjection FiniteModel.carrier)
      (𝟙 (packagePoint finiteAxisFoldSupportPackage))
      (Iso.refl finiteAxisFoldSupportPackage)
  comparator := fun _ => finiteAxisFoldSwap

/-- The right-edge adjacent swap is the source reselection on the named face. -/
noncomputable def indexedCovarianceSourceReselection :
    IndexedEdgeReselection indexedCovarianceSource :=
  fun _ _ edge => match edge with
    | .left => 1
    | .right => finiteAxisFoldSwap

/-- The source reselection is nonidentity on the participating right edge. -/
theorem indexedCovarianceSourceReselection_right_ne_one :
    indexedCovarianceSourceReselection
        SingleDiskVertex.source SingleDiskVertex.target SingleDiskEdge.right ≠ 1 :=
  finiteAxisFoldSwap_ne_one

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
      (1 : PackageFiberAut finiteAxisFoldSupportPackage) =
        PackageTotalHom.id finiteAxisFoldSupportPackage by rfl]
  have idCompId :
      (PackageTotalHom.id finiteAxisFoldSupportPackage).comp
          (PackageTotalHom.id finiteAxisFoldSupportPackage) =
        PackageTotalHom.id finiteAxisFoldSupportPackage :=
    @Category.comp_id
      (AATCorePackage FiniteModel.carrier)
      (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage
      (PackageTotalHom.id finiteAxisFoldSupportPackage)
  have idCompSwap :
      (PackageTotalHom.id finiteAxisFoldSupportPackage).comp
          (PackageFiberAut.hom finiteAxisFoldSwap) =
        PackageFiberAut.hom finiteAxisFoldSwap :=
    @Category.id_comp
      (AATCorePackage FiniteModel.carrier)
      (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage
      (PackageFiberAut.hom finiteAxisFoldSwap)
  have swapCompId :
      (PackageFiberAut.hom finiteAxisFoldSwap).comp
          (PackageTotalHom.id finiteAxisFoldSupportPackage) =
        PackageFiberAut.hom finiteAxisFoldSwap :=
    @Category.comp_id
      (AATCorePackage FiniteModel.carrier)
      (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage
      (PackageFiberAut.hom finiteAxisFoldSwap)
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
          (1 : PackageFiberAut finiteAxisFoldSupportPackage) =
        PackageTotalHom.id finiteAxisFoldSupportPackage by rfl]
      have idCompId :
          (PackageTotalHom.id finiteAxisFoldSupportPackage).comp
              (PackageTotalHom.id finiteAxisFoldSupportPackage) =
            PackageTotalHom.id finiteAxisFoldSupportPackage :=
        @Category.comp_id
          (AATCorePackage FiniteModel.carrier)
          (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
          finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage
          (PackageTotalHom.id finiteAxisFoldSupportPackage)
      rw [idCompId]
      exact idCompId.symm

/-- The initial raw defect on the named face is the adjacent swap. -/
theorem indexedCovariance_initialRawDefect_eq_swap :
    initialRawDefectCochain indexedCovarianceSource.toAdmissibleTransportData
        indexedCovarianceFace = finiteAxisFoldSwap := by
  rw [initialRawDefectCochain, rawDefectCochain, rawTwoCellDefect,
    indexedCovariance_initialCanonicalComparator_eq_one]
  simp [indexedCovarianceSource, indexedCovarianceFace]

/-- The named face has a nonidentity initial raw defect. -/
theorem indexedCovariance_initialRawDefect_ne_one :
    initialRawDefectCochain indexedCovarianceSource.toAdmissibleTransportData
        indexedCovarianceFace ≠ 1 := by
  rw [indexedCovariance_initialRawDefect_eq_swap]
  exact finiteAxisFoldSwap_ne_one

/-- The generated identity-index action sends the participating swap to a nonidentity image. -/
theorem indexedCovariance_generatedAction_image_ne_one :
    indexedCovarianceDiagramHom.endpointAction indexedCovarianceSource
        SingleDiskVertex.target finiteAxisFoldSwap ≠ 1 := by
  intro equality
  have comparison := coreFiberFunctorPackageAutHom_iso_naturality
    (indexedFiberIdentityComparison
      (packagePoint finiteAxisFoldSupportPackage))
    (indexedCovarianceSource.fiberPackage SingleDiskVertex.target)
    finiteAxisFoldSwap
  change packageFiberAutMulEquivOfCoreFiberIso _
      (indexedCovarianceDiagramHom.endpointAction indexedCovarianceSource
        SingleDiskVertex.target finiteAxisFoldSwap) = _ at comparison
  rw [equality, map_one] at comparison
  have coreIdentity :
      packageFiberAutCoreFiberEquiv
          (indexedCovarianceSource.fiberPackage indexedCovarianceTargetVertex)
          finiteAxisFoldSwap = 1 := by
    simpa using comparison.symm
  have sourceIdentity : finiteAxisFoldSwap = 1 :=
    (packageFiberAutCoreFiberEquiv
      (indexedCovarianceSource.fiberPackage indexedCovarianceTargetVertex)).injective
      (by simpa using coreIdentity)
  exact finiteAxisFoldSwap_ne_one sourceIdentity

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
    indexedCovarianceLeftPath ≠ indexedCovarianceRightPath ∧
      initialRawDefectCochain
        indexedCovarianceSource.toAdmissibleTransportData indexedCovarianceFace ≠ 1 ∧
      indexedCovarianceSourceReselection ≠ 1 ∧
      indexedCovarianceDiagramHom.transportedReselection indexedCovarianceSource
        indexedCovarianceSourceReselection SingleDiskVertex.source
          SingleDiskVertex.target SingleDiskEdge.right ≠ 1 ∧
      indexedCovarianceSource.IndexedCoherentAt
        indexedCovarianceSourceReselection ∧
      (indexedCovarianceDiagramHom.transportedInterpretation
        indexedCovarianceSource).IndexedCoherentAt
          (indexedCovarianceDiagramHom.transportedReselection
            indexedCovarianceSource indexedCovarianceSourceReselection) ∧
      TransportObstructionVanishes
        (indexedCovarianceDiagramHom.transportedInterpretation
          indexedCovarianceSource).toAdmissibleTransportData := by
  exact ⟨indexedCovariance_paths_ne,
    indexedCovariance_initialRawDefect_ne_one,
    indexedCovarianceSourceReselection_ne_one,
    indexedCovariance_targetReselection_right_ne_one,
    indexedCovarianceSourceReselection_coherent,
    indexedCovariance_target_coherent,
    indexedCovariance_target_obstruction_vanishes⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
