import ResearchLean.AG.DiagnosticConservativity.PathSquareDownstreamCompatibility
import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticCovarianceWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCleavageWitnesses

/-!
# G-113 revision 2 base-isomorphism independence and finite nondegeneracy

The diagnostic fiber transport equivalence is generated over every indexed
base component; no `IsIso` premise occurs in its construction.  The finite
witness below makes the independence concrete.  Its base component is the
selective-two arrow, which identifies two distinct source cells and is not an
isomorphism.  A visible target four-axis swap is pulled back by the generated
inverse equivalence and used as both the authored comparator and a nonidentity
reselection on a single disk.  Forward and inverse diagnostic transport then
preserve the nonidentity reselection and raw defect through both round trips.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

local instance finiteNonIsoDiagnosticAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace IndexedBaseDiagramHom

/-- The explicit fiber equivalence exists without a base `IsIso` assumption. -/
theorem indexedDiagnosticTransport_isEquivalence_arbitraryBase
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    (indexedDiagnosticTransportPush hom vertex).IsEquivalence :=
  indexedDiagnosticTransportPush_isEquivalence hom vertex

/-- A base `IsIso` assumption gives the same generated fiber equivalence. -/
theorem indexedDiagnosticTransport_isEquivalence_of_baseIsIso
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) [IsIso (hom.app vertex)] :
    (indexedDiagnosticTransportPush hom vertex).IsEquivalence :=
  hom.indexedDiagnosticTransport_isEquivalence_arbitraryBase vertex

end IndexedBaseDiagramHom

open IndexedBaseDiagramHom

/-! ## Finite non-isomorphic base witness -/

/-- The exact arbitrary-base equivalence on the finite selective-two arrow. -/
noncomputable def finiteNonIsoDiagnosticEquivalence :
    CoreFiber finiteSelectiveTwoToSupportInput.semantic.source ≌
      CoreFiber finiteSelectiveTwoToSupportInput.semantic.target :=
  semanticGlobalTransportEquivalence finiteSelectiveTwoToSupportInput.semantic.hom

/-- The visible target four-axis package. -/
noncomputable abbrev finiteNonIsoDiagnosticTargetObject :
    CoreFiber finiteSelectiveTwoToSupportInput.semantic.target :=
  finiteReindexFourAxisTarget

/-- The target adjacent swap as a package-fiber automorphism. -/
noncomputable def finiteNonIsoDiagnosticTargetSwap :
    PackageFiberAut finiteNonIsoDiagnosticTargetObject.1 :=
  ⟨finiteCleavageAxisPermutationIso finiteReindexAxisSwap, rfl⟩

/-- The visible target adjacent swap is nonidentity. -/
theorem finiteNonIsoDiagnosticTargetSwap_ne_one :
    finiteNonIsoDiagnosticTargetSwap ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteNonIsoDiagnosticTargetObject.1 =>
      (PackageFiberAut.hom automorphism).upper.axisMap finiteReindexAxisZero)
    equality
  change (1 : Fin 4) = 0 at axisEquality
  exact finiteReindexAxisZero_ne_one axisEquality.symm

/-- Pull the target package back along the generated inverse equivalence. -/
noncomputable def finiteNonIsoDiagnosticSourceObject :
    CoreFiber finiteSelectiveTwoToSupportInput.semantic.source :=
  finiteNonIsoDiagnosticEquivalence.inverse.obj finiteNonIsoDiagnosticTargetObject

/-- Pull the visible target swap back along the generated inverse equivalence. -/
noncomputable def finiteNonIsoDiagnosticSourceSwap :
    PackageFiberAut finiteNonIsoDiagnosticSourceObject.1 :=
  (packageFiberAutCoreFiberEquiv finiteNonIsoDiagnosticSourceObject).symm
    (finiteNonIsoDiagnosticEquivalence.inverse.mapIso
      ((packageFiberAutCoreFiberEquiv finiteNonIsoDiagnosticTargetObject)
        finiteNonIsoDiagnosticTargetSwap))

/-- The pulled-back source swap remains nonidentity. -/
theorem finiteNonIsoDiagnosticSourceSwap_ne_one :
    finiteNonIsoDiagnosticSourceSwap ≠ 1 := by
  intro equality
  have coreEquality := congrArg
    (packageFiberAutCoreFiberEquiv finiteNonIsoDiagnosticSourceObject) equality
  have mappedIsoEquality :
      finiteNonIsoDiagnosticEquivalence.inverse.mapIso
          ((packageFiberAutCoreFiberEquiv finiteNonIsoDiagnosticTargetObject)
            finiteNonIsoDiagnosticTargetSwap) =
        Iso.refl finiteNonIsoDiagnosticSourceObject := by
    simpa [finiteNonIsoDiagnosticSourceSwap] using coreEquality
  have mappedHomEquality := congrArg Iso.hom mappedIsoEquality
  letI : finiteNonIsoDiagnosticEquivalence.inverse.Faithful := inferInstance
  have targetHomEquality :
      ((packageFiberAutCoreFiberEquiv finiteNonIsoDiagnosticTargetObject)
        finiteNonIsoDiagnosticTargetSwap).hom =
        𝟙 finiteNonIsoDiagnosticTargetObject := by
    apply finiteNonIsoDiagnosticEquivalence.inverse.map_injective
    simpa using mappedHomEquality
  apply finiteNonIsoDiagnosticTargetSwap_ne_one
  apply (packageFiberAutCoreFiberEquiv finiteNonIsoDiagnosticTargetObject).injective
  apply Iso.ext
  simpa using targetHomEquality

/-- The constant source disk over the selective-two source. -/
noncomputable def finiteNonIsoDiagnosticSourceDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun _ => finiteSelectiveTwoToSupportInput.semantic.source
  edge := fun _ => 𝟙 _
  relation := by intro cell; cases cell; rfl

/-- The constant target disk over the selective-two target. -/
noncomputable def finiteNonIsoDiagnosticTargetDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun _ => finiteSelectiveTwoToSupportInput.semantic.target
  edge := fun _ => 𝟙 _
  relation := by intro cell; cases cell; rfl

/-- The disk hom whose every vertex component is the non-isomorphic base arrow. -/
noncomputable def finiteNonIsoDiagnosticDiagramHom :
    IndexedBaseDiagramHom finiteNonIsoDiagnosticSourceDiagram
      finiteNonIsoDiagnosticTargetDiagram where
  app := fun _ => finiteSelectiveTwoToSupportInput.semantic.hom
  naturality := by
    intro i j edge
    change finiteSelectiveTwoToSupportInput.semantic.hom ≫ 𝟙 _ =
      𝟙 _ ≫ finiteSelectiveTwoToSupportInput.semantic.hom
    simp

/-- Every witness vertex component is genuinely non-isomorphic. -/
theorem finiteNonIsoDiagnosticDiagramHom_not_isIso (vertex) :
    ¬ IsIso (finiteNonIsoDiagnosticDiagramHom.app vertex) := by
  simpa [finiteNonIsoDiagnosticDiagramHom] using
    finiteSelectiveTwoToSupportInput_not_isIso

/-- Its primitive source map visibly identifies two distinct finite cells. -/
theorem finiteNonIsoDiagnosticDiagramHom_identifies_distinct_cells (vertex) :
    finiteSelectiveTwoPoint ≠ finiteSelectiveTwoOther ∧
      (finiteNonIsoDiagnosticDiagramHom.app vertex).doctrineHom.sourceMap
          finiteSelectiveTwoPoint =
        (finiteNonIsoDiagnosticDiagramHom.app vertex).doctrineHom.sourceMap
          finiteSelectiveTwoOther := by
  exact ⟨finiteSelectiveTwoToSupport_source_points_ne,
    finiteSelectiveTwoToSupport_sourceMap_eq⟩

/-- Source interpretation with identity edges and the pulled-back swap comparator. -/
noncomputable def finiteNonIsoDiagnosticSource :
    IndexedDiagnosticInterpretation finiteNonIsoDiagnosticSourceDiagram where
  package := fun _ => finiteNonIsoDiagnosticSourceObject.1
  vertexBase := fun _ => finiteNonIsoDiagnosticSourceObject.2
  edgeLift := fun _ => PackageTotalHom.id finiteNonIsoDiagnosticSourceObject.1
  edgeOver := by
    intro i j edge
    exact CategoryTheory.IsHomLift.id finiteNonIsoDiagnosticSourceObject.2
  edgeStrong := by
    intro i j edge
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 finiteSelectiveTwoToSupportInput.semantic.source)
        (Iso.refl finiteNonIsoDiagnosticSourceObject.1).hom :=
      CategoryTheory.IsHomLift.id finiteNonIsoDiagnosticSourceObject.2
    simpa using CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (packageProjection FiniteModel.carrier)
      (𝟙 finiteSelectiveTwoToSupportInput.semantic.source)
      (Iso.refl finiteNonIsoDiagnosticSourceObject.1)
  comparator := fun _ => finiteNonIsoDiagnosticSourceSwap

/-- The right-edge pulled-back swap gives a nonidentity source reselection. -/
noncomputable def finiteNonIsoDiagnosticSourceReselection :
    IndexedEdgeReselection finiteNonIsoDiagnosticSource :=
  fun _ _ edge => match edge with
    | .left => 1
    | .right => finiteNonIsoDiagnosticSourceSwap

/-- The source reselection is nonidentity. -/
theorem finiteNonIsoDiagnosticSourceReselection_ne_one :
    finiteNonIsoDiagnosticSourceReselection ≠ 1 := by
  intro equality
  have rightEquality := congrFun
    (congrFun (congrFun equality indexedCovarianceSourceVertex)
      indexedCovarianceTargetVertex) indexedCovarianceRightEdge
  exact finiteNonIsoDiagnosticSourceSwap_ne_one rightEquality

/-- The initial canonical comparator on the finite non-isomorphic disk is identity. -/
theorem finiteNonIsoDiagnostic_initialCanonicalComparator_eq_one :
    canonicalTwoCellComparator
        finiteNonIsoDiagnosticSource.toAdmissibleTransportData 1
        indexedCovarianceFace = 1 := by
  let data := finiteNonIsoDiagnosticSource.toAdmissibleTransportData
  let left := TransportCoherence.reselectedPathLift data.lift 1
    indexedCovarianceLeftPath.toPresentedPath
  letI : (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      left.base left :=
    TransportCoherence.reselectedPathLift_isStronglyCocartesian data.lift 1
      indexedCovarianceLeftPath.toPresentedPath
  apply PackageFiberAut.ext_of_strong_fac left
  calc
    left.comp (PackageFiberAut.hom
        (canonicalTwoCellComparator data 1 indexedCovarianceFace)) =
      TransportCoherence.reselectedPathLift data.lift 1
        indexedCovarianceRightPath.toPresentedPath :=
      canonicalTwoCellComparator_fac data 1 indexedCovarianceFace
    _ = left.comp (PackageFiberAut.hom 1) := by
      simp [data, left, finiteNonIsoDiagnosticSource,
        indexedCovarianceLeftPath, indexedCovarianceRightPath,
        indexedCovarianceShape, IndexedBasePath.toPresentedPath,
        TransportCoherence.reselectedPathLift,
        TransportCoherence.reselectLiftData, AdmissibleLiftData.pathLift]
      rw [show PackageFiberAut.hom
          (1 : PackageFiberAut finiteNonIsoDiagnosticSourceObject.1) =
        PackageTotalHom.id finiteNonIsoDiagnosticSourceObject.1 by rfl]
      exact (@Category.comp_id
        (AATCorePackage FiniteModel.carrier)
        (PackageTotalHom.packageTotalCategory FiniteModel.carrier)
        finiteNonIsoDiagnosticSourceObject.1
        finiteNonIsoDiagnosticSourceObject.1
        (PackageTotalHom.id finiteNonIsoDiagnosticSourceObject.1)).symm

/-- The initial raw defect is exactly the pulled-back nonidentity swap. -/
theorem finiteNonIsoDiagnostic_initialRawDefect_eq_swap :
    initialRawDefectCochain
        finiteNonIsoDiagnosticSource.toAdmissibleTransportData
        indexedCovarianceFace = finiteNonIsoDiagnosticSourceSwap := by
  rw [initialRawDefectCochain, rawDefectCochain, rawTwoCellDefect,
    finiteNonIsoDiagnostic_initialCanonicalComparator_eq_one]
  simp [finiteNonIsoDiagnosticSource]

/-- The source initial raw defect is nonidentity. -/
theorem finiteNonIsoDiagnostic_initialRawDefect_ne_one :
    initialRawDefectCochain
        finiteNonIsoDiagnosticSource.toAdmissibleTransportData
        indexedCovarianceFace ≠ 1 := by
  rw [finiteNonIsoDiagnostic_initialRawDefect_eq_swap]
  exact finiteNonIsoDiagnosticSourceSwap_ne_one

/-- The nonidentity source reselection remains nonidentity after transport. -/
theorem finiteNonIsoDiagnostic_transportedReselection_ne_one :
    finiteNonIsoDiagnosticDiagramHom.transportedReselection
        finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection ≠ 1 := by
  intro equality
  apply finiteNonIsoDiagnosticSourceReselection_ne_one
  apply (indexedDiagnosticReselectionEquivalence finiteNonIsoDiagnosticDiagramHom
    finiteNonIsoDiagnosticSource).injective
  rw [indexedDiagnosticReselectionEquivalence_apply]
  calc
    finiteNonIsoDiagnosticDiagramHom.transportedReselection
        finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection = 1 :=
      equality
    _ = indexedDiagnosticReselectionEquivalence
        finiteNonIsoDiagnosticDiagramHom finiteNonIsoDiagnosticSource 1 :=
      (map_one (indexedDiagnosticReselectionEquivalence
        finiteNonIsoDiagnosticDiagramHom finiteNonIsoDiagnosticSource)).symm

/-- The source reselection is recovered after the forward-inverse round trip. -/
theorem finiteNonIsoDiagnostic_sourceReselection_roundTrip :
    finiteNonIsoDiagnosticDiagramHom.inverseTransportedReselection
        finiteNonIsoDiagnosticSource
        (finiteNonIsoDiagnosticDiagramHom.transportedReselection
          finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection) =
      finiteNonIsoDiagnosticSourceReselection :=
  IndexedBaseDiagramHom.inverseTransportedReselection_transportedReselection
    finiteNonIsoDiagnosticDiagramHom finiteNonIsoDiagnosticSource
    finiteNonIsoDiagnosticSourceReselection

/-- The transported reselection is recovered after the inverse-forward round trip. -/
theorem finiteNonIsoDiagnostic_targetReselection_roundTrip :
    finiteNonIsoDiagnosticDiagramHom.transportedReselection
        finiteNonIsoDiagnosticSource
        (finiteNonIsoDiagnosticDiagramHom.inverseTransportedReselection
          finiteNonIsoDiagnosticSource
          (finiteNonIsoDiagnosticDiagramHom.transportedReselection
            finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection)) =
      finiteNonIsoDiagnosticDiagramHom.transportedReselection
        finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection :=
  IndexedBaseDiagramHom.transportedReselection_inverseTransportedReselection
    finiteNonIsoDiagnosticDiagramHom finiteNonIsoDiagnosticSource _

/-- The transported initial raw defect on the named face is nonidentity. -/
theorem finiteNonIsoDiagnostic_transportedInitialRawDefect_ne_one :
    rawDefectCochain
        (finiteNonIsoDiagnosticDiagramHom.transportedInterpretation
          finiteNonIsoDiagnosticSource).toAdmissibleTransportData
        (finiteNonIsoDiagnosticDiagramHom.transportedReselection
          finiteNonIsoDiagnosticSource 1) indexedCovarianceFace ≠ 1 := by
  intro equality
  apply finiteNonIsoDiagnostic_initialRawDefect_ne_one
  have pointwise := congrFun
    (IndexedBaseDiagramHom.indexedDiagnosticDefectCochain_via_horizontalPasting
      finiteNonIsoDiagnosticDiagramHom finiteNonIsoDiagnosticSource 1)
      indexedCovarianceFace
  have mappedOne := map_one
    (indexedDiagnosticEndpointEquivalence finiteNonIsoDiagnosticDiagramHom
      finiteNonIsoDiagnosticSource indexedCovarianceTargetVertex)
  apply (indexedDiagnosticEndpointEquivalence finiteNonIsoDiagnosticDiagramHom
    finiteNonIsoDiagnosticSource indexedCovarianceTargetVertex).injective
  rw [initialRawDefectCochain]
  calc
    _ = rawDefectCochain
        (finiteNonIsoDiagnosticDiagramHom.transportedInterpretation
          finiteNonIsoDiagnosticSource).toAdmissibleTransportData
        (finiteNonIsoDiagnosticDiagramHom.transportedReselection
          finiteNonIsoDiagnosticSource 1) indexedCovarianceFace := by
      simpa [indexedDiagnosticDefectCochainEquivalence_apply,
        indexedCovarianceTargetVertex, indexedCovarianceFace,
        indexedCovarianceShape] using pointwise
    _ = 1 := equality
    _ = _ := mappedOne.symm

/-- The source raw cochain is recovered after its forward-inverse round trip. -/
theorem finiteNonIsoDiagnostic_sourceDefect_roundTrip :
    (indexedDiagnosticDefectCochainEquivalence finiteNonIsoDiagnosticDiagramHom
      finiteNonIsoDiagnosticSource).symm
        (indexedDiagnosticDefectCochainEquivalence finiteNonIsoDiagnosticDiagramHom
          finiteNonIsoDiagnosticSource
          (initialRawDefectCochain
            finiteNonIsoDiagnosticSource.toAdmissibleTransportData)) =
      initialRawDefectCochain
        finiteNonIsoDiagnosticSource.toAdmissibleTransportData :=
  (indexedDiagnosticDefectCochainEquivalence finiteNonIsoDiagnosticDiagramHom
    finiteNonIsoDiagnosticSource).symm_apply_apply _

/-- The transported raw cochain is recovered after its inverse-forward round trip. -/
theorem finiteNonIsoDiagnostic_targetDefect_roundTrip :
    indexedDiagnosticDefectCochainEquivalence finiteNonIsoDiagnosticDiagramHom
        finiteNonIsoDiagnosticSource
        ((indexedDiagnosticDefectCochainEquivalence
          finiteNonIsoDiagnosticDiagramHom finiteNonIsoDiagnosticSource).symm
          (rawDefectCochain
            (finiteNonIsoDiagnosticDiagramHom.transportedInterpretation
              finiteNonIsoDiagnosticSource).toAdmissibleTransportData
            (finiteNonIsoDiagnosticDiagramHom.transportedReselection
              finiteNonIsoDiagnosticSource 1))) =
      rawDefectCochain
        (finiteNonIsoDiagnosticDiagramHom.transportedInterpretation
          finiteNonIsoDiagnosticSource).toAdmissibleTransportData
        (finiteNonIsoDiagnosticDiagramHom.transportedReselection
          finiteNonIsoDiagnosticSource 1) :=
  (indexedDiagnosticDefectCochainEquivalence finiteNonIsoDiagnosticDiagramHom
    finiteNonIsoDiagnosticSource).apply_symm_apply _

/--
The finite counterexample to the converse "fiber equivalence implies base
`IsIso`", including the nonidentity defect and reselection round trips required
for diagnostic nondegeneracy.
-/
structure FiniteNonIsoDiagnosticNondegeneracy : Prop where
  baseNotIso :
    ¬ IsIso (finiteNonIsoDiagnosticDiagramHom.app indexedCovarianceTargetVertex)
  baseIdentifiesDistinctCells :
    finiteSelectiveTwoPoint ≠ finiteSelectiveTwoOther ∧
      (finiteNonIsoDiagnosticDiagramHom.app
        indexedCovarianceTargetVertex).doctrineHom.sourceMap
          finiteSelectiveTwoPoint =
        (finiteNonIsoDiagnosticDiagramHom.app
          indexedCovarianceTargetVertex).doctrineHom.sourceMap
            finiteSelectiveTwoOther
  fiberEquivalence :
    (indexedDiagnosticTransportPush finiteNonIsoDiagnosticDiagramHom
      indexedCovarianceTargetVertex).IsEquivalence
  sourceDefectNonidentity :
    initialRawDefectCochain
        finiteNonIsoDiagnosticSource.toAdmissibleTransportData
        indexedCovarianceFace ≠ 1
  targetDefectNonidentity :
    rawDefectCochain
        (finiteNonIsoDiagnosticDiagramHom.transportedInterpretation
          finiteNonIsoDiagnosticSource).toAdmissibleTransportData
        (finiteNonIsoDiagnosticDiagramHom.transportedReselection
          finiteNonIsoDiagnosticSource 1) indexedCovarianceFace ≠ 1
  sourceDefectRoundTrip :
    (indexedDiagnosticDefectCochainEquivalence finiteNonIsoDiagnosticDiagramHom
      finiteNonIsoDiagnosticSource).symm
        (indexedDiagnosticDefectCochainEquivalence finiteNonIsoDiagnosticDiagramHom
          finiteNonIsoDiagnosticSource
          (initialRawDefectCochain
            finiteNonIsoDiagnosticSource.toAdmissibleTransportData)) =
      initialRawDefectCochain
        finiteNonIsoDiagnosticSource.toAdmissibleTransportData
  targetDefectRoundTrip :
    indexedDiagnosticDefectCochainEquivalence finiteNonIsoDiagnosticDiagramHom
        finiteNonIsoDiagnosticSource
        ((indexedDiagnosticDefectCochainEquivalence
          finiteNonIsoDiagnosticDiagramHom finiteNonIsoDiagnosticSource).symm
          (rawDefectCochain
            (finiteNonIsoDiagnosticDiagramHom.transportedInterpretation
              finiteNonIsoDiagnosticSource).toAdmissibleTransportData
            (finiteNonIsoDiagnosticDiagramHom.transportedReselection
              finiteNonIsoDiagnosticSource 1))) =
      rawDefectCochain
        (finiteNonIsoDiagnosticDiagramHom.transportedInterpretation
          finiteNonIsoDiagnosticSource).toAdmissibleTransportData
        (finiteNonIsoDiagnosticDiagramHom.transportedReselection
          finiteNonIsoDiagnosticSource 1)
  sourceReselectionNonidentity :
    finiteNonIsoDiagnosticSourceReselection ≠ 1
  targetReselectionNonidentity :
    finiteNonIsoDiagnosticDiagramHom.transportedReselection
        finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection ≠ 1
  sourceReselectionRoundTrip :
    finiteNonIsoDiagnosticDiagramHom.inverseTransportedReselection
        finiteNonIsoDiagnosticSource
        (finiteNonIsoDiagnosticDiagramHom.transportedReselection
          finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection) =
      finiteNonIsoDiagnosticSourceReselection
  targetReselectionRoundTrip :
    finiteNonIsoDiagnosticDiagramHom.transportedReselection
        finiteNonIsoDiagnosticSource
        (finiteNonIsoDiagnosticDiagramHom.inverseTransportedReselection
          finiteNonIsoDiagnosticSource
          (finiteNonIsoDiagnosticDiagramHom.transportedReselection
            finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection)) =
      finiteNonIsoDiagnosticDiagramHom.transportedReselection
        finiteNonIsoDiagnosticSource finiteNonIsoDiagnosticSourceReselection

/-- Produce the complete finite non-isomorphic-base nondegeneracy witness. -/
theorem finiteNonIsoDiagnosticNondegeneracy :
    FiniteNonIsoDiagnosticNondegeneracy where
  baseNotIso := finiteNonIsoDiagnosticDiagramHom_not_isIso _
  baseIdentifiesDistinctCells :=
    finiteNonIsoDiagnosticDiagramHom_identifies_distinct_cells _
  fiberEquivalence :=
    IndexedBaseDiagramHom.indexedDiagnosticTransport_isEquivalence_arbitraryBase
      finiteNonIsoDiagnosticDiagramHom _
  sourceDefectNonidentity := finiteNonIsoDiagnostic_initialRawDefect_ne_one
  targetDefectNonidentity :=
    finiteNonIsoDiagnostic_transportedInitialRawDefect_ne_one
  sourceDefectRoundTrip := finiteNonIsoDiagnostic_sourceDefect_roundTrip
  targetDefectRoundTrip := finiteNonIsoDiagnostic_targetDefect_roundTrip
  sourceReselectionNonidentity :=
    finiteNonIsoDiagnosticSourceReselection_ne_one
  targetReselectionNonidentity :=
    finiteNonIsoDiagnostic_transportedReselection_ne_one
  sourceReselectionRoundTrip :=
    finiteNonIsoDiagnostic_sourceReselection_roundTrip
  targetReselectionRoundTrip :=
    finiteNonIsoDiagnostic_targetReselection_roundTrip

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
