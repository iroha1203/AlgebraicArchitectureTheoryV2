import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticCovariance
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparisonWitnesses

/-!
# Named finite firing witness for diagnostic covariance

The finite input is a validated identity Beck--Chevalley square carrying the
single-disk G-106 presentation.  Its source packages and edges lie in the
decoded southwest fiber.  The authored comparator is the reviewed adjacent
axis swap, so the initial raw defect is nonidentity.  The G-106 absorbing
right-edge reselection is itself nonidentity and makes the source coherent;
the two actual Beck--Chevalley functors then generate coherent target
reselections and preserve obstruction vanishing.

Implementation notes: a single-disk diagnostic is used because G-106 proves
its absorbing reselection for arbitrary authored data.  The closed
double-diamond fixture is deliberately not reused: its unequal authored faces
are reviewed evidence of nonvanishing and have no globally coherent
reselection.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

local instance finiteCovarianceAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Fully enumerated single-disk diagnostic code. -/
noncomputable def finiteCovarianceDiagnosticPresentation :
    FiniteDiagnosticPresentation.{0} where
  geometry := singleDiskPresentation FiniteModel.carrier.Atom
  vertexDecidableEq := Classical.decEq _
  edgeDecidableEq := fun _ _ => Classical.decEq _
  twoCellDecidableEq := Classical.decEq _
  threeCellDecidableEq := Classical.decEq _
  vertices := Finset.univ.toList
  vertices_nodup := Finset.nodup_toList _
  vertices_complete := fun vertex => Finset.mem_toList.mpr (Finset.mem_univ vertex)
  edges := fun _ _ => Finset.univ.toList
  edges_nodup := fun _ _ => Finset.nodup_toList _
  edges_complete := fun _ _ edge => Finset.mem_toList.mpr (Finset.mem_univ edge)
  twoCells := Finset.univ.toList
  twoCells_nodup := Finset.nodup_toList _
  twoCells_complete := fun cell => Finset.mem_toList.mpr (Finset.mem_univ cell)
  threeCells := Finset.univ.toList
  threeCells_nodup := Finset.nodup_toList _
  threeCells_complete := fun cell => Finset.mem_toList.mpr (Finset.mem_univ cell)

/-- A validated finite Beck--Chevalley presentation carrying the disk. -/
noncomputable def finiteCovarianceBCPresentation :
    BCPresentation FiniteModel.carrier :=
  bcPresentationOfCospan finiteAuthoredSupportCospan
    finiteCovarianceDiagnosticPresentation

/-- Identity source-fiber edges on the two disk boundaries. -/
noncomputable def finiteCovarianceLiftData :
    AdmissibleLiftData
      (singleDiskPresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier where
  package := fun _ => finiteAxisFoldSupportPackage
  edgeLift := fun _ => PackageTotalHom.id finiteAxisFoldSupportPackage
  edgeStrong := by
    intro i j edge
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 (packagePoint finiteAxisFoldSupportPackage))
        (Iso.refl finiteAxisFoldSupportPackage).hom :=
      CategoryTheory.IsHomLift.id rfl
    simpa using
      (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
        (packageProjection FiniteModel.carrier)
        (𝟙 (packagePoint finiteAxisFoldSupportPackage))
        (Iso.refl finiteAxisFoldSupportPackage))

/-- The unique authored face carries the reviewed nonidentity adjacent swap. -/
noncomputable def finiteCovarianceTransportData :
    AdmissibleTransportData
      (singleDiskPresentation FiniteModel.carrier.Atom)
      FiniteModel.carrier where
  lift := finiteCovarianceLiftData
  twoCellBase := by
    intro cell
    cases cell
    rfl
  comparator := fun _ => finiteAxisFoldSwap

/-- Interpret the finite disk over its decoded Beck--Chevalley square. -/
noncomputable def finiteCovarianceInterpretation :
    BCDiagnosticInterpretation FiniteModel.carrier
      (toSemanticBC finiteCovarianceBCPresentation) where
  data := by
    simpa [finiteCovarianceBCPresentation, bcPresentationOfCospan,
      toSemanticBC, finiteCovarianceDiagnosticPresentation] using
        finiteCovarianceTransportData

/-- The finite disk lies in the decoded southwest source fiber. -/
noncomputable def finiteCovarianceSourceFiberIncidence :
    BCDiagnosticSourceFiberIncidence finiteCovarianceBCPresentation
      finiteCovarianceInterpretation where
  vertexBase := by
    intro vertex
    rfl
  edgeVertical := by
    intro i j edge
    exact CategoryTheory.IsHomLift.id rfl

/-- With identity boundary edges, the generated baseline comparator is the
identity endpoint automorphism. -/
theorem finiteCovariance_canonicalComparator_face_eq_one :
    canonicalTwoCellComparator finiteCovarianceTransportData 1
        SingleDiskTwoCell.face = 1 := by
  let left := reselectedPathLift finiteCovarianceTransportData.lift 1
    (singleDiskLeftPath FiniteModel.carrier.Atom)
  letI : (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      left.base left :=
    reselectedPathLift_isStronglyCocartesian
      finiteCovarianceTransportData.lift 1
      (singleDiskLeftPath FiniteModel.carrier.Atom)
  apply PackageFiberAut.ext_of_strong_fac left
  change
    (reselectedPathLift finiteCovarianceTransportData.lift 1
        (singleDiskLeftPath FiniteModel.carrier.Atom)).comp
        (PackageFiberAut.hom
          (canonicalTwoCellComparator finiteCovarianceTransportData 1
            SingleDiskTwoCell.face)) =
      (reselectedPathLift finiteCovarianceTransportData.lift 1
        (singleDiskLeftPath FiniteModel.carrier.Atom)).comp
        (PackageFiberAut.hom 1)
  calc
    _ = reselectedPathLift finiteCovarianceTransportData.lift 1
        (singleDiskRightPath FiniteModel.carrier.Atom) :=
      canonicalTwoCellComparator_fac finiteCovarianceTransportData 1
        SingleDiskTwoCell.face
    _ = _ := by
      simp [finiteCovarianceTransportData, finiteCovarianceLiftData,
        reselectedPathLift, reselectLiftData, AdmissibleLiftData.pathLift,
        singleDiskLeftPath, singleDiskRightPath]
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

/-- The initial raw defect is exactly the reviewed adjacent swap. -/
theorem finiteCovariance_initialRawDefect_face_eq_swap :
    initialRawDefectCochain finiteCovarianceTransportData
        SingleDiskTwoCell.face = finiteAxisFoldSwap := by
  rw [initialRawDefectCochain, rawDefectCochain, rawTwoCellDefect,
    finiteCovariance_canonicalComparator_face_eq_one]
  simp [finiteCovarianceTransportData]

/-- The adjacent swap remains nonidentity in this source diagnostic. -/
theorem finiteCovariance_initialRawDefect_face_ne_one :
    initialRawDefectCochain finiteCovarianceTransportData
        SingleDiskTwoCell.face ≠ 1 := by
  rw [finiteCovariance_initialRawDefect_face_eq_swap]
  intro equality
  have axisEquality := congrArg
    (fun automorphism : PackageFiberAut finiteAxisFoldSupportPackage =>
      (PackageFiberAut.hom automorphism).upper.axisMap (0 : Fin 3)) equality
  change (1 : Fin 3) = 0 at axisEquality
  exact Fin.zero_ne_one axisEquality.symm

/-- The source reselection is generated by the G-106 disk absorption theorem. -/
noncomputable def finiteCovarianceSourceReselection :
    EdgeReselection finiteCovarianceSourceFiberIncidence.toFiberwise.toLiftData :=
  singleDiskAbsorbingReselection
    finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData

/-- The source-fiber reconstruction has the same nonidentity initial defect. -/
theorem finiteCovariance_sourceFiber_initialRawDefect_face_ne_one :
    initialRawDefectCochain
        finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData
        SingleDiskTwoCell.face ≠ 1 := by
  rw [toFiberwise_toTransportData_eq finiteCovarianceSourceFiberIncidence]
  exact finiteCovariance_initialRawDefect_face_ne_one

/-- The absorbing right-edge reselection is not the identity reselection. -/
theorem finiteCovarianceSourceReselection_ne_one :
    finiteCovarianceSourceReselection ≠ 1 := by
  intro equality
  have rightEquality := congrArg
    (fun reselection : EdgeReselection
        finiteCovarianceSourceFiberIncidence.toFiberwise.toLiftData =>
      reselection SingleDiskVertex.source SingleDiskVertex.target
        SingleDiskEdge.right) equality
  change initialRawDefectCochain
      finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData
      SingleDiskTwoCell.face = 1 at rightEquality
  exact finiteCovariance_sourceFiber_initialRawDefect_face_ne_one rightEquality

/-- The nonidentity source reselection is coherent on the unique authored face. -/
theorem finiteCovarianceSourceReselection_coherent :
    CoherentAt finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData
      finiteCovarianceSourceReselection :=
  singleDisk_coherentAt_absorbingReselection
    finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData

/-- The same source firing proves ordinary source obstruction vanishing. -/
theorem finiteCovariance_source_obstruction_vanishes :
    TransportObstructionVanishes finiteCovarianceInterpretation.data := by
  rw [← toFiberwise_toTransportData_eq finiteCovarianceSourceFiberIncidence]
  exact (transportObstructionVanishes_iff_coherentizable _).2
    ⟨finiteCovarianceSourceReselection,
      finiteCovarianceSourceReselection_coherent⟩

/-- `(d5)` fires on the mapped reselection along the direct actual route. -/
theorem finiteCovariance_direct_target_coherent :
    CoherentAt
      (bcDiagnosticDirectTransportedInterpretationData
        finiteCovarianceBCPresentation finiteCovarianceInterpretation
        finiteCovarianceSourceFiberIncidence)
      (bcDiagnosticDirectMapEdgeReselection finiteCovarianceBCPresentation
        finiteCovarianceInterpretation finiteCovarianceSourceFiberIncidence
        finiteCovarianceSourceReselection) :=
  bcDiagnosticDirectCoherentAt_map finiteCovarianceBCPresentation
    finiteCovarianceInterpretation finiteCovarianceSourceFiberIncidence
    finiteCovarianceSourceReselection
    finiteCovarianceSourceReselection_coherent

/-- `(d5)` fires on the mapped reselection along the via-base actual route. -/
theorem finiteCovariance_viaBase_target_coherent :
    CoherentAt
      (bcDiagnosticViaBaseTransportedInterpretationData
        finiteCovarianceBCPresentation finiteCovarianceInterpretation
        finiteCovarianceSourceFiberIncidence)
      (bcDiagnosticViaBaseMapEdgeReselection finiteCovarianceBCPresentation
        finiteCovarianceInterpretation finiteCovarianceSourceFiberIncidence
        finiteCovarianceSourceReselection) :=
  bcDiagnosticViaBaseCoherentAt_map finiteCovarianceBCPresentation
    finiteCovarianceInterpretation finiteCovarianceSourceFiberIncidence
    finiteCovarianceSourceReselection
    finiteCovarianceSourceReselection_coherent

/-- `(d6)` fires on the same finite input along the direct actual route. -/
theorem finiteCovariance_direct_target_obstruction_vanishes :
    TransportObstructionVanishes
      (bcDiagnosticDirectTransportedInterpretationData
        finiteCovarianceBCPresentation finiteCovarianceInterpretation
        finiteCovarianceSourceFiberIncidence) :=
  bcDiagnosticDirectTransportObstructionVanishes
    finiteCovarianceBCPresentation finiteCovarianceInterpretation
    finiteCovarianceSourceFiberIncidence
    finiteCovariance_source_obstruction_vanishes

/-- `(d6)` fires on the same finite input along the via-base actual route. -/
theorem finiteCovariance_viaBase_target_obstruction_vanishes :
    TransportObstructionVanishes
      (bcDiagnosticViaBaseTransportedInterpretationData
        finiteCovarianceBCPresentation finiteCovarianceInterpretation
        finiteCovarianceSourceFiberIncidence) :=
  bcDiagnosticViaBaseTransportObstructionVanishes
    finiteCovarianceBCPresentation finiteCovarianceInterpretation
    finiteCovarianceSourceFiberIncidence
    finiteCovariance_source_obstruction_vanishes

/-- Named finite nonvacuity for G-110(D): one validated input simultaneously
has a nonidentity initial defect, a nonidentity coherent source reselection,
coherent mapped reselections on both actual routes, and both `(d6)` vanishing
conclusions. -/
theorem finiteDiagnosticCovariance_nonvacuous :
    initialRawDefectCochain
        finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData
        SingleDiskTwoCell.face ≠ 1 ∧
      finiteCovarianceSourceReselection ≠ 1 ∧
      CoherentAt
        finiteCovarianceSourceFiberIncidence.toFiberwise.toTransportData
        finiteCovarianceSourceReselection ∧
      CoherentAt
        (bcDiagnosticDirectTransportedInterpretationData
          finiteCovarianceBCPresentation finiteCovarianceInterpretation
          finiteCovarianceSourceFiberIncidence)
        (bcDiagnosticDirectMapEdgeReselection finiteCovarianceBCPresentation
          finiteCovarianceInterpretation finiteCovarianceSourceFiberIncidence
          finiteCovarianceSourceReselection) ∧
      CoherentAt
        (bcDiagnosticViaBaseTransportedInterpretationData
          finiteCovarianceBCPresentation finiteCovarianceInterpretation
          finiteCovarianceSourceFiberIncidence)
        (bcDiagnosticViaBaseMapEdgeReselection finiteCovarianceBCPresentation
          finiteCovarianceInterpretation finiteCovarianceSourceFiberIncidence
          finiteCovarianceSourceReselection) ∧
      TransportObstructionVanishes
        (bcDiagnosticDirectTransportedInterpretationData
          finiteCovarianceBCPresentation finiteCovarianceInterpretation
          finiteCovarianceSourceFiberIncidence) ∧
      TransportObstructionVanishes
        (bcDiagnosticViaBaseTransportedInterpretationData
          finiteCovarianceBCPresentation finiteCovarianceInterpretation
          finiteCovarianceSourceFiberIncidence) := by
  exact ⟨finiteCovariance_sourceFiber_initialRawDefect_face_ne_one,
    finiteCovarianceSourceReselection_ne_one,
    finiteCovarianceSourceReselection_coherent,
    finiteCovariance_direct_target_coherent,
    finiteCovariance_viaBase_target_coherent,
    finiteCovariance_direct_target_obstruction_vanishes,
    finiteCovariance_viaBase_target_obstruction_vanishes⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
